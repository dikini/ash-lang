"""Exercise scheduling and reuse with actual pinned Lean compilations."""
import hashlib
import importlib.util
import json
from pathlib import Path
import runpy
import subprocess
import tempfile
import unittest
import sys
from unittest.mock import patch


SCRIPT = Path(__file__).with_name("module_build.py")
LEAN = Path(subprocess.check_output(["elan", "which", "lean"], text=True).strip())


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class ModuleBuildTests(unittest.TestCase):
    def setUp(self):
        self.assertTrue(SCRIPT.exists(), "module receipt/scheduler implementation is missing")
        spec = importlib.util.spec_from_file_location("module_build", SCRIPT)
        self.runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.runner)
        # Model an idle host for deterministic scheduling tests. The real
        # compiler inputs are tiny (<1 GiB combined in the two-job test), and
        # actual MemAvailable still gates launches. Test host occupancy below.
        inventory = patch.object(self.runner, "external_compiler_count", return_value=0)
        inventory.start()
        self.addCleanup(inventory.stop)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.store = self.root / "store"
        self.sources = {
            "Alpha": "def alpha : Nat := 1\n#print axioms alpha\n",
            "Beta": "import Alpha\ndef beta : Nat := alpha + 1\n#print axioms beta\n",
            "Gamma": "def gamma : Nat := 3\n#print axioms gamma\n",
        }
        self.imports = {"Alpha": [], "Beta": ["Alpha"], "Gamma": []}
        self.reports = {"Alpha": ["alpha"], "Beta": ["beta"], "Gamma": ["gamma"]}
        self.round = 0

    def build(self, **extra):
        self.round += 1
        cache = self.root / ("cache" + str(self.round))
        cache.mkdir()
        for name, text in self.sources.items():
            (self.source / (name + ".lean")).write_text(text)
        return self.runner.build(
            snapshot=self.source, cache=cache, store=self.store,
            modules=list(self.sources), imports=self.imports, reports=self.reports,
            source_hashes={n: digest(self.source / (n + ".lean")) for n in self.sources},
            compiler=LEAN, libraries={str(LEAN): digest(LEAN)},
            host_lock=self.root / "host.lock", headroom_mb=0,
            **extra,
        )

    def test_repeated_build_reuses_every_valid_success(self):
        first = self.build()
        self.assertEqual(first["status"], "complete")
        self.assertTrue(all(not r["cache_hit"] for r in first["records"].values()))
        second = self.build()
        self.assertTrue(all(r["cache_hit"] for r in second["records"].values()))
        self.assertGreater(first["records"]["Alpha"]["peak_rss_kib"], 0)

    def test_failure_blocks_consumers_but_retains_independent_success(self):
        self.sources["Alpha"] = "def alpha : Nat := missingName\n#print axioms alpha\n"
        failed = self.build(jobs=2)
        self.assertEqual(failed["status"], "failed")
        self.assertEqual(failed["blocked"], ["Beta"])
        self.assertEqual(set(failed["records"]), {"Gamma"})
        self.sources["Alpha"] = "def alpha : Nat := 1\n#print axioms alpha\n"
        retry = self.build()
        self.assertEqual(retry["status"], "complete")
        self.assertTrue(retry["records"]["Gamma"]["cache_hit"])
        self.assertFalse(retry["records"]["Alpha"]["cache_hit"])

    def test_source_and_selected_import_change_invalidate_consumers(self):
        self.build()
        self.sources["Alpha"] = "def alpha : Nat := 2\n#print axioms alpha\n"
        changed = self.build()
        self.assertFalse(changed["records"]["Alpha"]["cache_hit"])
        self.assertFalse(changed["records"]["Beta"]["cache_hit"])
        self.assertTrue(changed["records"]["Gamma"]["cache_hit"])

    def test_option_changes_invalidate_receipts(self):
        self.build()
        changed = self.build(memory_mb=2048)
        self.assertFalse(any(r["cache_hit"] for r in changed["records"].values()))

    def test_corrupted_artifact_is_recompiled(self):
        first = self.build()
        artifact = Path(first["records"]["Alpha"]["receipt"]).parent / "module.olean"
        artifact.write_bytes(b"broken")
        retry = self.build()
        self.assertEqual(retry["status"], "complete")
        self.assertFalse(retry["records"]["Alpha"]["cache_hit"])

    def test_axiom_report_and_warning_failures_are_not_cached(self):
        for text, reports in [
            ("axiom alpha : Nat\n#print axioms alpha\n", ["alpha"]),
            ("def alpha : Nat := 1\n#print axioms alpha\n", ["wrong"]),
            ("theorem alpha : True := by sorry\n#print axioms alpha\n", ["alpha"]),
        ]:
            with self.subTest(text=text):
                self.sources["Alpha"] = text
                self.reports["Alpha"] = reports
                result = self.build()
                self.assertEqual(result["status"], "failed")
                self.assertNotIn("Alpha", result["records"])

    def test_dependency_order_and_resource_bounds(self):
        result = self.build(jobs=2)
        self.assertEqual(result["status"], "complete")
        self.assertLessEqual(result["max_running"], 2)
        self.assertGreaterEqual(result["records"]["Beta"]["started_at"],
                                result["records"]["Alpha"]["finished_at"])
        with self.assertRaises(ValueError):
            self.build(jobs=3)

    def test_insufficient_memory_does_not_start_a_compiler(self):
        result = self.build(memory_mb=10**9)
        self.assertEqual(result["status"], "resource_blocked")
        self.assertEqual(result["max_running"], 0)

    def test_unmanaged_compilers_prevent_another_launch(self):
        self.assertTrue(hasattr(self.runner, "external_compiler_count"),
                        "scheduler must account for other host compilers")
        with patch.object(self.runner, "external_compiler_count", return_value=2):
            result = self.build()
        self.assertEqual(result["status"], "resource_blocked")
        self.assertEqual(result["max_running"], 0)

    def test_failure_propagates_with_arbitrary_registration_order(self):
        self.sources = {"Delta": "import Beta\ndef delta := beta\n#print axioms delta\n",
                        "Beta": self.sources["Beta"],
                        "Alpha": "def alpha : Nat := missingName\n#print axioms alpha\n"}
        self.imports["Delta"] = ["Beta"]
        self.reports["Delta"] = ["delta"]
        result = self.build()
        self.assertEqual(result["status"], "failed")
        self.assertEqual(set(result["blocked"]), {"Beta", "Delta"})

    def test_cached_log_rechecked_after_its_hash_is_updated(self):
        first = self.build()
        receipt = Path(first["records"]["Alpha"]["receipt"])
        log = receipt.parent / "module.log"
        log.write_text(log.read_text() + "warning: untrusted receipt log\n")
        data = json.loads(receipt.read_text())
        data["log_sha256"] = digest(log)
        receipt.write_text(json.dumps(data))
        retry = self.build()
        self.assertFalse(retry["records"]["Alpha"]["cache_hit"])

    def test_inventory_counts_elaboration_without_output_option(self):
        proc = self.root / "proc"
        proc.mkdir()
        for pid, args in enumerate((b"lean\0LargeProof.lean\0",
                                    b"lean\0-oLargeProof.olean\0LargeProof.lean\0",
                                    b"lean\0--deps\0SmallProof.lean\0"), 100):
            process = proc / str(pid)
            process.mkdir()
            (process / "comm").write_text("lean\n")
            (process / "status").write_text("State:\tS (sleeping)\nPPid:\t999999\n")
            (process / "cmdline").write_bytes(args)
        native_path = Path
        def paths(value):
            return proc if value == "/proc" else native_path(value)
        # Restore the real inventory while redirecting only its filesystem root.
        spec = importlib.util.spec_from_file_location("native_inventory", SCRIPT)
        native = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(native)
        with patch.object(native, "Path", side_effect=paths):
            self.assertEqual(native.external_compiler_count(), 2)

    def test_integration_freshness_flag_distinguishes_receipt_reuse(self):
        baseline = self.build()
        work = self.root / "work"
        live = work / "docs/design/direct-effects/one-shot"
        live.mkdir(parents=True)
        script = ('#!/usr/bin/env bash\n'
                  'lean -DwarningAsError=true -o "$proof_build_dir/Alpha.olean" Alpha.lean\n')
        (live / "check.sh").write_text(script)
        (live / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
        (live / "Alpha.lean").write_text(self.sources["Alpha"])
        subprocess.run(["git", "init", "-q", str(work)], check=True)
        subprocess.run(["git", "add", "."], cwd=work, check=True)
        subprocess.run(["git", "-c", "user.name=Tooling tests", "-c", "user.email=tests@example.invalid",
                        "-c", "commit.gpgSign=false", "commit", "-qm", "fixture"], cwd=work, check=True)
        old = baseline["records"]["Alpha"]
        parent = {"registered_order": ["Alpha"], "imports": {"Alpha": []},
                  "manifest": {p.name: digest(p) for p in live.iterdir()},
                  "version": subprocess.check_output([str(LEAN), "--version"], text=True).strip(),
                  "compiler_library_hashes": {str(LEAN): digest(LEAN)},
                  "cache": old["origin_lean_path"], "records": {"Alpha": {
                      **old, "source_sha256": digest(live / "Alpha.lean"),
                      "direct_import_artifacts": {}}}}
        parent_path = self.root / "parent.json"
        parent_path.write_text(json.dumps(parent))
        patch_source = self.root / "Alpha-patch.lean"
        patch_source.write_text(self.sources["Alpha"] + "-- comment-only delta\n")
        review = self.root / "review.json"
        review.write_text('{"scope": "comment-only fixture"}\n')
        config = {"worktree": str(work),
                  "parent_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=work, text=True).strip(),
                  "compiler": str(LEAN), "parent_evidence": str(parent_path),
                  "parent_evidence_sha256": digest(parent_path), "new_registered_order": [],
                  "module_cache": str(self.store), "headroom_mb": 0,
                  "components": [{"name": "fixture", "root_verified_review_pass": True,
                      "checkpoint": str(review), "checkpoint_sha256": digest(review),
                      "review": str(review), "review_sha256": digest(review), "sources": [{
                          "module": "Alpha", "source": str(patch_source),
                          "source_sha256": digest(patch_source), "reports": ["alpha"]}]}]}
        results = []
        for label in ("first", "retry"):
            prefix = self.root / label
            config["output_prefix"] = str(prefix)
            config_path = self.root / (label + ".json")
            config_path.write_text(json.dumps(config))
            with patch.dict(sys.modules, {"module_build": self.runner}), \
                    patch.object(sys, "argv", ["integrate.py", str(config_path)]):
                runpy.run_path(str(SCRIPT.with_name("integrate.py")), run_name="__main__")
            results.append(json.loads(Path(str(prefix) + "-evidence.json").read_text()))
        self.assertTrue(results[0]["all_modules_fresh"])
        self.assertFalse(results[1]["all_modules_fresh"])
        self.assertEqual(results[1]["module_scheduler"]["cache_hits"], 1)


if __name__ == "__main__":
    unittest.main()
