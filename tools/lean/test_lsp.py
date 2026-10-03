"""Pin checks use synthetic files; no compiler or language server starts here."""
import json
from pathlib import Path
import tempfile
import unittest

import lsp


class PinTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name, text in {"A.lean": "import Std\ndef a := 1\n", "B.lean": "import A\ndef b := a\n",
                           "A.olean": "artifact-a", "B.olean": "artifact-b", "A.log": "ok", "B.log": "ok",
                           "lean": "compiler"}.items():
            (self.root / name).write_text(text)
        self.data = {"cwd": str(self.root), "lean_path": str(self.root),
                     "version": "Lean (version 4.33.1, pinned)",
                     "compiler_library_hashes": {str(self.root / "lean"): lsp.digest(self.root / "lean")},
                     "manifest": {}, "records": {}, "imports": {"A": [], "B": ["A"]},
                     "selected_external_artifacts": {}}
        for name in ("A", "B"):
            source_pin, artifact_pin, log_pin = [lsp.digest(self.root / f"{name}.{ext}")
                                                 for ext in ("lean", "olean", "log")]
            self.data["manifest"][f"{name}.lean"] = source_pin
            self.data["records"][name] = {"source_sha256": source_pin, "artifact_sha256": artifact_pin,
                "log": str(self.root / f"{name}.log"), "log_sha256": log_pin,
                "direct_import_artifacts": {dep: lsp.digest(self.root / f"{dep}.olean")
                                            for dep in self.data["imports"][name]}}
            self.data["selected_external_artifacts"][name] = {
                "selected_path": str(self.root / f"{name}.olean"), "olean_sha256": artifact_pin}
        self.evidence = self.root / "evidence.json"
        self.save()

    def save(self):
        self.evidence.write_text(json.dumps(self.data))

    def test_import_closure_and_isolation(self):
        output = self.root / "workspace"
        lsp.prepare(self.evidence, output, ["B"])
        self.assertEqual(["A", "B"], json.loads((output / "lsp-receipt.json").read_text())["modules"])
        self.assertEqual("artifact-a", (output / "imports/A.olean").read_text())
        (output / "imports/A.olean").write_text("local-change")
        self.assertEqual("artifact-a", (self.root / "A.olean").read_text())
        self.assertNotIn("lean_lib", (output / "lakefile.toml").read_text())

    def test_changed_pins_fail_before_workspace_creation(self):
        for filename in ("A.lean", "A.olean", "A.log", "lean"):
            with self.subTest(filename=filename):
                path = self.root / filename
                original = path.read_bytes()
                path.write_bytes(b"changed")
                with self.assertRaisesRegex(ValueError, "Pin mismatch"):
                    lsp.prepare(self.evidence, self.root / "unused", ["B"])
                self.assertFalse((self.root / "unused").exists())
                path.write_bytes(original)

    def test_selected_import_pin_mismatch(self):
        self.data["records"]["B"]["direct_import_artifacts"]["A"] = "wrong"
        self.save()
        with self.assertRaisesRegex(ValueError, "Direct import artifact mismatch"):
            lsp.validate(self.evidence, ["B"])

    def test_import_graph_disagrees_with_source(self):
        self.data["imports"]["B"] = []
        self.save()
        with self.assertRaisesRegex(ValueError, "Import mismatch"):
            lsp.validate(self.evidence, ["B"])

    def test_wrong_toolchain_and_module_path_rejected(self):
        for module in ("../A", "A.B"):
            with self.assertRaisesRegex(ValueError, "Invalid module"):
                lsp.validate(self.evidence, [module])
        self.data["version"] = "Lean (version 4.34.0, other)"
        self.save()
        with self.assertRaisesRegex(ValueError, "Expected pinned Lean"):
            lsp.validate(self.evidence, ["B"])

    def test_existing_workspace_is_preserved(self):
        output = self.root / "workspace"
        output.mkdir()
        (output / "note").write_text("keep")
        with self.assertRaisesRegex(ValueError, "already exists"):
            lsp.prepare(self.evidence, output, ["B"])
        self.assertEqual("keep", (output / "note").read_text())


if __name__ == "__main__":
    unittest.main()
