"""Exercise actual pinned upstream routing with every client start mocked."""
import asyncio
import inspect
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import AsyncMock, patch

from lean_lsp_mcp import client_utils, server
import lsp


class WorkspaceRoutingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.workspace = self.root / "prepared"
        self.external = self.root / "external"
        self.nested = self.workspace / "nested"
        for project in (self.workspace, self.external, self.nested):
            project.mkdir(parents=True)
            (project / "lean-toolchain").write_text(lsp.TOOLCHAIN)
            (project / "lakefile.toml").write_text(lsp.LAKEFILE)
            (project / "Proof.lean").write_text("example : True := by trivial\n")
        self.context = SimpleNamespace(request_context=SimpleNamespace(lifespan_context=
            SimpleNamespace(lean_project_path=self.workspace, project_switching_allowed=True,
                            active_transport="stdio", project_cache={}, client=None)))
        for module, names in ((client_utils, ("bind_lean_project_path", "resolve_file_path",
                "infer_project_path", "_project_switching_allowed", "_MAX_SHARED_CLIENTS", "_start_client")),
                (server, ("_project_switching_allowed",))):
            for name in names:
                original = getattr(module, name)
                self.addCleanup(setattr, module, name, original)
        lsp.install_workspace_guard(self.workspace, client_utils, server)
        self.start = AsyncMock()
        patcher = patch.object(client_utils, "startup_client", self.start)
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_external_absolute_traversal_and_symlink_tool_requests(self):
        (self.workspace / "escape.lean").symlink_to(self.external / "Proof.lean")
        paths = (str(self.external / "Proof.lean"), "../external/Proof.lean", "escape.lean",
                 "nested/Proof.lean")
        for path in paths:
            with self.subTest(path=path):
                with self.assertRaises(ValueError):
                    asyncio.run(client_utils.require_client_for_file(self.context, path))
                self.start.assert_not_awaited()
                self.assertEqual(self.workspace, self.context.request_context.lifespan_context.lean_project_path)

    def test_all_exposed_file_tools_reject_external_workspace(self):
        exercised = set()
        for module in (server._diagnostic_tools, server._goal_tools, server._navigation_tools):
            for function in vars(module).values():
                definition = getattr(function, "__lean_lsp_mcp_tool__", None)
                if definition is None or definition.name not in lsp.TOOLS:
                    continue
                parameters = inspect.signature(function).parameters
                arguments = {"file_path": str(self.external / "Proof.lean")}
                if "symbol" in parameters:
                    arguments["symbol"] = "True"
                for position in ("line", "column"):
                    if position in parameters:
                        arguments[position] = 1
                with self.subTest(tool=definition.name):
                    with self.assertRaises(ValueError):
                        asyncio.run(function(self.context, **arguments))
                    self.start.assert_not_awaited()
                exercised.add(definition.name)
        self.assertEqual(lsp.TOOLS, exercised)

    def test_external_inference_binding_and_factory_rejected(self):
        with self.assertRaises(ValueError):
            client_utils.infer_project_path(str(self.external / "Proof.lean"), self.context)
        with self.assertRaises(ValueError):
            client_utils.bind_lean_project_path(self.context, self.external)
        with patch.object(lsp, "bounded_client", new_callable=AsyncMock) as factory:
            with self.assertRaises(ValueError):
                asyncio.run(client_utils._start_client(self.external))
            factory.assert_not_awaited()
        with self.assertRaises(ValueError):
            asyncio.run(lsp.bounded_client(self.external, self.workspace))
        self.start.assert_not_awaited()

    def test_relative_and_absolute_prepared_file_route_to_same_project(self):
        # Avoid stdlib discovery: it is unrelated to guarded routing and invokes lean --print-prefix.
        policy = SimpleNamespace(contains=lambda path: True,
                                 client_relative_path=lambda path: "Proof.lean")
        with patch.object(client_utils, "build_lean_path_policy", return_value=policy):
            for path in ("Proof.lean", str(self.workspace / "Proof.lean")):
                self.assertEqual("Proof.lean", asyncio.run(client_utils.require_client_for_file(self.context, path)))
        self.assertEqual(2, self.start.await_count)
        self.assertFalse(client_utils._project_switching_allowed(self.context))
        self.assertFalse(server._project_switching_allowed())
        self.assertEqual(1, client_utils._MAX_SHARED_CLIENTS)

    def test_configuration_is_rechecked_before_start_and_restart(self):
        lsp.check_workspace_configuration(self.workspace)
        client = SimpleNamespace(start=AsyncMock())
        with patch("leanclient.aio.AsyncLeanLSPClient", return_value=client) as constructor:
            asyncio.run(client_utils._start_client(self.workspace))
            command = constructor.call_args.kwargs["server_command"]
            self.assertEqual(["lake", "-f", "lakefile.toml", "serve"], command[:4])
            for name in ("lakefile.toml", "lean-toolchain"):
                path = self.workspace / name
                original = path.read_text()
                path.write_text("changed after initial client start")
                constructor.reset_mock()
                with self.subTest(config=name):
                    with self.assertRaisesRegex(ValueError, "targets changed"):
                        asyncio.run(client_utils._start_client(self.workspace))
                    constructor.assert_not_called()
                path.write_text(original)

    def test_duplicate_lake_config_and_dangling_symlink_rejected(self):
        alternative = self.workspace / "lakefile.lean"
        for dangling in (False, True):
            if dangling:
                alternative.symlink_to(self.root / "absent")
            else:
                alternative.write_text("import Lake\nopen Lake DSL\npackage unsafe")
            with patch("leanclient.aio.AsyncLeanLSPClient") as constructor:
                with self.subTest(dangling=dangling):
                    with self.assertRaisesRegex(ValueError, "must not contain lakefile.lean"):
                        lsp.check_workspace_configuration(self.workspace)
                    with self.assertRaisesRegex(ValueError, "must not contain lakefile.lean"):
                        asyncio.run(client_utils._start_client(self.workspace))
                    constructor.assert_not_called()
            alternative.unlink()

    def test_foreign_bound_context_is_rejected(self):
        self.context.request_context.lifespan_context.lean_project_path = self.external
        with self.assertRaises(ValueError):
            asyncio.run(client_utils.require_client_for_file(self.context, "Proof.lean"))
        self.start.assert_not_awaited()


if __name__ == "__main__":
    unittest.main()
