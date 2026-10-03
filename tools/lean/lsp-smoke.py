#!/usr/bin/env python3
"""Exercise the installed MCP in a prepared workspace within a 15-second deadline."""
import argparse
import asyncio
import json
from pathlib import Path
import sys
import time
import psutil

from mcp.client.session import ClientSession
from mcp.client.stdio import StdioServerParameters, stdio_client


async def smoke(workspace):
    from lsp import TOOLS
    probe = workspace / "LspSmoke.lean"
    if probe.exists():
        raise ValueError(f"Probe already exists: {probe}")
    probe.write_text("import OneShot\nexample (n : Nat) : n = n := by\n  rfl\n"
                     "#check Ash.OneShot.TypeArgument\nexample : True := by\n  exact False.intro\n")
    started = time.monotonic()
    peak_rss = 0
    async def sample_resources():
        nonlocal peak_rss
        process = psutil.Process()
        while True:
            rss = 0
            for item in [process, *process.children(recursive=True)]:
                try:
                    rss += item.memory_info().rss
                except psutil.NoSuchProcess:
                    pass
            peak_rss = max(peak_rss, rss)
            await asyncio.sleep(0.1)
    monitor = asyncio.create_task(sample_resources())
    parameters = StdioServerParameters(command=sys.executable,
        args=[str(Path(__file__).with_name("lsp.py")), "serve", "--workspace", str(workspace)])
    try:
        async with stdio_client(parameters) as (reader, writer):
            async with ClientSession(reader, writer) as session:
                await session.initialize()
                tools = {tool.name for tool in (await session.list_tools()).tools}
                assert tools == TOOLS, tools
                requests = [
                    ("lean_goal", {"file_path": probe.name, "line": 3, "column": 3, "timeout_s": 5}),
                    ("lean_hover_info", {"file_path": probe.name, "line": 4, "column": 26}),
                    ("lean_diagnostic_messages", {"file_path": probe.name, "timeout_s": 5}),
                ]
                for name, arguments in requests:
                    result = await session.call_tool(name, arguments)
                    assert not result.is_error, result
                    data = json.loads(result.content[0].text)
                    if name == "lean_goal":
                        assert data["status"] == "goals" and "⊢ n = n" in data["goals"][0], data
                    elif name == "lean_hover_info":
                        assert data["symbol"] == "Ash.OneShot.TypeArgument", data
                    else:
                        assert not data["partial"] and not data["failed_dependencies"], data
                        assert any(item["severity"] == "error" and "False.intro" in item["message"]
                                   for item in data["items"]), data
                    print(json.dumps({"tool": name, "arguments": arguments, "result": data}), flush=True)
        print(json.dumps({"wall_seconds": time.monotonic() - started, "tools": sorted(tools),
                          "sampled_process_tree_peak_rss_bytes": peak_rss}))
    finally:
        monitor.cancel()
        try:
            await monitor
        except asyncio.CancelledError:
            pass
        probe.unlink()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    args = parser.parse_args()
    asyncio.run(asyncio.wait_for(smoke(args.workspace.resolve()), timeout=15))
