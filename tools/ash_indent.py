#!/usr/bin/env python3
"""Indent Ash source with four spaces without changing tokens or line breaks.

This is a layout helper, not an Ash parser. It also accepts rejection fixtures.
Quoted experimental literals and comment-like rejection inputs are preserved.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re


def indent_source(source: str) -> str:
    """Indent blocks, grouped continuations and multiline type alternatives."""
    output: list[str] = []
    stack: list[str] = []
    quoted = False
    escaped = False
    alternatives = False
    for line in source.splitlines(keepends=True):
        # Never alter the contents of a multiline literal.
        literal_line = quoted
        body = line.lstrip(" \t")
        visible: list[str] = []
        for char in body:
            if quoted:
                visible.append(" ")
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    quoted = False
            elif char == '"':
                quoted = True
                visible.append(" ")
            else:
                visible.append(char)
        code = "".join(visible).split("//", 1)[0]
        closing = re.match(r"^[})\]\s]*", code).group()
        line_stack = stack.copy()
        for char in closing:
            if char in "})]" and line_stack:
                expected = {"}": "{", ")": "(", "]": "["}[char]
                if line_stack[-1] == expected:
                    line_stack.pop()
        depth = line_stack.count("{")
        if line_stack and line_stack[-1] != "{":
            depth += 1
        if not stack and body.strip():
            if re.match(r"(?:pub\s+)?(?:type|newtype)\b", code):
                alternatives = code.rstrip().endswith("=")
            elif code.startswith("|"):
                depth += 1
            elif alternatives:
                depth += 1
                alternatives = False
        output.append(line if literal_line or not body.strip() else " " * (4 * depth) + body)
        for char in code:
            if char in "{([":
                stack.append(char)
            elif char in "})]" and stack:
                expected = {"}": "{", ")": "(", "]": "["}[char]
                if stack[-1] == expected:
                    stack.pop()
    return "".join(output)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    changed = []
    for path in args.paths:
        original = path.read_bytes().decode("utf-8")
        formatted = indent_source(original)
        if formatted != original:
            changed.append(str(path))
            if not args.check:
                path.write_bytes(formatted.encode("utf-8"))
    if args.check and changed:
        parser.exit(1, "\n".join(changed) + "\n")
    print(f"{len(changed)} Ash files {'need indentation' if args.check else 'reindented'}")


if __name__ == "__main__":
    main()
