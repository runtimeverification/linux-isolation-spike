#!/usr/bin/env python3
"""Sanity-check INVENTORY.md line citations against the kernel tree.

For every table row of the form  | `symbol` | `path/file.c` | 123 |
open the file at that line and look for the symbol within a window.
Reports MISS for anything not found.
"""
import re, sys, os

INV  = os.path.expanduser("~/linux-isolation/INVENTORY.md")
TREE = os.path.expanduser("~/linux-full")
WINDOW = 4          # lines of slack above and below

row = re.compile(r'^\|(?P<sym>[^|]+)\|(?P<file>[^|]+)\|(?P<lines>[^|]+)\|\s*$')
tick = re.compile(r'`([^`]+)`')
ident = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')

def idents(cell):
    """Identifiers worth searching for, longest first."""
    names = []
    for m in tick.finditer(cell):
        names += ident.findall(m.group(1))
    if not names:
        names = ident.findall(cell)
    names = [n for n in names if len(n) > 3]
    return sorted(set(names), key=len, reverse=True)

def filepath(cell):
    m = tick.search(cell)
    raw = (m.group(1) if m else cell).strip()
    return raw if re.search(r'\.(c|h)$', raw) else None

def firstlines(cell):
    """Every bare number in the lines cell; ranges count as their start."""
    return [int(n) for n in re.findall(r'\d+', cell)]

cache = {}
def lines_of(path):
    if path not in cache:
        full = os.path.join(TREE, path)
        if not os.path.exists(full):
            cache[path] = None
        else:
            cache[path] = open(full, errors="replace").read().splitlines()
    return cache[path]

checked = hits = misses = 0
report = []

for raw in open(INV, errors="replace"):
    m = row.match(raw.rstrip("\n"))
    if not m:
        continue
    path = filepath(m.group("file"))
    if not path:
        continue
    names = idents(m.group("sym"))
    if not names:
        continue
    body = lines_of(path)
    if body is None:
        report.append(f"NOFILE {path}  ({m.group('sym').strip()})")
        misses += 1
        continue
    for ln in firstlines(m.group("lines")):
        checked += 1
        lo = max(0, ln - 1 - WINDOW)
        hi = min(len(body), ln + WINDOW)
        window = "\n".join(body[lo:hi])
        if any(n in window for n in names):
            hits += 1
        else:
            misses += 1
            actual = body[ln-1].strip() if 0 < ln <= len(body) else "<past EOF>"
            report.append(
                f"MISS  {path}:{ln}\n"
                f"      expected one of: {', '.join(names[:4])}\n"
                f"      line reads:      {actual[:100]}"
            )

print("\n".join(report))
print(f"\nchecked {checked} citations: {hits} ok, {misses} suspicious")
sys.exit(1 if misses else 0)