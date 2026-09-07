#!/usr/bin/env python3
"""Triage the suspicious citations from check_citations.py.

For each citation the window check did not confirm, find the function that
actually encloses the cited line and classify it:

  RANGE_END  the number is the end of a span, not a definition line
  IN_BODY    the line sits inside the function the table names
  REVIEW     it does not; open this one by hand
"""
import re, os

INV  = os.path.expanduser("~/linux-isolation/INVENTORY.md")
TREE = os.path.expanduser("~/linux-full")
WINDOW = 4

row   = re.compile(r'^\|(?P<sym>[^|]+)\|(?P<file>[^|]+)\|(?P<lines>[^|]+)\|\s*$')
tick  = re.compile(r'`([^`]+)`')
ident = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')
fname = re.compile(r'([A-Za-z_][A-Za-z0-9_]*)\s*\(')

def idents(cell):
    names = []
    for m in tick.finditer(cell):
        names += ident.findall(m.group(1))
    if not names:
        names = ident.findall(cell)
    return sorted({n for n in names if len(n) > 3}, key=len, reverse=True)

def filepath(cell):
    m = tick.search(cell)
    raw = (m.group(1) if m else cell).strip()
    return raw if re.search(r'\.(c|h)$', raw) else None

cache = {}
def lines_of(path):
    if path not in cache:
        full = os.path.join(TREE, path)
        cache[path] = open(full, errors="replace").read().splitlines() \
                      if os.path.exists(full) else None
    return cache[path]

def enclosing(body, ln):
    """Name of the function containing line `ln`, kernel C brace style."""
    i = ln - 1
    while i >= 0 and body[i] != "{":
        if body[i].startswith("}"):      # we are at file scope
            return None
        i -= 1
    if i < 0:
        return None
    header, j = [], i - 1
    while j >= 0 and body[j].strip() and not body[j].rstrip().endswith(";") \
          and len(header) < 6:
        header.insert(0, body[j]); j -= 1
    m = fname.findall(" ".join(header))
    return m[0] if m else None

out = []
for raw in open(INV, errors="replace"):
    m = row.match(raw.rstrip("\n"))
    if not m: continue
    path  = filepath(m.group("file"))
    names = idents(m.group("sym"))
    if not path or not names: continue
    body = lines_of(path)
    if body is None: continue

    nums = [int(n) for n in re.findall(r'\d+', m.group("lines"))]
    for pos, ln in enumerate(nums):
        lo, hi = max(0, ln-1-WINDOW), min(len(body), ln+WINDOW)
        if any(n in "\n".join(body[lo:hi]) for n in names):
            continue                                   # window check passed
        if pos > 0:
            verdict = "RANGE_END"
            enc = enclosing(body, ln) or "-"
        else:
            enc = enclosing(body, ln)
            verdict = "IN_BODY" if enc and any(n == enc for n in names) \
                      else ("IN_BODY" if enc and any(n in enc or enc in n
                                                     for n in names) else "REVIEW")
        text = body[ln-1].strip() if 0 < ln <= len(body) else "<past EOF>"
        out.append((verdict, path, ln, names[0], enc or "?", text[:78]))

order = {"REVIEW": 0, "IN_BODY": 1, "RANGE_END": 2}
for v, p, ln, want, got, text in sorted(out, key=lambda r: order[r[0]]):
    print(f"{v:<10} {p}:{ln}")
    print(f"           table says : {want}")
    print(f"           really in  : {got}")
    print(f"           line       : {text}\n")

print({k: sum(1 for r in out if r[0] == k) for k in order})