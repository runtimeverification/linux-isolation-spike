#!/usr/bin/env bash
# Wire this Lean project to the ALREADY-BUILT Aeneas backend and its mathlib,
# with no network access and without writing into that checkout.
#
# Why this exists: `lake build` on its own re-resolves the transitive git
# dependencies (mathlib, batteries, aesop, ...) into this project's own
# .lake/packages and starts a fresh mathlib4 clone + build. The pinned Aeneas
# checkout at ~/aeneas-project/aeneas already has all of them built against
# Lean v4.31.0, so we point at those instead. LAKE_PACKAGES_DIR is NOT honoured
# by lake v4.31.0 for this, hence the symlinks.
set -euo pipefail

AB="${AENEAS_LEAN_BACKEND:-$HOME/aeneas-project/aeneas/backends/lean}"
[ -d "$AB/.lake/build/lib/lean" ] || {
    echo "error: $AB is not built. Set AENEAS_LEAN_BACKEND or build it first." >&2
    exit 1
}

here="$(cd "$(dirname "$0")" && pwd)"
cd "$here"

# 1. Symlink the already-built dependency packages into our package store.
rm -rf .lake/packages
mkdir -p .lake/packages
for p in "$AB"/.lake/packages/*/; do
    ln -sfn "$(realpath "$p")" ".lake/packages/$(basename "$p")"
done

# 2. Seed the manifest from Aeneas' own (same revs) and add aeneas itself as a
#    path dependency. The absolute path is machine-specific, which is exactly
#    why the manifest is generated here rather than committed.
python3 - "$AB" <<'PY'
import json, sys
ab = sys.argv[1]
d = json.load(open(f"{ab}/lake-manifest.json"))
d["name"] = "uidmap_verif"
for x in d["packages"]:
    x["inherited"] = True
d["packages"].insert(0, {
    "type": "path", "scope": "", "name": "aeneas",
    "manifestFile": "lake-manifest.json", "inherited": False,
    "dir": ab, "configFile": "lakefile.lean",
})
json.dump(d, open("lake-manifest.json", "w"), indent=2)
PY

echo "ok: run 'lake build' (expect ~1700 replayed jobs, Uidmap built in seconds)"
