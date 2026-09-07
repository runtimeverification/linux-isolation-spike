#!/usr/bin/env bash
# Axiom audit. Prints the axiom dependencies of every top-level result.
# Expected: [propext, Classical.choice, Quot.sound] and nothing else.
# A fourth axiom -- in particular sorryAx -- is a stop-and-report.
set -euo pipefail
cd "$(cd "$(dirname "$0")" && pwd)"
lake env lean AxiomAudit.lean
