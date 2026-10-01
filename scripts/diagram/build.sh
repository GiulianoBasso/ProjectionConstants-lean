#!/usr/bin/env bash
# Regenerate diagram/dependency-tree.html from the compiled library.
# Run from anywhere after `lake build`.
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p .lake/diagram
lake env lean --run scripts/DepGraph.lean .lake/diagram/depgraph.json
python3 scripts/diagram/make_tree.py
python3 scripts/diagram/build_page.py
