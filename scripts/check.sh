#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
python3 scripts/check-palomar.py --check-dependencies
lake env lean scripts/CheckAxioms.lean
