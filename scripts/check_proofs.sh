#!/usr/bin/env bash
# Reproducible verification for MeaningDimension.
#   1. reject forbidden proof-faking constructs in project sources;
#   2. build the library and the specification tests;
#   3. audit the axioms of every MeaningDimension declaration;
#   4. record the environment (commit SHAs, toolchain).
# Logs go to logs/. Exit status is non-zero on any failure.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p logs

echo "== 1. forbidden constructs"
if grep -rnE '\bsorry\b|\badmit\b|^[[:space:]]*(private |protected )?axiom\b|native_decide|\bunsafe\b|implemented_by|@\[extern' \
     --include='*.lean' MeaningDimension Tests MeaningDimension.lean; then
  echo "FAIL: forbidden construct found" >&2
  exit 1
fi
echo "none"

echo "== 2. lake build"
lake build 2>&1 | tee logs/build.log
grep -q "Build completed successfully" logs/build.log

echo "== 3. axiom audit"
lake env lean Tests/AxiomAudit.lean 2>&1 | tee logs/axioms.log
grep -q "AXIOM AUDIT OK" logs/axioms.log

echo "== 4. environment"
{
  echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "project commit: $(git rev-parse --verify -q HEAD || echo uncommitted)"
  echo "project dirty: $(git status --porcelain 2>/dev/null | wc -l | tr -d ' ') files"
  echo "lean: $(lake env lean --version)"
  echo "lean-toolchain: $(cat lean-toolchain)"
  python3 -c "import json; m=json.load(open('lake-manifest.json')); [print(f\"{p['name']}: {p['rev']}\") for p in m['packages']]"
} | tee logs/env.txt
echo "ALL CHECKS PASSED"
