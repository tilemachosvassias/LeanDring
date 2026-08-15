#!/bin/bash
# Fast text-based pre-flight lint (no elaboration, seconds — safe before a rebuild).
# Runs Mathlib's lint-style executable on the whole project and filters two
# Mathlib-policy classes we deliberately do not follow:
#   - unicode allowlist (Ĝ, ⟺ are intentional mathematical notation here)
#   - UpperCamelCase module names (generated chunk modules use `_2` suffixes;
#     renaming them would churn files, imports, mapping.tsv and compile.sh)
# NOTE: pass the four umbrella modules explicitly — `lint-style LeanDring`
# (the root module) silently lints nothing.
set -u
cd "$(dirname "$0")/.."
out=$(taskset -c 0 lake exe lint-style \
  LeanDring.Theory LeanDring.P4 LeanDring.P5 LeanDring.MainResults LeanDring.CertificateAnchors 2>&1 \
  | grep -v "unicode character that is not on the allowlist" \
  | grep -v "othersInMathlib" \
  | grep -v "is not in 'UpperCamelCase'" \
  | grep -v "^error: found .* style error")
if [ -n "$out" ]; then
  echo "$out"
  echo "text-lint: FINDINGS (see above)"
  exit 1
fi
echo "text-lint: clean"
