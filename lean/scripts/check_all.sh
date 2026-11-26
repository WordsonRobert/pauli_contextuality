#!/bin/bash
# Fast module-by-module check against an EXISTING built Mathlib v4.31.0 checkout
# (useful when this project's own .lake lives on a slow disk).
#   MATHLIB_PROJ=/path/to/a/lake/project/with/built/mathlib ./scripts/check_all.sh
# MATHLIB_PROJ must be a lake project whose Mathlib is tag v4.31.0 and already built.
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
MP=${MATHLIB_PROJ:?set MATHLIB_PROJ to a lake project with a built Mathlib v4.31.0}
OUT=${OUT:-/tmp/pauli_ctx_olean}
TC=~/.elan/toolchains/leanprover--lean4---v4.31.0/bin
export PATH=$TC:$PATH
mkdir -p "$OUT/PauliData" "$OUT/PauliContextuality"
LP=$(cd "$MP" && lake env printenv LEAN_PATH):$OUT
# 1. native data module
lean --root="$ROOT" -o "$OUT/PauliData/Qm7Data.olean" -i "$OUT/PauliData/Qm7Data.ilean" \
  -c "$OUT/PauliData/Qm7Data.c" "$ROOT/PauliData/Qm7Data.lean" || exit 1
leanc -c -O3 -fPIC -DLEAN_EXPORTING -o "$OUT/PauliData/Qm7Data.o" "$OUT/PauliData/Qm7Data.c" &&
  leanc -shared -o "$OUT/PauliData/libQm7Data.so" "$OUT/PauliData/Qm7Data.o" || exit 1
echo "OK PauliData.Qm7Data (native)"
# data of the 5-qubit configuration X_496 (core only; evaluated by the interpreter)
lean --root="$ROOT" -o "$OUT/PauliData/Flat5Data.olean" -i "$OUT/PauliData/Flat5Data.ilean" \
  "$ROOT/PauliData/Flat5Data.lean" || exit 1
echo "OK PauliData.Flat5Data"
# 2. the library, in dependency order
for m in Basic Config Cover Bounds CycleSign Invariance Qminus Hardness PauliMatrix \
         Spectral SpectralConfig QminusBridge SpectralW SpectralExact Cone NegLines Transfer \
         Packing Profile GeoBounds ThreeQubit Tensor Gadget ToE3 HardMain NoDeletion Tractable \
         Quadrics5 GadgetModel Realize RealizeDeg PhaseStates \
         Density Game QuantumGame Tight TightExamples TightConverse GaugeKernel Chain Den3 Section \
         Intrinsic SectionCor ConeQuad QuadType ConeSub TangentQuad \
         Audit; do
  if LEAN_PATH=$LP lean --root="$ROOT" --load-dynlib="$OUT/PauliData/libQm7Data.so" \
      -o "$OUT/PauliContextuality/$m.olean" -i "$OUT/PauliContextuality/$m.ilean" \
      "$ROOT/PauliContextuality/$m.lean" > "$OUT/$m.log" 2>&1 && ! grep -q "sorry" "$OUT/$m.log"; then
    echo "OK $m"
  else
    echo "FAIL $m (see $OUT/$m.log)"; exit 1
  fi
done
grep -h "FAIL\|OK   " "$OUT/Audit.log" | sed 's/^.*info: //' > "$OUT/audit_summary.txt"
if grep -q "FAIL" "$OUT/Audit.log"; then echo "AXIOM AUDIT FAILED"; exit 1; fi
echo "axiom audit: $(grep -c "OK   " "$OUT/Audit.log") theorems OK (see $OUT/audit_summary.txt)"
echo "all modules compiled, no sorry"
