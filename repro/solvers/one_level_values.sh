#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
MS=("$@"); [ ${#MS[@]} -eq 0 ] && MS=(4 5 6 7 8 9 10)
T=$(mktemp -d)
g++ -O2 -std=c++17 -o "$T/a" one_level_solver_a.cpp
g++ -O2 -std=c++17 -o "$T/b" one_level_solver_b.cpp
V=(0 0 0 0 3 4 4 5 6 6 7 7)
for m in "${MS[@]}"; do
  v=${V[$m]}
  surv=$("$T/a" "$m" "$v" min -nm -tt 24 | head -1)
  forc=$("$T/a" "$m" "$((v - 1))" min -nm -tt 24 | head -1)
  echo "A: $surv"; echo "A: $forc"
  echo "$surv" | grep -q "adversary_forces_$((v + 1))=0"
  echo "$forc" | grep -q "adversary_forces_${v}=1"
done
for m in "${MS[@]}"; do
  [ "$m" -ge 9 ] || continue
  v=${V[$m]}
  forc=$("$T/b" "$m" "$((v - 1))" min | head -1)
  echo "B: $forc"
  echo "$forc" | grep -q "adversary_forces_${v}=1"
done
rm -rf "$T"
if [ $# -eq 0 ]; then
  echo "one_level_values OK: V(4..10) = 3 4 4 5 6 6 7; V(11) = 7 by monotonicity and the m = 11 certificate"
else
  echo "one_level_values OK for m = $*"
fi
