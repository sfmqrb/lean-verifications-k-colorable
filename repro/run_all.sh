#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
for s in check_posets check_sizes check_thresholds_uniform uniform_tower exhaustive static_sat flow_adversary simulate_adversary \
         oblivious_examples li_recursion; do
  echo "== $s"
  python3 "$s.py"
done
echo "== oblivious_dp (Appendix C and the table of Appendix D.5)"
python3 oblivious_dp.py paper
echo "== oblivious_dp_second (independent implementation, R = 1..7)"
python3 oblivious_dp_second.py 4 7
echo "== top_block (Theorem D.4)"
for K in 4 5 6 7; do python3 top_block_first.py "$K" stair | tail -1; done
for K in 4 5 6; do for s in $(seq 1 $((K - 1))); do python3 top_block_any.py "$K" "$s" | tail -1; done; done
echo "== one-level values V(m) (Appendix D.3)"
solvers/one_level_values.sh
echo "== certificates"
certificates/check_all.sh
echo "ALL CHECKS PASSED"
