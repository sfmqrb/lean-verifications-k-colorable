#!/bin/bash
set -e
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
for f in dag_k*_C*.gen.txt; do python3 check_adversary_dag.py "$f"; done
g++ -O2 -std=c++17 -o /tmp/check_one_level.$$ check_one_level.cpp
for f in one_m*_ALG.txt one_m*_ADV.txt; do /tmp/check_one_level.$$ "$f"; done
rm -f /tmp/check_one_level.$$
