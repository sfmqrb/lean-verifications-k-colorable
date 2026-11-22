# Reproduction material

The programs and certificates behind the computer-assisted values of the paper. The Lean library does not depend
on them: it contains the certificates as data and checks them in the kernel.

- `*.py`: one program per check. Each asserts its results and prints `... OK`.
- `certificates/`: the adversary strategies behind Proposition B.4 (`dag_k*_C*.gen.txt`) and the one-level
  certificates of Appendix D.3 (`one_m*_C*_ALG.txt`, `one_m*_C*_ADV.txt`), with two checkers. `check_all.sh`
  verifies the checksums and replays every certificate.
- `solvers/`: two solvers for the one-level values `V(m)`. `one_level_values.sh` runs them.
- `expected_output.txt`: the output of `./run_all.sh`.

`./run_all.sh` runs everything in 30 to 60 minutes. It needs Python 3, `g++`, and `pysat` with CaDiCaL for
`static_sat.py`.
