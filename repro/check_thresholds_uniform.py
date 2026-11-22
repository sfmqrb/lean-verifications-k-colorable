#!/usr/bin/env python3
import math

def f(X, j):
    lM = (X - j) / (j + 1)
    two_M_minus_1 = (2 * 2.0 ** lM - 1) if lM < 1000 else None
    l1 = math.log2(two_M_minus_1) if two_M_minus_1 else lM + 1
    lnM = lM * math.log(2)
    return l1 - math.log2(4 * (1 + math.log(4) + lnM)) - X / (j + 2), 1 + math.log(4) + lnM

rows = []
for kname, X0, j0, Lrange in [("3", 406, 6, "2^406 <= n <= 2^65536"), ("3", 65537, 7, "2^65536 < n <= tow(6)"),
                              (">=4", 201, 4, "2^201 <= n <= 2^65536"), (">=4", 65537, 5, "2^65536 < n <= tow(6)")]:
    vals = [(f(X0, j)[0], j) for j in range(1, j0 + 1)]
    for j in range(1, j0 + 1):
        assert f(X0, j)[0] >= 0, (kname, X0, j)
        assert f(X0, j)[1] >= j + 2
    mn = min(vals)
    rows.append((kname, Lrange, j0, X0, mn))
    print(f"k={kname:3s} {Lrange:24s} j0={j0}: min_j f_j(log2 n = {X0}) = {mn[0]:.4f} at j = {mn[1]}")
for kname, X0, j0 in [("3", 406, 6), (">=4", 201, 4)]:
    assert all(f(X, j)[0] >= 0 for X in range(X0, 65537) for j in range(1, j0 + 1))
    print(f"k={kname}: f_{j0}(log2 n = {X0 - 1}) = {f(X0 - 1, j0)[0]:.4f} < 0 (the threshold cannot be halved)")
    assert f(X0 - 1, j0)[0] < 0
def g(X, j, e):
    return f(X, j)[0] + X / (j + 2) - X / e
assert all(g(X, 5, 8) >= 0 for X in range(146, 65537)) and g(145, 5, 8) < 0
print(f"k=3, j=5: left side of (A.1) >= n^(1/8) for every integer log2 n in [146, 65536]; fails at 145 ({g(145, 5, 8):.4f})")
print("check_thresholds_uniform: OK")
