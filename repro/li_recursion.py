#!/usr/bin/env python3
from math import log2


def ceil_div(a, b):
    return -(-a // b)


def li_size(K):
    assert K >= 3
    beta = (K - 1).bit_length()
    assert beta >= 2 and 2 ** (beta - 1) < K <= 2 ** beta
    h, p = 0, 1
    while p < K:
        p *= beta
        h += 1
    ts = [beta ** i for i in range(h)] + [K]
    N, D = 1, 1
    for i in range(h - 1, -1, -1):
        t, q = ts[i], ts[i + 1]
        j = ceil_div(2 * q - t, ceil_div(t, 2))
        B = K * (2 ** (j + 1) - 1)
        R = K * q * D
        N, D = N * R * B, R * B + B - 1
    return N


def log2_big(N):
    e = N.bit_length()
    if e <= 1000:
        return log2(N)
    top = N >> (e - 64)
    return log2(top) + (e - 64)


PLOTTED = [(3, 27.645434), (4, 34.971556), (5, 36.102285), (8, 47.573306), (16, 71.99989), (100, 199.67788),
           (1000, 381.09641), (65536, 1039.0), (1048583, 1719.7699), (2 ** 32, 5179.9997), (2 ** 64, 26053.0),
           (2 ** 100, 84798.649)]

if __name__ == "__main__":
    for K, want in PLOTTED:
        got = log2_big(li_size(K))
        print("K=%-32d log2 N = %-14.6f plotted %s" % (K, got, want))
        assert abs(got - want) <= 1e-5 * max(1.0, abs(want)), (K, got, want)
    print("li_recursion OK")
