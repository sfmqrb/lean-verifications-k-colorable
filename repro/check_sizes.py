from common import block_sizes
from math import prod, log, ceil

def size(K, j):
    b = block_sizes(K, j)
    return (K - 1) * prod(b.values()) + 1

expected = {(7, 1): 187, (8, 2): 88796, (18, 2): 21464626, (4, 1): 22, (15, 1): 2563, (10, 2): 426394}
for (K, j), v in expected.items():
    got = size(K, j)
    b = block_sizes(K, j)
    print("K=%-3d j=%d  blocks %-40s size %-12d ratio %.2f" %
          (K, j, [b[l] for l in range(j, 0, -1)], got, log(got) / log(K)))
    assert got == v, (K, j, got)
    assert got <= K ** ((j + 1) * (j + 2) // 2)
    assert all(b[l] == (K - 1) ** (j - l + 1) * (K - 2) + 1 for l in b)
print("K=81 j=3 size %.3g, K=166 j=2 size %.3g" % (size(81, 3), size(166, 2)))
assert block_sizes(81, 3) == {3: 6321, 2: 505601, 1: 40448001}
assert block_sizes(166, 2) == {2: 27061, 1: 4464901}

def refined(K, j):
    D = {j: {t: K - t for t in range(1, K + 1)}}
    b = {}
    for l in range(j, 0, -1):
        b[l] = {t: ((K - t) * (D[l][t] - 1) + 1) if D[l][t] >= 1 else 1 for t in range(1, K + 1)}
        D[l - 1] = {t: max([b[l][u] for u in range(t + 1, K + 1)], default=0) for t in range(1, K + 1)}
    return sum(prod(b[l][t] for l in range(1, j + 1)) for t in range(1, K + 1))

exp_ref = {(4, 1): 12, (7, 1): 77, (8, 2): 14484, (10, 2): 70558, (18, 2): 3591642}
for key, v in exp_ref.items():
    got = refined(*key)
    print("Appendix B: K=%d j=%d refined %d (Theorem 6.4: %d)" % (key[0], key[1], got, size(*key)))
    assert got == v

L = 5
assert (L + 2) * (L + 3) // 2 == 28 and L * (L + 1) // 2 == 15
from math import comb
def cheap_top(K, j):
    m, D = 2 * K - 2, 2 * K - 4
    tot, r = comb(m, 2) + 1, (K - 1) * (D - 1) + 1
    for _ in range(j - 1):
        tot *= r
        r = (K - 1) * (r - 1) + 1
    return tot
for (K, j), v in {(7, 2): 3685, (8, 2): 7176, (10, 2): 20944}.items():
    assert cheap_top(K, j) == v
    print("cheaper top: K=%d j=%d at most %d vertices" % (K, j, v))
assert abs(cheap_top(18, 3) - 2.66e9) < 0.01e9
for K in range(3, 40):
    for j in range(1, 6):
        assert cheap_top(K, j) <= 2 ** j * K ** ((j * j + j + 2) // 2)

P3 = [3, 7, 18, 81, 8569]
def least_j(K):
    return max(1, next(i for i, p in enumerate(P3) if p >= K))
def explicit_K(n, size):
    return max(K for K in range(2, 400) if size(K, least_j(K)) <= n)
def uniform_K(n):
    best = 0
    for j in range(1, 5):
        for m in range(2, P3[j] + 1):
            if m * (2 * m) ** j > n:
                break
            best = max(best, ceil((2 * m + 1) / (4 * (1 + log(4 * m)))))
    return best
for x, ahead in [(49, False), (50, True)]:
    e, u = explicit_K(2 ** x, size), uniform_K(2 ** x)
    print("n=2^%d: Theorem 6.4 forces %d, Theorem 8.5(ii) forces %d" % (x, e, u))
    assert (u > e) == ahead
for x, ahead in [(53, False), (54, True)]:
    e, u = explicit_K(2 ** x, refined), uniform_K(2 ** x)
    print("n=2^%d: Appendix B instances force %d, Theorem 8.5(ii) forces %d" % (x, e, u))
    assert (u > e) == ahead
print("check_sizes: OK")
