#!/usr/bin/env python3
import sys, itertools, time, json
from fractions import Fraction
from functools import lru_cache
from math import comb
from collections import defaultdict


def compositions(R, parts):
    if parts == 0:
        if R == 0:
            yield ()
        return
    if parts == 1:
        yield (R,)
        return
    for a in range(R, -1, -1):
        for rest in compositions(R - a, parts - 1):
            yield (a,) + rest


def dp_exact(K, R, exact=True):
    C = K - 1
    one = Fraction(1) if exact else 1.0
    zero = 0 * one

    @lru_cache(None)
    def V(t, U):
        if t == K - 1:
            return one if min(U) == 0 else zero
        p = Fraction(1, K - t) if exact else 1.0 / (K - t)
        q = 1 - p
        tot = zero
        for r in itertools.product(*[range(u + 1) for u in U]):
            pr = one
            for u, rc in zip(U, r):
                pr *= comb(u, rc) * (p ** rc) * (q ** (u - rc))
            UF = tuple(sorted((u - rc, 1 if rc > 0 else 0) for u, rc in zip(U, r)))
            tot += pr * best(t, UF)
        return tot

    @lru_cache(None)
    def best(t, UF):
        allowed = [i for i, (u, f) in enumerate(UF) if f == 0]
        if not allowed:
            return zero
        base = [u for u, f in UF]
        bv = zero
        for h in compositions(R, len(allowed)):
            ok = True
            for x in range(len(allowed) - 1):
                i, j = allowed[x], allowed[x + 1]
                if base[i] == base[j] and h[x] < h[x + 1]:
                    ok = False
                    break
            if not ok:
                continue
            X = base[:]
            for i, hi in zip(allowed, h):
                X[i] += hi
            v = V(t + 1, tuple(sorted(X)))
            if v > bv:
                bv = v
        return bv

    res = best(0, tuple((0, 0) for _ in range(C)))
    return res


def ff_closed(K, R):
    pr = Fraction(1)
    for d in range(1, K):
        s = sum((-1) ** i * comb(d, i) * Fraction(d - i, d) ** R for i in range(d + 1))
        pr *= s
    return 1 - pr


def ff_dp(K, R):
    C = K - 1

    @lru_cache(None)
    def V(t, U):
        if t == K - 1:
            return Fraction(1) if min(U) == 0 else Fraction(0)
        p = Fraction(1, K - t)
        q = 1 - p
        tot = Fraction(0)
        for r in itertools.product(*[range(u + 1) for u in U]):
            pr = Fraction(1)
            for u, rc in zip(U, r):
                pr *= comb(u, rc) * (p ** rc) * (q ** (u - rc))
            allowed = [c for c in range(C) if r[c] == 0]
            if not allowed:
                continue
            X = list(u - rc for u, rc in zip(U, r))
            X[allowed[0]] += R
            tot += pr * V(t + 1, tuple(X))
        return tot
    X = [0] * C
    X[0] = R
    return V(1, tuple(X))


def dp_const(K, R, exact=True):
    C = K - 1
    one = Fraction(1) if exact else 1.0
    zero = 0 * one

    def canon(U):
        cols = sorted(zip(*U)) if U else []
        return tuple(zip(*cols)) if cols else U

    @lru_cache(None)
    def V(t, U):
        if t == K - 1:
            prod_all_hit = one
            for c in range(C):
                qc = one
                for s in range(t):
                    u = U[s][c]
                    if u:
                        m = s + K - t
                        qc *= (Fraction(m - 1, m) if exact else (m - 1) / m) ** u
                prod_all_hit *= (1 - qc)
            return 1 - prod_all_hit
        entries = [(s, c) for s in range(t) for c in range(C)]
        tot = zero
        for r in itertools.product(*[range(U[s][c] + 1) for (s, c) in entries]):
            pr = one
            Unew = [list(U[s]) for s in range(t)]
            F = [0] * C
            for (s, c), rc in zip(entries, r):
                u = U[s][c]
                m = s + K - t
                p = Fraction(1, m) if exact else 1.0 / m
                pr *= comb(u, rc) * (p ** rc) * ((1 - p) ** (u - rc))
                Unew[s][c] -= rc
                if rc:
                    F[c] = 1
            if pr == 0:
                continue
            tot += pr * best(t, tuple(tuple(x) for x in Unew), tuple(F))
        return tot

    @lru_cache(None)
    def best(t, U, F):
        allowed = [c for c in range(C) if F[c] == 0]
        if not allowed:
            return zero
        bv = zero
        for h in compositions(R, len(allowed)):
            row = [0] * C
            for c, hc in zip(allowed, h):
                row[c] = hc
            U2 = canon(U + (tuple(row),))
            v = V(t + 1, U2)
            if v > bv:
                bv = v
        return bv

    return best(0, (), tuple([0] * C))


def raw(K, R, variant):
    n = K * R
    ranges = []
    for t in range(K):
        d = (K - 1 - t) if variant == 'exact' else (K - 1)
        for _ in range(R):
            ranges.append(list(range(1, d + 1)) if d > 0 else [0])
    iotas = list(itertools.product(*ranges))
    blk = [i // R for i in range(n)]
    sys.setrecursionlimit(10000)

    def rec(i, group, cols, ncols):
        if i == n:
            return len(group)
        t = blk[i]
        parts = defaultdict(list)
        for g in group:
            io = iotas[g]
            nb = tuple(j for j in range(t * R) if io[j] > 0 and blk[j] + io[j] == t)
            parts[nb].append(g)
        tot = 0
        for nb, sub in parts.items():
            forb = {cols[j] for j in nb}
            bv = 0
            for c in range(min(ncols + 1, K - 1)):
                if c in forb:
                    continue
                v = rec(i + 1, sub, cols + (c,), max(ncols, c + 1))
                if v > bv:
                    bv = v
                    if bv == len(sub):
                        break
            tot += bv
        return tot
    return Fraction(rec(0, list(range(len(iotas))), (), 0), len(iotas))


def union_bound(K, R, variant):
    c = -(-R // (K - 1))
    tot = Fraction(0)
    for t in range(K):
        d = (K - 1 - t) if variant == 'exact' else (K - 1)
        if d >= 1:
            tot += d * Fraction(d - 1, d) ** c
    return tot


if __name__ == '__main__':
    mode = sys.argv[1]
    out = []
    if mode == 'raw':
        for (K, R, var) in [(3, 1, 'exact'), (3, 2, 'exact'), (3, 3, 'exact'), (3, 4, 'exact'), (3, 5, 'exact'),
                            (4, 1, 'exact'), (4, 2, 'exact'), (4, 3, 'exact'),
                            (3, 1, 'const'), (3, 2, 'const'), (3, 3, 'const'), (3, 4, 'const'),
                            (4, 1, 'const'), (4, 2, 'const')]:
            t0 = time.time()
            w = raw(K, R, var)
            dpv = dp_exact(K, R) if var == 'exact' else dp_const(K, R)
            line = dict(K=K, R=R, variant=var, raw=str(w), dp=str(dpv), agree=(w == dpv), secs=round(time.time() - t0, 2))
            print(json.dumps(line), flush=True)
    elif mode == 'exact':
        K = int(sys.argv[2]); Rmax = int(sys.argv[3])
        for R in range(1, Rmax + 1):
            t0 = time.time()
            w = dp_exact(K, R)
            ub = union_bound(K, R, 'exact')
            ff = ff_closed(K, R)
            ffd = ff_dp(K, R)
            print(json.dumps(dict(K=K, R=R, variant='exact', W=str(w), Wf=float(w), FF=str(ff), FF_dp_agree=(ff == ffd),
                                  FFf=float(ff), unionbound=float(ub), W_le_bound=(w <= ub),
                                  secs=round(time.time() - t0, 2))), flush=True)
    elif mode == 'paper':
        want_W = ['1', '1', '1', '263/324', '1211/1944', '1735/3888', '7343/23328', '90857/419904']
        want_FF = ['1', '1', '5/6', '11/18', '91/216', '61/216', '485/2592', '2881/23328']
        for R in range(1, 9):
            w, ff, ffd = dp_exact(4, R), ff_closed(4, R), ff_dp(4, R)
            print("K=4 R=%d best escape %s (%.6f)  First-Fit %s" % (R, w, float(w), ff), flush=True)
            assert str(w) == want_W[R - 1], (R, w)
            assert str(ff) == want_FF[R - 1] and ff == ffd, (R, ff, ffd)
        for (K, R) in [(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3)]:
            assert raw(K, R, 'exact') == dp_exact(K, R), (K, R)
        print("raw game tree = DP for K=3, R<=5 and K=4, R<=3")
        print("oblivious_dp OK")
    elif mode == 'const':
        K = int(sys.argv[2]); Rmax = int(sys.argv[3])
        for R in range(1, Rmax + 1):
            t0 = time.time()
            w = dp_const(K, R)
            ub = union_bound(K, R, 'const')
            print(json.dumps(dict(K=K, R=R, variant='const', W=str(w), Wf=float(w), unionbound=float(ub),
                                  W_le_bound=(w <= ub), secs=round(time.time() - t0, 2))), flush=True)
