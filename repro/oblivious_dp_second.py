import sys
from fractions import Fraction
from functools import lru_cache
from math import comb, ceil
from itertools import product


def compositions(R, m):
    if m == 1:
        yield (R,)
        return
    for a in range(R, -1, -1):
        for rest in compositions(R - a, m - 1):
            yield (a,) + rest


def binom_pmf(n, p):
    q = 1 - p
    return [comb(n, r) * p ** r * q ** (n - r) for r in range(n + 1)]


def solve(K, R, policy="opt", exact=True, first=None):
    C = K - 1
    ONE = Fraction(1) if exact else 1.0
    ZERO = Fraction(0) if exact else 0.0

    def canon(hists, nused):
        cols = list(zip(*hists)) if hists else [()] * C
        used = sorted(cols[:nused], reverse=True)
        rest = cols[nused:]
        cols2 = used + list(rest)
        return tuple(zip(*cols2)) if hists else hists

    @lru_cache(maxsize=None)
    def V(t, hists, nused):
        if t == K:
            return ONE
        p = Fraction(1, K - t) if exact else 1.0 / (K - t)
        cells = [(s, c, h) for s, hs in enumerate(hists) for c, h in enumerate(hs) if h > 0]
        pmfs = [binom_pmf(h, p) for (_, _, h) in cells]
        total = ZERO
        for rs in product(*[range(h + 1) for (_, _, h) in cells]):
            pr = ONE
            for (i, r) in enumerate(rs):
                pr *= pmfs[i][r]
            if pr == 0:
                continue
            F = set()
            new = [list(hs) for hs in hists]
            for (s, c, h), r in zip(cells, rs):
                if r > 0:
                    F.add(c)
                new[s][c] -= r
            total += pr * best_choice(t, tuple(tuple(x) for x in new), nused, frozenset(F))
        return total

    def best_choice(t, hists, nused, F):
        allowed_used = [c for c in range(nused) if c not in F]
        nnew = C - nused
        best = ZERO
        d_next = K - 1 - t
        options = []
        if policy == "ff":
            if allowed_used:
                options = [((min(allowed_used),), 0)]
            elif nnew > 0:
                options = [((nused,), 1)]
            else:
                return ZERO
        else:
            for m in range(0, nnew + 1):
                slots = allowed_used + list(range(nused, nused + m))
                if not slots:
                    continue
                options.append((tuple(slots), m))
        for slots, m in options:
            if t == K - 1 or d_next == 0:
                return ONE
            comps = [(R,)] if policy == "ff" else compositions(R, len(slots))
            for comp in comps:
                if policy != "ff" and m > 0 and comp[-1] == 0:
                    continue
                h = [0] * C
                for c, a in zip(slots, comp):
                    h[c] += a
                nu = nused + m
                hs2 = hists + (tuple(h),)
                val = V(t + 1, canon(hs2, nu), nu)
                if first is not None and t == 0:
                    first.append((tuple(h), float(val)))
                if val > best:
                    best = val
            if best == 1:
                break
        return best

    return V(0, (), 0)


def union_bound(K, R):
    c = ceil(R / (K - 1))
    return sum(d * (1 - 1 / d) ** c for d in range(1, K))


if __name__ == "__main__":
    K = int(sys.argv[1]); Rmax = int(sys.argv[2])
    exact = not (len(sys.argv) > 3 and sys.argv[3] == "float")
    Rmin = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    for R in range(Rmin, Rmax + 1):
        w = solve(K, R, "opt", exact)
        wf = solve(K, R, "ff", exact)
        print(f"K={K} R={R}: W_opt = {w} = {float(w):.6g}   W_FF = {float(wf):.6g}   union bound = "
              f"{min(1.0, union_bound(K, R)):.4g}", flush=True)
        want = {1: '1', 2: '1', 3: '1', 4: '263/324', 5: '1211/1944', 6: '1735/3888', 7: '7343/23328',
                8: '90857/419904'}
        if K == 4 and exact and R in want:
            assert str(w) == want[R], (R, w)
    if K == 4 and exact:
        print("oblivious_dp_second OK (agrees with oblivious_dp.py for R = %d..%d)" % (Rmin, Rmax))
