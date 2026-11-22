import sys
from functools import lru_cache
from itertools import product
from collections import Counter
from common import block_sizes
sys.setrecursionlimit(10000)


def block_outcomes(size, u, forbidden, K, raw):
    if raw:
        def rec(i, u, cnt):
            if i == size:
                yield ('done', Counter(cnt), u)
                return
            for c in [c for c in range(1, u + 1) if c not in forbidden] + [u + 1]:
                if c == u + 1 and u + 1 >= K:
                    yield ('stop', i + 1)
                    continue
                cnt[c] += 1
                yield from rec(i + 1, max(u, c), cnt)
                cnt[c] -= 1
        yield from rec(0, u, Counter())
    else:
        old = [c for c in range(1, u + 1) if c not in forbidden]
        free_new = K - 1 - u
        palette = old + list(range(u + 1, u + 1 + free_new))
        if not palette:
            yield ('stop', 1)
            return
        def comps(n, parts):
            if parts == 1:
                yield (n,)
                return
            for a in range(n + 1):
                for rest in comps(n - a, parts - 1):
                    yield (a,) + rest
        seen = set()
        for counts in comps(size, len(palette)):
            cnt = Counter({c: m for c, m in zip(palette, counts) if m})
            news = sorted(c for c in cnt if c > u)
            ren = {c: u + 1 + i for i, c in enumerate(news)}
            cnt = Counter({ren.get(c, c): m for c, m in cnt.items()})
            key = tuple(sorted(cnt.items()))
            if key in seen:
                continue
            seen.add(key)
            yield ('done', cnt, u + len(news))
        yield ('stop', size)


def popular(cnt, D):
    good = [c for c in cnt if cnt[c] >= D]
    assert good, "pigeonhole: some colour must occur D times"
    return min(good)


def check_one_level(K):
    b = block_sizes(K, 1)[1]
    D = K - 1

    @lru_cache(maxsize=None)
    def solve(t, cols, u):
        if t == K:
            return (False, 0)
        best, ok = 0, True
        for out in block_outcomes(b, u, set(cols), K, raw=True):
            if out[0] == 'stop':
                best = max(best, out[1])
                continue
            _, cnt, nu = out
            f, length = solve(t + 1, cols + (popular(cnt, D),), nu)
            ok &= f
            best = max(best, b + length)
        return (ok, best)
    return solve(0, (), 0), solve.cache_info().currsize


def check_two_levels(K, raw):
    b = block_sizes(K, 2)
    b2, b1 = b[2], b[1]
    D2, D1 = K - 1, b2

    @lru_cache(maxsize=None)
    def solve_l1(t, i, cols_top, cols_l1, u):
        if i == b2:
            return solve_top(t + 1, cols_top + (popular(Counter(cols_l1), D2),), u)
        best, ok = 0, True
        for out in block_outcomes(b1, u, set(cols_top), K, raw=raw):
            if out[0] == 'stop':
                best = max(best, out[1])
                continue
            _, cnt, nu = out
            f, length = solve_l1(t, i + 1, cols_top, cols_l1 + (popular(cnt, D1),), nu)
            ok &= f
            best = max(best, b1 + length)
        return (ok, best)

    @lru_cache(maxsize=None)
    def solve_top(t, cols_top, u):
        if t == K:
            return (False, 0)
        return solve_l1(t, 0, cols_top, (), u)

    return solve_top(0, (), 0), solve_l1.cache_info().currsize


r, states = check_one_level(4)
print("(K,j)=(4,1): forced against every algorithm: %s; longest play %d vertices; %d memo states" % (r[0], r[1], states))
assert r == (True, 22)
r, states = check_two_levels(3, raw=True)
print("(K,j)=(3,2): forced against every algorithm: %s; longest play %d vertices; %d memo states" % (r[0], r[1], states))
assert r[0] and r[1] == 2 * 3 * 5 + 1
r, states = check_two_levels(4, raw=False)
print("(K,j)=(4,2): forced against every algorithm: %s; longest play %d vertices; %d memo states" % (r[0], r[1], states))
assert r[0] and r[1] == 3 * 7 * 19 + 1
print("exhaustive: OK")
