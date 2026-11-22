import sys
from fractions import Fraction
from functools import lru_cache
from collections import deque
sys.setrecursionlimit(100000)


def konig_matchings(Y, W):
    colour_at = {}
    edges = []
    for (s, c), mult in sorted(Y.items()):
        for _ in range(mult):
            edges.append([s, c, None])
    def free(side, node):
        for a in range(W):
            if (side, node, a) not in colour_at:
                return a
        raise AssertionError("degree exceeds W")
    for e in range(len(edges)):
        s, c, _ = edges[e]
        a, b = free('r', s), free('c', c)
        if ('c', c, a) in colour_at:
            path, side, node, col = [], 'c', c, a
            while (side, node, col) in colour_at:
                f = colour_at[(side, node, col)]
                path.append(f)
                fs, fc, _ = edges[f]
                side, node = ('r', fs) if side == 'c' else ('c', fc)
                col = b if col == a else a
            for f in path:
                fs, fc, fa = edges[f]
                del colour_at[('r', fs, fa)]
                del colour_at[('c', fc, fa)]
            for f in path:
                fs, fc, fa = edges[f]
                nb = b if fa == a else a
                edges[f][2] = nb
                colour_at[('r', fs, nb)] = f
                colour_at[('c', fc, nb)] = f
        assert ('r', s, a) not in colour_at and ('c', c, a) not in colour_at
        edges[e][2] = a
        colour_at[('r', s, a)] = e
        colour_at[('c', c, a)] = e
    match = [dict() for _ in range(W)]
    for s, c, a in edges:
        assert s not in match[a]
        match[a][s] = c
    return match


def max_flow_augment(Y, rows, a, W):
    Y = dict(Y)
    cols = sorted({c for s in rows for c in a[s]})
    def rowsum(s): return sum(v for (r, c), v in Y.items() if r == s)
    def colsum(c): return sum(v for (r, cc), v in Y.items() if cc == c)
    while True:
        prev = {('src',): None}
        q = deque([('src',)])
        found = None
        while q and found is None:
            x = q.popleft()
            if x == ('src',):
                nxt = [('r', s) for s in rows if rowsum(s) < W]
            elif x[0] == 'r':
                s = x[1]
                nxt = [('c', c) for c in cols if Y.get((s, c), 0) < min(a[s].get(c, 0), W)]
            else:
                c = x[1]
                if colsum(c) < W:
                    found = x
                    break
                nxt = [('r', s) for s in rows if Y.get((s, c), 0) > 0]
            for y in nxt:
                if y not in prev:
                    prev[y] = x
                    q.append(y)
        if found is None:
            return Y
        y = found
        while prev[y] != ('src',):
            x = prev[y]
            if x[0] == 'r':
                Y[(x[1], y[1])] = Y.get((x[1], y[1]), 0) + 1
            else:
                Y[(y[1], x[1])] -= 1
                if Y[(y[1], x[1])] == 0:
                    del Y[(y[1], x[1])]
            y = x


def potential(Y, cols, W):
    tight = sum(1 for c in cols if sum(v for (s, cc), v in Y.items() if cc == c) == W)
    return Fraction(sum(Y.values()), W) + tight


def check(m):
    C = m // 2
    sizes = [max(1, m - t) for t in range(1, m + 1)]

    def multisets(n, colours):
        if not colours:
            if n == 0:
                yield ()
            return
        if len(colours) == 1:
            yield ((colours[0], n),) if n else ()
            return
        for k in range(n + 1):
            for rest in multisets(n - k, colours[1:]):
                yield (((colours[0], k),) if k else ()) + rest

    @lru_cache(maxsize=None)
    def solve(t, a_key, Y_key, u):
        a = {s: dict(d) for s, d in a_key}
        Y = dict(Y_key)
        W = m - t + 1
        rows = sorted(a)
        cols = list(range(1, u + 1))
        phi_before = potential(Y, cols, W) if t > 1 else Fraction(0)
        if rows:
            match = konig_matchings(Y, W)
            M = min(match, key=len)
            assert len(M) * W <= sum(Y.values())
            forb = set()
            for s in rows:
                if s in M:
                    c = M[s]
                else:
                    spare = [c for c in sorted(a[s]) if a[s][c] > Y.get((s, c), 0)]
                    assert spare, "a spare vertex must exist"
                    c = spare[0]
                forb.add(c)
                a[s][c] -= 1
                if a[s][c] == 0:
                    del a[s][c]
            Yp = {k: v for k, v in Y.items()}
            for s, c in M.items():
                Yp[(s, c)] -= 1
                if Yp[(s, c)] == 0:
                    del Yp[(s, c)]
        else:
            forb, Yp = set(), {}
        for c in cols:
            if sum(v for (s, cc), v in Y.items() if cc == c) == W:
                assert c in forb
        allowed_old = [c for c in cols if c not in forb]
        size = sizes[t - 1]
        new_max = C - u
        ok = True
        for nnew in range(0, min(new_max, size) + 1):
            palette = allowed_old + list(range(u + 1, u + 1 + nnew))
            for ms in multisets(size, palette):
                cnt = dict(ms)
                if any(cnt.get(u + 1 + i, 0) == 0 for i in range(nnew)):
                    continue
                if t == m:
                    return False
                nu = u + nnew
                na = {s: dict(d) for s, d in a.items()}
                na[t] = dict(cnt)
                Wn = W - 1
                for (s, c), v in Yp.items():
                    assert v <= min(na[s].get(c, 0), Wn)
                for s in na:
                    assert sum(v for (r, c), v in Yp.items() if r == s) <= Wn
                for c in range(1, nu + 1):
                    assert sum(v for (r, cc), v in Yp.items() if cc == c) <= Wn
                Yn = max_flow_augment(Yp, sorted(na), na, Wn) if Wn > 0 else {}
                if Wn > 0:
                    phi_after = potential(Yn, list(range(1, nu + 1)), Wn)
                    assert phi_after >= phi_before + 1, (m, t, phi_before, phi_after)
                key_a = tuple(sorted((s, tuple(sorted(d.items()))) for s, d in na.items()))
                ok &= solve(t + 1, key_a, tuple(sorted(Yn.items())), nu)
                if not ok:
                    return False
        return ok

    res = solve(1, (), (), 0)
    return res, solve.cache_info().currsize


for m in range(2, 10):
    res, states = check(m)
    print("m=%d: the flow adversary forces floor(m/2)+1 = %d colours against every algorithm: %s (%d states)"
          % (m, m // 2 + 1, res, states))
    sys.stdout.flush()
    assert res
print("flow_adversary: OK")
