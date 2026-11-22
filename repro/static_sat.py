from pysat.solvers import Cadical195
from pysat.formula import CNF


def clique(m):
    return m, [(s, t) for s in range(m) for t in range(s + 1, m)]


def blow_up(n, arcs):
    out = [[] for _ in range(n)]
    for s, t in arcs:
        out[s].append(t)
    start, size = [], []
    tot = 0
    for v in range(n):
        start.append(tot)
        size.append(max(1, len(out[v])))
        tot += size[-1]
    new_arcs = []
    for w in range(n):
        for i, v in enumerate(out[w]):
            x = start[w] + i
            new_arcs += [(x, start[v] + a) for a in range(size[v])]
    return tot, new_arcs


def tower(m, j):
    n, arcs = clique(m)
    for _ in range(j):
        n, arcs = blow_up(n, arcs)
    return n, arcs


def colourable(n, arcs, k):
    var = lambda v, c: v * k + c + 1
    s = Cadical195()
    for v in range(n):
        s.add_clause([var(v, c) for c in range(k)])
    for a, b in arcs:
        for c in range(k):
            s.add_clause([-var(a, c), -var(b, c)])
    s.add_clause([var(0, 0)])
    res = s.solve()
    s.delete()
    return res


cases = [(3, 1, 7, True), (3, 1, 8, False), (4, 1, 15, True), (4, 1, 16, False), (3, 2, 18, True), (3, 2, 19, False)]
for k, j, m, expect in cases:
    n, arcs = tower(m, j)
    res = colourable(n, arcs, k)
    print("k=%d j=%d m=%-3d minimal tower: %5d vertices %6d edges  %d-colourable: %s" % (k, j, m, n, len(arcs), k, res))
    assert res == expect
print("static_sat: OK")
