import random, sys
from collections import Counter
from math import prod
from common import label_poset, leq, block_sizes


class Stop(Exception):
    pass


def run(K, j, k, alg_name):
    b = block_sizes(K, j)
    Dlev = {j: K - 1}
    for l in range(j - 1, -1, -1):
        Dlev[l] = b[l + 1]
    level, parent, target, children = {}, {}, {}, {}
    Res, realidx = {}, {}
    nbrs, colours, used = [], [], set()
    stats = {"block": Counter(), "tot": Counter()}

    def alg(r, nb):
        forb = {colours[u] for u in nb}
        allowed = [c for c in range(1, K) if c not in forb]
        if alg_name == "first_fit":
            c = 1
            while c in forb:
                c += 1
            return c
        if not allowed:
            c = 1
            while c in forb:
                c += 1
            return c
        tot = stats["tot"]
        if alg_name == "least_used":
            return min(allowed, key=lambda c: (tot[c], c))
        if alg_name == "most_used":
            return max(allowed, key=lambda c: (tot[c], -c))
        if alg_name == "block_spread":
            key = frozenset(nb)
            cnt = stats["block"]
            c = min(allowed, key=lambda c: (cnt[(key, c)], tot[c], c))
            cnt[(key, c)] += 1
            return c
        if alg_name.startswith("random"):
            rng = random.Random(hash((alg_name, r, len(nb))))
            return rng.choice(allowed)
        raise ValueError(alg_name)

    counter = [0]

    def new_node(lev, par):
        counter[0] += 1
        v = counter[0]
        level[v], parent[v], children[v] = lev, par, []
        if par is not None:
            children[par].append(v)
        return v

    def present(lev, v, W):
        if lev == 0:
            r = len(nbrs)
            realidx[v] = r
            nb = [realidx[w] for w in W]
            c = alg(r, nb)
            assert all(colours[u] != c for u in nb), "algorithm must colour properly"
            nbrs.append(nb)
            colours.append(c)
            stats["tot"][c] += 1
            used.add(c)
            if len(used) >= K:
                raise Stop
            return c
        X = []
        for w in W:
            x = Res[w].pop(0)
            target[x] = v
            X.append(x)
        block = []
        for _ in range(b[lev]):
            c = new_node(lev - 1, v)
            block.append((c, present(lev - 1, c, X)))
        cnt = Counter(col for _, col in block)
        D = Dlev[lev]
        good = [col for col in cnt if cnt[col] >= D]
        assert good, "pigeonhole guarantees a colour with D vertices"
        col = min(good)
        Res[v] = [c for c, cc in block if cc == col][:D]
        return col

    tops = []
    try:
        for t in range(K):
            v = new_node(j, None)
            present(j, v, list(tops))
            tops.append(v)
    except Stop:
        pass
    n = len(nbrs)
    assert len(used) == K, "the adversary must force K colours"
    bound = (K - 1) * prod(b.values()) + 1
    assert n <= bound, (n, bound)

    P = label_poset(k, j)
    assert len(P) >= K
    lab = {}
    all_tops = [v for v in level if level[v] == j]
    for t, v in enumerate(sorted(all_tops)):
        lab[v] = P[t]
    for lev in range(j, 0, -1):
        for v in [u for u in level if level[u] == lev]:
            for x in children[v]:
                u = target.get(x)
                if u is not None:
                    cand = lab[v] - lab[u]
                    assert cand, "psi(w) is not contained in psi(v) for an arc w -> v"
                else:
                    cand = lab[v]
                lab[x] = min(cand, key=repr)
        for x, u in target.items():
            if level[x] == lev - 1:
                for y in children[u]:
                    assert not leq(lab[x], lab[y], lev - 1)
    colouring = [None] * n
    for v, r in realidx.items():
        colouring[r] = lab[v]
    assert all(0 <= c < k for c in colouring)
    edges = [(u, r) for r in range(n) for u in nbrs[r]]
    assert all(colouring[u] != colouring[r] for u, r in edges), "the k-colouring must be proper"
    adj = [set() for _ in range(n)]
    for u, r in edges:
        adj[u].add(r); adj[r].add(u)
    assert all(nb[a] not in adj[nb[b2]] for nb in nbrs for a in range(len(nb)) for b2 in range(a))
    return n, len(edges), bound


configs = [(4, 1, 3), (7, 1, 3), (5, 2, 3), (8, 2, 3), (10, 2, 3), (15, 1, 4)]
algs = ["first_fit", "least_used", "most_used", "block_spread", "random1", "random2"]
for K, j, k in configs:
    for a in algs:
        n, m, bound = run(K, j, k, a)
        print("K=%-2d j=%d k=%d %-12s forced %d colours with %-7d vertices (bound %d), %d edges, %d-colouring verified"
              % (K, j, k, a, K, n, bound, m, k))
        sys.stdout.flush()
print("simulate_adversary: OK")
