#!/usr/bin/env python3
import random, math
from fractions import Fraction as Fr
from collections import defaultdict

def play(m, j, alg, rng, b=None):
    A = 2 * m
    if b is None:
        b = math.log(4 * m)
    leafcol = []
    used = []
    colours_seen = set()
    alg_state = {"n": 0}
    hist = []
    leaf_id = []
    Hsum = 0.0
    def mass(c, t):
        tot = Fr(0)
        for s in range(t):
            cnt = sum(1 for p, col in leafcol[s].items() if col == c and p[0] not in used[s])
            tot += Fr(cnt, A ** j)
        return tot
    for t in range(m):
        cols = sorted(colours_seen)
        u = {c: mass(c, t) for c in cols}
        heavy = [c for c in cols if u[c] >= b]
        top = {}
        for s in range(t):
            free = [z for z in range(A) if z not in used[s]]
            top[s] = rng.choice(free)
        perm = {}
        def server_path(s, ypath):
            sp = (top[s],)
            for lvl in range(len(ypath)):
                key = (s, ypath[:lvl])
                if key not in perm:
                    q = list(range(A)); rng.shuffle(q); perm[key] = q
                sp = sp + (perm[key][ypath[lvl]],)
            return sp
        paths = [p for p in iter_paths(A, j)]
        nb = {}
        for p in paths:
            y = p[:-1]
            if y not in nb:
                nb[y] = [(s, server_path(s, y)) for s in range(t)]
        H = 0.0
        for c in heavy:
            bad = sum(A for y, lst in nb.items() if all(leafcol[s][sp] != c for s, sp in lst))
            H += bad / A ** j
        Hsum += H
        leafcol.append({}); used.append(set()); leaf_id.append({})
        newcol = defaultdict(int)
        for p in paths:
            y = p[:-1]
            nbr_ids = frozenset(leaf_id[s][sp] for s, sp in nb[y])
            nbr_cols = {leafcol[s][sp] for s, sp in nb[y]}
            col = alg(hist, nbr_ids, nbr_cols, rng)
            assert col not in nbr_cols
            leaf_id[t][p] = len(hist); hist.append((nbr_ids, col)); leafcol[t][p] = col
            colours_seen.add(col); newcol[col] += 1
        for s in range(t):
            used[s].add(top[s])
        for c in cols:
            after = mass(c, t + 1)
            if u[c] < b:
                assert after <= b + 1 + 1e-12
            else:
                q = sum(A for y, lst in nb.items() if all(leafcol[s][sp] != c for s, sp in lst)) / A ** j
                assert float(after - u[c]) <= q + 1e-12
    D = len(colours_seen)
    total = sum(mass(c, m) for c in colours_seen)
    assert total == Fr(3 * m + 1, 4), (total, Fr(3 * m + 1, 4))
    assert float(total) <= D * (b + 1) + Hsum + 1e-9
    return D, Hsum / m, Hsum

def iter_paths(A, j):
    if j == 0:
        yield (); return
    for a in range(A):
        for r in iter_paths(A, j - 1):
            yield (a,) + r

def first_fit(hist, ids, cols, rng):
    c = 1
    while c in cols: c += 1
    return c
def least_used(hist, ids, cols, rng):
    cnt = defaultdict(int)
    for _, c in hist: cnt[c] += 1
    cands = [c for c in cnt if c not in cols]
    return min(cands, key=lambda c: (cnt[c], c)) if cands else (max(cnt) + 1 if cnt else 1)
def most_used(hist, ids, cols, rng):
    cnt = defaultdict(int)
    for _, c in hist: cnt[c] += 1
    cands = [c for c in cnt if c not in cols]
    return max(cands, key=lambda c: (cnt[c], -c)) if cands else (max(cnt) + 1 if cnt else 1)
def hashed(hist, ids, cols, rng):
    pal = 1 + (len(hist) * 2654435761 % 7)
    c = pal
    while c in cols: c += 1
    return c

def mixed(hist, ids, cols, rng):
    free = [c for c in (1, 2, 3, 4) if c not in cols]
    if free: return rng.choice(free)
    c = 5
    while c in cols: c += 1
    return c

def part1():
    rng = random.Random(1)
    for (m, j, plays) in [(12, 1, 60), (24, 1, 30), (10, 2, 20), (14, 2, 8)]:
        bound = (2 * m + 1) / (4 * (1 + math.log(4 * m)))
        for name, alg in [("first_fit", first_fit), ("least_used", least_used), ("most_used", most_used), ("hashed", hashed)]:
            Ds, Hs = [], []
            for _ in range(plays):
                D, Hm, _ = play(m, j, alg, rng); Ds.append(D); Hs.append(Hm)
            print(f"m={m:3d} j={j} {name:10s} plays={plays:3d} meanC={sum(Ds)/len(Ds):6.2f} minC={min(Ds):3d} "
                  f"bound={bound:5.2f} meanH_t={sum(Hs)/len(Hs):.4f} (<=0.25)", flush=True)
    print("part 1: all per-play identities and inequalities hold")

def part1_heavy():
    rng = random.Random(3)
    for (m, j, plays) in [(8, 1, 40), (8, 2, 12)]:
        for b in (0.25, 0.5, 1.0):
            for name, alg in [("mixed", mixed), ("hashed", hashed), ("first_fit", first_fit)]:
                Cs, Hsums, slack = [], [], []
                for _ in range(plays):
                    C, _, Hsum = play(m, j, alg, rng, b); Cs.append(C); Hsums.append(Hsum)
                    slack.append(C * (1 + b) + Hsum - (3 * m + 1) / 4)
                if name != "first_fit":
                    assert max(Hsums) > 0, "no heavy colour was missed: (8.1) not exercised"
                print(f"m={m:3d} j={j} b={b:4.2f} {name:10s} plays={plays:3d} meanC={sum(Cs)/len(Cs):6.2f} "
                      f"mean sum_t H_t={sum(Hsums)/len(Hsums):7.4f} max={max(Hsums):7.4f} "
                      f"min slack in (8.1)={min(slack):7.4f} (>=0)", flush=True)
    print("part 1 (heavy colours): (8.1) holds on every play, with positive sum_t H_t")


def part2():
    rng = random.Random(7)

    m, j = 14, 2; A = 2 * m
    t = 10
    leafcol = []; used = []
    def sticky(cols):
        for c in (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20):
            if c not in cols: return c
    for ph in range(t):
        top = {s: rng.choice([z for z in range(A) if z not in used[s]]) for s in range(ph)}
        perm = {s: rng.sample(range(A), A) for s in range(ph)}
        leafcol.append({}); used.append(set())
        for y in range(A):
            cols = {leafcol[s][(top[s], perm[s][y])] for s in range(ph)}
            for i in range(A):
                free = [c for c in range(1, 9) if c not in cols]
                leafcol[ph][(y, i)] = rng.choice(free) if free else sticky(cols)
        for s in range(ph): used[s].add(top[s])
    colours = sorted({c for d in leafcol for c in d.values()})
    u = {}; prodp = {}
    for c in colours:
        us = 0.0; pr = 1.0
        for s in range(t):
            elig = [(z, i) for z in range(A) if z not in used[s] for i in range(A)]
            k = sum(1 for p in elig if leafcol[s][p] == c)
            us += k / A ** j; pr *= 1 - k / len(elig)
        u[c] = us; prodp[c] = pr
    TR = 40000; miss = defaultdict(int)
    for _ in range(TR):
        nb = []
        for s in range(t):
            z = rng.choice([z for z in range(A) if z not in used[s]])
            nb.append(leafcol[s][(z, rng.randrange(A))])
        for c in colours:
            if c not in nb: miss[c] += 1
    ok = True
    for c in colours:
        emp = miss[c] / TR; se = math.sqrt(max(prodp[c] * (1 - prodp[c]), 1e-9) / TR)
        good = abs(emp - prodp[c]) <= 5 * se + 1e-4 and prodp[c] <= math.exp(-u[c]) + 1e-12
        ok &= good
        print(f"c={c:2d} u_c={u[c]:.4f} exp(-u)={math.exp(-u[c]):.5f} prod(1-p)={prodp[c]:.5f} empirical={emp:.5f} {'ok' if good else 'FAIL'}")
    print("eq (1) consistent" if ok else "MISMATCH")
    assert ok

if __name__ == "__main__":
    part1()
    part1_heavy()
    part2()
    print("uniform_tower: OK")
