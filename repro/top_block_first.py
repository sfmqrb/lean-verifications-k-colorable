#!/usr/bin/env python3
import sys, math
from itertools import product

sys.setrecursionlimit(100000)
import os
RULE = os.environ.get("TOPBLOCK_RULE", "most")


def run(K, kind):
    stats = dict(states=0, maxcol=0, corrected_fail=0, proper_fail=0, reachedK=0)
    seen = set()

    def rnd(t, m, Lset, U, trans, Q):
        key = (t, m, Lset, U, trans)
        if key in seen:
            return
        seen.add(key)
        stats["states"] += 1
        md = dict(m)
        stats["maxcol"] = max(stats["maxcol"], len(U))
        if len(U) >= K:
            stats["reachedK"] += 1
            return
        untrans = [q for q in Q if q not in trans]
        g, rho = K - len(U), len(untrans)
        for v in range(1, max([md[q] for q in untrans], default=0) + 2):
            if sum(1 for q in untrans if md[q] >= v) > max(0, g + rho - 1 - v):
                stats["corrected_fail"] += 1
                break
        if t > K:
            return
        qs = sorted(md)
        ls = sorted(Lset)
        for take1 in product(*[range(md[q] + 1) for q in qs]):
            m2 = dict(md)
            F1 = set()
            for q, k in zip(qs, take1):
                if k:
                    m2[q] -= k; F1.add(q)
            mt = tuple(sorted(m2.items()))
            for take2 in product((0, 1), repeat=len(ls)):
                F = F1 | {c for c, k in zip(ls, take2) if k}
                W = [c for c in U if c not in F]
                Wq = [q for q in W if q in Q and q not in trans]
                if Wq:
                    if RULE == "least":
                        col, typ = min(Wq), "b"
                    elif RULE == "fewest":
                        col, typ = min(Wq, key=lambda q: (m2[q], q)), "b"
                    else:
                        col, typ = max(Wq, key=lambda q: (m2[q], -q)), "b"
                elif W:
                    col, typ = min(W), "c"
                else:
                    col, typ = (max(U) + 1 if U else 1), "a"
                if col in F:
                    stats["proper_fail"] += 1
                rnd(t + 1, mt, Lset, U, trans, Q)
                ntr = tuple(sorted(set(trans) | ({col} if typ == "b" else set())))
                rnd(t + 1, mt, tuple(sorted(set(Lset) | {col})), tuple(sorted(set(U) | {col})), ntr, Q)

    nmax = {"stair": math.comb(K - 1, 2), "rr": (K * K) // 4 - 1, "over": math.comb(K - 1, 2) + 1,
            "rrover": (K * K) // 4}[kind]
    for n1 in range(0, nmax + 1):
        cnt = {}
        if kind == "over" and n1 == nmax:
            cnt = {i: K - 1 - i for i in range(1, K - 1)}
            cnt[1] += 1
            Q = tuple(sorted(cnt))
            rnd(2, tuple(sorted(cnt.items())), (), Q, (), Q)
            continue
        for j in range(n1):
            if kind in ("stair", "over"):
                for i in range(1, K - 1):
                    if cnt.get(i, 0) < K - 1 - i:
                        cnt[i] = cnt.get(i, 0) + 1
                        break
            else:
                i = j % (K // 2) + 1
                cnt[i] = cnt.get(i, 0) + 1
        Q = tuple(sorted(cnt))
        rnd(2, tuple(sorted(cnt.items())), (), Q, (), Q)
    return nmax, stats


if __name__ == "__main__":
    K = int(sys.argv[1]); kind = sys.argv[2] if len(sys.argv) > 2 else "stair"
    nmax, st = run(K, kind)
    print(f"[fast] K={K} block1={kind} n1<={nmax}: {st}", flush=True)
    if kind == "stair" and RULE == "most":
        assert nmax == math.comb(K - 1, 2), nmax
        assert st["reachedK"] == 0 and st["corrected_fail"] == 0 and st["proper_fail"] == 0, st
        print(f"top_block_first K={K}: no adversary forces {K} colours with |sigma(v_1)| <= C(K-1,2) = {nmax}  OK")
