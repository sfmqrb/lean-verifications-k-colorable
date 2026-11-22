#!/usr/bin/env python3
import sys, math
from itertools import product

sys.setrecursionlimit(100000)


def run(K, s0):
    cap_s0 = math.comb(K - s0, 2)
    stats = dict(states=0, maxcol=0, corrected_fail=0, proper_fail=0, reachedK=0, overflow=0)
    seen = set()

    def check_inv(md, g, untrans):
        rho = len(untrans)
        for v in range(1, max([md[q] for q in untrans], default=0) + 2):
            hv = sum(1 for q in untrans if md[q] >= v)
            if hv > max(0, g + rho - 1 - v):
                stats["corrected_fail"] += 1
                return

    def rnd(t, m, L, U, trans, Q):
        key = (t, m, L, U, trans, Q)
        if key in seen:
            return
        seen.add(key)
        stats["states"] += 1
        md, Ld = dict(m), dict(L)
        stats["maxcol"] = max(stats["maxcol"], len(U))
        if len(U) >= K:
            stats["reachedK"] += 1
            return
        if t > s0:
            check_inv(md, K - len(U), [q for q in Q if q not in trans])
        if t > K:
            return
        qs = sorted(md)
        ls = sorted(c for c in Ld if Ld[c] >= 1)
        for take1 in product(*[range(md[q] + 1) for q in qs]):
            for take2 in product((0, 1), repeat=len(ls)):
                F = set()
                m2 = dict(md)
                for q, k in zip(qs, take1):
                    if k:
                        m2[q] -= k; F.add(q)
                L2 = dict(Ld)
                for c, k in zip(ls, take2):
                    if k:
                        L2[c] -= 1; F.add(c)
                newc = (max(U) + 1) if U else 1
                if t < s0:
                    W = [c for c in U if c not in F]
                    col = min(W) if W else newc
                    for size in range(0, K - t + 2):
                        if size == 0:
                            rnd(t + 1, (), tuple(sorted(L2.items())), U, (), ())
                        else:
                            nL = dict(L2); nL[col] = min(K, nL.get(col, 0) + size)
                            rnd(t + 1, (), tuple(sorted(nL.items())), tuple(sorted(set(U) | {col})), (), ())
                elif t == s0:
                    Kp = K - len(U)
                    base = newc
                    for n in range(0, cap_s0 + 1):
                        cnt = {}
                        okc = True
                        for _ in range(n):
                            for i in range(1, Kp - 1):
                                if cnt.get(i, 0) < Kp - 1 - i:
                                    cnt[i] = cnt.get(i, 0) + 1
                                    break
                            else:
                                okc = False
                        if not okc:
                            stats["overflow"] += 1
                            continue
                        Qn = tuple(sorted(base - 1 + i for i in cnt))
                        mm = tuple(sorted((base - 1 + i, k) for i, k in cnt.items()))
                        nU = tuple(sorted(set(U) | set(Qn)))
                        rnd(t + 1, mm, tuple(sorted(L2.items())), nU, (), Qn)
                else:
                    W = [c for c in U if c not in F]
                    Wq = [q for q in W if q in Q and q not in trans]
                    if Wq:
                        col, typ = max(Wq, key=lambda q: (m2[q], -q)), "b"
                    elif W:
                        col, typ = min(W), "c"
                    else:
                        col, typ = newc, "a"
                    if col in F:
                        stats["proper_fail"] += 1
                    for size in range(0, K - t + 2):
                        if size == 0:
                            rnd(t + 1, tuple(sorted(m2.items())), tuple(sorted(L2.items())), U, trans, Q)
                        else:
                            nL = dict(L2); nL[col] = min(K, nL.get(col, 0) + size)
                            ntr = tuple(sorted(set(trans) | ({col} if typ == "b" else set())))
                            rnd(t + 1, tuple(sorted(m2.items())), tuple(sorted(nL.items())),
                                tuple(sorted(set(U) | {col})), ntr, Q)

    rnd(1, (), (), (), (), ())
    return stats


if __name__ == "__main__":
    K, s0 = int(sys.argv[1]), int(sys.argv[2])
    st = run(K, s0)
    print(f"K={K} s0={s0} |sigma(v_s0)| <= C(K-s0,2)={math.comb(K - s0, 2)}: {st}", flush=True)
    assert st["reachedK"] == 0 and st["corrected_fail"] == 0 and st["proper_fail"] == 0, st
    print(f"top_block_any K={K} s={s0}: no adversary forces {K} colours with |sigma(v_s)| <= C(K-s,2)  OK")
