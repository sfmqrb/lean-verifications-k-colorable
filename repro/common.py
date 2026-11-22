from functools import lru_cache
import math


def leq(a, b, level):
    return a == b if level == 0 else a <= b


def nonempty_downsets(elems, level):
    n = len(elems)
    comparable = [[i != j and (leq(elems[i], elems[j], level) or leq(elems[j], elems[i], level))
                   for j in range(n)] for i in range(n)]
    below = [frozenset(elems[j] for j in range(n) if leq(elems[j], elems[i], level)) for i in range(n)]
    out = []

    def rec(start, chosen):
        if chosen:
            out.append(frozenset().union(*(below[i] for i in chosen)))
        for i in range(start, n):
            if all(not comparable[i][c] for c in chosen):
                chosen.append(i)
                rec(i + 1, chosen)
                chosen.pop()
    rec(0, [])
    assert len(set(out)) == len(out), "distinct antichains must give distinct down-sets"
    return out


@lru_cache(maxsize=None)
def label_poset(k, j):
    if j == 0:
        return tuple(range(k))
    elems = nonempty_downsets(list(label_poset(k, j - 1)), j - 1)
    elems.sort(key=lambda d: (-len(d), sorted(map(repr, d))))
    return tuple(elems)


def width(elems, level):
    n = len(elems)
    comp = [[i != j and (leq(elems[i], elems[j], level) or leq(elems[j], elems[i], level))
             for j in range(n)] for i in range(n)]
    best = 0

    def rec(start, chosen):
        nonlocal best
        best = max(best, len(chosen))
        for i in range(start, n):
            if all(not comp[i][c] for c in chosen):
                chosen.append(i)
                rec(i + 1, chosen)
                chosen.pop()
    rec(0, [])
    return best


def tow(i):
    t = 1
    for _ in range(i):
        t = 2 ** t
    return t


def log_star(x):
    i = 0
    while tow(i) < x:
        i += 1
    return i


def block_sizes(K, j):
    b = {}
    D = K - 1
    for level in range(j, 0, -1):
        b[level] = (K - 1) * (D - 1) + 1
        D = b[level]
    return b


def is_proper(colour, edges):
    return all(colour[u] != colour[v] for u, v in edges)
