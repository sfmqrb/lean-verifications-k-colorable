# The certificate converter

This file documents how the generated modules `OnlineColouring/CertK*.lean` were produced and how to produce them
again. It contains the two Python programs that do it.

## What is generated

Proposition B.4 of the paper states that `N_3(c) = 2c - 3` for `3 ≤ c ≤ 9`, that `N_3(10) ≥ 17`, and that
`N_k(c) = 2c - k` for `k ≤ c ≤ c_k` with `(k, c_k) = (4, 10), (5, 12), (6, 13)`. The thirty upper bounds
`N_k(c) ≤ 2c - k` are computer-assisted: the supplementary material of the paper contains, for every pair `(k, c)`,
an adversary strategy in the file `repro/certificates/dag_k<k>_C<c>.gen.txt`, as a DAG of *lemmas* (a
start position, one move of the adversary, and for every answer of the algorithm either "stop" or a reference to an
earlier lemma). The Python program `check_adversary_dag.py` in the same directory replays these files.

In the Lean library the same files are checked by the kernel:

* `OnlineColouring/CertCheck.lean` defines the format `Cert.Lem` of a lemma and the checker `Cert.checkLem`, and
  proves that the checker is sound (`Cert.nkLE_of_cert`, `Cert.Upto.nkLE`): if every lemma of a table passes, then
  `NkLE k C N`, that is, `N_k(C) ≤ N` in the sense of Definition 4.2.
* The nine modules `CertK3`, `CertK3C9`, `CertK4`, `CertK4C10`, `CertK5`, `CertK5C11`, `CertK5C12`, `CertK6`,
  `CertK6C13` contain the strategies as data of type `Cert.Lem` and, for every pair `(k, c)`, the theorem
  `Cert.nkLE_<k>_<c> : NkLE k c (2c - k)`, proved by evaluating the checker in the kernel (`decide +kernel`, sixteen
  lemmas per evaluation). `CertNk.lean` combines them with the lower bound of Lemma B.3 into `Cert.prop_small`.

The nine data modules are written by the converter below. **The converter is not trusted**: whatever it writes is
checked by `Cert.checkLem`, so an error in the converter can make a check fail but cannot make a false statement
pass. Neither the converter, nor the data, nor the checker belongs to the trust base of the library: the kernel
checks the soundness proof of the checker and evaluates the checker on the data. To trust Proposition B.4, a reader
compares the statement `Cert.prop_small` and the definition of `Nk` (`AdvBasic.lean`) with the paper.

## What the converter does

Besides translating the syntax (sets of vertices as bit masks, lemmas renumbered in topological order, a height for
every lemma), the converter adds the witnesses that the Lean checker verifies instead of searching for them:

* `wit`: a proper `k`-colouring (as `k` bit masks) of the graph after the move of the lemma;
* `sig`: for every reference to an earlier lemma, the map between the colours of the two positions;
* `wits`: for every reference, and for every proper `k`-colouring of the start position of the lemma referred to
  (up to renaming of the colours, in the order in which the checker enumerates them), an extension of that
  colouring to the current position.

It also renumbers the vertices of every start position so that the enumeration of its colourings has few dead ends.
Any numbering is sound, because a position is a history of a play.

## How to regenerate the data

Save the two listings below as `conv.py` and `gen.py` in one directory outside the repository. Then, from
the root of the repository:

```
OC_ROOT=$PWD OC_OUT=/some/empty/directory python3 /path/to/gen.py 16
```

writes the nine modules to the directory `OC_OUT`; a list of module names after `16` restricts the run to these
modules. The argument `16` is the number of lemmas per kernel evaluation. The run takes a few seconds. The output is
identical, byte for byte, to the nine modules of the library (compare with `cmp`). Without `OC_OUT` the program
overwrites the modules in `OnlineColouring/`; after that, each of them has to be rebuilt (see the table below
and the build instructions in `README.md`).

The header that `gen.py` writes into each module, and the header of `CertCheck.lean`, name the present file,
`docs/cert_converter.md`, as the place of this listing.

## Sizes, times and memory of the kernel checks

Measured with `lake env lean` on one module at a time under a memory limit of 5 GB (wall-clock time, and peak memory
of the control group; the resident set size of the process is about 1 GB larger, because it counts the
memory-mapped Mathlib files).

| Module | Certificates (number of lemmas) | Source size | Wall time | Memory peak |
|---|---|---|---|---|
| `CertK3` | `k = 3`, `c = 3, …, 8` (3, 5, 11, 22, 48, 336) | 0.15 MB | 16 s | 0.9 GB |
| `CertK3C9` | `k = 3`, `c = 9` (2863) | 1.35 MB | 3 min 22 s | 2.7 GB |
| `CertK4` | `k = 4`, `c = 4, …, 9` (4, 6, 11, 22, 41, 208) | 0.11 MB | 12 s | 0.8 GB |
| `CertK4C10` | `k = 4`, `c = 10` (824) | 0.38 MB | 51 s | 1.2 GB |
| `CertK5` | `k = 5`, `c = 5, …, 10` (5, 7, 14, 27, 58, 149) | 0.10 MB | 10 s | 0.8 GB |
| `CertK5C11` | `k = 5`, `c = 11` (460) | 0.23 MB | 30 s | 1.0 GB |
| `CertK5C12` | `k = 5`, `c = 12` (1461) | 0.84 MB | 2 min 6 s | 1.8 GB |
| `CertK6` | `k = 6`, `c = 6, …, 12` (6, 13, 18, 33, 67, 145, 132) | 0.21 MB | 26 s | 1.2 GB |
| `CertK6C13` | `k = 6`, `c = 13` (940) | 0.59 MB | 1 min 30 s | 1.5 GB |

In total there are 7939 lemmas, and the nine modules take about ten minutes of processor time. Lake compiles
independent modules in parallel, and the nine modules are independent of each other, so a build that starts all of
them at once needs the sum of the memory peaks. They are therefore built one after the other.

The checker is written for evaluation in the kernel: it works on bit masks with the primitive operations on natural
numbers that the kernel evaluates with GMP, it verifies witnesses instead of searching for them, and the data are
marked `noncomputable` so that no code is generated for the large literals.

## Listing of `conv.py`

```python
#!/usr/bin/env python3
"""Convert the adversary strategy DAGs `repro/certificates/dag_k*_C*.gen.txt` into Lean data for the
verified checker `OnlineColouring/CertCheck.lean` (type `Lem`).

This program is NOT trusted: everything it writes is checked by the Lean kernel.  Besides translating the syntax
(sets as bit masks, lemmas renumbered in topological order, heights), it adds the witnesses that the Lean checker
verifies instead of searching for them:
  wit   a proper k-colouring (k colour classes as bit masks) of the graph after the move of the lemma;
  sig   for each reference, the colour map (sig[c-1] = image of the colour c of the lemma referred to);
  wits  for each reference, for every proper k-colouring of the start position of the lemma referred to (up to
        renaming, in the order in which `allExt` enumerates them), an extension to the current position.

Usage: conv.py CERT.gen.txt NAME [STEP]   (writes the Lean declarations to stdout)
"""
import sys


def parse(path):
    recs = [ln.split() for ln in open(path) if ln.strip() and not ln.startswith('#')]
    par = dict(x.split('=') for x in recs[0][1:])
    k, C, N = int(par['k']), int(par['C']), int(par['N'])
    assert par['forest'] == '0'
    i = 1
    lem = {}
    while recs[i][0] == 'L':
        lid, n, m = map(int, recs[i][1:4])
        cols = [int(x) for x in recs[i + 1][1:]]
        e = [int(x) for x in recs[i + 2][1:]]
        assert recs[i + 1][0] == 'V' and recs[i + 2][0] == 'G' and len(cols) == n
        nbrs = [0] * n                       # earlier-neighbour masks
        for j in range(0, len(e), 2):
            u, w = sorted((e[j], e[j + 1]))
            assert u < w
            nbrs[w] |= 1 << u
        i += 3
        P = recs[i]
        assert P[0] == 'P' and int(P[1]) == n, 'a lemma must consist of one move'
        nb = 0
        for x in P[2:]:
            assert int(x) < n
            nb |= 1 << int(x)
        i += 1
        outs = {}
        while recs[i][0] == 'C':
            assert int(recs[i][1]) == n
            x = int(recs[i][2])
            r = recs[i + 1]
            if r[0] == 'W':
                outs[x] = None
            else:
                assert r[0] == 'R', r
                outs[x] = (int(r[1]), [int(y) for y in r[2:]])
            i += 2
        assert recs[i][0] == '/L'
        i += 1
        lem[lid] = (n, m, cols, nbrs, nb, outs)
    assert recs[i][0] == 'ROOT'
    root = int(recs[i][1])
    return k, C, N, lem, root


def extend(k, nbrs, forced):
    """Colour classes (k masks) of a proper k-colouring of the graph with earlier-neighbour masks `nbrs` in which
    vertex w has colour forced[w] when w is in `forced`."""
    n = len(nbrs)
    full = list(nbrs)
    for v in range(n):
        for u in range(v):
            if nbrs[v] >> u & 1:
                full[u] |= 1 << v
    cls = [0] * k
    for w, c in forced.items():
        cls[c] |= 1 << w
    for w, c in forced.items():
        assert cls[c] & full[w] == 0
    free = [v for v in range(n) if v not in forced]

    def rec(i):
        if i == len(free):
            return True
        v = free[i]
        for c in range(k):
            if cls[c] & full[v] == 0:
                cls[c] |= 1 << v
                if rec(i + 1):
                    return True
                cls[c] &= ~(1 << v)
        return False

    assert rec(0), 'no extension'
    return list(cls)


def witnesses(k, nbrsA, nbrsB, p):
    """Extensions for all canonical colourings of B, in the order of `allExt`."""
    out = []
    nB = len(nbrsB)
    fl = []

    def rec(m):
        v = len(fl)
        if v == nB:
            out.append(extend(k, nbrsA, {p[i]: fl[i] for i in range(nB)}))
            return
        for c in range(min(m + 1, k)):
            if any((nbrsB[v] >> u & 1) and fl[u] == c for u in range(v)):
                continue
            fl.append(c)
            rec(max(m, c + 1))
            fl.pop()

    rec(0)
    return out


def full_adj(nbrs):
    n = len(nbrs)
    full = list(nbrs)
    for v in range(n):
        for u in range(v):
            if nbrs[v] >> u & 1:
                full[u] |= 1 << v
    return full


def dfs_nodes(k, nbrs, limit):
    """Number of nodes of the enumeration of `allExt` for the position with earlier-neighbour masks nbrs."""
    n = len(nbrs)
    cnt = 0
    cls = [0] * k

    def rec(v, m):
        nonlocal cnt
        cnt += 1
        if cnt > limit or v == n:
            return
        for c in range(min(m + 1, k)):
            if cls[c] & nbrs[v] == 0:
                cls[c] |= 1 << v
                rec(v + 1, max(m, c + 1))
                cls[c] &= ~(1 << v)

    rec(0, 0)
    return cnt


def reorder(nbrs, order):
    """Earlier-neighbour masks after renumbering: new vertex i is old vertex order[i]."""
    n = len(nbrs)
    full = full_adj(nbrs)
    inv = [0] * n
    for i, u in enumerate(order):
        inv[u] = i
    out = []
    for i, u in enumerate(order):
        out.append(sum(1 << inv[w] for w in range(n) if full[u] >> w & 1 and inv[w] < i))
    return out, inv


def best_order(k, nbrs):
    """A vertex order of the position for which the enumeration of the colourings has few dead ends.  (Any order
    is sound: a position is a history, and the checker verifies everything.)"""
    import random
    n = len(nbrs)
    full = full_adj(nbrs)
    deg = [bin(x).count('1') for x in full]
    cands = [list(range(n))]
    for tie in (lambda u: -deg[u], lambda u: deg[u], lambda u: u):
        # maximum cardinality search: next the vertex with most neighbours among the chosen ones
        chosen, mask = [], 0
        while len(chosen) < n:
            u = max((u for u in range(n) if not mask >> u & 1),
                    key=lambda u: (bin(full[u] & mask).count('1'), -tie(u)))
            chosen.append(u)
            mask |= 1 << u
        cands.append(chosen)
    cands.append(sorted(range(n), key=lambda u: -deg[u]))
    rnd = random.Random(12345 + n)
    best, bestc = None, None
    for o in cands:
        c = dfs_nodes(k, reorder(nbrs, o)[0], bestc if bestc is not None else 10 ** 7)
        if bestc is None or c < bestc:
            best, bestc = o, c
    return best


def lst(l):
    return '[' + ', '.join(map(str, l)) + ']'


def convert(path):
    k, C, N, lem, root = parse(path)
    # renumber the vertices of every lemma position (see best_order)
    relem = {}
    invs = {}
    for l, (n, m, cols, nbrs, nb, outs) in lem.items():
        o = best_order(k, nbrs)
        nbrs2, inv = reorder(nbrs, o)
        invs[l] = (o, inv)
        cols2 = [cols[u] for u in o]
        nb2 = sum(1 << inv[u] for u in range(n) if nb >> u & 1)
        relem[l] = (n, m, cols2, nbrs2, nb2, outs)
    for l, (n, m, cols2, nbrs2, nb2, outs) in relem.items():
        inv = invs[l][1] + [n]
        outs2 = {}
        for x, o in outs.items():
            if o is None:
                outs2[x] = None
            else:
                j, p = o
                oj = invs[j][0]
                outs2[x] = (j, [inv[p[oj[i]]] for i in range(len(p))])
        relem[l] = (n, m, cols2, nbrs2, nb2, outs2)
    lem = relem
    order, seen = [], set()

    def visit(l):
        stack = [(l, False)]
        while stack:
            v, done = stack.pop()
            if done:
                order.append(v)
                continue
            if v in seen:
                continue
            seen.add(v)
            stack.append((v, True))
            for o in lem[v][5].values():
                if o is not None and o[0] not in seen:
                    stack.append((o[0], False))

    for l in sorted(lem):
        if l != root:
            visit(l)
    visit(root)
    assert order[-1] == root and len(order) == len(lem)
    new = {l: i for i, l in enumerate(order)}
    height = {}
    out = []
    for l in order:
        n, m, cols, nbrs, nb, outs = lem[l]
        h = 1 + max([0] + [height[o[0]] for o in outs.values() if o is not None])
        height[l] = h
        nbrsA = nbrs + [nb]
        wit = extend(k, nbrsA, {})
        ol = []
        for x in range(1, m + 2):
            o = outs.get(x)
            if o is None:
                ol.append('none')
            else:
                j, p = o
                nB, mB, colsB, nbrsB = lem[j][0], lem[j][1], lem[j][2], lem[j][3]
                assert new[j] < new[l] and len(p) == nB
                colsA = cols + [x]
                sig = [0] * mB
                for i in range(nB):
                    sig[colsB[i] - 1] = colsA[p[i]]
                ws = witnesses(k, nbrsA, nbrsB, p)
                ol.append('some (%d, %s, %s, [%s])' % (new[j], lst(p), lst(sig), ', '.join(lst(w) for w in ws)))
        pos = ', '.join('(%d, %d)' % (nbrs[v], cols[v]) for v in range(n))
        out.append('⟨%d, %d, [%s], %d, %s, [%s]⟩' % (h, m, pos, nb, lst(wit), ', '.join(ol)))
    assert height[root] <= N
    return k, C, N, out


CH = 32


def wrap(text, indent='    ', width=100):
    """Break a long line at ', ' boundaries."""
    toks = text.split(', ')
    lines, cur = [], indent[:-2]
    first = True
    for i, t in enumerate(toks):
        piece = t + (',' if i < len(toks) - 1 else '')
        if first:
            cur += piece
            first = False
        elif len(cur) + 1 + len(piece) <= width:
            cur += ' ' + piece
        else:
            lines.append(cur)
            cur = indent + piece
    lines.append(cur)
    return '\n'.join(lines)


def emit(path, name, step, out=sys.stdout):
    k, C, N, lems = convert(path)
    n = len(lems)
    nch = (n + CH - 1) // CH
    for c in range(nch):
        print('/-- Lemmas %d to %d of the certificate `%s`. -/' % (c * CH, min(n, (c + 1) * CH) - 1, name), file=out)
        print('noncomputable def %s_%d : List Lem := [' % (name, c), file=out)
        part = lems[c * CH:(c + 1) * CH]
        for i, l in enumerate(part):
            print(wrap(l + (',' if i < len(part) - 1 else '')), file=out)
        print(']\n', file=out)
    print('/-- The certificate for `N_%d(%d) ≤ %d`: %d lemmas. -/' % (k, C, N, n), file=out)
    print(wrap('noncomputable def %s : ℕ → Lem := table %d [%s]' % (name, CH, ', '.join('%s_%d' % (name, c) for c in range(nch)))),
          file=out)
    print(file=out)
    lo, q = 0, 0
    prev = 'Upto.zero'
    while lo < n:
        ln = min(step, n - lo)
        print('theorem %s_u%d : Upto %d %d %s %d :=\n  %s.add (lo := %d) (len := %d) (by decide +kernel)\n'
              % (name, q, k, C, name, lo + ln, prev, lo, ln), file=out)
        prev = '%s_u%d' % (name, q)
        lo += ln
        q += 1
    print('/-- `N_%d(%d) ≤ %d`, by the certificate `%s` (%d lemmas, kernel-checked). -/' % (k, C, N, name, n), file=out)
    print('theorem nkLE_%d_%d : NkLE %d %d %d :=\n  %s.nkLE (by decide) (by decide +kernel)' % (k, C, k, C, N, prev),
          file=out)
    return k, C, N, n


if __name__ == '__main__':
    emit(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 16)
```

## Listing of `gen.py`

```python
import sys, io, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import conv
# OC_ROOT: the root of the repository.
# OC_OUT: the directory to write to (default: the library, which overwrites the modules).
R = os.environ['OC_ROOT'].rstrip('/') + '/'
CD = R + 'repro/certificates/'
OUT = os.environ.get('OC_OUT', R + 'OnlineColouring').rstrip('/') + '/'
files = {
    'CertK3': (3, [3, 4, 5, 6, 7, 8]), 'CertK3C9': (3, [9]),
    'CertK4': (4, [4, 5, 6, 7, 8, 9]), 'CertK4C10': (4, [10]),
    'CertK5': (5, [5, 6, 7, 8, 9, 10]), 'CertK5C11': (5, [11]), 'CertK5C12': (5, [12]),
    'CertK6': (6, [6, 7, 8, 9, 10, 11, 12]), 'CertK6C13': (6, [13]),
}
STEP = int(sys.argv[1])
only = sys.argv[2:]
for fn, (k, cs) in files.items():
    if only and fn not in only:
        continue
    buf = io.StringIO()
    stats = []
    for c in cs:
        _, C, N, n = conv.emit(CD + 'dag_k%d_C%d.gen.txt' % (k, c), 'dagK%dC%d' % (k, c), STEP, buf)
        assert N == 2 * c - k
        stats.append((c, N, n))
        buf.write('\n')
    cl = ', '.join(str(c) for c in cs)
    head = '''module

public import OnlineColouring.CertCheck

/-!
# Certificates: `N_%d(c) ≤ 2c - %d` for `c = %s`

Paper: Appendix B, Proposition B.4 (exact values), upper bounds for `k = %d`.

Generated data (do not edit): the adversary strategies
`repro/certificates/dag_k%d_C*.gen.txt` in the format of `CertCheck.lean`, written by the
converter listed in `docs/cert_converter.md`.  The converter is not trusted: every lemma is
checked by the Lean kernel with the verified checker `checkLem` (`decide +kernel`, %d lemmas per
theorem), and `Upto.nkLE` turns the checks into the statement.  The data are marked
`noncomputable` only to skip code generation for the large literals.

%s
-/

public section

namespace OnlineColouring

namespace Cert

''' % (k, k, cl, k, k, STEP, '\n'.join('* `nkLE_%d_%d : NkLE %d %d %d` (%d lemmas).' % (k, c, k, c, N, n) for c, N, n in stats))
    open(OUT + fn + '.lean', 'w').write(head + buf.getvalue() + 'end Cert\n\nend OnlineColouring\n')
    print(fn, stats, len(buf.getvalue()))
```
