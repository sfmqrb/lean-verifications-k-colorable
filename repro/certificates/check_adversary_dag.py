#!/usr/bin/env python3
import sys, gzip, itertools

sys.setrecursionlimit(100000)


class Fail(Exception):
    pass


def open_any(path):
    return gzip.open(path, 'rt') if path.endswith('.gz') else open(path)


def colourings(n, adj, k):
    col = [-1] * n
    out = []

    def rec(v, maxc):
        if v == n:
            out.append(tuple(col))
            return
        forb = {col[u] for u in adj[v] if u < v}
        for c in range(min(k - 1, maxc + 1) + 1):
            if c not in forb:
                col[v] = c
                rec(v + 1, max(maxc, c))
        col[v] = -1

    rec(0, -1)
    return out


def extendable(n, adj, k, pre):
    col = [-1] * n
    for v, c in pre.items():
        col[v] = c
    for v, c in pre.items():
        for u in adj[v]:
            if col[u] == c:
                return False
    free = [v for v in range(n) if col[v] < 0]
    free.sort(key=lambda v: -sum(1 for u in adj[v] if col[u] >= 0))

    def rec(i):
        if i == len(free):
            return True
        v = free[i]
        forb = {col[u] for u in adj[v] if col[u] >= 0}
        for c in range(k):
            if c not in forb:
                col[v] = c
                if rec(i + 1):
                    return True
        col[v] = -1
        return False

    return rec(0)


def k_colourable(n, adj, k):
    return extendable(n, adj, k, {})


def components(n, adj):
    comp = [-1] * n
    t = 0
    for s in range(n):
        if comp[s] < 0:
            comp[s] = t
            st = [s]
            while st:
                u = st.pop()
                for w in adj[u]:
                    if comp[w] < 0:
                        comp[w] = t
                        st.append(w)
            t += 1
    return comp


def is_forest(n, adj):
    edges = sum(len(a) for a in adj) // 2
    return edges == n - max(components(n, adj) + [-1]) - 1 if n else True


class Checker:
    def __init__(self, path):
        self.path = path
        f = open_any(path)
        self.recs = [ln.split() for ln in f if ln.strip() and not ln.startswith('#')]
        f.close()
        h = self.recs[0]
        if h[0] != 'H':
            raise Fail('missing header')
        par = dict(x.split('=') for x in h[1:])
        self.k, self.forest, self.C, self.N = int(par['k']), int(par['forest']), int(par['C']), int(par['N'])
        self.transparent = int(par.get('transparent', 0))
        self.phi = []
        self.lemmas = {}
        self.height = {}
        self.state = {}
        self.stats = {'P': 0, 'W': 0, 'R': 0, 'colourings': 0}

    def walk(self, i, adj, col, allow_R):
        r = self.recs[i]
        v = len(col)
        if r[0] != 'P' or int(r[1]) != v:
            raise Fail('expected P %d at record %d, got %s' % (v, i, ' '.join(r[:6])))
        nb = [int(x) for x in r[2:]]
        if len(set(nb)) != len(nb) or any(u < 0 or u >= v for u in nb):
            raise Fail('bad neighbour list at record %d' % i)
        self.stats['P'] += 1
        adj.append(set(nb))
        for u in nb:
            adj[u].add(v)
        n = v + 1
        if self.forest and not is_forest(n, adj):
            raise Fail('not a forest after record %d' % i)
        if not k_colourable(n, adj, self.k):
            raise Fail('graph not %d-colourable after record %d' % (self.k, i))
        m = max(col) if col else 0
        used = {col[u] for u in nb}
        legal = [x for x in range(1, m + 2) if x not in used]
        seen = []
        i += 1
        hmax = 0
        while i < len(self.recs) and self.recs[i][0] == 'C' and int(self.recs[i][1]) == v:
            x = int(self.recs[i][2])
            seen.append(x)
            col.append(x)
            i += 1
            r2 = self.recs[i]
            ncol = len(set(col))
            if self.transparent and ncol < self.C:
                if r2[0] != 'Q' or int(r2[1]) != v:
                    raise Fail('transparent model: expected commitment Q %d at record %d' % (v, i))
                q = int(r2[2])
                if not (1 <= q <= self.k) or any(self.phi[u] == q for u in nb):
                    raise Fail('transparent model: commitment %d for vertex %d clashes with a neighbour' % (q, v))
                self.phi.append(q)
                i += 1
                r2 = self.recs[i]
            elif self.transparent:
                self.phi.append(0)
            if ncol >= self.C:
                if r2[0] != 'W' or int(r2[1]) != v:
                    raise Fail('expected W %d at record %d' % (v, i))
                self.stats['W'] += 1
                i += 1
                h = 0
            elif r2[0] == 'P':
                i, h = self.walk(i, adj, col, allow_R)
            elif r2[0] == 'R' and allow_R:
                h = self.reference(r2, adj, col)
                i += 1
            else:
                raise Fail('bad record after C at %d: %s' % (i, ' '.join(r2[:6])))
            hmax = max(hmax, h)
            col.pop()
            if self.transparent:
                self.phi.pop()
        if seen != legal:
            raise Fail('answers to vertex %d (record %d) are %s, legal colours are %s' % (v, i, seen, legal))
        if self.transparent and len(self.phi) != v:
            raise Fail('internal: commitment stack')
        for u in nb:
            adj[u].discard(v)
        adj.pop()
        return i, 1 + hmax

    def reference(self, r, adj, col):
        lid = int(r[1])
        p = [int(x) for x in r[2:]]
        if lid not in self.lemmas:
            raise Fail('reference to unknown lemma %d' % lid)
        hL = self.verify_lemma(lid)
        nB, colB, adjB = self.lemmas[lid][0], self.lemmas[lid][1], self.lemmas[lid][2]
        nA = len(col)
        self.stats['R'] += 1
        if len(p) != nB or len(set(p)) != nB or any(q < 0 or q >= nA for q in p):
            raise Fail('reference to lemma %d: map is not injective into the current position' % lid)
        mA = max(col) if col else 0
        mB = max(colB) if colB else 0
        if mA != mB:
            raise Fail('reference to lemma %d: colour counts differ (%d vs %d)' % (lid, mA, mB))
        sigma = {}
        for i in range(nB):
            a, b = colB[i], col[p[i]]
            if sigma.setdefault(a, b) != b:
                raise Fail('reference to lemma %d: colours not consistent' % lid)
        if len(set(sigma.values())) != len(sigma) or set(sigma) != set(range(1, mB + 1)):
            raise Fail('reference to lemma %d: colour map is not a bijection' % lid)
        for phi in self.lemma_colourings(lid):
            self.stats['colourings'] += 1
            if not extendable(nA, adj, self.k, {p[i]: phi[i] for i in range(nB)}):
                raise Fail('reference to lemma %d: a k-colouring of the lemma position does not extend' % lid)
        if self.forest:
            cB = components(nB, adjB)
            cA = components(nA, adj)
            img = {}
            for i in range(nB):
                if img.setdefault(cB[i], cA[p[i]]) != cA[p[i]]:
                    raise Fail('reference to lemma %d: a component is split' % lid)
            if len(set(img.values())) != len(img):
                raise Fail('reference to lemma %d: two components are merged' % lid)
        return hL

    def parse_colour(self, tok):
        return int(tok)

    def colour_set(self, cols):
        return set(cols)

    def lemma_colourings(self, lid):
        L = self.lemmas[lid]
        if L[5] is not None:
            return L[5]
        cs = colourings(L[0], L[2], self.k)
        if not getattr(self, 'streaming', False):
            L[5] = cs
        return cs

    def verify_lemma(self, lid):
        if lid in self.height:
            return self.height[lid]
        if self.state.get(lid) == 'busy':
            raise Fail('cyclic lemma references at %d' % lid)
        self.state[lid] = 'busy'
        n, colB, adjB, start, end, _ = self.lemmas[lid]
        if not k_colourable(n, adjB, self.k):
            raise Fail('lemma %d: start position not %d-colourable' % (lid, self.k))
        if self.forest and not is_forest(n, adjB):
            raise Fail('lemma %d: start position not a forest' % lid)
        adj = [set(a) for a in adjB]
        col = list(colB)
        i, h = self.walk(start, adj, col, True)
        if i != end:
            raise Fail('lemma %d: trailing records' % lid)
        self.height[lid] = h
        self.state[lid] = 'done'
        return h

    def run(self):
        recs = self.recs
        if recs[1][0] == 'P':
            i, h = self.walk(1, [], [], False)
            if recs[i][0] != 'E' or i != len(recs) - 1:
                raise Fail('trailing data')
            mode = 'tree'
            nlem = 0
        else:
            i = 1
            root = None
            while recs[i][0] == 'L':
                lid, n, m = int(recs[i][1]), int(recs[i][2]), int(recs[i][3])
                if lid in self.lemmas:
                    raise Fail('duplicate lemma id %d' % lid)
                V = recs[i + 1]
                G = recs[i + 2]
                if V[0] != 'V' or G[0] != 'G':
                    raise Fail('lemma %d: bad header' % lid)
                colB = [self.parse_colour(x) for x in V[1:]]
                if len(colB) != n or self.colour_set(colB) != set(range(1, m + 1)):
                    raise Fail('lemma %d: colours must be exactly 1..m' % lid)
                e = [int(x) for x in G[1:]]
                adjB = [set() for _ in range(n)]
                for j in range(0, len(e), 2):
                    u, w = e[j], e[j + 1]
                    if u == w or not (0 <= u < n and 0 <= w < n):
                        raise Fail('lemma %d: bad edge' % lid)
                    adjB[u].add(w)
                    adjB[w].add(u)
                j = i + 3
                while recs[j][0] != '/L':
                    j += 1
                self.lemmas[lid] = [n, colB, adjB, i + 3, j, None]
                i = j + 1
            if recs[i][0] != 'ROOT':
                raise Fail('missing ROOT')
            root = int(recs[i][1])
            if recs[i + 1][0] != 'E' or i + 1 != len(recs) - 1:
                raise Fail('trailing data')
            if self.lemmas[root][0] != 0:
                raise Fail('root lemma does not start from the empty position')
            for lid in sorted(self.lemmas, key=lambda x: x):
                self.verify_lemma(lid)
            h = self.height[root]
            mode = 'dag'
            nlem = len(self.lemmas)
        if h > self.N:
            raise Fail('strategy needs %d > N=%d vertices' % (h, self.N))
        if self.transparent:
            mode += ', TRANSPARENT model'
        print('OK %s [%s]: k=%d forest=%d: the adversary %s with at most %d vertices '
              '(height %d; lemmas %d, P %d, W %d, R %d, colourings tested %d)'
              % (self.path, mode, self.k, self.forest, self.claim(), self.N, h, nlem, self.stats['P'], self.stats['W'],
                 self.stats['R'], self.stats['colourings']))
        return h

    def claim(self):
        return 'forces %d colours' % self.C


class TFoldChecker(Checker):

    def __init__(self, path):
        Checker.__init__(self, path)
        par = dict(x.split('=') for x in self.recs[0][1:])
        self.t, self.goal, self.M, self.K = int(par['t']), par['goal'], int(par['M']), int(par['K'])
        if self.k != 2 or self.forest:
            raise Fail('t-fold mode is for bipartite graphs (k=2, forest=0)')

    def parse_colour(self, tok):
        return frozenset(int(y) for y in tok.split(','))

    def colour_set(self, cols):
        out = set()
        for c in cols:
            out |= c
        return out

    def claim(self):
        g = {'a': 'reaches %d colours' % self.M, 'b': 'gets a side with %d colours' % self.M,
             'c': 'gets %d two-sided colours or %d colours' % (self.M, self.K)}[self.goal]
        return 't=%d-fold, %s' % (self.t, g)

    def goal_reached(self, adj, col):
        n = len(col)
        allc = self.colour_set(col)
        if self.goal == 'a':
            return len(allc) >= self.M
        if self.goal == 'c' and len(allc) >= self.K:
            return True
        side = [-1] * n
        comps = []
        for s0 in range(n):
            if side[s0] >= 0:
                continue
            side[s0] = 0
            st = [s0]
            members = [s0]
            while st:
                u = st.pop()
                for w in adj[u]:
                    if side[w] < 0:
                        side[w] = 1 - side[u]
                        st.append(w)
                        members.append(w)
            A, B = set(), set()
            for u in members:
                (A if side[u] == 0 else B).update(col[u])
            comps.append((frozenset(A), frozenset(B)))
        best = 0
        if self.goal == 'b':
            unions = {frozenset()}
            for A, B in comps:
                unions = {u | A for u in unions} | {u | B for u in unions}
            best = max(len(u) for u in unions)
        else:
            for o in itertools.product((0, 1), repeat=len(comps)):
                L, R = set(), set()
                for (A, B), b in zip(comps, o):
                    if b:
                        A, B = B, A
                    L |= A
                    R |= B
                best = max(best, len(L & R))
        return best >= self.M

    def walk(self, i, adj, col, allow_R):
        r = self.recs[i]
        v = len(col)
        if r[0] != 'P' or int(r[1]) != v:
            raise Fail('expected P %d at record %d' % (v, i))
        nb = [int(x) for x in r[2:]]
        if len(set(nb)) != len(nb) or any(u < 0 or u >= v for u in nb):
            raise Fail('bad neighbour list at record %d' % i)
        self.stats['P'] += 1
        adj.append(set(nb))
        for u in nb:
            adj[u].add(v)
        if not k_colourable(v + 1, adj, 2):
            raise Fail('graph not bipartite after record %d' % i)
        allc = self.colour_set(col)
        m = len(allc)
        if allc != set(range(1, m + 1)):
            raise Fail('colours are not 1..m')
        F = self.colour_set([col[u] for u in nb])
        legal = []
        for j in range(0, self.t + 1):
            new = list(range(m + 1, m + j + 1))
            old = [x for x in range(1, m + 1) if x not in F]
            for comb in itertools.combinations(old, self.t - j):
                legal.append(tuple(sorted(list(comb) + new)))
        legal.sort()
        seen = []
        i += 1
        hmax = 0
        while i < len(self.recs) and self.recs[i][0] == 'C' and int(self.recs[i][1]) == v:
            X = self.parse_colour(self.recs[i][2])
            if len(X) != self.t:
                raise Fail('answer of wrong size at record %d' % i)
            seen.append(tuple(sorted(X)))
            col.append(X)
            i += 1
            r2 = self.recs[i]
            if self.goal_reached(adj, col):
                if r2[0] != 'W' or int(r2[1]) != v:
                    raise Fail('expected W %d at record %d (goal reached)' % (v, i))
                self.stats['W'] += 1
                i += 1
                h = 0
            elif r2[0] == 'P':
                i, h = self.walk(i, adj, col, allow_R)
            elif r2[0] == 'R' and allow_R:
                h = self.reference(r2, adj, col)
                i += 1
            else:
                raise Fail('bad record after C at %d: %s' % (i, ' '.join(r2[:6])))
            hmax = max(hmax, h)
            col.pop()
        if seen != legal:
            raise Fail('answers to vertex %d (record %d) are %s, legal answers are %s' % (v, i, seen[:8], legal[:8]))
        for u in nb:
            adj[u].discard(v)
        adj.pop()
        return i, 1 + hmax

    def reference(self, r, adj, col):
        lid = int(r[1])
        if '/' not in r:
            raise Fail('t-fold reference needs a colour map')
        cut = r.index('/')
        g = [[int(x) for x in tok.split('+')] for tok in r[2:cut]]
        s = [int(x) for x in r[cut + 1:]]
        if lid not in self.lemmas:
            raise Fail('reference to unknown lemma %d' % lid)
        hL = self.verify_lemma(lid)
        nB, colB, adjB = self.lemmas[lid][0], self.lemmas[lid][1], self.lemmas[lid][2]
        nA = len(col)
        self.stats['R'] += 1
        if len(g) != nB or any(not gi or len(set(gi)) != len(gi) or any(q < 0 or q >= nA for q in gi) for gi in g):
            raise Fail('reference to lemma %d: bad vertex map' % lid)
        mA = len(self.colour_set(col))
        mB = len(self.colour_set(colB))
        if mA != mB or len(s) != mB or sorted(s) != list(range(1, mA + 1)):
            raise Fail('reference to lemma %d: colour map is not a bijection' % lid)
        for i in range(nB):
            have = set()
            for q in g[i]:
                have |= col[q]
            if not {s[c - 1] for c in colB[i]} <= have:
                raise Fail('reference to lemma %d: colours of lemma vertex %d not covered' % (lid, i))
        for phi in self.lemma_colourings(lid):
            self.stats['colourings'] += 1
            pre = {}
            for i in range(nB):
                for q in g[i]:
                    if pre.setdefault(q, phi[i]) != phi[i]:
                        raise Fail('reference to lemma %d: a colouring is not consistent on the image sets' % lid)
            if not extendable(nA, adj, 2, pre):
                raise Fail('reference to lemma %d: a 2-colouring does not extend' % lid)
        cB = components(nB, adjB)
        cA = components(nA, adj)
        img = {}
        for i in range(nB):
            for q in g[i]:
                if img.setdefault(cB[i], cA[q]) != cA[q]:
                    raise Fail('reference to lemma %d: a component is split' % lid)
        if len(set(img.values())) != len(img):
            raise Fail('reference to lemma %d: two components are merged' % lid)
        return hL

def run_streaming(cls, path):
    f = open_any(path)
    it = (ln.split() for ln in f if ln.strip() and not ln.startswith('#'))
    hdr = next(it)
    chk = cls.__new__(cls)
    chk.path = path
    chk.recs = [hdr]
    if hdr[0] != 'H':
        raise Fail('missing header')
    par = dict(x.split('=') for x in hdr[1:])
    chk.k, chk.forest, chk.C, chk.N = int(par['k']), int(par['forest']), int(par['C']), int(par['N'])
    chk.transparent = int(par.get('transparent', 0))
    chk.phi = []
    chk.lemmas, chk.height, chk.state = {}, {}, {}
    chk.stats = {'P': 0, 'W': 0, 'R': 0, 'colourings': 0}
    chk.streaming = True
    if 't' in par:
        chk.t, chk.goal, chk.M, chk.K = int(par['t']), par['goal'], int(par['M']), int(par['K'])
    root = None
    intern = {}
    for rec in it:
        if rec[0] == 'L':
            lid, n, m = int(rec[1]), int(rec[2]), int(rec[3])
            if lid in chk.lemmas:
                raise Fail('duplicate lemma id %d' % lid)
            V = next(it); G = next(it)
            if V[0] != 'V' or G[0] != 'G':
                raise Fail('lemma %d: bad header' % lid)
            colB = [chk.parse_colour(x) for x in V[1:]]
            if len(colB) != n or chk.colour_set(colB) != set(range(1, m + 1)):
                raise Fail('lemma %d: colours must be exactly 1..m' % lid)
            e = [int(x) for x in G[1:]]
            adjB = [set() for _ in range(n)]
            for j in range(0, len(e), 2):
                u, w = e[j], e[j + 1]
                if u == w or not (0 <= u < n and 0 <= w < n):
                    raise Fail('lemma %d: bad edge' % lid)
                adjB[u].add(w); adjB[w].add(u)
            body = []
            for r2 in it:
                if r2[0] == '/L':
                    break
                body.append(r2)
            chk.recs = body + [['/L']]
            chk.lemmas[lid] = [n, colB, adjB, 0, len(body), None]
            for r2 in body:
                if r2[0] == 'R' and int(r2[1]) not in chk.height:
                    raise Fail('streaming mode: lemma %d references lemma %s that is not verified earlier' % (lid, r2[1]))
            chk.verify_lemma(lid)
            chk.lemmas[lid] = [n, tuple(intern.setdefault(c, c) for c in colB), tuple(tuple(sorted(a)) for a in adjB), None, None, None]
            chk.recs = None
        elif rec[0] == 'ROOT':
            root = int(rec[1])
        elif rec[0] == 'E':
            break
        else:
            raise Fail('unexpected record %s' % rec[0])
    if root is None or root not in chk.height:
        raise Fail('missing or unverified ROOT')
    if chk.lemmas[root][0] != 0:
        raise Fail('root lemma does not start from the empty position')
    h = chk.height[root]
    if h > chk.N:
        raise Fail('strategy needs %d > N=%d vertices' % (h, chk.N))
    print('OK %s [dag, streaming]: k=%d forest=%d: the adversary %s with at most %d vertices '
          '(height %d; lemmas %d, P %d, W %d, R %d, colourings tested %d)'
          % (path, chk.k, chk.forest, chk.claim(), chk.N, h, len(chk.lemmas), chk.stats['P'], chk.stats['W'],
             chk.stats['R'], chk.stats['colourings']))


if __name__ == '__main__':
    bad = 0
    streaming = '--stream' in sys.argv
    for p in [a for a in sys.argv[1:] if a != '--stream']:
        try:
            first = open_any(p).readline()
            while first.startswith('#'):
                break
            hdr = [l for l in open_any(p) if l.startswith('H ')][0]
            cls = TFoldChecker if ' t=' in hdr else Checker
            if streaming:
                run_streaming(cls, p)
            else:
                cls(p).run()
        except (Fail, IndexError, ValueError, KeyError) as e:
            print('FAIL %s: %s: %s' % (p, type(e).__name__, e))
            bad += 1
    sys.exit(1 if bad else 0)
