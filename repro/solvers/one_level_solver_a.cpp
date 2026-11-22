#include <bits/stdc++.h>
using namespace std;
typedef uint64_t u64;
typedef uint32_t u32;

static int M, C;
static int Bs[40];
static const int MAXR = 16;
static const int NSH = 32;

static inline int cnt(u64 r, int j) { return (int)((r >> (4 * j)) & 15); }
static inline int nulc(u64 r) { return (int)((r >> NSH) & 15); }
static inline u64 mix64(u64 x) {
    x += 0x9e3779b97f4a7c15ULL;
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL; x ^= x >> 27; x *= 0x94d049bb133111ebULL; x ^= x >> 31;
    return x;
}

struct St { int t, L, n; u64 r[MAXR]; };
struct Key { u64 a, b; bool operator==(const Key& o) const { return a == o.a && b == o.b; } };

static bool optNullMove = false, optWeak1 = false, optETC = true, optStats = false, optFirst = false;
static int optMaxF = -1;
static int optASupp = 99;
static int permLimit = 5040;
static int optOrd = 1;
static long long nAdv = 0, nAlg = 0, ttHit = 0, permFallback = 0, leafCalls = 0, nmCut = 0, w1Cut = 0, etcCut = 0;
static long long nodesAt[40];

struct TTE { u64 a, b; };
static TTE* TT = nullptr;
static u64 ttBuckets = 0;
static long long ttStores = 0, ttReplaced = 0;
static inline int lg2w(long long w) { int l = 1; while (w > 1 && l < 127) { w >>= 1; l++; } return l; }
static bool ttProbe(const Key& k, bool& val) {
    TTE* bk = TT + 4 * (k.a & (ttBuckets - 1));
    u64 tag = k.b >> 8;
    for (int i = 0; i < 4; i++)
        if ((bk[i].b & 0xFF) && bk[i].a == k.a && (bk[i].b >> 8) == tag) { val = (bk[i].b >> 1) & 1; return true; }
    return false;
}
static void ttStore(const Key& k, bool val, long long work) {
    TTE* bk = TT + 4 * (k.a & (ttBuckets - 1));
    u64 tag = k.b >> 8;
    u64 meta = 1 | ((u64)val << 1) | ((u64)lg2w(work) << 2);
    int victim = -1, best = 1 << 30;
    for (int i = 0; i < 4; i++) {
        if ((bk[i].b & 0xFF) && bk[i].a == k.a && (bk[i].b >> 8) == tag) { victim = i; break; }
        int w = (bk[i].b & 0xFF) ? (int)((bk[i].b >> 2) & 63) : -1;
        if (w < best) { best = w; victim = i; }
    }
    if (bk[victim].b & 0xFF) ttReplaced++;
    bk[victim].a = k.a; bk[victim].b = (tag << 8) | meta;
    ttStores++;
}

static int matchSize(int L, int n, const u32* sup, u32 colsAllowed) {
    int mc[8]; for (int j = 0; j < 8; j++) mc[j] = -1;
    int res = 0;
    for (int i = 0; i < n; i++) {
        u32 s = sup[i] & colsAllowed;
        if (!s) continue;

        int vis = 0;
        function<bool(int)> aug = [&](int r) -> bool {
            u32 ss = sup[r] & colsAllowed;
            while (ss) { int c = __builtin_ctz(ss); ss &= ss - 1;
                if (vis >> c & 1) continue; vis |= 1 << c;
                if (mc[c] < 0 || aug(mc[c])) { mc[c] = r; return true; } }
            return false;
        };
        if (aug(i)) res++;
    }
    (void)L;
    return res;
}
static inline u32 supOf(u64 r, int L) { u32 s = 0; for (int j = 0; j < L; j++) if (cnt(r, j)) s |= 1u << j; return s; }

static void normAdv(St& s) {
    int T = M - s.t;
    for (int i = 0; i < s.n; i++) {
        u64 r = s.r[i], o = 0;
        for (int j = 0; j < s.L; j++) { int c = cnt(r, j); if (c > T) c = T; o |= (u64)c << (4 * j); }
        int z = nulc(r); if (z > T) z = T; o |= (u64)z << NSH;
        s.r[i] = o;
    }
    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i < s.n && !changed; i++) {
            u64 r = s.r[i]; int sup = 0, last = -1;
            for (int j = 0; j < s.L; j++) if (cnt(r, j)) { sup++; last = j; }
            if (sup == 1 && cnt(r, last) >= T) {
                int c = last;
                u64 liveMaskOld = (s.L == 16) ? ~0ULL : ((1ULL << (4 * s.L)) - 1);
                for (int k = 0; k < s.n; k++) {
                    u64 x = s.r[k];
                    int z = nulc(x) + cnt(x, c); if (z > T) z = T;
                    u64 low = x & ((1ULL << (4 * c)) - 1);
                    u64 high = (x & liveMaskOld) >> (4 * (c + 1));
                    s.r[k] = low | (high << (4 * c)) | ((u64)z << NSH);
                }
                s.L--;
                changed = true;
            }
        }
    }
    int w = 0;
    u64 liveMask = (1ULL << (4 * s.L)) - 1;
    for (int i = 0; i < s.n; i++) if (s.r[i] & liveMask) s.r[w++] = s.r[i];
    s.n = w;
}

static inline u64 permRow(u64 r, const int* p, int L) {
    u64 o = r & (15ULL << NSH);
    for (int j = 0; j < L; j++) o |= (u64)cnt(r, p[j]) << (4 * j);
    return o;
}
static inline void sortRows(u64* a, int n) {
    for (int i = 1; i < n; i++) { u64 x = a[i]; int j = i - 1; while (j >= 0 && a[j] > x) { a[j + 1] = a[j]; j--; } a[j + 1] = x; }
}

static Key canonicalise(int type, St& s, int F, int& Fc) {
    int L = s.L, n = s.n;
    u64 h0[8], h1[8], rh[MAXR];
    for (int j = 0; j < L; j++) {
        u64 h = mix64(0x1234 + ((F >> j) & 1));
        for (int i = 0; i < n; i++) { int c = cnt(s.r[i], j); if (c) h += mix64(c * 7919 + 13); }
        h0[j] = h;
    }
    for (int i = 0; i < n; i++) {
        u64 h = mix64(nulc(s.r[i]) + 99991);
        for (int j = 0; j < L; j++) { int c = cnt(s.r[i], j); if (c) h += mix64(h0[j] * 31 + c); }
        rh[i] = h;
    }
    for (int j = 0; j < L; j++) {
        u64 h = mix64(0x5678 + ((F >> j) & 1));
        for (int i = 0; i < n; i++) { int c = cnt(s.r[i], j); if (c) h += mix64(rh[i] * 131 + c); }
        h1[j] = h;
    }
    int ord[8]; for (int j = 0; j < L; j++) ord[j] = j;
    sort(ord, ord + L, [&](int x, int y) { return h1[x] < h1[y]; });

    int gs[9], ng = 0; long long np = 1;
    for (int j = 0; j < L;) { int k = j; while (k < L && h1[ord[k]] == h1[ord[j]]) k++; gs[ng++] = j; for (int q = 2; q <= k - j; q++) np *= q; j = k; }
    gs[ng] = L;
    u64 best[MAXR], cur[MAXR]; int bestF = 0;
    bool have = false;
    int p[8]; for (int j = 0; j < L; j++) p[j] = ord[j];
    auto evalp = [&]() {
        for (int i = 0; i < n; i++) cur[i] = permRow(s.r[i], p, L);
        sortRows(cur, n);
        int fc = 0; for (int j = 0; j < L; j++) if (F >> p[j] & 1) fc |= 1 << j;
        bool better = !have;
        if (have) { for (int i = 0; i < n; i++) { if (cur[i] != best[i]) { better = cur[i] < best[i]; break; } } }
        if (better) { memcpy(best, cur, sizeof(u64) * n); bestF = fc; have = true; }
    };
    if (np > permLimit) { permFallback++; evalp(); }
    else {

        function<void(int)> rec = [&](int g) {
            if (g == ng) { evalp(); return; }
            int a = gs[g], b = gs[g + 1];
            if (b - a == 1) { rec(g + 1); return; }
            sort(p + a, p + b);
            do { rec(g + 1); } while (next_permutation(p + a, p + b));
        };
        rec(0);
    }
    memcpy(s.r, best, sizeof(u64) * n);
    Fc = bestF;
    u64 ha = mix64(((u64)type << 56) ^ ((u64)s.t << 48) ^ ((u64)L << 40) ^ ((u64)n << 32) ^ (u64)Fc);
    u64 hb = mix64(ha ^ 0xabcdef12345ULL);
    for (int i = 0; i < n; i++) { ha = mix64(ha ^ best[i]) + i; hb = mix64(hb + best[i] * 0x9E3779B97F4A7C15ULL) ^ (hb >> 7); }
    return Key{ha, hb};
}

static bool leafM2(const St& s) {
    leafCalls++;
    int n = s.n, L = s.L; u32 full = (1u << L) - 1;
    int opts[MAXR][9], no[MAXR];
    for (int i = 0; i < n; i++) { no[i] = 0; for (int j = 0; j < L; j++) if (cnt(s.r[i], j)) opts[i][no[i]++] = j; if (nulc(s.r[i])) opts[i][no[i]++] = 8; }
    int pick[MAXR];
    u32 sup[MAXR];
    function<bool(int, u32)> rec = [&](int i, u32 F) -> bool {
        if (i == n) {
            if (F == full) return true;
            for (int k = 0; k < n; k++) {
                u64 r = s.r[k];
                u32 sp = 0;
                for (int j = 0; j < L; j++) { int c = cnt(r, j) - (pick[k] == j); if (c > 0) sp |= 1u << j; }
                sup[k] = sp;
            }
            u32 A = full & ~F;
            while (A) { int a = __builtin_ctz(A); A &= A - 1;
                u32 need = full & ~(1u << a);
                if (matchSize(L, n, sup, need) < __builtin_popcount(need)) return false; }
            return true;
        }
        int lo = 0;
        if (i > 0 && s.r[i] == s.r[i - 1]) { for (int q = 0; q < no[i]; q++) if (opts[i][q] == pick[i - 1]) lo = q; }
        for (int q = lo; q < no[i]; q++) {
            pick[i] = opts[i][q];
            if (rec(i + 1, opts[i][q] == 8 ? F : (F | (1u << opts[i][q])))) return true;
        }
        return false;
    };
    return rec(0, 0);
}

static bool advNode(St s, const Key* knownKey);
static bool algNode(St s, int F, const Key& key);

struct AChild { St s; int F; Key k; int sc; };
struct BChild { St s; Key k; int sc; };

static bool advEval(St& s);

static bool advNode(St s, const Key* knownKey) {
    nAdv++; nodesAt[s.t]++;
    Key k;
    if (!knownKey) {
        normAdv(s);
        if (s.L == 0) return true;
        if (s.t >= M) return false;
        int dummy; k = canonicalise(0, s, 0, dummy);
    } else k = *knownKey;
    if (s.L == 0) return true;
    if (s.t >= M) return false;
    {
        u32 sup[MAXR]; for (int i = 0; i < s.n; i++) sup[i] = supOf(s.r[i], s.L);
        if (s.n >= s.L && matchSize(s.L, s.n, sup, (1u << s.L) - 1) == s.L) return true;
    }
    if (s.t == M - 1) return false;
    if (s.t == M - 2) return leafM2(s);
    bool v;
    if (ttProbe(k, v)) { ttHit++; return v; }
    long long w0 = nAdv + nAlg;

    int n = s.n, L = s.L; u32 full = (1u << L) - 1;
    int T = M - s.t, d = T - 1;
    int opts[MAXR][9], no[MAXR];
    for (int i = 0; i < n; i++) { no[i] = 0; for (int j = 0; j < L; j++) if (cnt(s.r[i], j)) opts[i][no[i]++] = j; if (nulc(s.r[i])) opts[i][no[i]++] = 8; }
    int target = 0;
    if (optMaxF >= 0) {
        u32 sup[MAXR]; for (int i = 0; i < n; i++) sup[i] = supOf(s.r[i], L);
        target = max(0, matchSize(L, n, sup, full) - optMaxF);
    }
    vector<AChild> ch;
    unordered_set<u64> seen;
    int pick[MAXR];
    function<void(int, u32)> rec = [&](int i, u32 F) {
        if (i == n) {
            if (optMaxF >= 0 && __builtin_popcount(F) < target) return;

            int pc[9] = {0};
            for (int q = 0; q < n; q++) pc[pick[q]]++;
            for (int q = 0; q < n; q++) if (pick[q] != 8 && pc[pick[q]] >= 2 && nulc(s.r[q])) return;
            AChild c; c.s.t = s.t; c.s.L = L; c.s.n = n;
            for (int q = 0; q < n; q++) {
                u64 r = s.r[q];
                if (pick[q] == 8) r -= 1ULL << NSH; else r -= 1ULL << (4 * pick[q]);

                u64 o = 0;
                for (int j = 0; j < L; j++) { int x = cnt(r, j); if (x > d) x = d; o |= (u64)x << (4 * j); }
                int z = nulc(r); if (z > d) z = d; o |= (u64)z << NSH;
                c.s.r[q] = o;
            }
            int Fc;
            c.k = canonicalise(1, c.s, (int)F, Fc);
            if (!seen.insert(c.k.a).second) return;
            c.F = Fc;
            c.sc = __builtin_popcount(F) * 1000;
            if (optOrd >= 1) {
                u32 sup[MAXR]; for (int q = 0; q < n; q++) sup[q] = supOf(c.s.r[q], L);
                c.sc += matchSize(L, n, sup, full) * 10;
                int tot = 0; for (int q = 0; q < n; q++) tot += __builtin_popcount(sup[q]);
                c.sc += tot;
            }
            ch.push_back(c);
            return;
        }
        int lo = 0;
        if (i > 0 && s.r[i] == s.r[i - 1]) { for (int q = 0; q < no[i]; q++) if (opts[i][q] == pick[i - 1]) lo = q; }
        for (int q = lo; q < no[i]; q++) {
            pick[i] = opts[i][q];
            if (optMaxF >= 0) { int newF = __builtin_popcount(opts[i][q] == 8 ? F : (F | (1u << opts[i][q]))); if (newF + (n - i - 1) < target) continue; }
            rec(i + 1, opts[i][q] == 8 ? F : (F | (1u << opts[i][q])));
        }
    };
    if (n == 0) {
        AChild c; c.s = s; c.F = 0; int Fc; c.k = canonicalise(1, c.s, 0, Fc); c.sc = 0; ch.push_back(c);
    } else rec(0, 0);

    for (auto& c : ch) if (c.F == (int)full) { ttStore(k, true, 1); return true; }
    if (optETC) for (auto& c : ch) { bool vv; if (ttProbe(c.k, vv) && vv) { etcCut++; ttStore(k, true, nAdv + nAlg - w0 + 1); return true; } }
    stable_sort(ch.begin(), ch.end(), [](const AChild& x, const AChild& y) { return x.sc > y.sc; });
    bool win = false;
    for (auto& c : ch) { if (algNode(c.s, c.F, c.k)) { win = true; break; } }
    ttStore(k, win, nAdv + nAlg - w0 + 1);
    return win;
}

static vector<string> firstMoves;

static bool algNode(St s, int F, const Key& key) {
    nAlg++;
    int L = s.L, n = s.n, t = s.t; u32 full = (1u << L) - 1;
    if ((u32)F == full) return true;
    if (t >= M - 1) return false;
    bool v;
    if (!(optFirst && t == 0) && ttProbe(key, v)) { ttHit++; return v; }
    long long w0 = nAdv + nAlg;
    int d = M - 1 - t, b = Bs[t];
    u32 A = full & ~(u32)F;
    auto makeChild = [&](u64 newRow, bool hasRow) {
        BChild c; c.s.t = t + 1; c.s.L = L; c.s.n = n;
        memcpy(c.s.r, s.r, sizeof(u64) * n);
        if (hasRow) c.s.r[c.s.n++] = newRow;
        normAdv(c.s);
        int dummy; c.k = canonicalise(0, c.s, 0, dummy);
        c.sc = 0;
        return c;
    };

    for (int i = 0; i < n; i++) {
        u32 sp = supOf(s.r[i], L);
        if (__builtin_popcount(sp) == 1 && (sp & A) && cnt(s.r[i], __builtin_ctz(sp)) >= d) {
            int c = __builtin_ctz(sp);
            BChild ch = makeChild((u64)d << (4 * c), true);
            bool r = advNode(ch.s, &ch.k);
            if (!(optFirst && t == 0)) ttStore(key, r, nAdv + nAlg - w0 + 1);
            return r;
        }
    }

    if (optNullMove) {
        BChild ch = makeChild(0, false);
        if (advNode(ch.s, &ch.k)) { nmCut++; ttStore(key, true, nAdv + nAlg - w0 + 1); return true; }
    }
    u32 Aeff = A;
    if (optWeak1 && d >= 2) {
        u32 Ab = A;
        while (Ab) { int a = __builtin_ctz(Ab); Ab &= Ab - 1;
            u64 w = (1ULL << (4 * a)) | ((u64)(d - 1) << NSH);
            BChild ch = makeChild(w, true);
            if (advNode(ch.s, &ch.k)) Aeff &= ~(1u << a);
        }
        if (!Aeff) { w1Cut++; ttStore(key, true, nAdv + nAlg - w0 + 1); return true; }
    }

    int Al[8], na = 0;
    { u32 x = Aeff; while (x) { Al[na++] = __builtin_ctz(x); x &= x - 1; } }
    u64 colsig[8];
    for (int q = 0; q < na; q++) { u64 h = 0; for (int i = 0; i < n; i++) h = h * 17 + cnt(s.r[i], Al[q]); colsig[q] = h; }

    { int idx[8]; for (int q = 0; q < na; q++) idx[q] = q;
      stable_sort(idx, idx + na, [&](int x, int y) { return colsig[x] < colsig[y]; });
      int Al2[8]; u64 cs2[8]; for (int q = 0; q < na; q++) { Al2[q] = Al[idx[q]]; cs2[q] = colsig[idx[q]]; }
      memcpy(Al, Al2, sizeof(Al)); memcpy(colsig, cs2, sizeof(colsig)); }
    bool same[8]; for (int q = 0; q < na; q++) same[q] = q > 0 && colsig[q] == colsig[q - 1];
    vector<BChild> ch;
    unordered_set<u64> seen;
    vector<string> desc;
    int freq[8] = {0};
    for (int j = 0; j < L; j++) for (int i = 0; i < n; i++) freq[j] += cnt(s.r[i], j);

    for (int q = 0; q < na; q++) {
        if (same[q]) continue;
        BChild c = makeChild((u64)d << (4 * Al[q]), true);
        if (!seen.insert(c.k.a).second) continue;
        c.sc = (optOrd >= 2) ? 0 : 100000 + (optOrd >= 1 ? freq[Al[q]] : 0);
        ch.push_back(c);
        if (optFirst && t == 0) desc.push_back("mono");
    }

    if (d >= 2 && (long long)na * (d - 1) >= b) {
        int x[8] = {0};
        function<void(int, int)> rec = [&](int q, int left) {
            if (q == na) {
                if (left) return;
                int supp = 0; u64 row = 0;
                for (int z = 0; z < na; z++) if (x[z]) { supp++; row |= (u64)x[z] << (4 * Al[z]); }
                if (supp > optASupp) return;
                BChild c = makeChild(row, true);
                if (!seen.insert(c.k.a).second) return;
                int fs = 0; for (int z = 0; z < na; z++) fs += x[z] * freq[Al[z]];
                c.sc = 50000 - supp * 1000 + (optOrd >= 1 ? fs : 0);
                ch.push_back(c);
                if (optFirst && t == 0) { string ds = "spread"; for (int z = 0; z < na; z++) ds += " " + to_string(x[z]); desc.push_back(ds); }
                return;
            }
            int rem = na - q - 1;
            int ub = min(d - 1, left);
            if (same[q]) ub = min(ub, x[q - 1]);
            for (int y = ub; y >= 0; y--) {
                if (left - y > rem * (d - 1)) break;
                x[q] = y;
                rec(q + 1, left - y);
            }
            x[q] = 0;
        };
        rec(0, b);
    }
    if (optFirst && t == 0) {
        for (size_t i = 0; i < ch.size(); i++) if (!advNode(ch[i].s, &ch[i].k)) firstMoves.push_back(desc[i]);
        return firstMoves.empty();
    }
    if (optETC) for (auto& c : ch) { bool vv; if (ttProbe(c.k, vv) && !vv) { etcCut++; ttStore(key, false, nAdv + nAlg - w0 + 1); return false; } }
    stable_sort(ch.begin(), ch.end(), [](const BChild& x, const BChild& y) { return x.sc > y.sc; });
    bool advWin = true;
    for (auto& c : ch) { if (!advNode(c.s, &c.k)) { advWin = false; break; } }
    ttStore(key, advWin, nAdv + nAlg - w0 + 1);
    return advWin;
}

typedef array<uint8_t, 8> FRow;
static string fcanon(int t, const vector<FRow>& rows, int F, vector<int>& bestPerm, vector<int>* rowOrder) {
    int n = rows.size();
    vector<vector<int>> inv(C);
    for (int c = 0; c < C; c++) {
        inv[c].push_back(F >= 0 ? ((F >> c) & 1) : 0);
        vector<int> col; for (int i = 0; i < n; i++) col.push_back(rows[i][c]);
        sort(col.rbegin(), col.rend());
        for (int x : col) inv[c].push_back(x);
    }
    vector<int> ord(C); iota(ord.begin(), ord.end(), 0);
    stable_sort(ord.begin(), ord.end(), [&](int a, int b) { return inv[a] < inv[b]; });
    vector<pair<int,int>> groups;
    for (int i = 0; i < C;) { int j = i; while (j < C && inv[ord[j]] == inv[ord[i]]) j++; groups.push_back({i, j}); i = j; }
    string best; bool have = false;
    vector<int> p = ord;
    function<void(int)> rec = [&](int g) {
        if (g == (int)groups.size()) {
            vector<pair<string,int>> rs(n);
            for (int i = 0; i < n; i++) { string s(C, 0); for (int j = 0; j < C; j++) s[j] = (char)rows[i][p[j]]; rs[i] = {s, i}; }
            sort(rs.begin(), rs.end());
            string key; key.push_back((char)t); key.push_back((char)n);
            int Fc = 0; if (F >= 0) for (int j = 0; j < C; j++) if (F >> p[j] & 1) Fc |= 1 << j;
            key.push_back((char)(F >= 0 ? Fc : 255));
            for (auto& r : rs) key += r.first;
            if (!have || key < best) { best = key; have = true; bestPerm = p; if (rowOrder) { rowOrder->clear(); for (auto& r : rs) rowOrder->push_back(r.second); } }
            return;
        }
        int a = groups[g].first, b = groups[g].second;
        sort(p.begin() + a, p.begin() + b);
        do { rec(g + 1); } while (next_permutation(p.begin() + a, p.begin() + b));
    };
    rec(0);
    return best;
}
struct H128 { u64 a, b; bool operator==(const H128& o) const { return a == o.a && b == o.b; } };
struct H128h { size_t operator()(const H128& h) const { return h.a; } };
static H128 hstr(const string& s) { u64 a = 0x1234567, b = 0x89abcdef; for (unsigned char ch : s) { a = mix64(a ^ ch); b = mix64(b + ch * 0x9E3779B97F4A7C15ULL) ^ (b >> 11); } return {a, b}; }
static unordered_set<H128, H128h> exSeenAdv, exSeenAlg;
static FILE* certOut = nullptr;
static long long exEntries = 0, exErrors = 0, exCalls = 0;
static char d32(int v) { return v < 10 ? '0' + v : 'a' + v - 10; }
static string rowStr(const FRow& r) { string s; for (int j = 0; j < C; j++) s.push_back(d32(r[j])); return s; }

static bool redAdvValue(int t, const vector<FRow>& rows) {
    St s; s.t = t; s.L = C; s.n = rows.size(); int T = M - t;
    for (int i = 0; i < s.n; i++) { u64 r = 0; for (int j = 0; j < C; j++) r |= (u64)min((int)rows[i][j], T) << (4 * j); s.r[i] = r; }
    normAdv(s);
    if (s.L == 0) return true;
    int dummy; Key k = canonicalise(0, s, 0, dummy);
    exCalls++;
    return advNode(s, &k);
}

static bool redAlgValue(int t, const vector<FRow>& pre, const vector<int>& picks, int Ffull) {
    int T = M - t, d = T - 1, n = pre.size();

    vector<FRow> cp = pre; for (auto& r : cp) for (int j = 0; j < C; j++) r[j] = min((int)r[j], T);
    int perm = 0; bool ch = true;
    while (ch) { ch = false;
        for (int i = 0; i < n && !ch; i++) { int sup = 0, last = -1; for (int j = 0; j < C; j++) if (!(perm >> j & 1) && cp[i][j]) { sup++; last = j; }
            if (sup == 1 && cp[i][last] >= T) { perm |= 1 << last; ch = true; } } }
    int full = (1 << C) - 1;
    if (perm == full) return true;
    if ((Ffull | perm) == full) return true;
    vector<int> live; for (int j = 0; j < C; j++) if (!(perm >> j & 1)) live.push_back(j);
    St s; s.t = t; s.L = live.size(); s.n = 0;
    for (int i = 0; i < n; i++) {
        FRow r = pre[i]; r[picks[i]]--;
        u64 o = 0; int z = 0, liveTot = 0;
        for (int q = 0; q < (int)live.size(); q++) { int x = min((int)r[live[q]], d); o |= (u64)x << (4 * q); liveTot += x; }
        for (int j = 0; j < C; j++) if (perm >> j & 1) z += r[j];
        z = min(z, d); o |= (u64)z << NSH;
        if (liveTot) s.r[s.n++] = o;
    }
    int Fr = 0; for (int q = 0; q < (int)live.size(); q++) if (Ffull >> live[q] & 1) Fr |= 1 << q;
    int Fc; Key k = canonicalise(1, s, Fr, Fc);
    exCalls++;
    return algNode(s, Fc, k);
}

static void exAdvALG(int t, vector<FRow> rows);
static void exAlgALG(int t, const vector<FRow>& post, int F) {
    vector<int> p; string k = fcanon(t, post, F, p, nullptr);
    H128 h = hstr(k);
    if (exSeenAlg.count(h)) return;
    exSeenAlg.insert(h);
    int d = M - 1 - t, b = Bs[t];
    vector<int> Al; for (int c = 0; c < C; c++) if (!(F >> c & 1)) Al.push_back(c);
    vector<FRow> cands;
    for (int c : Al) { FRow mv{}; mv[c] = b; cands.push_back(mv); }
    if (d >= 2 && (long long)Al.size() * (d - 1) >= b) {
        vector<FRow> sp; FRow x{};
        function<void(int, int)> rec = [&](int q, int left) {
            if (q == (int)Al.size()) { if (!left) sp.push_back(x); return; }
            int rem = Al.size() - q - 1;
            for (int y = min(d - 1, left); y >= 0; y--) { if (left - y > rem * (d - 1)) break; x[Al[q]] = y; rec(q + 1, left - y); }
            x[Al[q]] = 0;
        };
        rec(0, b);
        stable_sort(sp.begin(), sp.end(), [&](const FRow& a, const FRow& bb) { int sa = 0, sb = 0; for (int j = 0; j < C; j++) { sa += a[j] > 0; sb += bb[j] > 0; } return sa < sb; });
        for (auto& v : sp) cands.push_back(v);
    }
    for (auto& mv : cands) {
        vector<FRow> nr = post; nr.push_back(mv);
        if (!redAdvValue(t + 1, nr)) {
            fprintf(certOut, "A %d %d", t, F);
            for (auto& r : post) fprintf(certOut, " %s", rowStr(r).c_str());
            fprintf(certOut, " : %s\n", rowStr(mv).c_str());
            exEntries++;
            exAdvALG(t + 1, nr);
            return;
        }
    }
    exErrors++;
    fprintf(stderr, "extract: no surviving move found at t=%d\n", t);
}
static void exAdvALG(int t, vector<FRow> rows) {
    if (t >= M - 1) {
        if (t == M - 1) {  }
        if (t == M) return;
    }
    vector<int> p; string k = fcanon(t, rows, -1, p, nullptr);
    H128 h = hstr(k);
    if (exSeenAdv.count(h)) return;
    exSeenAdv.insert(h);
    sort(rows.begin(), rows.end());
    int n = rows.size(), full = (1 << C) - 1;
    vector<int> pick(n);
    function<void(int, int)> rec = [&](int i, int F) {
        if (i == n) {
            if (F == full) { exErrors++; fprintf(stderr, "extract: adversary covers at t=%d\n", t); return; }
            if (t == M - 1) return;
            vector<FRow> post = rows;
            for (int q = 0; q < n; q++) post[q][pick[q]]--;
            exAlgALG(t, post, F);
            return;
        }
        int lo = 0; if (i > 0 && rows[i] == rows[i - 1]) lo = pick[i - 1];
        for (int c = lo; c < C; c++) { if (!rows[i][c]) continue; pick[i] = c; rec(i + 1, F | (1 << c)); }
    };
    rec(0, 0);
}

static void exAdvADV(int t, vector<FRow> rows) {
    if (t >= M) { exErrors++; fprintf(stderr, "extract: reached t=M\n"); return; }
    vector<int> p; string k = fcanon(t, rows, -1, p, nullptr);
    H128 h = hstr(k);
    if (exSeenAdv.count(h)) return;
    exSeenAdv.insert(h);
    sort(rows.begin(), rows.end());
    int n = rows.size(), full = (1 << C) - 1;

    vector<pair<int, vector<int>>> cand;
    vector<int> pick(n);
    function<void(int, int)> rec = [&](int i, int F) {
        if (i == n) { cand.push_back({__builtin_popcount(F), pick}); return; }
        int lo = 0; if (i > 0 && rows[i] == rows[i - 1]) lo = pick[i - 1];
        for (int c = lo; c < C; c++) { if (!rows[i][c]) continue; pick[i] = c; rec(i + 1, F | (1 << c)); }
    };
    if (n == 0) cand.push_back({0, {}}); else rec(0, 0);
    stable_sort(cand.begin(), cand.end(), [](const pair<int, vector<int>>& a, const pair<int, vector<int>>& b) { return a.first > b.first; });
    for (auto& cd : cand) {
        int F = 0; for (int q = 0; q < n; q++) F |= 1 << cd.second[q];
        bool win = (F == full) || redAlgValue(t, rows, cd.second, F);
        if (!win) continue;
        fprintf(certOut, "D %d", t);
        for (auto& r : rows) fprintf(certOut, " %s", rowStr(r).c_str());
        fprintf(certOut, " :");
        for (int q = 0; q < n; q++) fprintf(certOut, " %d", cd.second[q]);
        fprintf(certOut, "\n");
        exEntries++;
        if (F == full) return;
        vector<FRow> post = rows;
        for (int q = 0; q < n; q++) post[q][cd.second[q]]--;
        vector<int> Al; for (int c = 0; c < C; c++) if (!(F >> c & 1)) Al.push_back(c);
        FRow ms{};
        function<void(int, int)> rm = [&](int q, int left) {
            if (q == (int)Al.size() - 1) { ms[Al[q]] = left; vector<FRow> nr = post; nr.push_back(ms); exAdvADV(t + 1, nr); ms[Al[q]] = 0; return; }
            for (int x = left; x >= 0; x--) { ms[Al[q]] = x; rm(q + 1, left - x); }
            ms[Al[q]] = 0;
        };
        rm(0, Bs[t]);
        return;
    }
    exErrors++;
    fprintf(stderr, "extract: no winning pick found at t=%d\n", t);
}

int main(int argc, char** argv) {
    if (argc < 4) { fprintf(stderr, "usage: m C (min|b_0..b_{m-1}) [opts]\n"); return 1; }
    M = atoi(argv[1]); C = atoi(argv[2]);
    int ttLog = 22;
    string certPath;
    vector<string> rest;
    for (int i = 3; i < argc; i++) {
        string a = argv[i];
        if (a == "-tt") ttLog = atoi(argv[++i]);
        else if (a == "-nm") optNullMove = true;
        else if (a == "-w1") optWeak1 = true;
        else if (a == "-noetc") optETC = false;
        else if (a == "-maxF") optMaxF = atoi(argv[++i]);
        else if (a == "-asupp") optASupp = atoi(argv[++i]);
        else if (a == "-plim") permLimit = atoi(argv[++i]);
        else if (a == "-ord") optOrd = atoi(argv[++i]);
        else if (a == "-stats") optStats = true;
        else if (a == "-first") optFirst = true;
        else if (a == "-cert") certPath = argv[++i];
        else rest.push_back(a);
    }
    if (rest.empty()) { fprintf(stderr, "sizes?\n"); return 1; }
    if (rest[0] == "min") { for (int t = 0; t < M; t++) Bs[t] = max(1, M - 1 - t); }
    else { if ((int)rest.size() != M) { fprintf(stderr, "need %d sizes\n", M); return 1; } for (int t = 0; t < M; t++) Bs[t] = atoi(rest[t].c_str()); }
    for (int t = 0; t < M; t++) if (Bs[t] < max(1, M - 1 - t)) { fprintf(stderr, "block %d too small\n", t); return 1; }
    if (C > 8 || M > 15) { fprintf(stderr, "C <= 8 and m <= 15 required\n"); return 1; }
    ttBuckets = 1ULL << (ttLog - 2);
    TT = (TTE*)calloc(ttBuckets * 4, sizeof(TTE));
    if (!TT) { fprintf(stderr, "TT alloc failed\n"); return 1; }
    auto t0 = chrono::steady_clock::now();
    St root; root.t = 0; root.L = C; root.n = 0;
    bool w = advNode(root, nullptr);
    double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    if (optFirst) { printf("surviving first moves (%zu):\n", firstMoves.size()); for (auto& s : firstMoves) printf("  %s\n", s.c_str()); }
    printf("m=%d C=%d sizes=", M, C);
    for (int t = 0; t < M; t++) printf("%d ", Bs[t]);
    printf(" adversary_forces_%d=%d advNodes=%lld algNodes=%lld ttHit=%lld leaf=%lld time=%.2fs", C + 1, (int)w, nAdv, nAlg, ttHit, leafCalls, secs);
    if (optMaxF >= 0) printf(" [adversary restricted maxF%d: a 0 proves nothing]", optMaxF);
    if (optASupp < 99) printf(" [algorithm restricted asupp%d: a 1 proves nothing]", optASupp);
    printf("\n");
    if (!certPath.empty()) {
        certOut = fopen(certPath.c_str(), "w");
        fprintf(certOut, "ONE %d %d", M, C); for (int t = 0; t < M; t++) fprintf(certOut, " %d", Bs[t]); fprintf(certOut, " %s\n", w ? "ADV" : "ALG");
        auto t1 = chrono::steady_clock::now();
        if (w) exAdvADV(0, {}); else exAdvALG(0, {});
        fclose(certOut);
        printf("certificate %s: %s entries=%lld errors=%lld solverCalls=%lld advStates=%zu algStates=%zu time=%.1fs\n", certPath.c_str(), w ? "ADV" : "ALG", exEntries, exErrors, exCalls, exSeenAdv.size(), exSeenAlg.size(), chrono::duration<double>(chrono::steady_clock::now() - t1).count());
    }
    if (optStats) {
        printf("  ttStores=%lld replaced=%lld permFallback=%lld nmCut=%lld w1Cut=%lld etcCut=%lld\n  advNodes by t:", ttStores, ttReplaced, permFallback, nmCut, w1Cut, etcCut);
        for (int t = 0; t < M; t++) printf(" %lld", nodesAt[t]);
        printf("\n");
    }
    return 0;
}
