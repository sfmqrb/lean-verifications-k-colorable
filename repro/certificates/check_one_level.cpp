#include <bits/stdc++.h>
using namespace std;
typedef array<uint8_t, 8> Row;
static int M, C;
static vector<int> B;
static bool ADVMODE;
static long long nVisit = 0, nChild = 0;

static int dig(char ch) { if (ch >= '0' && ch <= '9') return ch - '0'; if (ch >= 'a' && ch <= 'v') return ch - 'a' + 10; return -1; }

static string canon(int t, const vector<Row>& rows, int F, vector<int>& bestPerm, vector<int>* rowOrder = nullptr) {
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
            if (!have || key < best) {
                best = key; have = true; bestPerm = p;
                if (rowOrder) { rowOrder->clear(); for (auto& r : rs) rowOrder->push_back(r.second); }
            }
            return;
        }
        int a = groups[g].first, b = groups[g].second;
        sort(p.begin() + a, p.begin() + b);
        do { rec(g + 1); } while (next_permutation(p.begin() + a, p.begin() + b));
    };
    rec(0);
    return best;
}

static unordered_map<string, Row> certAlg;
static unordered_map<string, vector<uint8_t>> certAdv;
static unordered_set<string> verified;

static Row parseRow(const string& s) { Row r{}; for (int j = 0; j < C; j++) { int v = dig(s[j]); if (v < 0) { fprintf(stderr, "bad digit\n"); exit(2); } r[j] = v; } return r; }

static void fail(const char* why) { printf("CHECK FAILED: %s\n", why); fflush(stdout); exit(1); }

static bool algSurvivesFrom(int t, vector<Row> rows) {
    if (t == M) return true;
    nVisit++;
    vector<int> perm;
    string key = canon(t, rows, -1, perm);
    if (verified.count(key)) return true;
    int n = rows.size(), full = (1 << C) - 1;
    sort(rows.begin(), rows.end());
    vector<int> pick(n);
    bool ok = true;
    function<void(int, int)> rec = [&](int i, int F) {
        if (!ok) return;
        if (i == n) {
            nChild++;
            if (F == full) { ok = false; return; }
            if (t == M - 1) return;
            vector<Row> post = rows;
            for (int q = 0; q < n; q++) post[q][pick[q]]--;
            vector<int> p2;
            string k2 = canon(t, post, F, p2);
            auto it = certAlg.find(k2);
            if (it == certAlg.end()) { ok = false; fprintf(stderr, "missing algorithm entry at t=%d\n", t); return; }
            Row mv{}; int tot = 0;
            for (int j = 0; j < C; j++) { mv[p2[j]] = it->second[j]; tot += it->second[j]; }
            if (tot != B[t]) { ok = false; fprintf(stderr, "move has wrong size\n"); return; }
            for (int c = 0; c < C; c++) if (mv[c] && (F >> c & 1)) { ok = false; fprintf(stderr, "move uses a forbidden colour\n"); return; }
            post.push_back(mv);
            if (!algSurvivesFrom(t + 1, post)) ok = false;
            return;
        }
        int lo = 0;
        if (i > 0 && rows[i] == rows[i - 1]) lo = pick[i - 1];
        for (int c = lo; c < C && ok; c++) {
            if (!rows[i][c]) continue;
            pick[i] = c;
            rec(i + 1, F | (1 << c));
        }
    };
    rec(0, 0);
    if (ok) verified.insert(key);
    return ok;
}

static bool advWinsFrom(int t, vector<Row> rows) {
    if (t == M) return false;
    nVisit++;
    vector<int> perm, ro;
    string key = canon(t, rows, -1, perm, &ro);
    if (verified.count(key)) return true;
    auto it = certAdv.find(key);
    if (it == certAdv.end()) { fprintf(stderr, "missing adversary entry at t=%d\n", t); return false; }
    int n = rows.size(), full = (1 << C) - 1;

    vector<Row> cr(n);
    for (int i = 0; i < n; i++) for (int j = 0; j < C; j++) cr[i][j] = rows[ro[i]][perm[j]];
    int F = 0;
    for (int i = 0; i < n; i++) { int c = it->second[i]; if (c >= C || cr[i][c] == 0) { fprintf(stderr, "illegal pick\n"); return false; } cr[i][c]--; F |= 1 << c; }
    if (F == full) { verified.insert(key); return true; }

    vector<int> Al; for (int c = 0; c < C; c++) if (!(F >> c & 1)) Al.push_back(c);
    Row ms{};
    bool ok = true;
    function<void(int, int)> rec = [&](int q, int left) {
        if (!ok) return;
        if (q == (int)Al.size() - 1) {
            ms[Al[q]] = left;
            nChild++;
            vector<Row> nr = cr; nr.push_back(ms);
            if (!advWinsFrom(t + 1, nr)) ok = false;
            ms[Al[q]] = 0;
            return;
        }
        for (int x = left; x >= 0 && ok; x--) { ms[Al[q]] = x; rec(q + 1, left - x); }
        ms[Al[q]] = 0;
    };
    rec(0, B[t]);
    if (ok) verified.insert(key);
    return ok;
}

int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: check_one_level CERT|-\n"); return 2; }
    istream* in; ifstream f;
    if (string(argv[1]) == "-") in = &cin; else { f.open(argv[1]); in = &f; }
    string line;
    getline(*in, line);
    { istringstream hs(line); string tag; hs >> tag; if (tag != "ONE") { fprintf(stderr, "bad header\n"); return 2; }
      hs >> M >> C; B.resize(M); for (int t = 0; t < M; t++) hs >> B[t]; string mode; hs >> mode; ADVMODE = (mode == "ADV");
      if (mode != "ADV" && mode != "ALG") { fprintf(stderr, "bad mode\n"); return 2; } }
    if (C > 8) { fprintf(stderr, "C <= 8\n"); return 2; }
    for (int t = 0; t < M; t++) if (B[t] < max(1, M - 1 - t)) { fprintf(stderr, "block %d smaller than its out-degree\n", t); return 2; }
    long long ne = 0;
    while (getline(*in, line)) {
        if (line.empty()) continue;
        istringstream ls(line); string tag; ls >> tag;
        if (tag == "A") {
            int t, F; ls >> t >> F; vector<Row> rows; string tok;
            while (ls >> tok && tok != ":") rows.push_back(parseRow(tok));
            ls >> tok; Row mv = parseRow(tok);
            vector<int> p; string k = canon(t, rows, F, p);
            Row cm{}; for (int j = 0; j < C; j++) cm[j] = mv[p[j]];
            certAlg[k] = cm; ne++;
        } else if (tag == "D") {
            int t; ls >> t; vector<Row> rows; string tok;
            while (ls >> tok && tok != ":") rows.push_back(parseRow(tok));
            vector<int> pk; int x; while (ls >> x) pk.push_back(x);
            if (pk.size() != rows.size()) { fprintf(stderr, "bad D entry\n"); return 2; }
            vector<int> p, ro; string k = canon(t, rows, -1, p, &ro);
            vector<int> pinv(C); for (int j = 0; j < C; j++) pinv[p[j]] = j;
            vector<uint8_t> cp(rows.size()); for (size_t i = 0; i < rows.size(); i++) cp[i] = pinv[pk[ro[i]]];
            certAdv[k] = cp; ne++;
        }
    }
    fprintf(stderr, "loaded %lld entries\n", ne);
    bool res;
    if (ADVMODE) res = advWinsFrom(0, {}); else res = algSurvivesFrom(0, {});
    printf("check one m=%d C=%d b=", M, C); for (int x : B) printf("%d ", x);
    if (ADVMODE) printf(" claim=adversary_forces_%d", C + 1); else printf(" claim=algorithm_survives_with_%d", C);
    printf(" result=%s visited=%lld children=%lld entries=%lld\n", res ? "VERIFIED" : "FAILED", nVisit, nChild, ne);
    return res ? 0 : 1;
}
