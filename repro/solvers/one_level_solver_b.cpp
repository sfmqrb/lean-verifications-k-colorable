#include <bits/stdc++.h>
using namespace std;
typedef vector<uint8_t> Row;
int M, C;
vector<int> B;
struct HashS { size_t operator()(const string& s) const { return std::hash<string>()(s); } };
unordered_map<string, char> memo;
long long nodes = 0;
bool listFirst = false;
int restrictSlack = -1;
vector<string> firstMoves;

static string canon(int t, const vector<Row>& rows) {

    int R = rows.size();
    vector<vector<int>> sig(C);
    for (int j = 0; j < C; j++) {
        for (int i = 0; i < R; i++) sig[j].push_back(rows[i][j]);
        sort(sig[j].begin(), sig[j].end());
    }
    vector<int> cols(C);
    iota(cols.begin(), cols.end(), 0);
    sort(cols.begin(), cols.end(), [&](int a, int b) { return sig[a] > sig[b]; });

    vector<pair<int,int>> groups;
    for (int i = 0; i < C;) {
        int j = i;
        while (j < C && sig[cols[j]] == sig[cols[i]]) j++;
        groups.push_back({i, j});
        i = j;
    }
    long long nperm = 1;
    for (auto& g : groups) for (int x = 2; x <= g.second - g.first; x++) nperm *= x;
    string best;
    bool have = false;
    auto evalp = [&](const vector<int>& cp) {
        vector<string> rs(R);
        for (int i = 0; i < R; i++) {
            string s(C, 0);
            for (int j = 0; j < C; j++) s[j] = (char)rows[i][cp[j]];
            rs[i] = s;
        }
        sort(rs.begin(), rs.end());
        string out;
        out.push_back((char)t);
        for (auto& s : rs) out += s;
        if (!have || out < best) { best = out; have = true; }
    };
    if (nperm > 720) {
        evalp(cols);
        return best;
    }

    vector<int> cp = cols;

    function<void(int)> rec = [&](int gi) {
        if (gi == (int)groups.size()) { evalp(cp); return; }
        int a = groups[gi].first, b = groups[gi].second;
        sort(cp.begin() + a, cp.begin() + b);
        do { rec(gi + 1); } while (next_permutation(cp.begin() + a, cp.begin() + b));
    };
    rec(0);
    return best;
}

bool advWins(int t, vector<Row> rows);

bool algSurvives(int t, const vector<Row>& rows, int Fmask) {
    int full = (1 << C) - 1;
    if (Fmask == full) return false;
    int d = M - 1 - t;
    if (d == 0) {

        return !advWins(t + 1, rows);
    }
    vector<int> A;
    for (int c = 0; c < C; c++) if (!(Fmask >> c & 1)) A.push_back(c);

    vector<Row> base = rows;
    for (auto& r : base) for (auto& x : r) if (x > d) x = d;

    vector<string> ck(C);
    for (int c = 0; c < C; c++) { string s; for (auto& r : base) s.push_back((char)r[c]); ck[c] = s; }
    stable_sort(A.begin(), A.end(), [&](int a, int b) { return ck[a] < ck[b]; });
    vector<char> sameAsPrev(A.size(), 0);
    for (size_t i = 1; i < A.size(); i++) sameAsPrev[i] = (ck[A[i]] == ck[A[i - 1]]);
    set<string> seen;

    for (size_t ai = 0; ai < A.size(); ai++) {
        if (sameAsPrev[ai]) continue;
        int c = A[ai];
        vector<Row> nr = base;
        Row r(C, 0); r[c] = d;
        nr.push_back(r);
        string key = canon(t + 1, nr);
        if (seen.count(key)) continue;
        seen.insert(key);
        if (!advWins(t + 1, nr)) { if (listFirst && t == 0) { firstMoves.push_back("mono"); continue; } return true; }
    }

    int bt = B[t];
    if ((long long)A.size() * (d - 1) >= bt) {
        Row r(C, 0);
        bool found = false;
        function<bool(int,int)> rec = [&](int idx, int left) -> bool {
            if (idx == (int)A.size()) {
                if (left != 0) return false;
                vector<Row> nr = base; nr.push_back(r);
                string key = canon(t + 1, nr);
                if (seen.count(key)) return false;
                seen.insert(key);
                if (!advWins(t + 1, nr)) {
                    if (listFirst && t == 0) { string s = "spread"; for (int c : A) s += " " + to_string(r[c]); firstMoves.push_back(s); return false; }
                    return true; }
                return false;
            }
            int rem = (int)A.size() - idx - 1;
            int ub = min(d - 1, left);
            if (idx > 0 && sameAsPrev[idx]) ub = min(ub, (int)r[A[idx - 1]]);
            for (int x = ub; x >= 0; x--) {
                if (left - x > rem * (d - 1)) break;
                r[A[idx]] = x;
                if (rec(idx + 1, left - x)) return true;
            }
            r[A[idx]] = 0;
            return false;
        };
        found = rec(0, bt);
        if (found) return true;
    }
    return false;
}

bool advWins(int t, vector<Row> rows) {
    if (t == M) return false;
    nodes++;

    int rem = M - t;
    for (auto& r : rows) for (auto& x : r) if (x > rem) x = rem;
    string key = canon(t, rows);
    auto it = memo.find(key);
    if (it != memo.end()) return it->second;

    int R = rows.size();
    bool win = false;
    set<string> seen;
    vector<Row> cur = rows;
    int target = 0;
    if (restrictSlack >= 0) {

        vector<int> mc(C, -1);
        for (int i = 0; i < R; i++) {
            vector<char> vis(C, 0);
            function<bool(int)> aug = [&](int r) -> bool {
                for (int c = 0; c < C; c++) if (rows[r][c] > 0 && !vis[c]) {
                    vis[c] = 1;
                    if (mc[c] < 0 || aug(mc[c])) { mc[c] = r; return true; }
                }
                return false;
            };
            aug(i);
        }
        int mx = 0; for (int c = 0; c < C; c++) if (mc[c] >= 0) mx++;
        target = max(0, mx - restrictSlack);
    }
    function<void(int,int)> rec = [&](int i, int Fmask) {
        if (win) return;
        if (restrictSlack >= 0 && __builtin_popcount(Fmask) + (R - i) < target) return;
        if (i == R) {

            vector<Row> withF = cur;
            Row fr(C, 0); for (int c = 0; c < C; c++) if (Fmask >> c & 1) fr[c] = 254;
            withF.push_back(fr);
            string k2 = canon(t, withF);
            if (seen.count(k2)) return;
            seen.insert(k2);
            if (!algSurvives(t, cur, Fmask)) win = true;
            return;
        }

        for (int pass = 0; pass < 2 && !win; pass++)
        for (int c = 0; c < C && !win; c++) {
            if (cur[i][c] == 0) continue;
            bool isNew = !(Fmask >> c & 1);
            if ((pass == 0) != isNew) continue;
            cur[i][c]--;
            rec(i + 1, Fmask | (1 << c));
            cur[i][c]++;
        }
    };
    rec(0, 0);
    memo[key] = win;
    return win;
}

int main(int argc, char** argv) {
    if (argc < 4) { fprintf(stderr, "usage\n"); return 1; }
    M = atoi(argv[1]); C = atoi(argv[2]);
    bool verbose = false;
    vector<string> args;
    for (int i = 3; i < argc; i++) { if (string(argv[i]) == "-v") verbose = true; else if (string(argv[i]) == "-first") listFirst = true; else if (string(argv[i]).rfind("-maxF", 0) == 0) restrictSlack = atoi(argv[i] + 5); else args.push_back(argv[i]); }
    if (args[0] == "min") {
        for (int t = 0; t < M; t++) B.push_back(max(1, M - 1 - t));
    } else if (args[0] == "uni") {
        int b = atoi(args[1].c_str());
        for (int t = 0; t < M; t++) B.push_back(max(min(b, 1 << 20), max(1, M - 1 - t)));
    } else {
        for (auto& a : args) B.push_back(atoi(a.c_str()));
    }
    if ((int)B.size() != M) { fprintf(stderr, "need %d sizes\n", M); return 1; }
    for (int t = 0; t < M; t++) if (B[t] < max(1, M - 1 - t)) { fprintf(stderr, "block %d too small\n", t); return 1; }
    for (int t = 0; t < M; t++) if (B[t] > 250) B[t] = 250;
    bool w = advWins(0, {});
    if (listFirst) { w = firstMoves.empty(); printf("surviving first moves (%zu):\n", firstMoves.size()); for (auto& s : firstMoves) printf("  %s\n", s.c_str()); }
    printf("m=%d C=%d sizes=", M, C);
    for (int x : B) printf("%d ", x);
    printf(" adversary_forces_%d=%d nodes=%lld memo=%zu\n", C + 1, (int)w, nodes, memo.size());
    return 0;
}
