# Generated modules `Num*`: sizes, times, and the generators

The modules `NumP3`, `NumP4`, `NumAlg*` and `NumAdv*` contain generated data that the kernel checks. The generators
below are not trusted: everything they write is verified by checkers that are proved sound in `NumPoset.lean`,
`NumGameCheck.lean` and `NumGameSkip.lean`.

## Sizes, time and memory of the kernel checks

`lake build OnlineColouring.<Module>` under a memory limit of 5 GB; wall time as printed by lake, and maximum resident
set size from `/usr/bin/time -v` (it includes about 0.9 GB of memory-mapped Mathlib `.olean` files).

| Module | Content | Source size | Wall time | Max RSS |
|---|---|---|---|---|
| NumPoset, NumTwo, NumValues | proofs | | 1.3 s, 0.8 s, 0.7 s | 0.9 GB |
| NumP4 | coding of `P_1(4)` (15 elements), count 167, chain cover and antichain of width 6 | 2 KB | 0.7 s | 1.0 GB |
| NumP3 | codings of `P_1(3)`, `P_2(3)`, `P_3(3)` (7, 18, 81 masks; tables of 7², 18², 81² bits), count 8570 on 81 rows, three chain covers and antichains, the layer of 235 masks | 14 KB | 5.9 s | 1.5 GB |
| NumGame, NumGameCheck, NumGameSkip, NumOneLevel, NumOneLevelAdv, NumVDef, NumV, NumV10 | proofs | | about 1 s each | 0.9–1.5 GB |
| NumAlgSmall | algorithm certificates `m = 4..10` (198 lemmas, 623 responses) | 44 KB | 5 s | 1.3 GB |
| NumAlg11 | algorithm certificate `m = 11` (421 lemmas, 2 998 responses) | 163 KB | 26 s | 2.3 GB |
| NumAdvSmall | adversary certificates `m = 4..7` (515 lemmas, 1 049 references) | 61 KB | 7 s | 1.3 GB |
| NumAdv8 | adversary certificate with null moves, `m = 8` (2 457 lemmas, 8 530 references) | 288 KB | 46 s | 2.0 GB |
| NumAdv9 | the same for `m = 9` (2 458 lemmas, 8 531 references) | 288 KB | 47 s | 2.0 GB |
| NumAdv10D0 … D13 | data for `m = 10` (107 285 lemmas, 433 801 references) | 1.0–1.2 MB each, 15.7 MB | 25–30 s each | 2.2–2.5 GB |
| NumAdv10T | the table | 10 KB | 0.5 s | 0.9 GB |
| NumAdv10C0 … C11 | kernel checks for `m = 10`, about 8 960 lemmas each | 8.4–8.5 KB each | 189–290 s each, 48 min of CPU time in total | 2.4–4.0 GB |
| NumAdv10 | 839 chaining steps and `win_10` | 111 KB | 30 s | 2.2 GB |

Totals: the label posets (`NumPoset`, `NumTwo`, `NumValues`, `NumP3`, `NumP4`) 10 s; `V(4..9)` (all bounds) about 2.5 minutes; `V(10) ≥ 7`: 6.5 min for the 14 data modules, 48 min for the 12 check modules (16 min of wall time with three of them running at a time), 30 s for the chain: about 55 minutes when the modules are built one at a time.

Speed of the kernel on this code: 5–6 ms per reference of an adversary certificate (one reference = renaming and
sorting the rows of a position, comparing it with the position referred to as a multiset of rows, one table lookup),
8 ms per response of the `m = 11` algorithm certificate.

## Generators (untrusted)

The data modules are written by Python scripts (listed here in full, so
that the modules can be regenerated). Nothing they write is trusted: every list is checked by the kernel.
Run them from the root of the repository, with the four scripts in the current directory and the files
`s8.txt`, `s9.txt`, `s10.txt` in a directory `solver/`; they write into `OnlineColouring/`.

* `posets.py`, `gen_posets_lean.py` → `NumP3.lean`, `NumP4.lean`.
* `onelevel.py`, `gen_onelevel_lean.py` → `NumAlgSmall`, `NumAlg11`, `NumAdvSmall` (arguments `alg adv`; input: the
  certificates of `repro/certificates/`), `NumAdv8`, `NumAdv9` (argument `adv89`; input `solver/s8.txt`,
  `solver/s9.txt`), `NumAdv10*` (arguments `adv10 14 12`; input `solver/s10.txt`).
* The inputs `s8.txt`, `s9.txt`, `s10.txt` (SHA-256 `23408134…`, `77308000…`, `600cafe0…`; 2 457, 2 458 and 107 285
  entries) are written by solver A with the change below, compiled with `g++ -O2 -std=c++17`, as
  `./solver_skip 8 5 min -nm -tt 22 -cert s8.txt`, `./solver_skip 9 5 min -nm -tt 22 -cert s9.txt`,
  `./solver_skip 10 6 min -nm -tt 24 -cert s10.txt` (7 s for `m = 10`). An entry `S t rows : picks` means: after
  these picks the adversary wins from the position with the remaining rows at time `t+1`, without a row for block
  `t`; an entry `D t rows : picks` is as in the paper's format.

`posets.py`:

```python
#!/usr/bin/env python3
"""Label posets as coded posets (untrusted generator for the Lean data modules NumP*.lean).

A coded poset is (n, dn): elements 0..n-1, dn[j] = bit mask of {i : i <= j}.  Level 0 is the antichain on k
elements.  The next level lists the nonzero closed masks (down-sets) in increasing numerical order; this is a
linear extension of inclusion.
"""
import sys
sys.setrecursionlimit(100000)


def closed_masks(n, dn):
    """All down-sets (as masks), by the recursion that the Lean function `cnt` uses."""
    out = []

    def rec(f, S, acc):
        # S: set of undecided elements (all < f); acc: chosen elements
        while f > 0 and not (S >> (f - 1)) & 1:
            f -= 1
        if f == 0:
            out.append(acc)
            return
        x = f - 1
        rec(x, S ^ (1 << x), acc)                      # x not in the down-set... (x maximal in S)
        rec(x, S ^ (S & dn[x]), acc | (S & dn[x]))     # x in: all of S below x is in
    rec(n, (1 << n) - 1, 0)
    return out


def all_downsets(n, dn):
    """down-sets D: for the recursion above 'acc' collects only elements below chosen maximal ones within S; to
    get the true down-set take the closure."""
    res = set()
    for a in closed_masks(n, dn):
        d = 0
        for i in range(n):
            if a >> i & 1:
                d |= dn[i]
        res.add(d)
    return sorted(res)


def next_level(n, dn):
    L = [m for m in all_downsets(n, dn) if m]
    N = len(L)
    dn2 = [sum(1 << i for i in range(N) if L[i] & L[j] == L[i]) for j in range(N)]
    return N, dn2, L


def levels(k, J):
    n, dn = k, [1 << i for i in range(k)]
    out = [(n, dn, None)]
    for _ in range(J):
        n, dn, L = next_level(n, dn)
        out.append((n, dn, L))
    return out


if __name__ == '__main__':
    lv = levels(3, 3)
    print([x[0] for x in lv])
    n, dn, L = lv[3]
    L4 = [m for m in all_downsets(n, dn) if m]
    print(len(L4))
    lay = {}
    for m in L4:
        lay[bin(m).count('1')] = lay.get(bin(m).count('1'), 0) + 1
    print(lay[39], max(lay.values()))
    lv4 = levels(4, 2)
    print([x[0] for x in lv4])
    lv2 = levels(2, 5)
    print([x[0] for x in lv2])
```

`gen_posets_lean.py`:

```python
#!/usr/bin/env python3
"""Writes OnlineColouring/NumP3.lean and NumP4.lean (untrusted generator: every list it writes is checked by
the Lean kernel through the verified Bool checks of NumPoset.lean)."""
import sys
sys.path.insert(0, '.')
from posets import levels, all_downsets

OUT = 'OnlineColouring/'


def wrap(items, indent='  ', width=100):
    lines, cur = [], ''
    for i, t in enumerate(items):
        piece = t + (',' if i < len(items) - 1 else '')
        if cur == '':
            cur = indent + piece
        elif len(cur) + 1 + len(piece) <= width:
            cur += ' ' + piece
        else:
            lines.append(cur)
            cur = indent + piece
    lines.append(cur)
    return '\n'.join(lines)


def lst(name, doc, xs):
    return '/-- %s -/\ndef %s : List ℕ := [\n%s]\n' % (doc, name, wrap([str(x) for x in xs]))


def chain_cover(n, dn):
    """Minimum chain cover by bipartite matching (Dilworth): returns chain numbers."""
    less = [[i != j and (dn[j] >> i) & 1 for j in range(n)] for i in range(n)]   # i < j
    match_r = [-1] * n   # right j matched to left i  (i -> j means j is the successor of i in its chain)

    def aug(i, seen):
        for j in range(n):
            if less[i][j] and not seen[j]:
                seen[j] = True
                if match_r[j] == -1 or aug(match_r[j], seen):
                    match_r[j] = i
                    return True
        return False
    for i in range(n):
        aug(i, [False] * n)
    succ = [-1] * n
    for j in range(n):
        if match_r[j] != -1:
            succ[match_r[j]] = j
    ch = [-1] * n
    c = 0
    for i in range(n):
        if match_r[i] == -1:          # start of a chain
            x = i
            while x != -1:
                ch[x] = c
                x = succ[x]
            c += 1
    assert all(x >= 0 for x in ch)
    for i in range(n):
        for j in range(n):
            if ch[i] == ch[j]:
                assert (dn[j] >> i) & 1 or (dn[i] >> j) & 1
    return ch, c


def max_antichain(n, dn, w):
    comp = [[(dn[j] >> i) & 1 or (dn[i] >> j) & 1 for j in range(n)] for i in range(n)]
    res = []

    def rec(start, chosen):
        if len(chosen) == w:
            res.append(list(chosen))
            return True
        for i in range(start, n):
            if all(not comp[i][c] for c in chosen):
                chosen.append(i)
                if rec(i + 1, chosen):
                    return True
                chosen.pop()
        return False
    assert rec(0, [])
    return res[0]


HEAD = '''module

public import OnlineColouring.NumPoset
public import OnlineColouring.BaseFacts

/-!
%s
-/

@[expose] public section

namespace OnlineColouring

namespace Num

'''
TAIL = '''
end Num

end OnlineColouring
'''


def gen3():
    lv = levels(3, 3)
    out = []
    widths = []
    for j in (1, 2, 3):
        n, dn, L = lv[j]
        ch, c = chain_cover(n, dn)
        a = max_antichain(n, dn, c)
        widths.append(c)
        out.append(lst('L3%d' % j, 'The elements of `P_%d(3)`: the bit masks of the nonempty down-sets of `P_%d(3)`,'
                       '\nin increasing order.' % (j, j - 1), L))
        out.append(lst('R3%d' % j, 'The order of `P_%d(3)`: bit `i` of row `j` says whether element `i` lies below '
                       'element `j`.' % j, dn))
        out.append(lst('C3%d' % j, 'A cover of `P_%d(3)` by %d chains: the chain of each element.' % (j, c), ch))
        out.append(lst('A3%d' % j, 'An antichain of `P_%d(3)` with %d elements.' % (j, c), a))
    assert widths == [3, 4, 7], widths
    n, dn, L = lv[3]
    L4 = [m for m in all_downsets(n, dn) if m]
    assert len(L4) == 8569
    A39 = [m for m in L4 if bin(m).count('1') == 39]
    assert len(A39) == 235
    out.append(lst('A39', 'The 235 down-sets of `P_3(3)` with exactly 39 elements (bit masks, increasing).', A39))
    doc = '''# The label posets `P_j(3)`: sizes, widths, and the antichain of `P_4(3)`

Paper: Section 5: "The first values are … `|P_j(3)| = 3, 7, 18, 81, 8569`",
"For `k = 3` the width is `3` after one level and `4` after two"; `check_posets.py` (widths
`3, 3, 4, 7` of `P_j(3)`, `j = 0, …, 3`); the remark after Lemma A.1:
"for `k = 3` this is `j = 5` whenever `8569 < n < 2^235`, since `P_4(3)` has an antichain of `235`
elements".

* `card_labelPoset_three_three : |P_3(3)| = 81`, `card_labelPoset_three_four : |P_4(3)| = 8569`.
* `width_labelPoset_three_zero`, `…_one`, `…_two`, `…_three`: the widths `3, 3, 4, 7`.
* `exists_layer_three_four`: `P_4(3)` contains 235 down-sets of `P_3(3)` with exactly 39 elements;
  `hasAntichain_labelPoset_three_four`: they form an antichain;
  `two_pow_sub_one_le_card_labelPoset_three_five : 2^235 - 1 ≤ |P_5(3)|`;
  `le_card_labelPoset_three_iff`: for `8569 < n < 2^235`, `n ≤ |P_j(3)| ↔ 5 ≤ j`.

How: `NumPoset.lean`.  The lists below are generated data (elements of `P_{j+1}(3)` as bit masks
of down-sets of `P_j(3)`, the order relation, chain covers, antichains); the generator is not
trusted.  Each list is checked by the kernel (`decide +kernel`) with the Bool checks of
`NumPoset.lean`, whose soundness is proved there; completeness of a list of down-sets follows
from the verified count `cnt`.  The count `|P_4(3)| + 1 = 8570` is one kernel evaluation of
`cntL`, the list form of `cnt`, on the 81 rows `R33`.'''
    body = HEAD % doc + '/-! ### Data (generated) -/\n\n' + '\n'.join(out) + '''
/-! ### Codings of `P_1(3)`, `P_2(3)`, `P_3(3)` -/

/-- The numbering of `P_1(3)`. -/
def idx31 : LabelPoset 3 1 → ℕ := jstIdx (idxAnti 3) 3 L31

/-- The numbering of `P_2(3)`. -/
def idx32 : LabelPoset 3 2 → ℕ := jstIdx idx31 7 L32

/-- The numbering of `P_3(3)`. -/
def idx33 : LabelPoset 3 3 → ℕ := jstIdx idx32 18 L33

theorem coding31 : IsCoding (LabelPoset 3 1) 7 (fun j => R31.getD j 0) idx31 :=
  (isCoding_labelPoset_zero 3).jst (L := L31) (rows := R31)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem coding32 : IsCoding (LabelPoset 3 2) 18 (fun j => R32.getD j 0) idx32 :=
  coding31.jst (L := L32) (rows := R32) (by decide +kernel)
    (cnt_eq_of_cntL rfl (by decide +kernel)) (by decide +kernel)

theorem coding33 : IsCoding (LabelPoset 3 3) 81 (fun j => R33.getD j 0) idx33 :=
  coding32.jst (L := L33) (rows := R33) (by decide +kernel)
    (cnt_eq_of_cntL rfl (by decide +kernel)) (by decide +kernel)

/-! ### Sizes -/

/-- `|P_3(3)| = 81`. -/
theorem card_labelPoset_three_three : Fintype.card (LabelPoset 3 3) = 81 := coding33.card_eq

/-- `|P_4(3)| = 8569`: the poset `P_3(3)` has 8570 down-sets (kernel evaluation of `cntL`). -/
theorem card_labelPoset_three_four : Fintype.card (LabelPoset 3 4) = 8569 :=
  coding33.card_jst (cnt_eq_of_cntL rfl (by decide +kernel))

/-! ### Widths -/

/-- `width(P_0(3)) = 3`. -/
theorem width_labelPoset_three_zero : width (LabelPoset 3 0) = 3 :=
  le_antisymm (width_le_card.trans_eq (card_labelPoset_zero 3))
    (le_width_iff.2 (hasAntichain_labelPoset_zero 3))

/-- `width(P_1(3)) = 3`. -/
theorem width_labelPoset_three_one : width (LabelPoset 3 1) = 3 :=
  le_antisymm (coding31.width_le (ch := C31) rfl (by decide +kernel))
    (le_width_iff.2 (coding31.hasAntichain (a := A31) (by decide +kernel)))

/-- `width(P_2(3)) = 4`. -/
theorem width_labelPoset_three_two : width (LabelPoset 3 2) = 4 :=
  le_antisymm (coding32.width_le (ch := C32) rfl (by decide +kernel))
    (le_width_iff.2 (coding32.hasAntichain (a := A32) (by decide +kernel)))

/-- `width(P_3(3)) = 7`. -/
theorem width_labelPoset_three_three : width (LabelPoset 3 3) = 7 :=
  le_antisymm (coding33.width_le (ch := C33) rfl (by decide +kernel))
    (le_width_iff.2 (coding33.hasAntichain (a := A33) (by decide +kernel)))

/-! ### The antichain of `P_4(3)` (remark after Lemma A.1) -/

/-- `P_4(3)` contains 235 down-sets of `P_3(3)` with exactly 39 elements. -/
theorem exists_layer_three_four :
    ∃ F : Finset (LabelPoset 3 4), F.card = 235 ∧
      ∀ D ∈ F, (Jst.val (P := LabelPoset 3 3) D).card = 39 :=
  coding33.exists_layer (A := A39) (by decide +kernel)

/-- **`P_4(3)` has an antichain of 235 elements** (down-sets of the same size are incomparable). -/
theorem hasAntichain_labelPoset_three_four : HasAntichain (LabelPoset 3 4) 235 := by
  obtain ⟨F, hF, hr⟩ := exists_layer_three_four
  exact ⟨F, isAntichain_of_card_eq (P := LabelPoset 3 3) hr, hF⟩

/-- `|P_5(3)| ≥ 2^235 - 1`, by Lemma 5.5 (i). -/
theorem two_pow_sub_one_le_card_labelPoset_three_five :
    2 ^ 235 - 1 ≤ Fintype.card (LabelPoset 3 5) :=
  HasAntichain.two_pow_sub_one_le_card_jst (P := LabelPoset 3 4)
    hasAntichain_labelPoset_three_four

theorem card_labelPoset_mono (k : ℕ) : Monotone fun j => Fintype.card (LabelPoset k j) :=
  monotone_nat_of_le_succ (card_labelPoset_le_succ k)

/-- **Remark after Lemma A.1.**  For `8569 < n < 2^235`, the least `j` with `|P_j(3)| ≥ n` is
`j = 5`: `|P_j(3)| ≥ n` holds exactly for `j ≥ 5`. -/
theorem le_card_labelPoset_three_iff {n : ℕ} (h1 : 8569 < n) (h2 : n < 2 ^ 235) (j : ℕ) :
    n ≤ Fintype.card (LabelPoset 3 j) ↔ 5 ≤ j := by
  constructor
  · intro h
    by_contra hj
    have h4 := card_labelPoset_mono 3 (Nat.lt_succ_iff.1 (not_le.1 hj))
    simp only [card_labelPoset_three_four] at h4
    omega
  · intro hj
    have h5 := card_labelPoset_mono 3 hj
    have h6 := two_pow_sub_one_le_card_labelPoset_three_five
    simp only at h5
    omega
''' + TAIL
    open(OUT + 'NumP3.lean', 'w').write(body)


def gen4():
    lv = levels(4, 1)
    n, dn, L = lv[1]
    ch, c = chain_cover(n, dn)
    assert c == 6
    a = max_antichain(n, dn, c)
    out = [lst('L41', 'The elements of `P_1(4)`: the bit masks of the nonempty subsets of `{0, 1, 2, 3}`.', L),
           lst('R41', 'The order of `P_1(4)`: bit `i` of row `j` says whether element `i` lies below\nelement `j`.', dn),
           lst('C41', 'A cover of `P_1(4)` by 6 chains: the chain of each element.', ch),
           lst('A41', 'An antichain of `P_1(4)` with 6 elements (the 2-element subsets).', a)]
    doc = '''# The label posets `P_j(4)`: `|P_2(4)| = 166` and `width(P_1(4)) = 6`

Paper: Section 5: "The first values are … `|P_j(4)| = 4, 15, 166`";
Section 9: "`width(P_1(4)) = binom(4, 2) = 6`".

* `card_labelPoset_four_two : |P_2(4)| = 166` (`P_1(4)` has 167 down-sets: kernel evaluation of
  `cntL`, the list form of the verified count `cnt` of `NumPoset.lean`).
* `width_labelPoset_four_one : width(P_1(4)) = 6`.

The lists are generated data, checked by the kernel with the Bool checks of `NumPoset.lean`.'''
    body = HEAD % doc + '/-! ### Data (generated) -/\n\n' + '\n'.join(out) + '''
/-- The numbering of `P_1(4)`. -/
def idx41 : LabelPoset 4 1 → ℕ := jstIdx (idxAnti 4) 4 L41

theorem coding41 : IsCoding (LabelPoset 4 1) 15 (fun j => R41.getD j 0) idx41 :=
  (isCoding_labelPoset_zero 4).jst (L := L41) (rows := R41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `|P_2(4)| = 166`. -/
theorem card_labelPoset_four_two : Fintype.card (LabelPoset 4 2) = 166 :=
  coding41.card_jst (cnt_eq_of_cntL rfl (by decide +kernel))

/-- `width(P_1(4)) = 6`. -/
theorem width_labelPoset_four_one : width (LabelPoset 4 1) = 6 :=
  le_antisymm (coding41.width_le (ch := C41) rfl (by decide +kernel))
    (le_width_iff.2 (coding41.hasAntichain (a := A41) (by decide +kernel)))
''' + TAIL
    open(OUT + 'NumP4.lean', 'w').write(body)


if __name__ == '__main__':
    gen3()
    gen4()
    print('written')
```

`onelevel.py`:

```python
#!/usr/bin/env python3
"""One-level certificates (repro/certificates/one_m*_C*_{ALG,ADV}.txt) -> DAGs for the Lean checkers.

Untrusted: everything written is checked by the Lean kernel.  A state is a list of rows; a row is a sorted tuple of
colours (the colours of the unused vertices of an earlier block).  States are identified up to permuting rows and
renaming colours; each reference carries the renaming (sigma) and its inverse (tau).
"""
import sys, itertools
sys.setrecursionlimit(1000000)
CD = 'repro/certificates/'


def dig(ch):
    return int(ch, 32)


def parse(path):
    lines = [l.split() for l in open(path) if l.strip()]
    hd = lines[0]
    assert hd[0] == 'ONE'
    m, C = int(hd[1]), int(hd[2])
    B = [int(x) for x in hd[3:3 + m]]
    mode = hd[3 + m]
    ent = []
    for l in lines[1:]:
        if l[0] == 'A':
            t, F = int(l[1]), int(l[2])
            k = l.index(':')
            rows = [tuple(dig(ch) for ch in tok) for tok in l[3:k]]
            mv = tuple(dig(ch) for ch in l[k + 1])
            ent.append((t, F, rows, mv))
        else:
            # D: the adversary's picks; S: picks after which it wins without the next block (null move)
            assert l[0] in ('D', 'S')
            t = int(l[1])
            k = l.index(':')
            rows = [tuple(dig(ch) for ch in tok) for tok in l[2:k]]
            pk = [int(x) for x in l[k + 1:]]
            assert len(pk) == len(rows)
            ent.append((t, 'S' if l[0] == 'S' else None, rows, pk))
    return m, C, B, mode, ent


def canon(C, rows, F):
    """rows: list of count vectors; F: bit mask or None.  Returns (key, p) with p[j] = old colour at new position j;
    key = (sorted permuted rows, permuted F).  A canonical form: equal keys iff the states are symmetric."""
    inv = []
    for c in range(C):
        col = sorted((r[c] for r in rows), reverse=True)
        inv.append(((F >> c) & 1 if F is not None else 0, tuple(col)))
    order = sorted(range(C), key=lambda c: inv[c])
    groups = []
    i = 0
    while i < C:
        j = i
        while j < C and inv[order[j]] == inv[order[i]]:
            j += 1
        groups.append(order[i:j])
        i = j
    best = None
    for combo in itertools.product(*[itertools.permutations(g) for g in groups]):
        p = [c for g in combo for c in g]
        rs = sorted(tuple(r[p[j]] for j in range(C)) for r in rows)
        Fc = None if F is None else sum(1 << j for j in range(C) if (F >> p[j]) & 1)
        key = (tuple(rs), Fc)
        if best is None or key < best[0]:
            best = (key, p)
    return best


def cv_to_row(cv):
    """count vector -> sorted tuple of colours"""
    return tuple(c for c in range(len(cv)) for _ in range(cv[c]))


def row_to_cv(C, row):
    cv = [0] * C
    for c in row:
        cv[c] += 1
    return tuple(cv)


def distinct(row):
    """the Lean function `distinct`: keeps the last occurrence of each element"""
    out = []
    for i, a in enumerate(row):
        if a not in row[i + 1:]:
            out.append(a)
    return out


def erase(row, c):
    l = list(row)
    l.remove(c)
    return tuple(l)


def all_picks(rows):
    """the Lean function `allPicks`: list of (rows', F) with F the list of picked colours"""
    if not rows:
        return [((), ())]
    r, rs = rows[0], rows[1:]
    out = []
    for (rs2, F) in all_picks(rs):
        for c in distinct(r):
            out.append(((erase(r, c),) + rs2, (c,) + F))
    return out


def all_multisets(allowed, size):
    """the Lean function `allMs`: for k = 0, ..., size copies of the first allowed colour, the multisets of the
    remaining size over the other allowed colours"""
    if not allowed:
        return [()] if size == 0 else []
    a, rest = allowed[0], allowed[1:]
    out = []
    for k in range(size + 1):
        for l in all_multisets(rest, size - k):
            out.append((a,) * k + l)
    return out


class Conv:
    def __init__(self, path):
        self.m, self.C, self.B, self.mode, ent = parse(path if '/' in path else CD + path)
        C = self.C
        self.tab = {}
        self.skips = self.mode == 'ADV' and any(e[1] == 'S' for e in ent)
        for (t, F, rows, mv) in ent:
            skip = F == 'S'
            if self.mode == 'ADV':
                F = None
            key, p = canon(C, rows, F)
            if self.mode == 'ALG':
                self.tab[(t, key)] = tuple(mv[p[j]] for j in range(C))        # move in canonical labels
            else:
                # picks per row -> per canonical row: canonical row i is some old row; keep a multiset matching
                pinv = [0] * C
                for j in range(C):
                    pinv[p[j]] = j
                prow = [(tuple(r[p[j]] for j in range(C)), pinv[pk]) for r, pk in zip(rows, mv)]
                prow.sort()
                self.tab[(t, key)] = (prow, skip)
        self.ids = {}       # canonical key of a pre-pick state -> lemma id
        self.lems = []      # (rows (tuple of sorted colour tuples), resp list)
        self.nresp = 0

    def state_id(self, t, rows):
        """rows: tuple of sorted colour tuples (current labels).  Returns (id, sigma) with sigma[c] = label of the
        colour c in the stored representative."""
        C = self.C
        cvs = [row_to_cv(C, r) for r in rows]
        key, p = canon(C, cvs, None)
        sigma = [0] * C
        for j in range(C):
            sigma[p[j]] = j
        if (t, key) not in self.ids:
            rep = tuple(cv_to_row(cv) for cv in key[0])
            self.ids[(t, key)] = None          # in progress
            self.ids[(t, key)] = self.build(t, rep)
        assert self.ids[(t, key)] is not None
        return self.ids[(t, key)], sigma

    def build(self, t, rows):
        m, C, B = self.m, self.C, self.B
        if self.mode == 'ALG':
            resp = []
            for (rows2, F) in all_picks(rows):
                Fm = 0
                for c in F:
                    Fm |= 1 << c
                assert Fm != (1 << C) - 1, 'the algorithm is stuck'
                if t == m - 1:
                    c = min(c for c in range(C) if not (Fm >> c) & 1)
                    resp.append(((c,) * B[t], 0, list(range(C)), list(range(C))))
                    continue
                cvs = [row_to_cv(C, r) for r in rows2]
                key, p = canon(C, cvs, Fm)
                mvc = self.tab[(t, key)]
                mv = [0] * C
                for j in range(C):
                    mv[p[j]] = mvc[j]
                assert sum(mv) == B[t] and all(not (mv[c] and (Fm >> c) & 1) for c in range(C))
                M = cv_to_row(mv)
                j, sigma = self.state_id(t + 1, (M,) + rows2)
                tau = [0] * C
                for c in range(C):
                    tau[sigma[c]] = c
                resp.append((M, j, sigma, tau))
            self.nresp += len(resp)
            self.lems.append((rows, resp))
            return len(self.lems) - 1
        else:
            # adversary: picks for this state
            cvs = [row_to_cv(C, r) for r in rows]
            key, p = canon(C, cvs, None)
            prow, skip = self.tab[(t, key)]    # sorted list of (canonical row, canonical pick)
            # match rows to canonical rows (as multisets)
            avail = list(prow)
            picks = []
            for cv in cvs:
                crow = tuple(cv[p[j]] for j in range(C))
                k = next(i for i, (r, _) in enumerate(avail) if r == crow)
                picks.append(p[avail[k][1]])
                avail.pop(k)
            rows2 = []
            Fm = 0
            for r, c in zip(rows, picks):
                assert c in r
                rows2.append(erase(r, c))
                Fm |= 1 << c
            rows2 = tuple(rows2)
            allowed = [c for c in range(C) if not (Fm >> c) & 1]
            resp = []
            if skip:
                assert t + 1 < m and B[t] >= m - t - 1
                j, sigma = self.state_id(t + 1, rows2)
                tau = [0] * C
                for c in range(C):
                    tau[sigma[c]] = c
                resp.append((j, sigma, tau))
            else:
                for M in all_multisets(allowed, B[t]):
                    assert t + 1 < m, 'the adversary does not win'
                    j, sigma = self.state_id(t + 1, (M,) + rows2)
                    tau = [0] * C
                    for c in range(C):
                        tau[sigma[c]] = c
                    resp.append((j, sigma, tau))
            self.nresp += len(resp)
            if self.skips:
                self.lems.append((t, rows, picks, skip, resp))
            else:
                self.lems.append((rows, picks, resp))
            return len(self.lems) - 1

    def run(self):
        root, _ = self.state_id(0, ())
        assert root == len(self.lems) - 1
        return root


if __name__ == '__main__':
    for f in sys.argv[1:]:
        cv = Conv(f)
        cv.run()
        print(f, 'm', cv.m, 'C', cv.C, 'lemmas', len(cv.lems), 'responses', cv.nresp)
```

`gen_onelevel_lean.py`:

```python
#!/usr/bin/env python3
"""Writes the Lean data modules NumAlg*.lean / NumAdv*.lean from the one-level certificates (untrusted).

Usage: gen_onelevel_lean.py [alg] [adv] [adv89] [adv10 <data> <checks>] [adv8raw] [adv9raw]
"""
import sys, io
sys.path.insert(0, '.')
from onelevel import Conv, CD

OUT = 'OnlineColouring/'


def lst(l):
    return '[' + ', '.join(str(x) for x in l) + ']'


def code(p):
    """a renaming of the colours as a number: octal digit c = p[c]"""
    return sum(x << (3 * c) for c, x in enumerate(p))


def wrap(text, indent='    ', width=100):
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


def alg_lem(lem):
    rows, resp = lem
    rs = '[' + ', '.join(lst(r) for r in rows) + ']'
    es = '[' + ', '.join('(%s, %d, %d, %d)' % (lst(M), j, code(sg), code(tu)) for (M, j, sg, tu) in resp) + ']'
    return '⟨%s, %s⟩' % (rs, es)


def adv_lem(lem):
    rows, picks, resp = lem
    rs = '[' + ', '.join(lst(r) for r in rows) + ']'
    es = '[' + ', '.join('(%d, %d, %d)' % (j, code(sg), code(tu)) for (j, sg, tu) in resp) + ']'
    return '⟨%s, %s, %s⟩' % (rs, lst(picks), es)


def lstc(l):
    return '[' + ','.join(str(x) for x in l) + ']'


def skip_lem(lem):
    """compact text (no spaces) for the certificates with null moves"""
    t, rows, picks, skip, resp = lem
    rs = '[' + ','.join(lstc(r) for r in rows) + ']'
    es = '[' + ','.join('(%d,%d)' % (j, code(sg)) for (j, sg, tu) in resp) + ']'
    return '⟨%d,%s,%s,%s,%s⟩' % (t, rs, lstc(picks), 'true' if skip else 'false', es)


def wrapc(text, indent='    ', width=100):
    """break a compact text at commas"""
    toks = text.split(',')
    lines, cur = [], indent[:-2]
    for i, t in enumerate(toks):
        piece = t + (',' if i < len(toks) - 1 else '')
        if len(cur) + len(piece) <= width or cur.strip() == '':
            cur += piece
        else:
            lines.append(cur)
            cur = indent + piece
    lines.append(cur)
    return '\n'.join(lines)


class Cert:
    def __init__(self, fname, name):
        self.name = name
        cv = Conv(fname)
        self.fname = fname.split('/')[-1]
        cv.run()
        self.cv = cv
        self.m, self.C, self.B = cv.m, cv.C, cv.B
        self.alg = cv.mode == 'ALG'
        self.skips = cv.skips
        self.ty = 'ALem' if self.alg else ('SLem' if self.skips else 'DLem')
        self.n = len(cv.lems)
        self.nleaf = (self.n + 15) // 16
        self.nmid = (self.nleaf + 15) // 16
        self.ntop = (self.nmid + 15) // 16
        self.up = 'AUpto' if self.alg else ('SUpto' if self.skips else 'DUpto')
        self.rng = 'chkARange' if self.alg else ('chkSRange' if self.skips else 'chkDRange')
        self.chk = 'chkALem' if self.alg else ('chkSLem' if self.skips else 'chkDLem')
        self.base = 'NumGameSkip' if self.skips else 'NumGameCheck'

    def leaves_mids(self, out, mids):
        """the leaf and mid definitions of the mids in `mids`"""
        name, ty, n = self.name, self.ty, self.n
        for j in mids:
            leaves = range(16 * j, min(self.nleaf, 16 * j + 16))
            for k in leaves:
                part = self.cv.lems[16 * k:16 * k + 16]
                out.write('/-- Lemmas %d to %d of the certificate `%s`. -/\n' % (16 * k, min(n, 16 * k + 16) - 1, self.fname))
                out.write('noncomputable def %s_L%d : List %s := [\n' % (name, k, ty))
                for i, l in enumerate(part):
                    if self.skips:
                        out.write(wrapc(skip_lem(l) + (',' if i < len(part) - 1 else '')) + '\n')
                    else:
                        s = (alg_lem(l) if self.alg else adv_lem(l)) + (',' if i < len(part) - 1 else '')
                        out.write(wrap(s) + '\n')
                out.write(']\n\n')
            out.write('/-- Lemmas %d to %d of the certificate `%s`. -/\n' % (256 * j, min(n, 256 * j + 256) - 1, self.fname))
            out.write(wrap('noncomputable def %s_M%d : List (List %s) := [%s]'
                           % (name, j, ty, ', '.join('%s_L%d' % (name, k) for k in leaves)), indent='  ') + '\n\n')

    def table(self, out):
        name, ty = self.name, self.ty
        for i in range(self.ntop):
            mids = range(16 * i, min(self.nmid, 16 * i + 16))
            out.write('/-- Lemmas %d to %d of the certificate `%s`. -/\n' % (4096 * i, min(self.n, 4096 * i + 4096) - 1, self.fname))
            out.write(wrap('noncomputable def %s_T%d : List (List (List %s)) := [%s]'
                           % (name, i, ty, ', '.join('%s_M%d' % (name, j) for j in mids)), indent='  ') + '\n\n')
        out.write('/-- The certificate `%s` (%d lemmas). -/\n' % (self.fname, self.n))
        out.write(wrap('noncomputable def %s : ℕ → %s := tbl [%s]'
                       % (name, ty, ', '.join('%s_T%d' % (name, i) for i in range(self.ntop))), indent='  ') + '\n\n')

    def nchecks(self, step):
        return (self.n + step - 1) // step

    def checks(self, out, step, qs):
        for q in qs:
            lo = q * step
            ln = min(step, self.n - lo)
            out.write('theorem %s_c%d :\n    %s %d %s %s %d %d = true := by\n  decide +kernel\n\n'
                      % (self.name, q, self.rng, self.C, lst(self.B), self.name, lo, ln))

    def chain(self, out, step):
        prev = '%s.zero' % self.up
        nq = self.nchecks(step)
        for q in range(nq):
            lo = q * step
            ln = min(step, self.n - lo)
            out.write('theorem %s_u%d : %s %d %s %s %d :=\n  %s.add (lo := %d) (len := %d) %s_c%d\n\n'
                      % (self.name, q, self.up, self.C, lst(self.B), self.name, lo + ln, prev, lo, ln, self.name, q))
            prev = '%s_u%d' % (self.name, q)
        m, C, Bs, n = self.m, self.C, lst(self.B), self.n
        if self.alg:
            out.write('/-- The algorithm survives the abstract one-level game for `m = %d` with %d colours\n(certificate `%s`, %d lemmas, kernel-checked). -/\n' % (m, C, self.fname, n))
            out.write('theorem surv_%d : Surv %d %s [] :=\n  surv_of_aupto (r := %d) %s (by decide +kernel)\n\n' % (m, C, Bs, n - 1, prev))
        else:
            out.write('/-- The adversary beats the palette of %d colours in the abstract one-level game for\n`m = %d` (certificate `%s`, %d lemmas, kernel-checked). -/\n' % (C, m, self.fname, n))
            out.write('theorem win_%d : Win %d %s [] :=\n  %s (r := %d) %s (by decide +kernel)\n\n'
                      % (m, C, Bs, 'win_of_supto' if self.skips else 'win_of_dupto', n - 1, prev))

    def summary(self):
        if self.alg:
            return '* `surv_%d : Surv %d %s []` (%d lemmas, %d responses).' % (self.m, self.C, lst(self.B), self.n, self.cv.nresp)
        return '* `win_%d : Win %d %s []` (%d lemmas, %d responses).' % (self.m, self.C, lst(self.B), self.n, self.cv.nresp)


HEAD = '''module

%s

/-!
# %s

Paper: Appendix D.3, the table of `V(m)`:
%s.

%s
-/

%spublic section

namespace OnlineColouring

namespace Num

'''
TAIL = '''end Num

end OnlineColouring
'''
GENS = '''Generated data (do not edit): adversary certificates with null moves (%s),
written by a variant of the solver of the supplementary material
(`repro/solvers/one_level_solver_a.cpp` with the change listed in
`docs/num_generators.md`: whenever the adversary wins without the next block, the certificate
says so instead of answering every colouring of that block), in the format of `NumGameSkip.lean`.
Neither the solver nor the converter is trusted: every lemma is checked by the Lean kernel with the
verified checker `chkSLem` (`decide +kernel`, %d lemmas per theorem).  The data are marked
`noncomputable` only to skip code generation for the literals.'''
GEN = '''Generated data (do not edit): the certificates
`repro/certificates/%s` as tables of lemmas in the format of
`NumGameCheck.lean`, written by the converter listed in `docs/num_generators.md`.  The
converter is not trusted: every lemma is checked by the Lean kernel with the verified checker
`%s` (`decide +kernel`, %d lemmas per theorem).  The data are marked `noncomputable` only to
skip code generation for the literals.'''


def write(modname, imports, title, what, body, text, expose=False):
    head = HEAD % ('\n'.join('public import OnlineColouring.' + i for i in imports), title, what, body,
                   '@[expose] ' if expose else '')
    open(OUT + modname + '.lean', 'w').write(head + text + TAIL)
    print(modname, len(text))


def gen_single(modname, title, what, files, step):
    """several small certificates in one module"""
    buf = io.StringIO()
    certs = []
    for (fname, name) in files:
        c = Cert(fname, name)
        certs.append(c)
        c.leaves_mids(buf, range(c.nmid))
        c.table(buf)
        c.checks(buf, step, range(c.nchecks(step)))
        c.chain(buf, step)
    alg = certs[0].alg
    if certs[0].skips:
        body = GENS % (', '.join('`%s`' % c.fname.split('/')[-1] for c in certs), step) + '\n\n' + \
            '\n'.join(c.summary() for c in certs)
    else:
        body = GEN % ('one_m*_C*_%s.txt' % ('ALG' if alg else 'ADV'), 'chkALem' if alg else 'chkDLem', step) + '\n\n' + \
            '\n'.join(c.summary() for c in certs)
    write(modname, [certs[0].base], title, what, body, buf.getvalue())
    for c in certs:
        print('  ', c.fname, c.n, c.cv.nresp)


def gen_big(prefix, title, what, fname, name, ndata, ncheck, step):
    """one large certificate in several modules: data, table, checks, conclusion"""
    c = Cert(fname, name)
    per = (c.nmid + ndata - 1) // ndata
    datamods = []
    for d in range(ndata):
        mids = range(d * per, min(c.nmid, (d + 1) * per))
        if not mids:
            continue
        buf = io.StringIO()
        c.leaves_mids(buf, mids)
        mod = '%sD%d' % (prefix, d)
        body = ('Generated data (do not edit), part %d of the certificate `%s`:\nthe lemmas %d to %d.  '
                'See `%s.lean`.') % (d, fname.split('/')[-1], 256 * mids[0], min(c.n, 256 * (mids[-1] + 1)) - 1, prefix)
        write(mod, [c.base], title + ' (data, part %d)' % d, what, body, buf.getvalue(), expose=True)
        datamods.append(mod)
    nq = c.nchecks(step)
    if ncheck == 0:
        buf = io.StringIO()
        c.table(buf)
        c.checks(buf, step, range(nq))
        c.chain(buf, step)
        body = (GENS % ('`%s`' % fname.split('/')[-1], step) if c.skips else GEN % (fname, 'chkDLem', step)) + \
            '\nThe data are in the modules `%sD*`.\n\n' % prefix + c.summary()
        write(prefix, datamods, title, what, body, buf.getvalue())
    else:
        buf = io.StringIO()
        c.table(buf)
        body = 'The table of the certificate `%s` (data in the modules `%sD*`).\nSee `%s.lean`.' % (fname.split('/')[-1], prefix, prefix)
        write(prefix + 'T', datamods, title + ' (table)', what, body, buf.getvalue(), expose=True)
        perq = (nq + ncheck - 1) // ncheck
        cmods = []
        for k in range(ncheck):
            qs = range(k * perq, min(nq, (k + 1) * perq))
            if not qs:
                continue
            buf = io.StringIO()
            c.checks(buf, step, qs)
            mod = '%sC%d' % (prefix, k)
            body = ('Kernel checks (`decide +kernel` with the verified checker `%s`), part %d: the lemmas\n'
                    '%d to %d of the certificate `%s`, %d lemmas per theorem.  See `%s.lean`.') % (
                        c.chk, k, qs[0] * step, min(c.n, (qs[-1] + 1) * step) - 1, fname.split('/')[-1], step, prefix)
            write(mod, [prefix + 'T'], title + ' (checks, part %d)' % k, what, body, buf.getvalue())
            cmods.append(mod)
        buf = io.StringIO()
        c.chain(buf, step)
        body = (GENS % ('`%s`' % fname.split('/')[-1], step) if c.skips else GEN % (fname, 'chkDLem', step)) + \
            ('\nThe data are in the modules `%sD*`, the table in `%sT`, the kernel checks in\n'
             '`%sC*`; this module only chains them.\n\n' % (prefix, prefix, prefix)) + c.summary()
        write(prefix, cmods, title, what, body, buf.getvalue())
    print('  ', c.fname, c.n, c.cv.nresp)


if __name__ == '__main__':
    which = sys.argv[1:]
    algs = [(4, 3), (5, 4), (6, 4), (7, 5), (8, 6), (9, 6), (10, 7), (11, 7)]
    if 'alg' in which:
        gen_single('NumAlgSmall', 'Algorithm certificates for the one-level game, `m = 4, …, 10`',
                   'the upper bounds `V(m) ≤ 3, 4, 4, 5, 6, 6, 7` for `m = 4, …, 10`',
                   [('one_m%d_C%d_ALG.txt' % (m, C), 'alg%d' % m) for (m, C) in algs[:7]], 64)
        gen_single('NumAlg11', 'Algorithm certificate for the one-level game, `m = 11`',
                   'the upper bound `V(11) ≤ 7`', [('one_m11_C7_ALG.txt', 'alg11')], 64)
    advs = [(4, 2), (5, 3), (6, 3), (7, 4)]
    if 'adv' in which:
        gen_single('NumAdvSmall', 'Adversary certificates for the one-level game, `m = 4, …, 7`',
                   'the lower bounds `V(m) ≥ 3, 4, 4, 5` for `m = 4, …, 7`',
                   [('one_m%d_C%d_ADV.txt' % (m, C), 'adv%d' % m) for (m, C) in advs], 64)
    SD = 'solver/'
    if 'adv8raw' in which:      # the certificates of the supplementary material (large)
        gen_big('NumAdv8', 'Adversary certificate for the one-level game, `m = 8`', 'the lower bound `V(8) ≥ 6`',
                'one_m8_C5_ADV.txt', 'adv8', 2, 0, 128)
    if 'adv9raw' in which:
        gen_big('NumAdv9', 'Adversary certificate for the one-level game, `m = 9`', 'the lower bound `V(9) ≥ 6`',
                'one_m9_C5_ADV.txt', 'adv9', 6, 4, 128)
    if 'adv89' in which:        # certificates with null moves
        gen_single('NumAdv8', 'Adversary certificate for the one-level game, `m = 8`', 'the lower bound `V(8) ≥ 6`',
                   [(SD + 's8.txt', 'adv8')], 128)
        gen_single('NumAdv9', 'Adversary certificate for the one-level game, `m = 9`', 'the lower bound `V(9) ≥ 6`',
                   [(SD + 's9.txt', 'adv9')], 128)
    if 'adv10' in which:
        gen_big('NumAdv10', 'Adversary certificate for the one-level game, `m = 10`', 'the lower bound `V(10) ≥ 7`',
                SD + 's10.txt', 'adv10', int(sys.argv[-2]), int(sys.argv[-1]), 128)
```

The change to `repro/solvers/one_level_solver_a.cpp` (applied to a copy, `solver_skip.cpp`; the file in `repro/` is unchanged):

```diff
--- repro/solvers/one_level_solver_a.cpp
+++ solver_skip.cpp
@@ -489,7 +489,7 @@
 static H128 hstr(const string& s) { u64 a = 0x1234567, b = 0x89abcdef; for (unsigned char ch : s) { a = mix64(a ^ ch); b = mix64(b + ch * 0x9E3779B97F4A7C15ULL) ^ (b >> 11); } return {a, b}; }
 static unordered_set<H128, H128h> exSeenAdv, exSeenAlg;
 static FILE* certOut = nullptr;
-static long long exEntries = 0, exErrors = 0, exCalls = 0;
+static long long exEntries = 0, exErrors = 0, exCalls = 0, exSkips = 0;
 static char d32(int v) { return v < 10 ? '0' + v : 'a' + v - 10; }
 static string rowStr(const FRow& r) { string s; for (int j = 0; j < C; j++) s.push_back(d32(r[j])); return s; }
 
@@ -611,6 +611,32 @@
     };
     if (n == 0) cand.push_back({0, {}}); else rec(0, 0);
     stable_sort(cand.begin(), cand.end(), [](const pair<int, vector<int>>& a, const pair<int, vector<int>>& b) { return a.first > b.first; });
+    // --- skip certificates (null move): prefer an immediate win, then a pick after which the adversary wins without
+    // the new block (entry S: the position (t+1, post rows) is winning, whatever the algorithm does), then any win.
+    for (auto& cd : cand) {
+        int F = 0; for (int q = 0; q < n; q++) F |= 1 << cd.second[q];
+        if (F != full) continue;
+        fprintf(certOut, "D %d", t);
+        for (auto& r : rows) fprintf(certOut, " %s", rowStr(r).c_str());
+        fprintf(certOut, " :");
+        for (int q = 0; q < n; q++) fprintf(certOut, " %d", cd.second[q]);
+        fprintf(certOut, "\n");
+        exEntries++;
+        return;
+    }
+    if (t + 1 < M) for (auto& cd : cand) {
+        vector<FRow> post = rows;
+        for (int q = 0; q < n; q++) post[q][cd.second[q]]--;
+        if (!redAdvValue(t + 1, post)) continue;
+        fprintf(certOut, "S %d", t);
+        for (auto& r : rows) fprintf(certOut, " %s", rowStr(r).c_str());
+        fprintf(certOut, " :");
+        for (int q = 0; q < n; q++) fprintf(certOut, " %d", cd.second[q]);
+        fprintf(certOut, "\n");
+        exEntries++; exSkips++;
+        exAdvADV(t + 1, post);
+        return;
+    }
     for (auto& cd : cand) {
         int F = 0; for (int q = 0; q < n; q++) F |= 1 << cd.second[q];
         bool win = (F == full) || redAlgValue(t, rows, cd.second, F);
@@ -684,7 +710,7 @@
         auto t1 = chrono::steady_clock::now();
         if (w) exAdvADV(0, {}); else exAdvALG(0, {});
         fclose(certOut);
-        printf("certificate %s: %s entries=%lld errors=%lld solverCalls=%lld advStates=%zu algStates=%zu time=%.1fs\n", certPath.c_str(), w ? "ADV" : "ALG", exEntries, exErrors, exCalls, exSeenAdv.size(), exSeenAlg.size(), chrono::duration<double>(chrono::steady_clock::now() - t1).count());
+        printf("certificate %s: %s entries=%lld errors=%lld solverCalls=%lld skips=%lld advStates=%zu algStates=%zu time=%.1fs\n", certPath.c_str(), w ? "ADV" : "ALG", exEntries, exErrors, exCalls, exSkips, exSeenAdv.size(), exSeenAlg.size(), chrono::duration<double>(chrono::steady_clock::now() - t1).count());
     }
     if (optStats) {
         printf("  ttStores=%lld replaced=%lld permFallback=%lld nmCut=%lld w1Cut=%lld etcCut=%lld\n  advNodes by t:", ttStores, ttReplaced, permFallback, nmCut, w1Cut, etcCut);
```
