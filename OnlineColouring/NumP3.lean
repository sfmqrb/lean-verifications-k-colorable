module

public import OnlineColouring.NumPoset
public import OnlineColouring.BaseFacts

/-!
# The label posets `P_j(3)`: sizes, widths, and the antichain of `P_4(3)`

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
`cntL`, the list form of `cnt`, on the 81 rows `R33`.
-/

@[expose] public section

namespace OnlineColouring

namespace Num

/-! ### Data (generated) -/

/-- The elements of `P_1(3)`: the bit masks of the nonempty down-sets of `P_0(3)`,
in increasing order. -/
def L31 : List ℕ := [
  1, 2, 3, 4, 5, 6, 7]

/-- The order of `P_1(3)`: bit `i` of row `j` says whether element `i` lies below element `j`. -/
def R31 : List ℕ := [
  1, 2, 7, 8, 25, 42, 127]

/-- A cover of `P_1(3)` by 3 chains: the chain of each element. -/
def C31 : List ℕ := [
  0, 1, 0, 2, 2, 1, 0]

/-- An antichain of `P_1(3)` with 3 elements. -/
def A31 : List ℕ := [
  0, 1, 3]

/-- The elements of `P_2(3)`: the bit masks of the nonempty down-sets of `P_1(3)`,
in increasing order. -/
def L32 : List ℕ := [
  1, 2, 3, 7, 8, 9, 10, 11, 15, 25, 27, 31, 42, 43, 47, 59, 63, 127]

/-- The order of `P_2(3)`: bit `i` of row `j` says whether element `i` lies below element `j`. -/
def R32 : List ℕ := [
  1, 2, 7, 15, 16, 49, 82, 247, 511, 561, 1783, 4095, 4178, 12535, 29183, 46839, 131071, 262143]

/-- A cover of `P_2(3)` by 4 chains: the chain of each element. -/
def C32 : List ℕ := [
  0, 1, 0, 0, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 0, 1]

/-- An antichain of `P_2(3)` with 4 elements. -/
def A32 : List ℕ := [
  3, 7, 9, 12]

/-- The elements of `P_3(3)`: the bit masks of the nonempty down-sets of `P_2(3)`,
in increasing order. -/
def L33 : List ℕ := [
  1, 2, 3, 7, 15, 16, 17, 18, 19, 23, 31, 49, 51, 55, 63, 82, 83, 87, 95, 115, 119, 127, 247, 255,
  511, 561, 563, 567, 575, 627, 631, 639, 759, 767, 1023, 1783, 1791, 2047, 4095, 4178, 4179, 4183,
  4191, 4211, 4215, 4223, 4343, 4351, 4607, 4723, 4727, 4735, 4855, 4863, 5119, 5879, 5887, 6143,
  8191, 12535, 12543, 12799, 13047, 13055, 13311, 14071, 14079, 14335, 16383, 29183, 29695, 30719,
  32767, 46839, 46847, 47103, 49151, 63487, 65535, 131071, 262143]

/-- The order of `P_3(3)`: bit `i` of row `j` says whether element `i` lies below element `j`. -/
def R33 : List ℕ := [
  1, 2, 7, 15, 31, 32, 97, 162, 487, 1007, 2047, 2145, 6631, 15343, 32767, 32930, 98791, 230383,
  493567, 629223, 1817583, 4194303, 6011887, 16777215, 33554431, 33556577, 100669927, 234896367,
  503349247, 638163431, 1847311343, 4265607167, 6146472943, 17163091967, 34359738367, 40506211311,
  120242307071, 274877906943, 549755813887, 549755846818, 1649267540455, 3848290927599,
  8246337701887, 10445361093095, 30236571581423, 69818992558079, 100605319953391, 280925237673983,
  562400231161855, 573395952048615, 1719088277339119, 4010472927920127, 6293060948048879,
  17732390940049407, 36028281622888447, 42321892326751215, 125818885076156415, 288230101273804799,
  576460752303423487, 576561357623376879, 1729663182147944447, 4035787666355126271,
  5194439831678860271, 15582172703132483583, 36353055676738568191, 42123956810476665839,
  126370723639525900287, 294859674528323207167, 590295810358705651711, 594331598025060777983,
  1807240486752855523327, 4426930347039262769151, 9444732965739290427391, 9486856922549767093231,
  28460569620857397182463, 66407990434703356198911, 142261290296448062062591,
  221655788559042942599167, 604462909807314587353087, 1208925819614629174706175,
  2417851639229258349412351]

/-- A cover of `P_3(3)` by 7 chains: the chain of each element. -/
def C33 : List ℕ := [
  0, 1, 1, 0, 0, 2, 2, 3, 1, 3, 1, 2, 2, 3, 0, 4, 4, 4, 1, 2, 2, 1, 2, 1, 1, 5, 5, 3, 0, 5, 3, 0, 3,
  0, 1, 3, 0, 0, 0, 6, 6, 4, 4, 6, 6, 4, 2, 2, 2, 5, 5, 4, 5, 4, 2, 3, 4, 1, 4, 6, 6, 6, 5, 5, 2, 3,
  5, 5, 2, 6, 6, 6, 2, 3, 3, 5, 1, 6, 2, 4, 0]

/-- An antichain of `P_3(3)` with 7 elements. -/
def A33 : List ℕ := [
  14, 18, 20, 27, 29, 41, 43]

/-- The 235 down-sets of `P_3(3)` with exactly 39 elements (bit masks, increasing). -/
def A39 : List ℕ := [
  549755813887, 824633720831, 1786706395135, 3917010173951, 3968549781503, 8280696946687,
  8297876815871, 8366579515391, 10514079940607, 10565619548159, 12678743457791, 12695923326975,
  12764626026495, 17059610099711, 17085379903487, 17093953060863, 30253749633023, 30279519436799,
  30288092594175, 34643206209535, 34651779366911, 34675418464255, 34677549170687, 69823283331071,
  69825430814719, 69827561521151, 69859522117631, 69859773775871, 69861912870911, 100613903876095,
  100622477033471, 100646116130815, 100648246837247, 105007655419903, 105009802903551,
  105011933609983, 105043894206463, 105044145864703, 105046284959743, 140189880025087,
  140192010731519, 140193906556927, 140194158215167, 140196297310207, 140228249518079,
  140228509564927, 280926294638591, 280927099944959, 280927351603199, 280931378135039,
  562400734478335, 562401002913791, 573429673623551, 573446853492735, 573515556192255,
  575611517009919, 575637286813695, 575645859971071, 580000973586431, 580009546743807,
  580033185841151, 580035316547583, 593195113119743, 593203686277119, 593227325374463,
  593229456080895, 597588864663551, 597591012147199, 597593142853631, 597625103450111,
  597625355108351, 597627494203391, 632771089268735, 632773219975167, 632775115800575,
  632775367458815, 632777506553855, 632809458761727, 632809718808575, 663559562330111,
  663561709813759, 663563840520191, 663595801116671, 663596052774911, 663598191869951,
  667955461357567, 667957592063999, 667959487889407, 667959739547647, 667961878642687,
  667993830850559, 667994090897407, 703138759704575, 703139565010943, 703139816669183,
  703141955764223, 703143843201023, 703144103247871, 703178194550783, 843875979624447,
  843876231282687, 843877036589055, 1125350822117375, 1719090724995071, 1719092872478719,
  1719095003185151, 1719126963781631, 1719127215439871, 1719129354534911, 1723486624022527,
  1723488754728959, 1723490650554367, 1723490902212607, 1723493041307647, 1723524993515519,
  1723525253562367, 1758670727675903, 1758670979334143, 1758673118429183, 1758675005865983,
  1758675265912831, 1758709357215743, 1789457321689087, 1789459452395519, 1789461348220927,
  1789461599879167, 1789463738974207, 1789495691182079, 1789495951228927, 1793855099764735,
  1793855351422975, 1793857490518015, 1793859377954815, 1793859638001663, 1793893729304575,
  1793893995642879, 1829039455076351, 1829039715123199, 1829043741655039, 4010472927920127,
  6293060958814207, 6293061218861055, 6293095310163967, 6293095576502271, 6297458996936703,
  6297459263275007, 6297493354577919, 42321892327030783, 42321892595204095, 42326290373525503,
  576561361912332287, 576561364059815935, 576561366190522367, 576561398151118847,
  576561398402777087, 576561400541872127, 576565757811359743, 576565759942066175,
  576565761837891583, 576565762089549823, 576565764228644863, 576565796180852735,
  576565796440899583, 576600941109706751, 576600941915013119, 576600942166671359,
  576600944305766399, 576600946193203199, 576600946453250047, 576600980544552959,
  576741678061191167, 576741678329626623, 576741678581284863, 576741679386591231,
  577023152769466367, 577023153172119551, 577124309718269951, 577124311848976383,
  577124313744801791, 577124313996460031, 577124316135555071, 577124348087762943,
  577124348347809791, 577128706691039231, 577128707496345599, 577128707748003839,
  577128709887098879, 577128711774535679, 577128712034582527, 577128746125885439,
  577128746392223743, 577163890794692607, 577163891046350847, 577163891851657215,
  577163892111704063, 577163896138235903, 577304628148830207, 577304628266270719,
  578250209356677119, 578250209608335359, 578250211747430399, 578250213634867199,
  578250213894914047, 578250247986216959, 578250248252555263, 578254607386411007,
  578254607646457855, 578254611672989695, 578254611939327999, 578254646030630911,
  578289791750111231, 582753813253849087, 582753813520187391, 582753847611490303,
  582753847879663615, 582758211298263039, 582758245657985023, 618782644630192127,
  618782644630437887, 1729663182399602687, 1729663182651260927, 1729663182802255871,
  1729663182919696383, 1729944657242095615, 1730226132738899967, 4035787666388680703,
  5194439831679139839, 5194439831947313151, 5194439866038616063, 5194439866038861823,
  5194444229725634559, 5230468663057563647, 42123956810476665855, 594331598025060777983,
  9486856922549767093231]

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

end Num

end OnlineColouring
