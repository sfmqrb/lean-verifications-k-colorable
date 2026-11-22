module

public import OnlineColouring.NumAdv10T

/-!
# Adversary certificate for the one-level game, `m = 10` (checks, part 3)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

Kernel checks (`decide +kernel` with the verified checker `chkSLem`), part 3: the lemmas
26880 to 35839 of the certificate `s10.txt`, 128 lemmas per theorem.  See `NumAdv10.lean`.
-/

public section

namespace OnlineColouring

namespace Num

theorem adv10_c210 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 26880 128 = true := by
  decide +kernel

theorem adv10_c211 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 27008 128 = true := by
  decide +kernel

theorem adv10_c212 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 27136 128 = true := by
  decide +kernel

theorem adv10_c213 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 27264 128 = true := by
  decide +kernel

theorem adv10_c214 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 27392 128 = true := by
  decide +kernel

theorem adv10_c215 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 27520 128 = true := by
  decide +kernel

theorem adv10_c216 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 27648 128 = true := by
  decide +kernel

theorem adv10_c217 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 27776 128 = true := by
  decide +kernel

theorem adv10_c218 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 27904 128 = true := by
  decide +kernel

theorem adv10_c219 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 28032 128 = true := by
  decide +kernel

theorem adv10_c220 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 28160 128 = true := by
  decide +kernel

theorem adv10_c221 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 28288 128 = true := by
  decide +kernel

theorem adv10_c222 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 28416 128 = true := by
  decide +kernel

theorem adv10_c223 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 28544 128 = true := by
  decide +kernel

theorem adv10_c224 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 28672 128 = true := by
  decide +kernel

theorem adv10_c225 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 28800 128 = true := by
  decide +kernel

theorem adv10_c226 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 28928 128 = true := by
  decide +kernel

theorem adv10_c227 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 29056 128 = true := by
  decide +kernel

theorem adv10_c228 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 29184 128 = true := by
  decide +kernel

theorem adv10_c229 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 29312 128 = true := by
  decide +kernel

theorem adv10_c230 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 29440 128 = true := by
  decide +kernel

theorem adv10_c231 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 29568 128 = true := by
  decide +kernel

theorem adv10_c232 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 29696 128 = true := by
  decide +kernel

theorem adv10_c233 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 29824 128 = true := by
  decide +kernel

theorem adv10_c234 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 29952 128 = true := by
  decide +kernel

theorem adv10_c235 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 30080 128 = true := by
  decide +kernel

theorem adv10_c236 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 30208 128 = true := by
  decide +kernel

theorem adv10_c237 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 30336 128 = true := by
  decide +kernel

theorem adv10_c238 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 30464 128 = true := by
  decide +kernel

theorem adv10_c239 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 30592 128 = true := by
  decide +kernel

theorem adv10_c240 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 30720 128 = true := by
  decide +kernel

theorem adv10_c241 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 30848 128 = true := by
  decide +kernel

theorem adv10_c242 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 30976 128 = true := by
  decide +kernel

theorem adv10_c243 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 31104 128 = true := by
  decide +kernel

theorem adv10_c244 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 31232 128 = true := by
  decide +kernel

theorem adv10_c245 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 31360 128 = true := by
  decide +kernel

theorem adv10_c246 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 31488 128 = true := by
  decide +kernel

theorem adv10_c247 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 31616 128 = true := by
  decide +kernel

theorem adv10_c248 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 31744 128 = true := by
  decide +kernel

theorem adv10_c249 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 31872 128 = true := by
  decide +kernel

theorem adv10_c250 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 32000 128 = true := by
  decide +kernel

theorem adv10_c251 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 32128 128 = true := by
  decide +kernel

theorem adv10_c252 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 32256 128 = true := by
  decide +kernel

theorem adv10_c253 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 32384 128 = true := by
  decide +kernel

theorem adv10_c254 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 32512 128 = true := by
  decide +kernel

theorem adv10_c255 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 32640 128 = true := by
  decide +kernel

theorem adv10_c256 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 32768 128 = true := by
  decide +kernel

theorem adv10_c257 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 32896 128 = true := by
  decide +kernel

theorem adv10_c258 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 33024 128 = true := by
  decide +kernel

theorem adv10_c259 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 33152 128 = true := by
  decide +kernel

theorem adv10_c260 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 33280 128 = true := by
  decide +kernel

theorem adv10_c261 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 33408 128 = true := by
  decide +kernel

theorem adv10_c262 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 33536 128 = true := by
  decide +kernel

theorem adv10_c263 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 33664 128 = true := by
  decide +kernel

theorem adv10_c264 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 33792 128 = true := by
  decide +kernel

theorem adv10_c265 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 33920 128 = true := by
  decide +kernel

theorem adv10_c266 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 34048 128 = true := by
  decide +kernel

theorem adv10_c267 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 34176 128 = true := by
  decide +kernel

theorem adv10_c268 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 34304 128 = true := by
  decide +kernel

theorem adv10_c269 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 34432 128 = true := by
  decide +kernel

theorem adv10_c270 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 34560 128 = true := by
  decide +kernel

theorem adv10_c271 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 34688 128 = true := by
  decide +kernel

theorem adv10_c272 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 34816 128 = true := by
  decide +kernel

theorem adv10_c273 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 34944 128 = true := by
  decide +kernel

theorem adv10_c274 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 35072 128 = true := by
  decide +kernel

theorem adv10_c275 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 35200 128 = true := by
  decide +kernel

theorem adv10_c276 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 35328 128 = true := by
  decide +kernel

theorem adv10_c277 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 35456 128 = true := by
  decide +kernel

theorem adv10_c278 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 35584 128 = true := by
  decide +kernel

theorem adv10_c279 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 35712 128 = true := by
  decide +kernel

end Num

end OnlineColouring
