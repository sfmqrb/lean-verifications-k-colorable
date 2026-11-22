module

public import OnlineColouring.NumAdv10T

/-!
# Adversary certificate for the one-level game, `m = 10` (checks, part 0)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

Kernel checks (`decide +kernel` with the verified checker `chkSLem`), part 0: the lemmas
0 to 8959 of the certificate `s10.txt`, 128 lemmas per theorem.  See `NumAdv10.lean`.
-/

public section

namespace OnlineColouring

namespace Num

theorem adv10_c0 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 0 128 = true := by
  decide +kernel

theorem adv10_c1 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 128 128 = true := by
  decide +kernel

theorem adv10_c2 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 256 128 = true := by
  decide +kernel

theorem adv10_c3 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 384 128 = true := by
  decide +kernel

theorem adv10_c4 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 512 128 = true := by
  decide +kernel

theorem adv10_c5 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 640 128 = true := by
  decide +kernel

theorem adv10_c6 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 768 128 = true := by
  decide +kernel

theorem adv10_c7 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 896 128 = true := by
  decide +kernel

theorem adv10_c8 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 1024 128 = true := by
  decide +kernel

theorem adv10_c9 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 1152 128 = true := by
  decide +kernel

theorem adv10_c10 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 1280 128 = true := by
  decide +kernel

theorem adv10_c11 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 1408 128 = true := by
  decide +kernel

theorem adv10_c12 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 1536 128 = true := by
  decide +kernel

theorem adv10_c13 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 1664 128 = true := by
  decide +kernel

theorem adv10_c14 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 1792 128 = true := by
  decide +kernel

theorem adv10_c15 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 1920 128 = true := by
  decide +kernel

theorem adv10_c16 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 2048 128 = true := by
  decide +kernel

theorem adv10_c17 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 2176 128 = true := by
  decide +kernel

theorem adv10_c18 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 2304 128 = true := by
  decide +kernel

theorem adv10_c19 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 2432 128 = true := by
  decide +kernel

theorem adv10_c20 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 2560 128 = true := by
  decide +kernel

theorem adv10_c21 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 2688 128 = true := by
  decide +kernel

theorem adv10_c22 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 2816 128 = true := by
  decide +kernel

theorem adv10_c23 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 2944 128 = true := by
  decide +kernel

theorem adv10_c24 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 3072 128 = true := by
  decide +kernel

theorem adv10_c25 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 3200 128 = true := by
  decide +kernel

theorem adv10_c26 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 3328 128 = true := by
  decide +kernel

theorem adv10_c27 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 3456 128 = true := by
  decide +kernel

theorem adv10_c28 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 3584 128 = true := by
  decide +kernel

theorem adv10_c29 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 3712 128 = true := by
  decide +kernel

theorem adv10_c30 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 3840 128 = true := by
  decide +kernel

theorem adv10_c31 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 3968 128 = true := by
  decide +kernel

theorem adv10_c32 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 4096 128 = true := by
  decide +kernel

theorem adv10_c33 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 4224 128 = true := by
  decide +kernel

theorem adv10_c34 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 4352 128 = true := by
  decide +kernel

theorem adv10_c35 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 4480 128 = true := by
  decide +kernel

theorem adv10_c36 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 4608 128 = true := by
  decide +kernel

theorem adv10_c37 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 4736 128 = true := by
  decide +kernel

theorem adv10_c38 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 4864 128 = true := by
  decide +kernel

theorem adv10_c39 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 4992 128 = true := by
  decide +kernel

theorem adv10_c40 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 5120 128 = true := by
  decide +kernel

theorem adv10_c41 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 5248 128 = true := by
  decide +kernel

theorem adv10_c42 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 5376 128 = true := by
  decide +kernel

theorem adv10_c43 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 5504 128 = true := by
  decide +kernel

theorem adv10_c44 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 5632 128 = true := by
  decide +kernel

theorem adv10_c45 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 5760 128 = true := by
  decide +kernel

theorem adv10_c46 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 5888 128 = true := by
  decide +kernel

theorem adv10_c47 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 6016 128 = true := by
  decide +kernel

theorem adv10_c48 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 6144 128 = true := by
  decide +kernel

theorem adv10_c49 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 6272 128 = true := by
  decide +kernel

theorem adv10_c50 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 6400 128 = true := by
  decide +kernel

theorem adv10_c51 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 6528 128 = true := by
  decide +kernel

theorem adv10_c52 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 6656 128 = true := by
  decide +kernel

theorem adv10_c53 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 6784 128 = true := by
  decide +kernel

theorem adv10_c54 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 6912 128 = true := by
  decide +kernel

theorem adv10_c55 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 7040 128 = true := by
  decide +kernel

theorem adv10_c56 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 7168 128 = true := by
  decide +kernel

theorem adv10_c57 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 7296 128 = true := by
  decide +kernel

theorem adv10_c58 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 7424 128 = true := by
  decide +kernel

theorem adv10_c59 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 7552 128 = true := by
  decide +kernel

theorem adv10_c60 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 7680 128 = true := by
  decide +kernel

theorem adv10_c61 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 7808 128 = true := by
  decide +kernel

theorem adv10_c62 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 7936 128 = true := by
  decide +kernel

theorem adv10_c63 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 8064 128 = true := by
  decide +kernel

theorem adv10_c64 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 8192 128 = true := by
  decide +kernel

theorem adv10_c65 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 8320 128 = true := by
  decide +kernel

theorem adv10_c66 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 8448 128 = true := by
  decide +kernel

theorem adv10_c67 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 8576 128 = true := by
  decide +kernel

theorem adv10_c68 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 8704 128 = true := by
  decide +kernel

theorem adv10_c69 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 8832 128 = true := by
  decide +kernel

end Num

end OnlineColouring
