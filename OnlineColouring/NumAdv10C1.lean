module

public import OnlineColouring.NumAdv10T

/-!
# Adversary certificate for the one-level game, `m = 10` (checks, part 1)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

Kernel checks (`decide +kernel` with the verified checker `chkSLem`), part 1: the lemmas
8960 to 17919 of the certificate `s10.txt`, 128 lemmas per theorem.  See `NumAdv10.lean`.
-/

public section

namespace OnlineColouring

namespace Num

theorem adv10_c70 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 8960 128 = true := by
  decide +kernel

theorem adv10_c71 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 9088 128 = true := by
  decide +kernel

theorem adv10_c72 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 9216 128 = true := by
  decide +kernel

theorem adv10_c73 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 9344 128 = true := by
  decide +kernel

theorem adv10_c74 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 9472 128 = true := by
  decide +kernel

theorem adv10_c75 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 9600 128 = true := by
  decide +kernel

theorem adv10_c76 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 9728 128 = true := by
  decide +kernel

theorem adv10_c77 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 9856 128 = true := by
  decide +kernel

theorem adv10_c78 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 9984 128 = true := by
  decide +kernel

theorem adv10_c79 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 10112 128 = true := by
  decide +kernel

theorem adv10_c80 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 10240 128 = true := by
  decide +kernel

theorem adv10_c81 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 10368 128 = true := by
  decide +kernel

theorem adv10_c82 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 10496 128 = true := by
  decide +kernel

theorem adv10_c83 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 10624 128 = true := by
  decide +kernel

theorem adv10_c84 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 10752 128 = true := by
  decide +kernel

theorem adv10_c85 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 10880 128 = true := by
  decide +kernel

theorem adv10_c86 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 11008 128 = true := by
  decide +kernel

theorem adv10_c87 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 11136 128 = true := by
  decide +kernel

theorem adv10_c88 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 11264 128 = true := by
  decide +kernel

theorem adv10_c89 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 11392 128 = true := by
  decide +kernel

theorem adv10_c90 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 11520 128 = true := by
  decide +kernel

theorem adv10_c91 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 11648 128 = true := by
  decide +kernel

theorem adv10_c92 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 11776 128 = true := by
  decide +kernel

theorem adv10_c93 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 11904 128 = true := by
  decide +kernel

theorem adv10_c94 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 12032 128 = true := by
  decide +kernel

theorem adv10_c95 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 12160 128 = true := by
  decide +kernel

theorem adv10_c96 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 12288 128 = true := by
  decide +kernel

theorem adv10_c97 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 12416 128 = true := by
  decide +kernel

theorem adv10_c98 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 12544 128 = true := by
  decide +kernel

theorem adv10_c99 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 12672 128 = true := by
  decide +kernel

theorem adv10_c100 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 12800 128 = true := by
  decide +kernel

theorem adv10_c101 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 12928 128 = true := by
  decide +kernel

theorem adv10_c102 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 13056 128 = true := by
  decide +kernel

theorem adv10_c103 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 13184 128 = true := by
  decide +kernel

theorem adv10_c104 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 13312 128 = true := by
  decide +kernel

theorem adv10_c105 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 13440 128 = true := by
  decide +kernel

theorem adv10_c106 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 13568 128 = true := by
  decide +kernel

theorem adv10_c107 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 13696 128 = true := by
  decide +kernel

theorem adv10_c108 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 13824 128 = true := by
  decide +kernel

theorem adv10_c109 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 13952 128 = true := by
  decide +kernel

theorem adv10_c110 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 14080 128 = true := by
  decide +kernel

theorem adv10_c111 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 14208 128 = true := by
  decide +kernel

theorem adv10_c112 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 14336 128 = true := by
  decide +kernel

theorem adv10_c113 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 14464 128 = true := by
  decide +kernel

theorem adv10_c114 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 14592 128 = true := by
  decide +kernel

theorem adv10_c115 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 14720 128 = true := by
  decide +kernel

theorem adv10_c116 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 14848 128 = true := by
  decide +kernel

theorem adv10_c117 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 14976 128 = true := by
  decide +kernel

theorem adv10_c118 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 15104 128 = true := by
  decide +kernel

theorem adv10_c119 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 15232 128 = true := by
  decide +kernel

theorem adv10_c120 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 15360 128 = true := by
  decide +kernel

theorem adv10_c121 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 15488 128 = true := by
  decide +kernel

theorem adv10_c122 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 15616 128 = true := by
  decide +kernel

theorem adv10_c123 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 15744 128 = true := by
  decide +kernel

theorem adv10_c124 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 15872 128 = true := by
  decide +kernel

theorem adv10_c125 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 16000 128 = true := by
  decide +kernel

theorem adv10_c126 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 16128 128 = true := by
  decide +kernel

theorem adv10_c127 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 16256 128 = true := by
  decide +kernel

theorem adv10_c128 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 16384 128 = true := by
  decide +kernel

theorem adv10_c129 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 16512 128 = true := by
  decide +kernel

theorem adv10_c130 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 16640 128 = true := by
  decide +kernel

theorem adv10_c131 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 16768 128 = true := by
  decide +kernel

theorem adv10_c132 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 16896 128 = true := by
  decide +kernel

theorem adv10_c133 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 17024 128 = true := by
  decide +kernel

theorem adv10_c134 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 17152 128 = true := by
  decide +kernel

theorem adv10_c135 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 17280 128 = true := by
  decide +kernel

theorem adv10_c136 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 17408 128 = true := by
  decide +kernel

theorem adv10_c137 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 17536 128 = true := by
  decide +kernel

theorem adv10_c138 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 17664 128 = true := by
  decide +kernel

theorem adv10_c139 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 17792 128 = true := by
  decide +kernel

end Num

end OnlineColouring
