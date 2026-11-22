module

public import OnlineColouring.NumAdv10T

/-!
# Adversary certificate for the one-level game, `m = 10` (checks, part 7)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

Kernel checks (`decide +kernel` with the verified checker `chkSLem`), part 7: the lemmas
62720 to 71679 of the certificate `s10.txt`, 128 lemmas per theorem.  See `NumAdv10.lean`.
-/

public section

namespace OnlineColouring

namespace Num

theorem adv10_c490 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 62720 128 = true := by
  decide +kernel

theorem adv10_c491 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 62848 128 = true := by
  decide +kernel

theorem adv10_c492 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 62976 128 = true := by
  decide +kernel

theorem adv10_c493 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 63104 128 = true := by
  decide +kernel

theorem adv10_c494 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 63232 128 = true := by
  decide +kernel

theorem adv10_c495 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 63360 128 = true := by
  decide +kernel

theorem adv10_c496 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 63488 128 = true := by
  decide +kernel

theorem adv10_c497 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 63616 128 = true := by
  decide +kernel

theorem adv10_c498 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 63744 128 = true := by
  decide +kernel

theorem adv10_c499 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 63872 128 = true := by
  decide +kernel

theorem adv10_c500 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 64000 128 = true := by
  decide +kernel

theorem adv10_c501 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 64128 128 = true := by
  decide +kernel

theorem adv10_c502 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 64256 128 = true := by
  decide +kernel

theorem adv10_c503 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 64384 128 = true := by
  decide +kernel

theorem adv10_c504 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 64512 128 = true := by
  decide +kernel

theorem adv10_c505 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 64640 128 = true := by
  decide +kernel

theorem adv10_c506 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 64768 128 = true := by
  decide +kernel

theorem adv10_c507 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 64896 128 = true := by
  decide +kernel

theorem adv10_c508 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 65024 128 = true := by
  decide +kernel

theorem adv10_c509 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 65152 128 = true := by
  decide +kernel

theorem adv10_c510 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 65280 128 = true := by
  decide +kernel

theorem adv10_c511 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 65408 128 = true := by
  decide +kernel

theorem adv10_c512 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 65536 128 = true := by
  decide +kernel

theorem adv10_c513 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 65664 128 = true := by
  decide +kernel

theorem adv10_c514 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 65792 128 = true := by
  decide +kernel

theorem adv10_c515 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 65920 128 = true := by
  decide +kernel

theorem adv10_c516 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 66048 128 = true := by
  decide +kernel

theorem adv10_c517 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 66176 128 = true := by
  decide +kernel

theorem adv10_c518 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 66304 128 = true := by
  decide +kernel

theorem adv10_c519 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 66432 128 = true := by
  decide +kernel

theorem adv10_c520 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 66560 128 = true := by
  decide +kernel

theorem adv10_c521 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 66688 128 = true := by
  decide +kernel

theorem adv10_c522 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 66816 128 = true := by
  decide +kernel

theorem adv10_c523 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 66944 128 = true := by
  decide +kernel

theorem adv10_c524 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 67072 128 = true := by
  decide +kernel

theorem adv10_c525 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 67200 128 = true := by
  decide +kernel

theorem adv10_c526 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 67328 128 = true := by
  decide +kernel

theorem adv10_c527 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 67456 128 = true := by
  decide +kernel

theorem adv10_c528 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 67584 128 = true := by
  decide +kernel

theorem adv10_c529 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 67712 128 = true := by
  decide +kernel

theorem adv10_c530 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 67840 128 = true := by
  decide +kernel

theorem adv10_c531 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 67968 128 = true := by
  decide +kernel

theorem adv10_c532 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 68096 128 = true := by
  decide +kernel

theorem adv10_c533 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 68224 128 = true := by
  decide +kernel

theorem adv10_c534 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 68352 128 = true := by
  decide +kernel

theorem adv10_c535 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 68480 128 = true := by
  decide +kernel

theorem adv10_c536 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 68608 128 = true := by
  decide +kernel

theorem adv10_c537 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 68736 128 = true := by
  decide +kernel

theorem adv10_c538 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 68864 128 = true := by
  decide +kernel

theorem adv10_c539 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 68992 128 = true := by
  decide +kernel

theorem adv10_c540 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 69120 128 = true := by
  decide +kernel

theorem adv10_c541 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 69248 128 = true := by
  decide +kernel

theorem adv10_c542 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 69376 128 = true := by
  decide +kernel

theorem adv10_c543 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 69504 128 = true := by
  decide +kernel

theorem adv10_c544 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 69632 128 = true := by
  decide +kernel

theorem adv10_c545 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 69760 128 = true := by
  decide +kernel

theorem adv10_c546 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 69888 128 = true := by
  decide +kernel

theorem adv10_c547 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 70016 128 = true := by
  decide +kernel

theorem adv10_c548 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 70144 128 = true := by
  decide +kernel

theorem adv10_c549 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 70272 128 = true := by
  decide +kernel

theorem adv10_c550 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 70400 128 = true := by
  decide +kernel

theorem adv10_c551 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 70528 128 = true := by
  decide +kernel

theorem adv10_c552 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 70656 128 = true := by
  decide +kernel

theorem adv10_c553 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 70784 128 = true := by
  decide +kernel

theorem adv10_c554 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 70912 128 = true := by
  decide +kernel

theorem adv10_c555 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 71040 128 = true := by
  decide +kernel

theorem adv10_c556 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 71168 128 = true := by
  decide +kernel

theorem adv10_c557 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 71296 128 = true := by
  decide +kernel

theorem adv10_c558 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 71424 128 = true := by
  decide +kernel

theorem adv10_c559 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 71552 128 = true := by
  decide +kernel

end Num

end OnlineColouring
