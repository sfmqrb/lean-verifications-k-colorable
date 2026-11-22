module

public import OnlineColouring.NumAdv10T

/-!
# Adversary certificate for the one-level game, `m = 10` (checks, part 9)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

Kernel checks (`decide +kernel` with the verified checker `chkSLem`), part 9: the lemmas
80640 to 89599 of the certificate `s10.txt`, 128 lemmas per theorem.  See `NumAdv10.lean`.
-/

public section

namespace OnlineColouring

namespace Num

theorem adv10_c630 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 80640 128 = true := by
  decide +kernel

theorem adv10_c631 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 80768 128 = true := by
  decide +kernel

theorem adv10_c632 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 80896 128 = true := by
  decide +kernel

theorem adv10_c633 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 81024 128 = true := by
  decide +kernel

theorem adv10_c634 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 81152 128 = true := by
  decide +kernel

theorem adv10_c635 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 81280 128 = true := by
  decide +kernel

theorem adv10_c636 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 81408 128 = true := by
  decide +kernel

theorem adv10_c637 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 81536 128 = true := by
  decide +kernel

theorem adv10_c638 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 81664 128 = true := by
  decide +kernel

theorem adv10_c639 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 81792 128 = true := by
  decide +kernel

theorem adv10_c640 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 81920 128 = true := by
  decide +kernel

theorem adv10_c641 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 82048 128 = true := by
  decide +kernel

theorem adv10_c642 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 82176 128 = true := by
  decide +kernel

theorem adv10_c643 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 82304 128 = true := by
  decide +kernel

theorem adv10_c644 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 82432 128 = true := by
  decide +kernel

theorem adv10_c645 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 82560 128 = true := by
  decide +kernel

theorem adv10_c646 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 82688 128 = true := by
  decide +kernel

theorem adv10_c647 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 82816 128 = true := by
  decide +kernel

theorem adv10_c648 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 82944 128 = true := by
  decide +kernel

theorem adv10_c649 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 83072 128 = true := by
  decide +kernel

theorem adv10_c650 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 83200 128 = true := by
  decide +kernel

theorem adv10_c651 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 83328 128 = true := by
  decide +kernel

theorem adv10_c652 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 83456 128 = true := by
  decide +kernel

theorem adv10_c653 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 83584 128 = true := by
  decide +kernel

theorem adv10_c654 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 83712 128 = true := by
  decide +kernel

theorem adv10_c655 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 83840 128 = true := by
  decide +kernel

theorem adv10_c656 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 83968 128 = true := by
  decide +kernel

theorem adv10_c657 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 84096 128 = true := by
  decide +kernel

theorem adv10_c658 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 84224 128 = true := by
  decide +kernel

theorem adv10_c659 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 84352 128 = true := by
  decide +kernel

theorem adv10_c660 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 84480 128 = true := by
  decide +kernel

theorem adv10_c661 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 84608 128 = true := by
  decide +kernel

theorem adv10_c662 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 84736 128 = true := by
  decide +kernel

theorem adv10_c663 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 84864 128 = true := by
  decide +kernel

theorem adv10_c664 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 84992 128 = true := by
  decide +kernel

theorem adv10_c665 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 85120 128 = true := by
  decide +kernel

theorem adv10_c666 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 85248 128 = true := by
  decide +kernel

theorem adv10_c667 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 85376 128 = true := by
  decide +kernel

theorem adv10_c668 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 85504 128 = true := by
  decide +kernel

theorem adv10_c669 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 85632 128 = true := by
  decide +kernel

theorem adv10_c670 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 85760 128 = true := by
  decide +kernel

theorem adv10_c671 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 85888 128 = true := by
  decide +kernel

theorem adv10_c672 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 86016 128 = true := by
  decide +kernel

theorem adv10_c673 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 86144 128 = true := by
  decide +kernel

theorem adv10_c674 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 86272 128 = true := by
  decide +kernel

theorem adv10_c675 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 86400 128 = true := by
  decide +kernel

theorem adv10_c676 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 86528 128 = true := by
  decide +kernel

theorem adv10_c677 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 86656 128 = true := by
  decide +kernel

theorem adv10_c678 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 86784 128 = true := by
  decide +kernel

theorem adv10_c679 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 86912 128 = true := by
  decide +kernel

theorem adv10_c680 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 87040 128 = true := by
  decide +kernel

theorem adv10_c681 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 87168 128 = true := by
  decide +kernel

theorem adv10_c682 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 87296 128 = true := by
  decide +kernel

theorem adv10_c683 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 87424 128 = true := by
  decide +kernel

theorem adv10_c684 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 87552 128 = true := by
  decide +kernel

theorem adv10_c685 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 87680 128 = true := by
  decide +kernel

theorem adv10_c686 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 87808 128 = true := by
  decide +kernel

theorem adv10_c687 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 87936 128 = true := by
  decide +kernel

theorem adv10_c688 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 88064 128 = true := by
  decide +kernel

theorem adv10_c689 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 88192 128 = true := by
  decide +kernel

theorem adv10_c690 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 88320 128 = true := by
  decide +kernel

theorem adv10_c691 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 88448 128 = true := by
  decide +kernel

theorem adv10_c692 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 88576 128 = true := by
  decide +kernel

theorem adv10_c693 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 88704 128 = true := by
  decide +kernel

theorem adv10_c694 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 88832 128 = true := by
  decide +kernel

theorem adv10_c695 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 88960 128 = true := by
  decide +kernel

theorem adv10_c696 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 89088 128 = true := by
  decide +kernel

theorem adv10_c697 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 89216 128 = true := by
  decide +kernel

theorem adv10_c698 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 89344 128 = true := by
  decide +kernel

theorem adv10_c699 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 89472 128 = true := by
  decide +kernel

end Num

end OnlineColouring
