module

public import OnlineColouring.NumAdv10T

/-!
# Adversary certificate for the one-level game, `m = 10` (checks, part 10)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

Kernel checks (`decide +kernel` with the verified checker `chkSLem`), part 10: the lemmas
89600 to 98559 of the certificate `s10.txt`, 128 lemmas per theorem.  See `NumAdv10.lean`.
-/

public section

namespace OnlineColouring

namespace Num

theorem adv10_c700 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 89600 128 = true := by
  decide +kernel

theorem adv10_c701 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 89728 128 = true := by
  decide +kernel

theorem adv10_c702 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 89856 128 = true := by
  decide +kernel

theorem adv10_c703 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 89984 128 = true := by
  decide +kernel

theorem adv10_c704 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 90112 128 = true := by
  decide +kernel

theorem adv10_c705 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 90240 128 = true := by
  decide +kernel

theorem adv10_c706 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 90368 128 = true := by
  decide +kernel

theorem adv10_c707 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 90496 128 = true := by
  decide +kernel

theorem adv10_c708 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 90624 128 = true := by
  decide +kernel

theorem adv10_c709 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 90752 128 = true := by
  decide +kernel

theorem adv10_c710 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 90880 128 = true := by
  decide +kernel

theorem adv10_c711 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 91008 128 = true := by
  decide +kernel

theorem adv10_c712 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 91136 128 = true := by
  decide +kernel

theorem adv10_c713 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 91264 128 = true := by
  decide +kernel

theorem adv10_c714 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 91392 128 = true := by
  decide +kernel

theorem adv10_c715 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 91520 128 = true := by
  decide +kernel

theorem adv10_c716 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 91648 128 = true := by
  decide +kernel

theorem adv10_c717 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 91776 128 = true := by
  decide +kernel

theorem adv10_c718 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 91904 128 = true := by
  decide +kernel

theorem adv10_c719 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 92032 128 = true := by
  decide +kernel

theorem adv10_c720 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 92160 128 = true := by
  decide +kernel

theorem adv10_c721 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 92288 128 = true := by
  decide +kernel

theorem adv10_c722 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 92416 128 = true := by
  decide +kernel

theorem adv10_c723 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 92544 128 = true := by
  decide +kernel

theorem adv10_c724 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 92672 128 = true := by
  decide +kernel

theorem adv10_c725 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 92800 128 = true := by
  decide +kernel

theorem adv10_c726 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 92928 128 = true := by
  decide +kernel

theorem adv10_c727 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 93056 128 = true := by
  decide +kernel

theorem adv10_c728 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 93184 128 = true := by
  decide +kernel

theorem adv10_c729 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 93312 128 = true := by
  decide +kernel

theorem adv10_c730 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 93440 128 = true := by
  decide +kernel

theorem adv10_c731 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 93568 128 = true := by
  decide +kernel

theorem adv10_c732 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 93696 128 = true := by
  decide +kernel

theorem adv10_c733 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 93824 128 = true := by
  decide +kernel

theorem adv10_c734 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 93952 128 = true := by
  decide +kernel

theorem adv10_c735 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 94080 128 = true := by
  decide +kernel

theorem adv10_c736 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 94208 128 = true := by
  decide +kernel

theorem adv10_c737 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 94336 128 = true := by
  decide +kernel

theorem adv10_c738 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 94464 128 = true := by
  decide +kernel

theorem adv10_c739 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 94592 128 = true := by
  decide +kernel

theorem adv10_c740 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 94720 128 = true := by
  decide +kernel

theorem adv10_c741 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 94848 128 = true := by
  decide +kernel

theorem adv10_c742 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 94976 128 = true := by
  decide +kernel

theorem adv10_c743 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 95104 128 = true := by
  decide +kernel

theorem adv10_c744 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 95232 128 = true := by
  decide +kernel

theorem adv10_c745 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 95360 128 = true := by
  decide +kernel

theorem adv10_c746 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 95488 128 = true := by
  decide +kernel

theorem adv10_c747 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 95616 128 = true := by
  decide +kernel

theorem adv10_c748 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 95744 128 = true := by
  decide +kernel

theorem adv10_c749 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 95872 128 = true := by
  decide +kernel

theorem adv10_c750 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 96000 128 = true := by
  decide +kernel

theorem adv10_c751 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 96128 128 = true := by
  decide +kernel

theorem adv10_c752 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 96256 128 = true := by
  decide +kernel

theorem adv10_c753 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 96384 128 = true := by
  decide +kernel

theorem adv10_c754 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 96512 128 = true := by
  decide +kernel

theorem adv10_c755 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 96640 128 = true := by
  decide +kernel

theorem adv10_c756 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 96768 128 = true := by
  decide +kernel

theorem adv10_c757 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 96896 128 = true := by
  decide +kernel

theorem adv10_c758 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 97024 128 = true := by
  decide +kernel

theorem adv10_c759 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 97152 128 = true := by
  decide +kernel

theorem adv10_c760 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 97280 128 = true := by
  decide +kernel

theorem adv10_c761 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 97408 128 = true := by
  decide +kernel

theorem adv10_c762 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 97536 128 = true := by
  decide +kernel

theorem adv10_c763 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 97664 128 = true := by
  decide +kernel

theorem adv10_c764 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 97792 128 = true := by
  decide +kernel

theorem adv10_c765 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 97920 128 = true := by
  decide +kernel

theorem adv10_c766 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 98048 128 = true := by
  decide +kernel

theorem adv10_c767 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 98176 128 = true := by
  decide +kernel

theorem adv10_c768 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 98304 128 = true := by
  decide +kernel

theorem adv10_c769 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 98432 128 = true := by
  decide +kernel

end Num

end OnlineColouring
