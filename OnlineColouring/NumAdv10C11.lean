module

public import OnlineColouring.NumAdv10T

/-!
# Adversary certificate for the one-level game, `m = 10` (checks, part 11)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

Kernel checks (`decide +kernel` with the verified checker `chkSLem`), part 11: the lemmas
98560 to 107284 of the certificate `s10.txt`, 128 lemmas per theorem.  See `NumAdv10.lean`.
-/

public section

namespace OnlineColouring

namespace Num

theorem adv10_c770 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 98560 128 = true := by
  decide +kernel

theorem adv10_c771 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 98688 128 = true := by
  decide +kernel

theorem adv10_c772 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 98816 128 = true := by
  decide +kernel

theorem adv10_c773 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 98944 128 = true := by
  decide +kernel

theorem adv10_c774 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 99072 128 = true := by
  decide +kernel

theorem adv10_c775 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 99200 128 = true := by
  decide +kernel

theorem adv10_c776 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 99328 128 = true := by
  decide +kernel

theorem adv10_c777 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 99456 128 = true := by
  decide +kernel

theorem adv10_c778 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 99584 128 = true := by
  decide +kernel

theorem adv10_c779 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 99712 128 = true := by
  decide +kernel

theorem adv10_c780 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 99840 128 = true := by
  decide +kernel

theorem adv10_c781 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 99968 128 = true := by
  decide +kernel

theorem adv10_c782 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 100096 128 = true := by
  decide +kernel

theorem adv10_c783 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 100224 128 = true := by
  decide +kernel

theorem adv10_c784 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 100352 128 = true := by
  decide +kernel

theorem adv10_c785 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 100480 128 = true := by
  decide +kernel

theorem adv10_c786 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 100608 128 = true := by
  decide +kernel

theorem adv10_c787 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 100736 128 = true := by
  decide +kernel

theorem adv10_c788 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 100864 128 = true := by
  decide +kernel

theorem adv10_c789 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 100992 128 = true := by
  decide +kernel

theorem adv10_c790 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 101120 128 = true := by
  decide +kernel

theorem adv10_c791 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 101248 128 = true := by
  decide +kernel

theorem adv10_c792 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 101376 128 = true := by
  decide +kernel

theorem adv10_c793 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 101504 128 = true := by
  decide +kernel

theorem adv10_c794 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 101632 128 = true := by
  decide +kernel

theorem adv10_c795 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 101760 128 = true := by
  decide +kernel

theorem adv10_c796 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 101888 128 = true := by
  decide +kernel

theorem adv10_c797 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 102016 128 = true := by
  decide +kernel

theorem adv10_c798 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 102144 128 = true := by
  decide +kernel

theorem adv10_c799 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 102272 128 = true := by
  decide +kernel

theorem adv10_c800 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 102400 128 = true := by
  decide +kernel

theorem adv10_c801 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 102528 128 = true := by
  decide +kernel

theorem adv10_c802 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 102656 128 = true := by
  decide +kernel

theorem adv10_c803 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 102784 128 = true := by
  decide +kernel

theorem adv10_c804 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 102912 128 = true := by
  decide +kernel

theorem adv10_c805 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 103040 128 = true := by
  decide +kernel

theorem adv10_c806 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 103168 128 = true := by
  decide +kernel

theorem adv10_c807 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 103296 128 = true := by
  decide +kernel

theorem adv10_c808 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 103424 128 = true := by
  decide +kernel

theorem adv10_c809 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 103552 128 = true := by
  decide +kernel

theorem adv10_c810 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 103680 128 = true := by
  decide +kernel

theorem adv10_c811 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 103808 128 = true := by
  decide +kernel

theorem adv10_c812 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 103936 128 = true := by
  decide +kernel

theorem adv10_c813 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 104064 128 = true := by
  decide +kernel

theorem adv10_c814 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 104192 128 = true := by
  decide +kernel

theorem adv10_c815 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 104320 128 = true := by
  decide +kernel

theorem adv10_c816 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 104448 128 = true := by
  decide +kernel

theorem adv10_c817 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 104576 128 = true := by
  decide +kernel

theorem adv10_c818 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 104704 128 = true := by
  decide +kernel

theorem adv10_c819 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 104832 128 = true := by
  decide +kernel

theorem adv10_c820 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 104960 128 = true := by
  decide +kernel

theorem adv10_c821 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 105088 128 = true := by
  decide +kernel

theorem adv10_c822 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 105216 128 = true := by
  decide +kernel

theorem adv10_c823 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 105344 128 = true := by
  decide +kernel

theorem adv10_c824 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 105472 128 = true := by
  decide +kernel

theorem adv10_c825 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 105600 128 = true := by
  decide +kernel

theorem adv10_c826 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 105728 128 = true := by
  decide +kernel

theorem adv10_c827 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 105856 128 = true := by
  decide +kernel

theorem adv10_c828 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 105984 128 = true := by
  decide +kernel

theorem adv10_c829 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 106112 128 = true := by
  decide +kernel

theorem adv10_c830 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 106240 128 = true := by
  decide +kernel

theorem adv10_c831 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 106368 128 = true := by
  decide +kernel

theorem adv10_c832 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 106496 128 = true := by
  decide +kernel

theorem adv10_c833 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 106624 128 = true := by
  decide +kernel

theorem adv10_c834 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 106752 128 = true := by
  decide +kernel

theorem adv10_c835 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 106880 128 = true := by
  decide +kernel

theorem adv10_c836 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 107008 128 = true := by
  decide +kernel

theorem adv10_c837 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 107136 128 = true := by
  decide +kernel

theorem adv10_c838 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 107264 21 = true := by
  decide +kernel

end Num

end OnlineColouring
