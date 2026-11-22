module

public import OnlineColouring.NumAdv10T

/-!
# Adversary certificate for the one-level game, `m = 10` (checks, part 6)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

Kernel checks (`decide +kernel` with the verified checker `chkSLem`), part 6: the lemmas
53760 to 62719 of the certificate `s10.txt`, 128 lemmas per theorem.  See `NumAdv10.lean`.
-/

public section

namespace OnlineColouring

namespace Num

theorem adv10_c420 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 53760 128 = true := by
  decide +kernel

theorem adv10_c421 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 53888 128 = true := by
  decide +kernel

theorem adv10_c422 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 54016 128 = true := by
  decide +kernel

theorem adv10_c423 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 54144 128 = true := by
  decide +kernel

theorem adv10_c424 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 54272 128 = true := by
  decide +kernel

theorem adv10_c425 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 54400 128 = true := by
  decide +kernel

theorem adv10_c426 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 54528 128 = true := by
  decide +kernel

theorem adv10_c427 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 54656 128 = true := by
  decide +kernel

theorem adv10_c428 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 54784 128 = true := by
  decide +kernel

theorem adv10_c429 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 54912 128 = true := by
  decide +kernel

theorem adv10_c430 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 55040 128 = true := by
  decide +kernel

theorem adv10_c431 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 55168 128 = true := by
  decide +kernel

theorem adv10_c432 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 55296 128 = true := by
  decide +kernel

theorem adv10_c433 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 55424 128 = true := by
  decide +kernel

theorem adv10_c434 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 55552 128 = true := by
  decide +kernel

theorem adv10_c435 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 55680 128 = true := by
  decide +kernel

theorem adv10_c436 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 55808 128 = true := by
  decide +kernel

theorem adv10_c437 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 55936 128 = true := by
  decide +kernel

theorem adv10_c438 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 56064 128 = true := by
  decide +kernel

theorem adv10_c439 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 56192 128 = true := by
  decide +kernel

theorem adv10_c440 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 56320 128 = true := by
  decide +kernel

theorem adv10_c441 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 56448 128 = true := by
  decide +kernel

theorem adv10_c442 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 56576 128 = true := by
  decide +kernel

theorem adv10_c443 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 56704 128 = true := by
  decide +kernel

theorem adv10_c444 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 56832 128 = true := by
  decide +kernel

theorem adv10_c445 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 56960 128 = true := by
  decide +kernel

theorem adv10_c446 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 57088 128 = true := by
  decide +kernel

theorem adv10_c447 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 57216 128 = true := by
  decide +kernel

theorem adv10_c448 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 57344 128 = true := by
  decide +kernel

theorem adv10_c449 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 57472 128 = true := by
  decide +kernel

theorem adv10_c450 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 57600 128 = true := by
  decide +kernel

theorem adv10_c451 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 57728 128 = true := by
  decide +kernel

theorem adv10_c452 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 57856 128 = true := by
  decide +kernel

theorem adv10_c453 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 57984 128 = true := by
  decide +kernel

theorem adv10_c454 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 58112 128 = true := by
  decide +kernel

theorem adv10_c455 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 58240 128 = true := by
  decide +kernel

theorem adv10_c456 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 58368 128 = true := by
  decide +kernel

theorem adv10_c457 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 58496 128 = true := by
  decide +kernel

theorem adv10_c458 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 58624 128 = true := by
  decide +kernel

theorem adv10_c459 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 58752 128 = true := by
  decide +kernel

theorem adv10_c460 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 58880 128 = true := by
  decide +kernel

theorem adv10_c461 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 59008 128 = true := by
  decide +kernel

theorem adv10_c462 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 59136 128 = true := by
  decide +kernel

theorem adv10_c463 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 59264 128 = true := by
  decide +kernel

theorem adv10_c464 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 59392 128 = true := by
  decide +kernel

theorem adv10_c465 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 59520 128 = true := by
  decide +kernel

theorem adv10_c466 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 59648 128 = true := by
  decide +kernel

theorem adv10_c467 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 59776 128 = true := by
  decide +kernel

theorem adv10_c468 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 59904 128 = true := by
  decide +kernel

theorem adv10_c469 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 60032 128 = true := by
  decide +kernel

theorem adv10_c470 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 60160 128 = true := by
  decide +kernel

theorem adv10_c471 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 60288 128 = true := by
  decide +kernel

theorem adv10_c472 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 60416 128 = true := by
  decide +kernel

theorem adv10_c473 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 60544 128 = true := by
  decide +kernel

theorem adv10_c474 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 60672 128 = true := by
  decide +kernel

theorem adv10_c475 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 60800 128 = true := by
  decide +kernel

theorem adv10_c476 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 60928 128 = true := by
  decide +kernel

theorem adv10_c477 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 61056 128 = true := by
  decide +kernel

theorem adv10_c478 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 61184 128 = true := by
  decide +kernel

theorem adv10_c479 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 61312 128 = true := by
  decide +kernel

theorem adv10_c480 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 61440 128 = true := by
  decide +kernel

theorem adv10_c481 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 61568 128 = true := by
  decide +kernel

theorem adv10_c482 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 61696 128 = true := by
  decide +kernel

theorem adv10_c483 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 61824 128 = true := by
  decide +kernel

theorem adv10_c484 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 61952 128 = true := by
  decide +kernel

theorem adv10_c485 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 62080 128 = true := by
  decide +kernel

theorem adv10_c486 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 62208 128 = true := by
  decide +kernel

theorem adv10_c487 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 62336 128 = true := by
  decide +kernel

theorem adv10_c488 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 62464 128 = true := by
  decide +kernel

theorem adv10_c489 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 62592 128 = true := by
  decide +kernel

end Num

end OnlineColouring
