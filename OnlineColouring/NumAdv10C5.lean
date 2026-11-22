module

public import OnlineColouring.NumAdv10T

/-!
# Adversary certificate for the one-level game, `m = 10` (checks, part 5)

Paper: Appendix D.3, the table of `V(m)`:
the lower bound `V(10) ≥ 7`.

Kernel checks (`decide +kernel` with the verified checker `chkSLem`), part 5: the lemmas
44800 to 53759 of the certificate `s10.txt`, 128 lemmas per theorem.  See `NumAdv10.lean`.
-/

public section

namespace OnlineColouring

namespace Num

theorem adv10_c350 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 44800 128 = true := by
  decide +kernel

theorem adv10_c351 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 44928 128 = true := by
  decide +kernel

theorem adv10_c352 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 45056 128 = true := by
  decide +kernel

theorem adv10_c353 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 45184 128 = true := by
  decide +kernel

theorem adv10_c354 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 45312 128 = true := by
  decide +kernel

theorem adv10_c355 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 45440 128 = true := by
  decide +kernel

theorem adv10_c356 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 45568 128 = true := by
  decide +kernel

theorem adv10_c357 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 45696 128 = true := by
  decide +kernel

theorem adv10_c358 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 45824 128 = true := by
  decide +kernel

theorem adv10_c359 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 45952 128 = true := by
  decide +kernel

theorem adv10_c360 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 46080 128 = true := by
  decide +kernel

theorem adv10_c361 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 46208 128 = true := by
  decide +kernel

theorem adv10_c362 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 46336 128 = true := by
  decide +kernel

theorem adv10_c363 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 46464 128 = true := by
  decide +kernel

theorem adv10_c364 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 46592 128 = true := by
  decide +kernel

theorem adv10_c365 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 46720 128 = true := by
  decide +kernel

theorem adv10_c366 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 46848 128 = true := by
  decide +kernel

theorem adv10_c367 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 46976 128 = true := by
  decide +kernel

theorem adv10_c368 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 47104 128 = true := by
  decide +kernel

theorem adv10_c369 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 47232 128 = true := by
  decide +kernel

theorem adv10_c370 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 47360 128 = true := by
  decide +kernel

theorem adv10_c371 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 47488 128 = true := by
  decide +kernel

theorem adv10_c372 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 47616 128 = true := by
  decide +kernel

theorem adv10_c373 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 47744 128 = true := by
  decide +kernel

theorem adv10_c374 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 47872 128 = true := by
  decide +kernel

theorem adv10_c375 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 48000 128 = true := by
  decide +kernel

theorem adv10_c376 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 48128 128 = true := by
  decide +kernel

theorem adv10_c377 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 48256 128 = true := by
  decide +kernel

theorem adv10_c378 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 48384 128 = true := by
  decide +kernel

theorem adv10_c379 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 48512 128 = true := by
  decide +kernel

theorem adv10_c380 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 48640 128 = true := by
  decide +kernel

theorem adv10_c381 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 48768 128 = true := by
  decide +kernel

theorem adv10_c382 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 48896 128 = true := by
  decide +kernel

theorem adv10_c383 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 49024 128 = true := by
  decide +kernel

theorem adv10_c384 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 49152 128 = true := by
  decide +kernel

theorem adv10_c385 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 49280 128 = true := by
  decide +kernel

theorem adv10_c386 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 49408 128 = true := by
  decide +kernel

theorem adv10_c387 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 49536 128 = true := by
  decide +kernel

theorem adv10_c388 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 49664 128 = true := by
  decide +kernel

theorem adv10_c389 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 49792 128 = true := by
  decide +kernel

theorem adv10_c390 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 49920 128 = true := by
  decide +kernel

theorem adv10_c391 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 50048 128 = true := by
  decide +kernel

theorem adv10_c392 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 50176 128 = true := by
  decide +kernel

theorem adv10_c393 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 50304 128 = true := by
  decide +kernel

theorem adv10_c394 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 50432 128 = true := by
  decide +kernel

theorem adv10_c395 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 50560 128 = true := by
  decide +kernel

theorem adv10_c396 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 50688 128 = true := by
  decide +kernel

theorem adv10_c397 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 50816 128 = true := by
  decide +kernel

theorem adv10_c398 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 50944 128 = true := by
  decide +kernel

theorem adv10_c399 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 51072 128 = true := by
  decide +kernel

theorem adv10_c400 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 51200 128 = true := by
  decide +kernel

theorem adv10_c401 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 51328 128 = true := by
  decide +kernel

theorem adv10_c402 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 51456 128 = true := by
  decide +kernel

theorem adv10_c403 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 51584 128 = true := by
  decide +kernel

theorem adv10_c404 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 51712 128 = true := by
  decide +kernel

theorem adv10_c405 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 51840 128 = true := by
  decide +kernel

theorem adv10_c406 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 51968 128 = true := by
  decide +kernel

theorem adv10_c407 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 52096 128 = true := by
  decide +kernel

theorem adv10_c408 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 52224 128 = true := by
  decide +kernel

theorem adv10_c409 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 52352 128 = true := by
  decide +kernel

theorem adv10_c410 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 52480 128 = true := by
  decide +kernel

theorem adv10_c411 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 52608 128 = true := by
  decide +kernel

theorem adv10_c412 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 52736 128 = true := by
  decide +kernel

theorem adv10_c413 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 52864 128 = true := by
  decide +kernel

theorem adv10_c414 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 52992 128 = true := by
  decide +kernel

theorem adv10_c415 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 53120 128 = true := by
  decide +kernel

theorem adv10_c416 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 53248 128 = true := by
  decide +kernel

theorem adv10_c417 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 53376 128 = true := by
  decide +kernel

theorem adv10_c418 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 53504 128 = true := by
  decide +kernel

theorem adv10_c419 :
    chkSRange 6 [9, 8, 7, 6, 5, 4, 3, 2, 1, 1] adv10 53632 128 = true := by
  decide +kernel

end Num

end OnlineColouring
