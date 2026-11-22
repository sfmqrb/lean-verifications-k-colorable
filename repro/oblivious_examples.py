#!/usr/bin/env python3
from fractions import Fraction
from decimal import Decimal, getcontext, ROUND_CEILING

getcontext().prec = 60


def ceil_div(a, b):
    return -(-a // b)


def top_level(K, R):
    c = ceil_div(R, K - 1)
    return sum(d * (1 - Fraction(1, d)) ** c for d in range(1, K))


def lower_level_upper(count, delta, R, K):
    c = ceil_div(R, K - 1)
    getcontext().rounding = ROUND_CEILING
    base = Decimal(delta - 1) / Decimal(delta)
    val = Decimal(count) * Decimal(delta) * (base ** c)
    return val


def check():
    K, R = 7, 150
    n1 = K * R
    d1 = top_level(K, R)
    p1 = 1 - d1
    print("instance 1: K=7, one level, block 150: vertices %d, failure <= %.6f, success >= %.6f"
          % (n1, float(d1), float(p1)))
    assert n1 == 1050
    assert p1 >= Fraction(915, 1000)

    K, R1, R0 = 8, 245, 27293
    n2 = K * R1 * R0
    top = top_level(K, R1)
    low = lower_level_upper(count=(K - 1) * R1, delta=R1, R=R0, K=K)
    delta = Decimal(top.numerator) / Decimal(top.denominator) + low
    getcontext().rounding = ROUND_CEILING
    expected = Decimal(K) - Decimal(K - 1) * delta
    print("instance 2: K=8, two levels, blocks 245 and 27293: vertices %d, failure <= %.6f (top %.6f + lower %.6f),"
          " success >= %.6f, expected colours >= %.4f" % (n2, delta, float(top), low, 1 - delta, expected))
    assert n2 == 53_494_280
    assert delta <= Decimal("0.094")
    assert Decimal(K) - Decimal(K - 1) * Decimal("0.094") > Decimal("7.25")

    print("colourability: K=7 <= |P_1(3)| = 7 and K=8 <= |P_2(3)| = 18 (Corollary 5.4)")
    print("oblivious_examples OK")


if __name__ == "__main__":
    check()
