from common import label_poset, width, nonempty_downsets, tow
import math

sizes = {(2, j): len(label_poset(2, j)) for j in range(6)}
sizes.update({(3, j): len(label_poset(3, j)) for j in range(5)})
sizes.update({(4, j): len(label_poset(4, j)) for j in range(3)})
for key in sorted(sizes):
    print("|P_%d(%d)| = %d" % (key[1], key[0], sizes[key]))
assert [sizes[(2, j)] for j in range(6)] == [j + 2 for j in range(6)]
assert [sizes[(3, j)] for j in range(5)] == [3, 7, 18, 81, 8569]
assert [sizes[(4, j)] for j in range(3)] == [4, 15, 166]

assert sizes[(3, 2)] == 20 - 2 and sizes[(4, 2)] == 168 - 2

w = [width(list(label_poset(3, j)), j) for j in range(4)]
print("width(P_j(3)), j=0..3:", w)
assert w[0] == 3 and w[1] == 3 and w[2] == 4 and w[3] == 7

P1 = label_poset(3, 1)
def down(*sets):
    gens = [frozenset(s) for s in sets]
    return frozenset(x for x in P1 if any(x <= g for g in gens))
A = [down({0, 1}), down({0, 2}), down({1, 2}), frozenset(frozenset({i}) for i in range(3))]
assert all(a in set(label_poset(3, 2)) for a in A)
assert all(not (A[i] <= A[t]) for i in range(4) for t in range(4) if i != t)
print("Poljak's antichain {down(12), down(13), down(23), {1},{2},{3}} found in P_2(3)")

T = [4]
for i in range(3):
    T.append(math.comb(T[-1], T[-1] // 2))
print("T_0..T_3 =", T)
assert T == [4, 6, 20, 184756]
assert all(T[i] >= tow(i + 1) for i in range(4)) and T[3] >= 2 * tow(4)
x = tow(4)
assert 2 ** 16 == x and all(2 ** y >= 4 * y + 2 for y in range(5, 200))
print("tower bound T_i >= tow(i+1) checked for i <= 3; induction step 2^x >= 4x+2 holds for x >= 5")
layers = {}
for d in label_poset(3, 4):
    layers[len(d)] = layers.get(len(d), 0) + 1
assert layers[39] == 235 and max(layers.values()) == 235
print("largest layer of P_4(3): 235 down-sets of P_3(3) with exactly 39 elements, so |P_5(3)| >= 2^235 - 1")
print("check_posets: OK")
