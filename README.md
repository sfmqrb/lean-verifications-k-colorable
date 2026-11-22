# OnlineColouring

`OnlineColouring` is a Lean 4 library, built on Mathlib, that formalizes the paper "An n^{1/O(log* n)} Lower Bound
for Online Coloring of k-Colorable Graphs". It contains the definitions of the paper and proves every numbered
observation, lemma, theorem, corollary, proposition and remark, from the online model of Section 4 to the five
theorems of the introduction and the computer-assisted exact values of Appendix B. Every proof is complete and
checked by the Lean kernel: the library uses no `sorry` and no `native_decide`, and its theorems depend on no axioms
other than `propext`, `Classical.choice` and `Quot.sound`.

| Path | Content |
|---|---|
| `PAPER_MAP.md` | For every statement of the paper, the Lean declaration that states it, the deviations, and what is not formalized. |
| `docs/library.md` | The definitions to compare with the paper (the trust base), the layout of the modules, and the conventions. |
| `OnlineColouring/*.lean`, `OnlineColouring.lean` | The 153 modules of the library, and the root that imports them. |
| `AxiomCheck.lean` | Prints the axioms behind every declaration named in `PAPER_MAP.md`. |
| `docs/cert_converter.md`, `docs/num_generators.md` | How the generated modules were produced, with the programs. |
| `repro/` | The supplementary material: the programs and certificates behind the computer-assisted values of the paper. |

## Building and checking

The library uses Lean `v4.36.0` and Mathlib `v4.36.0`; elan installs the toolchain. Run the commands from the root
of this repository.

```
# 1. Once per checkout: download the compiled Mathlib (about 7 GB, into .lake/).
lake exe cache get

# 2. The generated certificate modules, one at a time (about 70 minutes).
for m in CertK3 CertK4 CertK5 CertK6 CertK4C10 CertK5C11 CertK6C13 CertK5C12 CertK3C9 \
         NumP4 NumP3 NumAlgSmall NumAlg11 NumAdvSmall NumAdv8 NumAdv9 \
         NumAdv10D0 NumAdv10D1 NumAdv10D2 NumAdv10D3 NumAdv10D4 NumAdv10D5 NumAdv10D6 NumAdv10D7 NumAdv10D8 \
         NumAdv10D9 NumAdv10D10 NumAdv10D11 NumAdv10D12 NumAdv10D13 NumAdv10T \
         NumAdv10C0 NumAdv10C1 NumAdv10C2 NumAdv10C3 NumAdv10C4 NumAdv10C5 NumAdv10C6 NumAdv10C7 NumAdv10C8 \
         NumAdv10C9 NumAdv10C10 NumAdv10C11 NumAdv10; do
  lake build OnlineColouring.$m || break
done

# 3. The whole library.
lake build

# 4. The axioms of every declaration named in PAPER_MAP.md.
lake env lean AxiomCheck.lean
```

Step 2 comes first because the kernel needs between 0.8 and 4 GB of memory to check each generated module, and a
plain `lake build` would start many of them at the same time. Step 3 ends with a line that begins with
`Build completed successfully` and prints no warning. Every line of step 4 must read
`… depends on axioms: [propext, Classical.choice, Quot.sound]`, with this list or a part of it, or
`… does not depend on any axioms`. `docs/library.md` has the details and the times.
