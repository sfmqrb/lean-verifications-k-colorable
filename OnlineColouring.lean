module

-- Posets, labellings, blow-ups, towers (Definitions 4.5-4.7) and the calculus of labels (Section 5)
public import OnlineColouring.Labels
public import OnlineColouring.BlowUp
public import OnlineColouring.Cliques
public import OnlineColouring.Towers
public import OnlineColouring.Growth
public import OnlineColouring.BaseFacts
public import OnlineColouring.TowerGrowth
public import OnlineColouring.Existence
-- The online model (Section 4): inputs, algorithms, chi^det, chi^rand, Yao's principle; forcing
-- with a given probability, counting lemmas for uniform distributions (used for Lemma 8.4 and in
-- Appendix C), First-Fit with Lemma 9.5, and Lemma B.3 for First-Fit
public import OnlineColouring.Online
public import OnlineColouring.Play
public import OnlineColouring.RandModel
public import OnlineColouring.DetYao
public import OnlineColouring.ProbForcing
public import OnlineColouring.OblCount
public import OnlineColouring.FirstFit
public import OnlineColouring.TwoPerColour
-- Reservation blow-ups against a fixed algorithm (Section 6), Remark 6.5
public import OnlineColouring.Counting
public import OnlineColouring.Reservation
public import OnlineColouring.SeqBlowUp
public import OnlineColouring.Structure
public import OnlineColouring.Forcing
public import OnlineColouring.PlayBound
public import OnlineColouring.OddGirth
-- Adversaries (Definition 4.2), determinacy (Observation 4.3), Proposition 9.4, and Theorem 6.4
-- as a consequence of determinacy
public import OnlineColouring.LabellingCap
public import OnlineColouring.AdvBasic
public import OnlineColouring.Det
public import OnlineColouring.DetBlow
-- The adversaries of Section 6: Construction 6.1, Lemmas 6.2 and 6.3, Theorem 6.4, Remark 6.5;
-- Theorem 1.2, from the adversary of Theorem 6.4 and Observation 4.3
public import OnlineColouring.Blow
public import OnlineColouring.BlowStack
public import OnlineColouring.BlowTower
public import OnlineColouring.MainTheorem
-- Known graphs (Section 7): Lemmas 7.1 and 7.2, Theorem 1.3 for G, the known-graph game
public import OnlineColouring.Iso
public import OnlineColouring.KnownGraphs
public import OnlineColouring.PadGraph
public import OnlineColouring.KnownGame
public import OnlineColouring.StrBlow
public import OnlineColouring.StrTower
public import OnlineColouring.StrKnown
-- Uniform towers (Section 8, Appendix A): R_j(m), Lemmas 8.2-8.4, Theorem 8.5, Corollary 8.6,
-- Lemma A.1, Theorem 1.1 and Theorem 1.3 for G'
public import OnlineColouring.TowerIndex
public import OnlineColouring.UTowerE
public import OnlineColouring.Phases
public import OnlineColouring.UWiringE
public import OnlineColouring.RjmGraph
public import OnlineColouring.MassArith
public import OnlineColouring.UniformBound
public import OnlineColouring.UExact
public import OnlineColouring.RjmMass
public import OnlineColouring.ExplUniform
public import OnlineColouring.DetTower
public import OnlineColouring.ExplAdv
public import OnlineColouring.ExplKnown
public import OnlineColouring.UniformArith
public import OnlineColouring.UniformThresholds
public import OnlineColouring.LogStarGeneric
public import OnlineColouring.MainLogStar
-- Transfer between values of k and slowly growing chromatic number (Section 9): Theorem 1.4,
-- Construction 9.1, Lemma 9.2, Theorem 9.3; the asymptotic form of Theorem 1.2 (in Asymptotic)
public import OnlineColouring.Transfer
public import OnlineColouring.Asymptotic
public import OnlineColouring.BlowPairing
public import OnlineColouring.BlowSlow
-- The ceiling for towers (Section 9): Theorem 1.5 (Lemma 9.5 is in FirstFit, above)
public import OnlineColouring.Ceiling
public import OnlineColouring.CeilingAsymptotic
public import OnlineColouring.CeilingPadded
-- Statements in the paper's literal form, and properness on the histories that occur
public import OnlineColouring.PaperRand
public import OnlineColouring.PaperMeasure
public import OnlineColouring.PaperStatements
public import OnlineColouring.PaperFirstFit
public import OnlineColouring.ExplProper
-- The value of towers (Corollary 9.6)
public import OnlineColouring.DetValue
public import OnlineColouring.ExplCor
-- Appendix B: Proposition B.1, Lemma B.3 and Proposition B.4 (kernel-checked certificates)
public import OnlineColouring.StrRefBlocks
public import OnlineColouring.StrRefBlow
public import OnlineColouring.StrRefTower
public import OnlineColouring.CertGame
public import OnlineColouring.CertCheck
public import OnlineColouring.CertLower
public import OnlineColouring.CertK3
public import OnlineColouring.CertK3C9
public import OnlineColouring.CertK4
public import OnlineColouring.CertK4C10
public import OnlineColouring.CertK5
public import OnlineColouring.CertK5C11
public import OnlineColouring.CertK5C12
public import OnlineColouring.CertK6
public import OnlineColouring.CertK6C13
public import OnlineColouring.CertNk
-- Appendix C: oblivious blow-ups (Construction C.1, Lemma C.2, Theorem C.3, Corollary C.4)
public import OnlineColouring.Oblivious
public import OnlineColouring.OblProb
public import OnlineColouring.OblTower
public import OnlineColouring.OblCor
-- Appendix D: Proposition D.1, Theorems D.2, D.4 and D.5, Lemma D.3; Corollary B.2, which uses
-- the adversary of Theorem D.2; transfer for randomized algorithms (Appendix D.5)
public import OnlineColouring.ReservationFree
public import OnlineColouring.AppBDMatching
public import OnlineColouring.AppBDFlow
public import OnlineColouring.AppBDOneLevel
public import OnlineColouring.AppBDCheapTop
public import OnlineColouring.AppBDCheapTopAdv
public import OnlineColouring.AppBDTopBlock
public import OnlineColouring.AppBDLST
public import OnlineColouring.AppBDPJArith
public import OnlineColouring.AppBDPJ
public import OnlineColouring.AppBDPJAsymp
public import OnlineColouring.AppBDWitness
public import OnlineColouring.ExplTransfer
public import OnlineColouring.ExplTransferSize
public import OnlineColouring.ExplTransferPoly
-- Numbers computed in the paper: tables, explicit instances, Section 8.4, the recursion of D.6
public import OnlineColouring.CertNumbers
public import OnlineColouring.CertOvertake
public import OnlineColouring.CertLink
-- Computed values with kernel-checked certificates: sizes and widths of the label posets
-- (Section 5), the antichain of P_4(3) (Appendix A), and the one-level values V(m), m = 4..11
-- (Appendix D.3, Question 10.3)
public import OnlineColouring.NumValues
public import OnlineColouring.NumV10

/-!
# OnlineColouring

The root of the library: a formalization of the paper "An n^{1/O(log* n)} Lower Bound for Online
Coloring of k-Colorable Graphs".  It imports all modules, ordered by layer (the modules `Num*`
through `NumValues` and `NumV10`); the comments above name the part of the paper that each group
covers.  `docs/library.md` describes the library and its conventions, and `PAPER_MAP.md` gives
the declarations for the statements of the paper and lists what is not formalized.
-/
