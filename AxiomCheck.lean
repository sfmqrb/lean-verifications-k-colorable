import OnlineColouring

/-! Axiom check for the declarations that `PAPER_MAP.md` names, grouped by paper section.

Run from the root of the repository with
`lake env lean AxiomCheck.lean`.
Every line of the output must read `… depends on axioms: [propext, Classical.choice, Quot.sound]`
(or a sublist of these three), or `… does not depend on any axioms`.

The declarations are those that `PAPER_MAP.md` names, alone or applied to arguments (in the
columns "Lean declaration(s)" and "Notes" and in the text of its last two sections), in the order
of that file, except that the computed values of the modules `Num*` are grouped near the end; a
declaration that occurs in several rows is printed once, as a rule at its first occurrence.  When
`PAPER_MAP.md` changes, change this file with it. -/

open OnlineColouring

-- ======================================================================
-- Section 1: Introduction (the main theorems)
-- ======================================================================

-- Theorem 1.1 (main theorem)
#print axioms main_logStar_three
#print axioms main_logStar_of_four_le
#print axioms Rjm.chiRand_three_ge_uniform
#print axioms Rjm.chiRand_ge_uniform_of_four_le
#print axioms Rjm.chiRand_three_ge_rpow
#print axioms Rjm.chiRand_ge_rpow_of_four_le
#print axioms chiDet_three_ge_uniform
#print axioms chiDet_ge_uniform_of_four_le
#print axioms chiDet_three_ge_rpow
#print axioms chiDet_ge_rpow_of_four_le
#print axioms chiRand_le_chiDet

-- Theorem 1.2 (explicit deterministic bound)
#print axioms floor_rpow_le_chiDet_three
#print axioms floor_rpow_le_chiDet_of_four_le
#print axioms exists_chiDet_ge_rpow_two_sub
#print axioms Paper.floor_rpow_28_le_chiDet_three
#print axioms Paper.floor_rpow_15_le_chiDet_of_four_le
#print axioms chiDet_ge_asymptotic
#print axioms chiDet_three_ge
#print axioms chiDet_ge_of_four_le
#print axioms chiDetAtLeast_three_of_le_tow_five
#print axioms chiDetAtLeast_of_four_le_of_le_tow_five
#print axioms Cert.exponents_L5
#print axioms chiDetAtLeast_of_adversary

-- Theorem 1.3 (known graphs)
#print axioms Paper.known_graphs_three
#print axioms Paper.known_graphs_of_four_le
#print axioms Paper.chiOl
#print axioms known_graph_three_floor
#print axioms known_graph_of_four_le_floor
#print axioms known_graph_uniform_three
#print axioms known_graph_uniform_of_four_le
#print axioms known_graph_uniform_three_large
#print axioms known_graph_uniform_of_four_le_large
#print axioms RandKnownAtLeast
#print axioms knownGraph
#print axioms Rjm.Gjm

-- Table 1 (caption)
#print axioms chiDet_mono_left

-- Theorem 1.4 (transfer between values of `k`)
#print axioms Paper.transfer_chiDet
#print axioms transfer_poly_real
#print axioms Paper.transfer_Nk
#print axioms transfer
#print axioms transfer_least
#print axioms chiDet_transfer
#print axioms transfer_poly_real_of_three_le
#print axioms transfer_isBigO

-- Theorem 1.5 (a ceiling for towers)
#print axioms IsPaddedTower.ceiling_of_two_le
#print axioms exists_threshold_le_rpow
#print axioms Paper.ceiling_online
#print axioms Paper.exists_threshold_online
#print axioms IsPaddedTower.ceiling
#print axioms exists_threshold_firstFit_pow_le
#print axioms IsPaddedTower.firstFit_pow_le
#print axioms IsFullTowerAnc.ceiling
#print axioms IsFullTower.ceiling
#print axioms IsFullTowerAnc.firstFit_pow_le

-- ======================================================================
-- Section 4: Preliminaries
-- ======================================================================

-- Online colouring (first paragraph)
#print axioms OnlineInput
#print axioms OnlineAlg
#print axioms OnlineAlg.IsProper
#print axioms OnlineInput.run
#print axioms OnlineInput.cost
#print axioms OnlineInput.graph
#print axioms postDeg
#print axioms History
#print axioms OnlineInput.equivGraph
#print axioms ChiDetAtLeast.of_isProperOn
#print axioms Expl.chiDetAtLeast_iff_properOn

-- Definition 4.1 (online chromatic numbers), `χ^det`
#print axioms chiDet
#print axioms le_chiDet_iff
#print axioms exists_maxCost_eq_chiDet
#print axioms maxCost

-- Definition 4.1, `χ^rand`
#print axioms chiRand
#print axioms le_chiRand_iff
#print axioms Paper.chiRand_isLeast
#print axioms IsProperRand
#print axioms expCost
#print axioms Paper.exists_finite_support_minimizer
#print axioms Paper.chiRand_isLeast_finite
#print axioms Paper.exists_finite_support_of_measure
#print axioms Paper.chiRand_le_of_measure
#print axioms ChiRandAtLeast

-- Remarks after Definition 4.1
#print axioms chiDet_mono_right
#print axioms Paper.chiRand_mono
#print axioms Paper.exists_finite_support_expCost_eq
#print axioms ChiDetAtLeast.mono
#print axioms ChiRandAtLeast.mono
#print axioms padInput

-- Definition 4.2 (adversaries)
#print axioms Adversary
#print axioms Adversary.hist
#print axioms Adversary.Forces
#print axioms Adversary.SizeLE
#print axioms Adversary.PostDegLE
#print axioms Adversary.LandsIn
#print axioms Adversary.move
#print axioms History.graph
#print axioms Expl.forces_iff_properAgainst
#print axioms Expl.sizeLE_iff_properAgainst
#print axioms Expl.postDegLE_iff_properAgainst
#print axioms Expl.landsIn_iff_properAgainst
#print axioms Adversary.StopsAt
#print axioms History.postDeg

-- `N_k(K)` (after Definition 4.2)
#print axioms Nk
#print axioms NkLE
#print axioms Nk_le_iff

-- Observation 4.3 (determinacy)
#print axioms Det.le_chiDet_iff_Nk_le
#print axioms Det.Nk_le_of_forall_alg
#print axioms Det.le_chiDet_of_forall_alg
#print axioms Det.exists_presents
#print axioms Det.chiDetAtLeast_iff_NkLE
#print axioms Det.NkLE_of_chiDetAtLeast
#print axioms Det.chiDetAtLeast_of_NkLE

-- Lemma 4.4 (Yao's principle)
#print axioms Det.yao_expectation_chiRand
#print axioms Det.yao_chiRand
#print axioms yao_expectation
#print axioms yao
#print axioms Paper.yao_chiRand
#print axioms Paper.yao_prob_chiRand
#print axioms detExpCost

-- Remark after Lemma 4.4
#print axioms Paper.yao_known

-- First-Fit
#print axioms OnlineAlg.firstFit
#print axioms firstFit
#print axioms Paper.run_firstFit_eq
#print axioms firstFit_le_ncard
#print axioms Paper.cost_firstFit_eq

-- Posets and labels
#print axioms Jst
#print axioms IsLowerFinset
#print axioms width
#print axioms labelPoset
#print axioms LabelPoset
#print axioms Jst.lowerSetEmbedding
#print axioms Jst.exists_lowerSet_eq
#print axioms le_width_iff
#print axioms Anti

-- Definition 4.5 (templates and labellings)
#print axioms IsLabelling
#print axioms HasLabelling
#print axioms HasLabelling.induce
#print axioms hasLabelling_anti_fin_iff_colorable

-- Towers of exponentials (paragraph "Towers")
#print axioms tow
#print axioms logStar
#print axioms logStar_examples
#print axioms logStar_le_iff
#print axioms tow_five

-- Definition 4.6 (blow-up)
#print axioms BlowUp
#print axioms BlowUp.IsFull
#print axioms BlowUp.IsReservation
#print axioms BlowUp.π
#print axioms BlowUp.lt_of_π_lt
#print axioms BlowUp.serve_spec
#print axioms BlowUp.adj_iff
#print axioms BlowUp.not_adj_of_π_eq
#print axioms canonBlowUp
#print axioms canonBlowUp_isReservation

-- Definition 4.7 (towers)
#print axioms IsFullTower
#print axioms IsPaddedTower
#print axioms IsTower
#print axioms IsFullTowerAnc
#print axioms Paper.ordConnected_subtree
#print axioms Paper.ordConnected_block
#print axioms Paper.lt_of_comp_lt
#print axioms IsFullTowerAnc.lt_of_lt

-- ======================================================================
-- Section 5: The calculus of labels
-- ======================================================================

-- Lemma 5.1 (cliques and antichains)
#print axioms hasLabelling_clique_iff
#print axioms hasLabelling_of_colorable

-- Lemma 5.2 (labels descend through blow-ups)
#print axioms BlowUp.hasLabelling_of_jst

-- Lemma 5.3 (labels ascend through full blow-ups)
#print axioms BlowUp.hasLabelling_jst_of_full
#print axioms Paper.exists_isLabelling_down

-- Corollary 5.4 (colourability of iterated blow-ups)
#print axioms IsTower.colorable
#print axioms IsTower.colorable_induce
#print axioms IsFullTower.le_card
#print axioms IsFullTower.colorable_iff
#print axioms exists_isFullTower
#print axioms exists_fullTower_colorable_iff

-- Lemma 5.5 (growth)
#print axioms downEmbedding
#print axioms HasAntichain.two_pow_sub_one_le_card_jst
#print axioms Paper.le_width_jst
#print axioms card_jst_le
#print axioms principalEmbedding
#print axioms BaseFacts.isAntichain_A
#print axioms Paper.four_le_width_labelPoset_three_two
#print axioms HasAntichain
#print axioms HasAntichain.jst
#print axioms hasAntichain_labelPoset_three_two

-- The recursion `T_i` (after Lemma 5.5)
#print axioms T
#print axioms T_values
#print axioms tow_succ_le_T

-- Lemma 5.6 (tower growth)
#print axioms Paper.tow_le_width_labelPoset_of_four_le
#print axioms Paper.tow_le_width_labelPoset_three
#print axioms card_labelPoset_le_tow
#print axioms hasAntichain_labelPoset_of_four_le
#print axioms hasAntichain_labelPoset_three

-- Corollary 5.7 (number of levels)
#print axioms le_card_labelPoset_of_four_le
#print axioms le_card_labelPoset_three
#print axioms logStar_sub_logStar_le

-- First values of `card P_j(k)` (after Corollary 5.7, and in Section 1)
#print axioms card_labelPoset_zero
#print axioms card_labelPoset_one
#print axioms card_labelPoset_three_one

-- ======================================================================
-- Section 6: Reservation blow-ups (proof of Theorem 1.2)
-- ======================================================================

-- Construction 6.1 (reservation blow-up `B(𝒜)`)
#print axioms Blow.B
#print axioms Blow.R
#print axioms Blow.indColour
#print axioms Blow.innerHist
#print axioms Blow.clean
#print axioms resAdv
#print axioms outSeq

-- Lemma 6.2 (forcing survives a blow-up)
#print axioms Blow.lemma_6_2
#print axioms Blow.induced_isProper
#print axioms Blow.induced
#print axioms forcing_step
#print axioms exists_large_colour_class

-- Remark after Lemma 6.2
#print axioms blowUpOf
#print axioms blowUpOf_isReservation
#print axioms Blow.Good.blow
#print axioms Blow.Good
#print axioms blowSeq

-- Lemma 6.3 (stacking)
#print axioms Blow.lemma_6_3
#print axioms Blow.StackOK
#print axioms Blow.server_colour
#print axioms Blow.stack_lemma
#print axioms Blow.stack
#print axioms Blow.deg
#print axioms Blow.deg_succ_eq
#print axioms Blow.remark_6_3
#print axioms forcing_structure
#print axioms ForcesWith.iterate

-- Theorem 6.4 (the iterated reservation adversary)
#print axioms Blow.theorem_6_4
#print axioms Blow.tower_stackOK
#print axioms Adversary.clique
#print axioms Blow.tower_play
#print axioms Blow.tower_spec
#print axioms Blow.tower_presents
#print axioms Blow.hasLabelling_runHist
#print axioms Blow.tower_colorable
#print axioms Blow.tower_first_last
#print axioms Blow.tower_sizeLE
#print axioms Blow.NkLE_playSize
#print axioms blockSize
#print axioms playSize
#print axioms playSize_le
#print axioms blockSize_top
#print axioms blockSize_pred
#print axioms iterated_reservation_adversary
#print axioms iterated_reservation_adversary_play
#print axioms chiDetAtLeast_of_card_labelPoset
#print axioms Det.iterated_reservation_adversary_exists

-- Table 2 (size bounds of the adversary of Theorem 6.4)
#print axioms blockSize_table
#print axioms playSize_table
#print axioms Cert.playSize_81_3_approx
#print axioms Cert.playSize_166_2_approx
#print axioms Cert.logRatio_table
#print axioms Cert.playSize_more

-- Text after the proof of Theorem 1.2
#print axioms Det.forces_le_seven_of_one_level
#print axioms Det.forces_le_card_labelPoset

-- Remark 6.5 (the hard instances)
#print axioms BlowUp.cliqueFree_three
#print axioms IsTower.isBipartite_or_oddGirth
#print axioms Blow.tower_firstFit_le
#print axioms Blow.tower_firstFit_eq
#print axioms IsTower.le_length_of_odd
#print axioms IsTower.le_length_of_isCycle
#print axioms BlowUp.exists_closed_walk
#print axioms Blow.tower
#print axioms Blow.tower_cliqueFree_three
#print axioms Blow.tower_isBipartite_or_oddGirth
#print axioms Blow.tower_card_usedColours_eq

-- ======================================================================
-- Section 7: Known graphs (proof of Theorem 1.3 for `G`)
-- ======================================================================

-- The known-graph game and `χ_ol`
#print axioms OnlineChromaticAtLeast
#print axioms Paper.le_chiOl_iff
#print axioms OnlineChromaticAtLeast.mono
#print axioms OnlineChromaticAtLeast.of_iso
#print axioms OnlineChromaticAtLeast.pad

-- The adversary `𝒜^str` ("Completing every block")
#print axioms Str.strTower
#print axioms Str.strTower_move_eq
#print axioms Str.strTower_forces
#print axioms Str.strTower_stopsAt_iff
#print axioms Str.Bstr
#print axioms Str.strPopular
#print axioms Str.strResOrder
#print axioms Str.strTower_final_length
#print axioms Str.strTower_move_eq_none_iff
#print axioms Str.strTower_move_valid
#print axioms Str.strTower_inner_all
#print axioms Str.strInduced_not_isProper

-- Server assignments and `Bl_ρ(H)`
#print axioms BlockPerm

-- Lemma 7.1 (the server assignment does not matter)
#print axioms Paper.blowSeq_iso_blocks
#print axioms SeqIso.blowSeq
#print axioms SeqIso

-- The digraph `H_j(K)`
#print axioms Str.HjK
#print axioms canonSeq
#print axioms Str.IsBlTower.seqIso
#print axioms Str.HjK_zero
#print axioms Str.HjK_succ
#print axioms Str.IsBlTower
#print axioms towerSize

-- Lemma 7.2 (one final graph)
#print axioms Str.lemma_7_2
#print axioms Str.lemma_7_2_seq
#print axioms Str.lemma_7_2_graph
#print axioms Str.lemma_7_2_landsIn
#print axioms forcing_structure_iso

-- Proof of Theorem 1.3 for `G`
#print axioms Str.known_graph_adversary
#print axioms known_graph
#print axioms Str.strPad_final_graph
#print axioms Str.strPad_legal
#print axioms Str.strPad_forces
#print axioms Str.strPad
#print axioms knownGraph_colorable
#print axioms known_graph_three
#print axioms known_graph_of_four_le
#print axioms knownGraph_cliqueFree
#print axioms known_graph_of_inputs

-- ======================================================================
-- Section 8: Uniform towers (proof of Theorem 1.1)
-- ======================================================================

-- Uniform towers and servers (Section 8.1)
#print axioms ueNb
#print axioms ueSeq
#print axioms ueInput
#print axioms utSize
#print axioms phase
#print axioms Det.ueInput_isFullTower
#print axioms Rjm.ueInput_isResTower
#print axioms ueInput_isTower

-- Construction 8.1 (random wiring `R_j(m)`)
#print axioms EΩ
#print axioms EZ
#print axioms uInputE
#print axioms uSeqE
#print axioms topCE
#print axioms permOf
#print axioms pickR
#print axioms exists_pickR_eq
#print axioms pickR_injective
#print axioms unifPMF
#print axioms uSeqE_congr
#print axioms uColE_congr

-- Lemma 8.2 (one graph)
#print axioms Rjm.uniform_graph
#print axioms Rjm.IsResTower
#print axioms Rjm.gSeq
#print axioms Rjm.Gjm_colorable
#print axioms Rjm.Gjm_cliqueFree
#print axioms Rjm.uInputE_isResTower
#print axioms Rjm.uInputE_cliqueFree
#print axioms uInputE_colorable
#print axioms Rjm.uSeqE_seqIso_gSeq
#print axioms Rjm.uInputE_iso_Gjm
#print axioms Det.uInputE_isFullTower

-- Unused mass (Section 8.2, definitions)
#print axioms eligE
#print axioms uME
#print axioms qME
#print axioms fME

-- Lemma 8.3 (bookkeeping)
#print axioms Rjm.mass
#print axioms Rjm.sum_uME_end

-- Lemma 8.4 (colours with large mass are seen)
#print axioms Rjm.miss
#print axioms Rjm.SameHistory
#print axioms Rjm.card_noNbr_update_le
#print axioms card_bad_leE
#print axioms Expl.card_fiber_mul_card_eligE
#print axioms Expl.card_nbrs_mul_prod
#print axioms Expl.card_noNbr_mul_prod

-- Theorem 8.5 (i)
#print axioms avg_numCols_geE
#print axioms uniform_tower_randE
#print axioms uniformBound

-- Theorem 8.5 (ii)
#print axioms Expl.adv_presents
#print axioms Expl.uniform_tower_adversary
#print axioms Expl.advW_apply
#print axioms Expl.advW_le
#print axioms Expl.HME_advW_le
#print axioms Det.Presents
#print axioms Det.uniform_tower_adversary
#print axioms Rjm.exists_numColsE_ge
#print axioms Rjm.uniform_tower_detE

-- Inequality (8.1) and `E[H_t]`
#print axioms perPlay_boundE
#print axioms sum_HME_update_le
#print axioms sum_HME_le
#print axioms HME
#print axioms numColsE
#print axioms mass_le_of_steps
#print axioms mass_le_one_colour

-- Proof of Theorem 1.1: parameters and the chain (8.2)
#print axioms Rjm.jMin
#print axioms Rjm.jMin_three_le
#print axioms Rjm.jMin_le_of_four_le
#print axioms levelM
#print axioms xLower_le_uniformBound
#print axioms rpow_div_le_xLower
#print axioms uniform_rpow_div
#print axioms uniform_step
#print axioms Rjm.logStar_three
#print axioms Rjm.logStar_of_four_le
#print axioms Rjm.logStar_three_large
#print axioms Rjm.logStar_of_four_le_large
#print axioms Paper.chiRand_ge_of_level
#print axioms Paper.chiRand_ge_of_level_large_three
#print axioms Paper.chiRand_ge_of_level_large_of_four_le
#print axioms Paper.main_logStar_three_least
#print axioms Paper.main_logStar_of_four_le_least
#print axioms Paper.exists_least_level_three
#print axioms Paper.exists_least_level_of_four_le

-- Section 8.4, sentence after the proof of Theorem 1.1
#print axioms Cert.overtake_two_pow_50
#print axioms Cert.not_yet_two_pow_49
#print axioms Cert.overtake_two_pow_54
#print axioms Cert.not_yet_two_pow_53
#print axioms Cert.refinedSize
#print axioms Cert.refinedSize_eq_refSize
#print axioms Cert.NkLE_refinedSize

-- Corollary 8.6 (forcing with high probability)
#print axioms uniform_tower_eps_probE
#print axioms probForcing_logStar_three
#print axioms probForcing_logStar_of_four_le
#print axioms uniform_tower_eps_countE
#print axioms uniform_tower_eps_inputE
#print axioms uniform_tower_epsE
#print axioms epsBound
#print axioms ProbForcing
#print axioms rpow_div_le_epsBound
#print axioms Rjm.probForcing_rpow_div

-- Proof of Theorem 1.3 for `G′`
#print axioms Rjm.uniform_known_graph
#print axioms Expl.Gjm_onlineChromaticAtLeast
#print axioms Rjm.Gjm_randKnownAtLeast
#print axioms Expl.onlineChromaticAtLeast_of_forces
#print axioms Rjm.Gjm_onlineChromaticAtLeast
#print axioms padGraph
#print axioms RandKnownAtLeast.pad

-- ======================================================================
-- Section 9: Transfer, slowly growing chromatic number, and limits
-- ======================================================================

-- Proof of Theorem 1.4 ("other adversaries at the top")
#print axioms chiDetAtLeast_of_labelled_top
#print axioms chiDetAtLeast_transfer
#print axioms transferSize
#print axioms transferSize_le_mul
#print axioms transferSize_le_pow
#print axioms ForcesWith
#print axioms ForcesWith.blowUp

-- Examples after the proof of Theorem 1.4
#print axioms transfer_three_four
#print axioms transfer_four_of_le_six
#print axioms ChiDetAtLeast

-- Construction 9.1 (pairing top)
#print axioms Blow.pairing
#print axioms Blow.phi
#print axioms Blow.pairNbrs

-- Lemma 9.2 (the pairing top)
#print axioms Blow.lemma_9_2

-- Theorem 9.3 (polynomial bounds at chromatic number `log log n`)
#print axioms Blow.theorem_9_3
#print axioms Blow.theorem_9_3_chiDet
#print axioms HasAntichain.labelPoset_succ
#print axioms Blow.exists_m_le
#print axioms Blow.slowAdv
#print axioms Blow.theorem_9_3_NkLE
#print axioms Blow.theorem_9_3_loglog

-- Proposition 9.4 (a cap for adversaries that commit to labels)
#print axioms Adversary.le_card_jst
#print axioms Adversary.logStar_sub_le_of_commitsTo
#print axioms Adversary.CommitsTo
#print axioms Adversary.le_two_pow_of_commitsTo_colouring
#print axioms OnlineInput.cost_labelAlg_le
#print axioms le_card_jst_of_labelled_inputs
#print axioms Expl.le_card_jst_of_properAgainst
#print axioms Adversary.clique_forces
#print axioms Adversary.clique_commitsTo

-- Lemma 9.5 (First-Fit commutes with blow-ups)
#print axioms BlowUp.firstFit_eq
#print axioms BlowUp.firstFit_induce_eq
#print axioms IsFullTowerAnc.firstFit_eq
#print axioms IsFullTowerAnc.ncard_range_firstFit_induce
#print axioms firstFit_eq_zero
#print axioms IsFullTower.ncard_range_firstFit
#print axioms IsFullTowerAnc.firstFit_induce_eq

-- Corollary 9.6 (the value of towers)
#print axioms Det.value_of_towers
#print axioms Det.value_of_towers_exponent
#print axioms Det.towerValue
#print axioms Det.IsColTower
#print axioms Det.towerValue_eq_all
#print axioms Expl.adv_forces_rpow
#print axioms Expl.adv_forces_rpow_of_four_le
#print axioms Det.towerForces_le_rpow

-- ======================================================================
-- Appendix A: Thresholds for Theorem 1.1
-- ======================================================================

-- Lemma A.1 (thresholds)
#print axioms threshold_three
#print axioms threshold_four
#print axioms xLower
#print axioms base_six
#print axioms base_four

-- ======================================================================
-- Appendix B: Smaller explicit instances and exact small cases
-- ======================================================================

-- The sizes `D_ℓ(t)`, `b_ℓ(t)` and the adversary `𝒜′`
#print axioms Str.Dl
#print axioms Str.bl
#print axioms Str.Dl_top
#print axioms Str.bl_eq
#print axioms Str.Dl_pred
#print axioms Str.refTower
#print axioms Str.GB
#print axioms Str.GB_const
#print axioms Str.refD_eq_zero_iff
#print axioms Str.refD_succ_of_lt

-- Proposition B.1 (smaller blocks)
#print axioms Str.proposition_B_1
#print axioms Str.refTower_colorable
#print axioms Str.NkLE_refSize
#print axioms Str.chiDetAtLeast_of_refSize
#print axioms Str.refSize_le_playSize
#print axioms Str.refSize

-- Table 3 (size bounds of the two adversaries)
#print axioms Str.refSize_table
#print axioms Str.playSize_table_B
#print axioms Cert.refinedSize_table
#print axioms Str.NkLE_table

-- Corollary B.2 (a cheaper top)
#print axioms AppBD.cheaper_top_composed
#print axioms AppBD.cheapAdv
#print axioms AppBD.flowAdv
#print axioms AppBD.cheapTopSize
#print axioms AppBD.cheapAdv_sizeLE
#print axioms AppBD.cheapTopSize_le
#print axioms AppBD.cheapAdv_colorable
#print axioms AppBD.flowAdv_good
#print axioms AppBD.cheaper_top_adversary
#print axioms AppBD.Nk_le_cheapTop
#print axioms AppBD.cheaper_top

-- Numbers after Corollary B.2
#print axioms Cert.cheapTop_values
#print axioms Cert.cheapTop_le
#print axioms Cert.cheapTop
#print axioms Cert.cheapTop_eq_cheapTopSize
#print axioms Cert.cheapAdv_sizeLE_cheapTop

-- Lemma B.3 (two vertices per colour)
#print axioms Cert.le_Nk
#print axioms Cert.two_mul_sub_le_of_nkLE
#print axioms ChiDetAtLeast.two_mul_sub_le
#print axioms two_mul_chiDet_le
#print axioms OnlineInput.two_mul_cost_firstFit_le

-- Proposition B.4 (exact values)
#print axioms Cert.prop_small
#print axioms Cert.Nk_three
#print axioms Cert.Nk_three_ten
#print axioms Cert.Nk_four
#print axioms Cert.Nk_five
#print axioms Cert.Nk_six
#print axioms Cert.checkLem
#print axioms Cert.nkLE_of_cert
#print axioms Cert.nkLE_3_9
#print axioms Cert.Force
#print axioms Cert.Force.transfer
#print axioms Cert.nkLE_of_force

-- ======================================================================
-- Appendix C: Oblivious blow-ups
-- ======================================================================

-- Construction C.1 (oblivious blow-up `OB_R(ℋ)`)
#print axioms Obl.OB
#print axioms Obl.obInput
#print axioms Obl.Idx
#print axioms Obl.idx
#print axioms Obl.mem_obInput_nbr
#print axioms obSeq

-- Remarks after Construction C.1
#print axioms Obl.obInput_blowUp
#print axioms Obl.postDeg_obInput_le
#print axioms Obl.postDeg_obInput_eq_zero

-- Lemma C.2 (forcing survives an oblivious blow-up)
#print axioms Obl.oblivious_blowup
#print axioms Obl.oblivious_blowup_labelling
#print axioms Obl.oblivious_blowup_forcing
#print axioms probAtLeast
#print axioms simAlg
#print axioms simAlgP
#print axioms runCol_simAlgP
#print axioms comparison

-- Remark after Lemma C.2
#print axioms Obl.cond_c_of_weak

-- Theorem C.3 (iterated oblivious blow-ups)
#print axioms Obl.oblivious_towers
#print axioms Obl.towN
#print axioms Obl.towD

-- Corollary C.4 (high probability)
#print axioms Obl.oblivious_high_prob_three
#print axioms Obl.oblivious_high_prob_of_four_le
#print axioms Obl.Lam

-- ======================================================================
-- Appendix D: Further results on the method
-- ======================================================================

-- Proposition D.1 (reservation-free levels)
#print axioms ResFreeLevel.exists_isNClique
#print axioms IsResFreeChain.exists_isNClique
#print axioms IsResFreeChain.not_colorable
#print axioms IsResFreeChain.not_adj_of_colorable
#print axioms ResFreeLevel
#print axioms IsResFreeChain
#print axioms IsResFreeChain.exists_isNClique_of_adj
#print axioms resFreeLevel
#print axioms exists_isResFreeChain

-- Theorem D.2 (one level, minimal blocks)
#print axioms AppBD.one_level_minimal_blocks_paper
#print axioms AppBD.IsOneLevelAdv
#print axioms AppBD.flowAdv_forces
#print axioms AppBD.flowAdv_isOneLevelAdv
#print axioms AppBD.one_level_minimal_blocks
#print axioms AppBD.exists_matching

-- Lemma D.3 (potential gain at one level)
#print axioms AppBD.phi_gain
#print axioms AppBD.phi_one
#print axioms AppBD.phi0_gain

-- Appendix D.3, the table of one-level values
#print axioms Cert.oneLevel_rows

-- Theorem D.4 (top block)
#print axioms AppBD.top_block
#print axioms AppBD.IsTopBlockAdv
#print axioms AppBD.top_block_witness

-- Theorem D.5 (partial joins)
#print axioms AppBD.partial_joins
#print axioms AppBD.partial_joins_rpow
#print axioms AppBD.partial_joins_exponent
#print axioms AppBD.IsPJAdv
#print axioms AppBD.partial_joins_witness
#print axioms AppBD.towerOne_isPJAdv
#print axioms AppBD.blowRes
#print axioms AppBD.pj_forces
#print axioms AppBD.lst_colour_le

-- Appendix D.5, First-Fit on one oblivious blow-up
#print axioms Cert.ffEscape_four
#print axioms Cert.ffEscape
#print axioms Cert.surj

-- Appendix D.5, explicit instances
#print axioms Cert.instance_one
#print axioms Cert.instance_two
#print axioms Cert.condC

-- Appendix D.5, transfer for randomized algorithms
#print axioms Expl.transfer_rand
#print axioms Expl.transfer_rand_poly
#print axioms Expl.transfer_rand_quasipoly
#print axioms Expl.prob_half_of_detExpCost
#print axioms Expl.trR
#print axioms Expl.trR_one
#print axioms Expl.trR_succ_eq
#print axioms Expl.trDist
#print axioms Expl.trN_le
#print axioms Expl.probForcing_pow
#print axioms Expl.transfer_rand_of_antichain
#print axioms Expl.probForcing_transfer

-- Appendix D.6, the recursion for Li's construction (Figure 4)
#print axioms Cert.liSize_log2
#print axioms Cert.liSize
#print axioms Cert.liStep
#print axioms Cert.IsLiParams

-- Computed values: label posets (Section 5, Appendix A) and one-level values (Appendix D.3)
#print axioms Num.first_values
#print axioms Num.widths_three
#print axioms Num.width_labelPoset_two
#print axioms Num.width_labelPoset_four_one
#print axioms Num.hasAntichain_labelPoset_three_four
#print axioms Num.le_card_labelPoset_three_iff
#print axioms Num.V_table_full
#print axioms Num.V
#print axioms Num.Forceable
#print axioms Num.V_mono
#print axioms Num.half_le_V
#print axioms Num.V_le_self
#print axioms Num.surv_self
#print axioms Num.mem_forceable_10
#print axioms Num.win_10
#print axioms Num.sGood_of_chk
#print axioms Num.Win.cons_row
#print axioms Num.forceable_subset_succ
#print axioms Num.V_eleven_ne_guess
#print axioms Num.not_forces_of_surv
#print axioms Num.exists_adv_of_win

-- ======================================================================
-- Section "Where the formal proof takes a different route"
-- ======================================================================

-- declarations named in the text
#print axioms Det.exists_input_of_hist
#print axioms labelAlg
#print axioms Rjm.ueSeq_seqIso
#print axioms card_le_card_fiber_mul
#print axioms Expl.adv
#print axioms Det.towerForces_rpow
#print axioms lf_of_base
#print axioms threshold_big
#print axioms Str.gsim
#print axioms Str.faithful_of_lt
#print axioms popCol
#print axioms Obl.card_filter_mul_le
#print axioms Obl.mix_bound
