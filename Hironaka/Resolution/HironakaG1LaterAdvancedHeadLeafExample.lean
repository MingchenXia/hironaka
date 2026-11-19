import Hironaka.Resolution.HironakaG1LaterAdvancedHeadCanonicalExample
import Hironaka.Resolution.HironakaG1LaterPositiveSelectedExample

/-! The inner leaf on the literal born-positive companion. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterAdvancedHeadLeafExample

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneLowerDomain MemberInterLocusAlong HomogenizedIdealAlong
  InvDomainMemberRestriction InvDomainCompanion InvDomainTowerAlong MarkedIdealRestrictOpen
  MarkedIdealBiholomorphism
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  HironakaG1LaterPositiveNormalExample HironakaG1LaterPositiveSelectedExample
  HironakaG1LaterAdvancedHeadExample HironakaG1LaterAdvancedHeadCanonicalExample
  HironakaG1LaterPositiveSuccessorRead HironakaG1InitialPositiveGeneralRead
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialTransformAlong
  GeneralValue CompanionRebase CompanionReductionAlong CoefficientIdeal
  InvertibleIdealQuotient RelativePrincipalizationSpan GermIdealOrder

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}
private abbrev D (i : Fin 3) : Set X := {z | z.val i = 0}
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev M : MarkedIdeal 3 X := {P with E := [D 0, D 1]}
private abbrev O := maskA M B q
private abbrev A := CMfd.of (n := 3) O
private abbrev L := lowerMarkedM M 1 B q
private abbrev e : BlowupTower A A := .refl
private abbrev W := ordMask (M := A) L 1
private abbrev V := CMfd.of (n := 3) W
private abbrev J := compAt (X := A) L 1 e
private abbrev E : BlowupTower V V := .refl
private abbrev R₂ := invFamily (by decide : 0 < 3) 2
private abbrev R₁ := invFamily (by decide : 0 < 3) 1
private abbrev G := geoTransformAlong (barMarked M) B
private abbrev K := memberRestrict G (membersThrough G.E (origMembers M B) q)
private abbrev D' (i : Fin 3) : Set Y := geoStrictTransform π C (D i)
private abbrev F : Set Y := π ⁻¹' C
private abbrev φ (z : W) : Y := z.val.val
private abbrev c (z : Y) : ℂ := yChart.toFun z (2 : Fin 3)

private theorem bar_eq : barMarked M = M := by
  change coeffMarkedAlong (homMarkedAlong M) = M
  have hM : IsInvDomain 3 M := joint_added_boundary_test.1
  rw [homMarkedAlong_eq_of_mark_one M rfl hM.isWellFormed.isCoherent,
    coeffMarkedAlong_eq_of_mark_one M rfl hM.isWellFormed.isCoherent]

private theorem G_wf : G.IsWellFormed := by
  change (geoTransformAlong (barMarked M) B).IsWellFormed
  rw [bar_eq]
  exact MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    joint_added_boundary_test.1.isWellFormed B joint_added_boundary_test.2

private theorem G_mark : G.d = 1 := by
  change (geoTransformAlong (barMarked M) B).d = 1
  rw [bar_eq]
  rfl

private theorem G_carrier : G.N = univ := by
  change (geoTransformAlong (barMarked M) B).N = univ
  rw [bar_eq]
  change geoStrictTransform π C M.N = univ
  rw [show M.N = univ from preimage_univ, geoStrictTransform_univ hπ]

private theorem q_mem_D0 : q ∈ D' 0 :=
  joint_first_point_blowup_positive_normal_contact.2.2.2.2.2.1

private theorem q_not_D1 : q ∉ D' 1 := by
  have hLevel := joint_added_boundary_upper_regime_advances.2.1
  change BoundaryCount.boundaryCount [D' 0, D' 1] q = 1 at hLevel
  intro h
  classical
  unfold BoundaryCount.boundaryCount at hLevel
  rw [Finset.filter_true_of_mem] at hLevel
  · simp at hLevel
  · intro i _
    fin_cases i
    · exact q_mem_D0
    · exact h

private theorem K_carrier : K.N = D' 0 := by
  have hSub : ∀ H ∈ origMembers M B, H ∈ G.E := fun _ h => List.mem_of_mem_take h
  rw [memberRestrict_N, G_carrier, univ_inter, memberInter_membersThrough hSub]
  change {x | ∀ H ∈ [D' 0, D' 1], q ∈ H → x ∈ H} = D' 0
  ext x
  change (∀ H ∈ [D' 0, D' 1], q ∈ H → x ∈ H) ↔ x ∈ D' 0
  constructor
  · intro h
    exact h _ (by simp) q_mem_D0
  · intro hx H hH hq
    rcases List.mem_cons.mp hH with rfl | hH
    · exact hx
    · rw [List.mem_singleton] at hH
      exact (q_not_D1 (hH ▸ hq)).elim

private theorem K_wf : K.IsWellFormed := isWellFormed_memberRestrict (by decide) G_wf _

private theorem K_normal_member {z : Y} (hz : z ∈ yChart.source) : K.ideal.mem z c := by
  rw [memberRestrict_ideal, coeffMarkedAlong_eq_of_mark_one G G_mark G_wf.isCoherent]
  change (geoTransformAlong (barMarked M) B).ideal.mem z c
  rw [bar_eq]
  change (M.geoTransform C π).ideal.mem z c
  rw [geoTransform_ideal_eq_controlledTransform (𝔪 := M) (show M.N = univ from preimage_univ)
    joint_added_boundary_test.1.isWellFormed.isCoherent hπ]
  exact normal_generator z hz

private theorem L_domain : IsInvDomain 2 L := by
  have hM : IsInvDomain 3 M := joint_added_boundary_test.1
  have hTest : IsGeoTestTower (barMarked M) B := by rw [bar_eq]; exact joint_added_boundary_test.2
  exact isInvDomain_lowerMarked_succ M hM.isWellFormed hM.one_le_d (by decide) B hTest
    hM.dimLE joint_added_boundary_upper_regime_advances.2.1

private theorem L_cosupp (hq : q ∈ O) : (⟨q, hq⟩ : O) ∈ L.cosupp := by
  change (⟨q, hq⟩ : O) ∈ (MarkedIdeal.pullback (Subtype.val : O → Y) K).cosupp
  rw [cosupp_pullback_val K (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem K_wf.isCoherent h) O]
  change q ∈ K.cosupp
  have hG : q ∈ G.cosupp := by
    change q ∈ (geoTransformAlong (barMarked M) B).cosupp
    rw [bar_eq]
    exact joint_added_boundary_survives_nonspecial.1
  rw [cosupp_memberRestrict G_wf G_mark.ge]
  exact ⟨hG, fun i hi => (mem_membersThrough.mp hi).2⟩

private theorem L_mark : L.d = 1 := by
  change (coeffMarkedAlong G).d = 1
  rw [coeffMarkedAlong_eq_of_mark_one G G_mark G_wf.isCoherent, G_mark]

/-- The first companion retains the strict original divisor as its carrier. -/
theorem J_carrier : J.N = φ ⁻¹' D' 0 := by
  simp only [J, compAt, companionOf, companionAlong_N]
  change (Subtype.val : W → O) ⁻¹' ((Subtype.val : O → Y) ⁻¹' K.N) = _
  rw [K_carrier]
  rfl

/-- The first companion retains the empty old slot and the born divisor. -/
theorem J_boundary : J.E = [∅, φ ⁻¹' F] := by
  simp only [J, compAt, companionOf, companionAlong_E]
  change L.E.map ((Subtype.val : W → O) ⁻¹' ·) = _
  rw [joint_advanced_head_selected_boundary]
  rfl

/-- The actual companion has its invariant domain, maximal order, and anchor cosupport. -/
theorem J_data (hq : q ∈ O) (hw : (⟨q, hq⟩ : O) ∈ W) :
    IsInvDomain 2 J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧ (⟨⟨q, hq⟩, hw⟩ : W) ∈ J.cosupp := by
  let z : O := ⟨q, hq⟩
  have hOrder : nmOrd (M := A) L z = 1 :=
    (joint_advanced_head_lower_true_order z rfl).1.trans L_mark
  have h := original_positive_order_successor_read (k := 1) (by decide : 0 < 3) (X := A)
    L L_domain e trivial z (L_cosupp hq) 1 hOrder (by decide)
  obtain ⟨hw', hJ, hMax, _, hz, _⟩ := h
  exact ⟨hJ, hMax, hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- The normal chart ratio belongs to the actual companion ideal on its order mask. -/
theorem J_normal_member {z : W} (hz : φ z ∈ yChart.source) :
    J.ideal.mem z (c ∘ φ) := by
  let I : MarkedIdeal 3 V := MarkedIdeal.pullback (M' := V) (Subtype.val : W → O) L
  have hI : I.ideal.IsCoherent :=
    (isInvDomain_pullback_val (M := A) (𝔪 := L) W L_domain).isWellFormed.isCoherent
  have hL : L.ideal.mem z.val (c ∘ (Subtype.val : O → Y)) :=
    comp_val_mem_pullback_val O K_wf.isCoherent (K_normal_member hz)
  have hMem : I.ideal.mem z (c ∘ φ) :=
    comp_val_mem_pullback_val W L_domain.isWellFormed.isCoherent hL
  have hNm := le_nonmonomialPartAlong_self (N := I.N) (E := I.E) hI z (c ∘ φ) hMem
  have hd : I.d = 1 := L_mark
  change (companionOf 3 (M := V) I 1).ideal.mem z _
  rw [companionOf, companionAlong_ideal, hd, if_neg (by decide : ¬ 1 < 1)]
  exact hNm

/-- The literal normal line lies in the strict original divisor and the born fibre. -/
theorem normal_line (a : ℂ) :
    let v := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)
    let f := yChart.invFun (a • v)
    f ∈ yChart.source ∧ f ∈ D' 0 ∧ f ∈ F ∧ c f = a := by
  intro v f
  have ht := chart_all (a • v)
  have hf := yChart.toPartialEquiv.map_target ht
  have hc : yChart.toFun f = a • v := yChart.toPartialEquiv.right_inv ht
  refine ⟨hf, (strict_chart_coordinate 0 (by decide) f hf).mpr (by rw [hc]; simp [v]), ?_, ?_⟩
  · change π f ∈ C
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    have hp : p.val = 0 := map_zero (HironakaRelativeNormalIdeal.tangentInclusion 2 1)
    rw [chart_projection f hf, hc, hp]
    ext i
    by_cases hi : i = 1
    · subst i
      simp [monomial_apply, v]
    · simp [monomial_apply, v, hi]
  · change yChart.toFun f (2 : Fin 3) = a
    simp [hc, v]

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem J_nonspecial (hq : q ∈ O) (hw : (⟨q, hq⟩ : O) ∈ W)
    (hd : J.d = 1) (hl : level J E (⟨⟨q, hq⟩, hw⟩ : W) = 1) :
    ¬ IsSpecial J E (⟨⟨q, hq⟩, hw⟩ : W) := by
  let z : W := ⟨⟨q, hq⟩, hw⟩
  obtain ⟨hJ, _, _⟩ := J_data hq hw
  intro hSpecial
  rcases hSpecial with hZero | ⟨_, hMember⟩
  · exact (by decide : (1 : ℕ) ≠ 0) (hl.symm.trans hZero.1)
  have hBar : barMarked J = J := by
    change coeffMarkedAlong (homMarkedAlong J) = J
    rw [homMarkedAlong_eq_of_mark_one J hd hJ.isWellFormed.isCoherent,
      coeffMarkedAlong_eq_of_mark_one J hd hJ.isWellFormed.isCoherent]
  have hOrig : origMembers J E = J.E := List.take_length
  change z ∈ memberInterLocus (barMarked J).N (origMembers J E) (barMarked J).cosupp at hMember
  rw [hOrig, hBar, J_boundary] at hMember
  have hEv := (mem_memberInterLocus_iff.mp hMember).2
  have hEvW : ∀ᶠ u : W in 𝓝 z, φ u ∈ D' 0 → φ u ∈ F → u ∈ J.cosupp := by
    filter_upwards [hEv] with u hu huD huF
    apply hu (J_carrier.symm ▸ huD)
    intro H hH hzH
    rcases List.mem_cons.mp hH with rfl | hH
    · exact False.elim hzH
    · rw [List.mem_singleton] at hH
      rw [hH]
      exact huF
  have hMap : Filter.map φ (𝓝 z) = 𝓝 q := by
    change Filter.map ((Subtype.val : O → Y) ∘ (Subtype.val : W → O)) (𝓝 z) = _
    rw [← Filter.map_map]
    have h₁ : Filter.map (Subtype.val : W → O) (𝓝 z) = 𝓝 z.val :=
      W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z
    have h₂ : Filter.map (Subtype.val : O → Y) (𝓝 z.val) = 𝓝 q :=
      O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z.val
    rw [h₁, h₂]
  have hEvY : ∀ᶠ w : Y in 𝓝 q, ∃ u : W, φ u = w ∧ (w ∈ D' 0 → w ∈ F → u ∈ J.cosupp) := by
    rw [← hMap]
    exact hEvW.mono fun u hu => ⟨u, rfl, hu⟩
  let v : ComplexModel 3 := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)
  let f : ℂ → Y := fun a => yChart.invFun (a • v)
  have hT : Tendsto f (𝓝 0) (𝓝 q) := by
    have hf : Continuous (fun a : ℂ => a • v) := continuous_id.smul continuous_const
    have hAt : Tendsto (fun a : ℂ => a • v) (𝓝 0) (𝓝 (yChart.toFun q)) := by
      simpa [chart_q.2] using hf.tendsto (0 : ℂ)
    exact (yChart.homeo.tendsto_symm chart_q.1).comp hAt
  have hne : ∃ᶠ a : ℂ in 𝓝 0, a ≠ 0 := by
    have hF : ∃ᶠ a : ℂ in 𝓝[≠] 0, True :=
      Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => trivial)
    exact ((frequently_nhdsWithin_iff).mp hF).mono (fun _ ha => ha.2)
  obtain ⟨a, ha0, u, hEq, hu⟩ := (hne.and_eventually (hT.eventually hEvY)).exists
  obtain ⟨haV, haD, haF, haNorm⟩ := normal_line a
  have haCos := hu haD haF
  have haUV : φ u ∈ yChart.source := by
    rw [hEq]
    exact haV
  have haMem := J_normal_member haUV
  have hHol := GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent haMem
  have hVan := haCos.2 (c ∘ φ) haMem
  rw [hd] at hVan
  have h0 := (vanishesToOrderOn_one_iff haCos.1 hHol).mp hVan
  change c (φ u) = 0 at h0
  change c (f a) = a at haNorm
  rw [hEq, haNorm] at h0
  exact ha0 h0

private theorem J_mark : J.d = 1 := by
  simp only [J, compAt, companionOf, companionAlong_d]
  change (if 1 < L.d then 1 * (L.d - 1) else 1) = _
  simp [L_mark]

/-- The full bar operation retains the mark-one companion. -/
theorem J_bar : barMarked J = J := by
  obtain ⟨_, hq, hw, _, _, _⟩ := joint_advanced_canonical_positive_successor
  have hI := (J_data hq hw).1.isWellFormed.isCoherent
  change coeffMarkedAlong (homMarkedAlong J) = J
  rw [homMarkedAlong_eq_of_mark_one J J_mark hI, coeffMarkedAlong_eq_of_mark_one J J_mark hI]

private theorem next_mark (z : W) : (lowerMarkedM J 1 E z).d = 1 := by
  change (coeffMarkedAlong (barMarked J)).d = 1
  rw [J_bar]
  obtain ⟨_, hq, hw, _, _, _⟩ := joint_advanced_canonical_positive_successor
  rw [coeffMarkedAlong_eq_of_mark_one J J_mark (J_data hq hw).1.isWellFormed.isCoherent, J_mark]

private theorem next_boundary (z : W) (hzF : φ z ∈ F) :
    (lowerMarkedM J 1 E z).E = [∅] := by
  classical
  let O' := maskA J E z
  change List.map (fun H => (Subtype.val : O' → W) ⁻¹' H)
    (memberRestrict (barMarked J) (membersThrough (barMarked J).E (origMembers J E) z)).E = _
  have hOrig : origMembers J E = J.E := List.take_length
  rw [J_bar]
  erw [hOrig, memberRestrict_E]
  have hList :
      ((List.finRange ([∅, φ ⁻¹' F] : List (Set W)).length).filter (fun i =>
        i ∉ membersThrough ([∅, φ ⁻¹' F] : List (Set W)) [∅, φ ⁻¹' F] z)).map
          ([∅, φ ⁻¹' F] : List (Set W)).get = [∅] := by
    change (((List.finRange 2).filter (fun i =>
      i ∉ membersThrough ([∅, φ ⁻¹' F] : List (Set W)) [∅, φ ⁻¹' F] z)).map
        ([∅, φ ⁻¹' F] : List (Set W)).get) = _
    have hf0 : (0 : Fin 2) ∉ membersThrough ([∅, φ ⁻¹' F] : List (Set W)) [∅, φ ⁻¹' F] z := by
      rw [mem_membersThrough]
      exact fun h => h.2
    have hf1 : (1 : Fin 2) ∈ membersThrough ([∅, φ ⁻¹' F] : List (Set W)) [∅, φ ⁻¹' F] z :=
      mem_membersThrough.mpr ⟨by simp, hzF⟩
    rw [show List.finRange 2 = [(0 : Fin 2), 1] from by decide]
    simp [hf0, hf1]
  rw [← J_boundary] at hList
  exact congrArg (List.map (fun H => (Subtype.val : O' → W) ⁻¹' H)) hList

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical upper value takes a finite inner leaf at its
born-positive companion. That leaf is evaluated on the next literal
positive mask and empty tail. -/
theorem joint_advanced_head_finite_inner_leaf :
    ∃ (hq : q ∈ O) (hw : (⟨q, hq⟩ : O) ∈ W),
      let z : W := ⟨⟨q, hq⟩, hw⟩
      let O' := maskA J E z
      let L' := lowerMarkedM J 1 E z
      ¬ IsSpecial J E z ∧ L'.d = 1 ∧ L'.E = [∅] ∧
      ∃ hz : z ∈ O',
        let v := R₁.inv L' (BlowupTower.refl (X := CMfd.of (n := 3) O')) (⟨z, hz⟩ : O')
        Seq.StepOneValueMasked.stepOneInvM (X := V) R₁ J E z =
          toLex (1, (v : WithTop (ValTy 1))) ∧
        Seq.StepOneValueMasked.stepOneInvM R₂ M B q =
          toLex (1, (positiveSuccessorRead 1 (toLex (1, (v : WithTop (ValTy 1)))) :
            WithTop (ValTy 2))) := by
  obtain ⟨_, hq, hw, hd, hLev, hUpper⟩ := joint_advanced_canonical_positive_successor
  let z : W := ⟨⟨q, hq⟩, hw⟩
  let O' := maskA J E z
  let L' := lowerMarkedM J 1 E z
  have hNS := J_nonspecial hq hw hd hLev
  obtain ⟨hJ, _, _⟩ := J_data hq hw
  have hz : z ∈ O' := mem_maskA (X := V) J hJ.isWellFormed hJ.one_le_d (by decide) E
    trivial hLev.ge hNS
  let v := R₁.inv L' (BlowupTower.refl (X := CMfd.of (n := 3) O')) (⟨z, hz⟩ : O')
  have hInner : Seq.StepOneValueMasked.stepOneInvM (X := V) R₁ J E z =
      toLex (1, (v : WithTop (ValTy 1))) := by
    change Seq.StepOneValueMasked.stepOneInvL (X := V) R₁ J (lowerMarkedM J) E z = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R₁ J (lowerMarkedM J) E hNS, hLev]
    change toLex (1, Seq.StepOneValueMasked.lowerValueL (X := V) R₁ J (lowerMarkedM J) 1 E E z) = _
    unfold Seq.StepOneValueMasked.lowerValueL
    rw [dif_pos (show E.proj z ∈ lowerMask J 1 E (E.proj z) from hz)]
    rfl
  have hzF : φ z ∈ F := by
    change π q ∈ C
    have hqp : π q = p := joint_first_point_blowup_positive_normal_contact.2.2.2.1
    rw [hqp]
    exact mem_singleton _
  refine ⟨hq, hw, hNS, next_mark z, next_boundary z hzF, hz, hInner, ?_⟩
  exact hUpper.trans (congrArg (fun a : ℕ ×ₗ WithTop (ValTy 1) =>
    toLex (1, (positiveSuccessorRead 1 a : WithTop (ValTy 2)))) hInner)

end
end Hironaka.HironakaG1LaterAdvancedHeadLeafExample
