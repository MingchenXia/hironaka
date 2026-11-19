import Hironaka.Resolution.HironakaG1NormalFiniteRecodingExample
import Hironaka.Invariant.StepOneSeq
import Hironaka.Analytic.SNCGlobalPrimeComponents
import Hironaka.Blowup.BlowupExistenceOriginIdeal

/-! The canonical tangent choice on the concrete padded positive lower mask. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1CanonicalNormalSelectedExample
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealPullbackCalculus
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealOrder
  StepOneValue StepOneValueMasked StepOneLowerDomain BoundaryCount
  HomogenizedIdealAlong HomogenizedGlueingTower CodimOneSupportAlong
  TangentDirectionAlong ResolutionInvariantSpec ContactStageKept ContactStageInvDomain StepOneTangentChange
  HironakaG8MixedOrderInvariance CanonicalCentres
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualRelativeNormalGeometry
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  HironakaG1NormalFiniteRecodingExample HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalDerivativeTrace

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev H : Set X := projection U ⁻¹' ((Subtype.val : U → ComplexModel 2) ⁻¹' firstCoordinateDivisor)
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev T : BlowupTower X X := .refl
private abbrev O := lowerMask P 1 T p
private abbrev M := CMfd.of (n := 3) O
private abbrev L : MarkedIdeal 3 M := lowerMarkedM P 1 T p
private abbrev e : BlowupTower M M := .refl
private abbrev t : M → ℂ := relativeNormalCoordinate U ∘ Subtype.val

private theorem P_domain : IsInvDomain 3 P :=
  properNormalMarked_isInvDomain sourceRecord sourceRecord_domain

private theorem p_mem_H : p ∈ H := by
  change tangentProjection 2 1 (tangentInclusion 2 1 0) ∈ firstCoordinateDivisor
  rw [tangentProjection_tangentInclusion]
  simp [firstCoordinateDivisor]

private theorem lower_eq :
    L = MarkedIdeal.pullback (Subtype.val : O → X) (⟨H, [], P.ideal, 1⟩ : MarkedIdeal 3 X) := by
  have h := positive_mark_one_single_member_lower_eq (X := X) P rfl
    P_domain.isWellFormed.isCoherent H rfl p p_mem_H
  have hN : P.N = univ := preimage_univ
  rw [hN, univ_inter] at h
  exact h

private theorem lower_nil : L.E = [] := by rw [lower_eq]; rfl
private theorem lower_d : L.d = 1 := by rw [lower_eq]; rfl

private theorem P_cosupp_subset : P.cosupp ⊆ {p} := by
  intro x hx
  have hHol : ∀ x g, P.ideal.mem x g → HolomorphicAt 3 g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem P_domain.isWellFormed.isCoherent hg
  have hxZ : x ∈ P.ideal.zeroLocus := by
    have he : P.cosupp = P.N ∩ P.ideal.zeroLocus := cosupport_one hHol
    exact (he ▸ hx).2
  let i : X → ComplexModel 3 := Subtype.val
  have hi : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ∞ i := contMDiff_subtype_val
  have hz (j : Bool ⊕ Unit) : paddedGenerator j x.val = 0 := by
    apply hxZ (paddedGenerator j ∘ i)
    rw [proper_source_generators]
    refine GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨paddedGenerator j, ?_, rfl⟩ ?_)
    · exact isInSpanAt_self ⟨j, rfl⟩ (Eventually.of_forall fun z => paddedGenerator_hol j z)
    · exact Eventually.of_forall fun z => ((paddedGenerator_hol j).comp (hi.mdifferentiable (by simp))) z
  have h0 : x.val (0 : Fin 3) = 0 := hz (.inl true)
  have h1 : x.val (1 : Fin 3) = 0 := eq_zero_of_pow_eq_zero (show x.val (1 : Fin 3) ^ 2 = 0 from hz (.inl false))
  have h2 : x.val (2 : Fin 3) = 0 := hz (.inr ())
  apply mem_singleton_iff.mpr
  apply Subtype.ext
  have hp0 : p.val = 0 := map_zero (tangentInclusion 2 1)
  rw [hp0]
  ext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

private theorem lower_cosupp (pO : O) (hp : pO.val = p) (hpCos : p ∈ P.cosupp) :
    L.cosupp = {pO} := by
  let K : MarkedIdeal 3 X := ⟨H, [], P.ideal, 1⟩
  have hK : K.cosupp = H ∩ P.ideal.zeroLocus :=
    cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem P_domain.isWellFormed.isCoherent hg)
  have hP : P.cosupp = P.N ∩ P.ideal.zeroLocus :=
    cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem P_domain.isWellFormed.isCoherent hg)
  rw [lower_eq, cosupp_pullback_val K (fun _ _ hg =>
    GermIdeal.IsCoherent.holomorphicAt_mem P_domain.isWellFormed.isCoherent hg), hK]
  ext q
  constructor
  · intro hq
    have h : q.val ∈ P.cosupp := hP.symm ▸ ⟨mem_univ _, hq.2⟩
    exact mem_singleton_iff.mpr (Subtype.ext ((mem_singleton_iff.mp (P_cosupp_subset h)).trans hp.symm))
  · intro hq
    rw [mem_singleton_iff.mp hq]
    change pO.val ∈ H ∩ P.ideal.zeroLocus
    rw [hp]
    exact ⟨p_mem_H, (hP ▸ hpCos).2⟩

private theorem lower_regular (x : O) (hx : x ∈ L.N) :
    RegularAtDim (n := 3) L.N x 2 := by
  rw [lower_eq] at hx ⊢
  have he : P.E = [H] := rfl
  have hH : H ∈ P.E := he.symm ▸ List.mem_singleton_self H
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hH
  change RegularAtDim (n := 3) ((Subtype.val : O → X) ⁻¹' H) x 2
  apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
  exact hi ▸ SNCGlobalPrimeComponents.regularAtDim_member P_domain.isWellFormed.isSNCDivisor i
    (hi.symm ▸ hx)

private theorem lower_codim_empty (pO : O) (hp : pO.val = p) (hpCos : p ∈ P.cosupp) :
    codimOnePartAlong L.N L.ideal L.d = ∅ := by
  have hCos := lower_cosupp pO hp hpCos
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨j, hN, hC⟩ := hy
  have hj : j + 1 = 2 := RegularPointDimension.eq_of_regularAtDim hN (lower_regular y hN.2.1)
  change RegularAtDim (n := 3) L.cosupp y j at hC
  rw [hCos] at hC
  have hq : y = pO := hC.2.1
  have hzeroReg : RegularAtDim (n := 3) ({pO} : Set O) y 0 := by
    subst y
    have h0 : p.val = 0 := map_zero (tangentInclusion 2 1)
    have hPre1 : (Subtype.val : productOpen U → ComplexModel 3) ⁻¹' ({0} : Set (ComplexModel 3)) = {p} := by
      ext a
      exact ⟨fun ha => Subtype.ext (ha.trans h0.symm), fun ha => (congrArg Subtype.val ha).trans h0⟩
    have hPre2 : (Subtype.val : O → X) ⁻¹' ({p} : Set X) = {pO} := by
      ext a
      exact ⟨fun ha => Subtype.ext (ha.trans hp.symm), fun ha => (congrArg Subtype.val ha).trans hp⟩
    rw [← hPre2]
    apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    rw [hp, ← hPre1]
    apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    rw [h0]
    exact BlowupExistenceOriginIdeal.regularAtDim_zero
  have hj0 := RegularPointDimension.eq_of_regularAtDim hC hzeroReg
  omega

private theorem lower_domain (h : level P T p = 1) : IsInvDomain 2 L :=
  isInvDomain_lowerMarked_succ (X := X) P P_domain.isWellFormed P_domain.one_le_d
    (by decide) T trivial P_domain.dimLE h

private theorem lower_bar (hL : IsInvDomain 2 L) : barMarked (X := M) L = L := by
  change coeffMarkedAlong (homMarkedAlong L) = L
  rw [homMarkedAlong_eq_of_mark_one L lower_d hL.isWellFormed.isCoherent,
    coeffMarkedAlong_eq_of_mark_one L lower_d hL.isWellFormed.isCoherent]

private theorem first_one_eq_first_three {Y : CMfd.{0} 3}
    (C : MarkedIdeal 3 Y) (q : Y) :
    fstEntry (k := 0) ((invFamily (by decide : 0 < 3) 1).inv C .refl q) =
      fstEntry (k := 2) ((canonicalInvariant 3).inv C .refl q) := rfl

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency false in
private theorem chosen_next_value (pO : O) (hp : pO.val = p) (hCos : p ∈ P.cosupp)
    (hLevel : level P T p = 1) :
    let W := maskB L e pO
    ∃ h : pO ∈ W,
      (invFamily (by decide : 0 < 3) 1).inv (lowerMarkedB L e pO)
          (BlowupTower.refl (X := CMfd.of (n := 3) W)) ⟨pO, h⟩ =
        (invFamily (by decide : 0 < 3) 1).inv (contactMarkedKept L t e (⊤ : Opens M))
          (BlowupTower.refl (X := CMfd.of (n := 3) (⊤ : Opens M))) ⟨pO, mem_univ _⟩ ∧
      fstEntry (k := 0) ((invFamily (by decide : 0 < 3) 1).inv (lowerMarkedB L e pO)
        (BlowupTower.refl (X := CMfd.of (n := 3) W)) ⟨pO, h⟩) = 2 := by
  intro W
  let R := invFamily (by decide : 0 < 3) 1
  let v := (tangentChoice (X := M) L pO).2
  have hL := lower_domain hLevel
  have hNull := lower_codim_empty pO hp hCos
  have hBar := lower_bar hL
  have hpL : pO ∈ L.cosupp := (lower_cosupp pO hp hCos).symm ▸ mem_singleton _
  have ht : IsTangentDirectionAlong L.N L.ideal L.d univ t := padded_selected_normal_tangent
  obtain ⟨hpU, hv⟩ := tangentChoice_spec (X := M) L ⟨univ, t, mem_univ _, ht⟩
  let Uv : Opens M := ⟨(tangentChoice (X := M) L pO).1, hv.isOpen⟩
  have hWU : W = Uv := by
    apply Opens.ext
    change interior {z | z ∈ (Uv : Set M) ∧
      (∀ H' ∈ origMembers L e, z ∉ H') ∧
      z ∉ codimOnePartAlong (geoTransformAlong (barMarked L) e).N
        (geoTransformAlong (barMarked L) e).ideal (geoTransformAlong (barMarked L) e).d} = _
    rw [geoTransformAlong_refl, hBar, hNull]
    have hE : origMembers L e = [] := by simp [origMembers, lower_nil]
    rw [hE]
    simp [Uv.isOpen.interior_eq]
  have hpW : pO ∈ W := hWU.symm ▸ hpU
  have hWsub : (W : Set M) ⊆ e.proj ⁻¹' (tangentChoice (X := M) L pO).1 := by
    intro y hy
    change y ∈ Uv
    exact hWU ▸ hy
  have hOff (y : M) :
      y ∉ codimOnePartAlong (geoTransformAlong (barMarked L) e).N
        (geoTransformAlong (barMarked L) e).ideal (geoTransformAlong (barMarked L) e).d := by
    rw [geoTransformAlong_refl, hBar, hNull]
    simp
  have hDomW : IsInvDomain 1 (contactMarkedKept L v e W) :=
    isInvDomain_stage_coeffHomAlong_of_le (X := M) L hL.isWellFormed hL.one_le_d hL.dimLE
      Uv hv e trivial W hWsub
      (fun y _ _ => hOff y)
      (by simp [lower_nil])
  have hDomT : IsInvDomain 1 (contactMarkedKept L t e (⊤ : Opens M)) :=
    isInvDomain_stage_coeffHomAlong_of_le (X := M) L hL.isWellFormed hL.one_le_d hL.dimLE
      ⊤ ht e trivial ⊤ (subset_rfl)
      (fun y _ _ => hOff y)
      (by simp [lower_nil])
  let q : (⊤ : Opens M) := ⟨pO, mem_univ _⟩
  have hpBar : pO ∈ (geoTransformAlong (barMarked L) (e.append e)).cosupp := by
    change pO ∈ (barMarked L).cosupp
    rwa [hBar]
  obtain ⟨V, hpV, hEq⟩ := Seq.StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens (X := M) R L
    hL.isWellFormed.isCoherent hL.isWellFormed.isClosedSubmanifold_N hL.one_le_d
    hpL hv hpU ht (mem_univ pO)
  have hVal := hEq e e trivial W ⊤ hWsub (subset_univ _)
    (by simp [lower_nil]) (by simp [lower_nil]) hDomW trivial hDomT trivial
    ⟨pO, hpW⟩ q rfl hpV hpBar
  have hVal' : fstEntry (k := 0) (R.inv (contactMarkedKept L v e W)
      (BlowupTower.refl (X := CMfd.of (n := 3) W)) ⟨pO, hpW⟩) =
      fstEntry (k := 0) (R.inv (contactMarkedKept L t e (⊤ : Opens M))
      (BlowupTower.refl (X := CMfd.of (n := 3) (⊤ : Opens M))) q) :=
    congrArg (fstEntry (k := 0)) hVal
  have htVal := (first_one_eq_first_three (Y := CMfd.of (n := 3) (⊤ : Opens M))
    (contactMarkedKept L t e (⊤ : Opens M)) q).trans (padded_selected_normal_contact_fst pO hp)
  exact ⟨hpW, hVal, hVal'.trans htVal⟩

/-- The actual chosen zero-level lower record at the padded positive lower
anchor reads nonmonomial order two. The empty history uses the original
canonical tangent choice on its own mask. -/
theorem canonical_normal_selected_next_first_entry :
    ∃ (pO : O) (hpW : pO ∈ maskB L e pO), pO.val = p ∧
      fstEntry (k := 0) ((invFamily (by decide : 0 < 3) 1).inv (lowerMarkedB L e pO)
        (BlowupTower.refl (X := CMfd.of (n := 3) (maskB L e pO))) ⟨pO, hpW⟩) = 2 := by
  obtain ⟨_, _, pO, _, _, _, hp, _, hCos, _, hLevel, _, _, _, _, _, _⟩ :=
    joint_positive_nonspecial_first_entries
  obtain ⟨h, _, hVal⟩ := chosen_next_value pO hp hCos hLevel
  exact ⟨pO, h, hp, hVal⟩

/-- The actual canonical Step One on the padded selected record takes
its finite branch at level zero, with lower nonmonomial first entry two. -/
theorem canonical_normal_selected_finite_stepOne :
    ∃ (pO : O) (v : ValTy 1), pO.val = p ∧
      Seq.StepOneValueMasked.stepOneInvM (X := M) (invFamily (by decide : 0 < 3) 1) L e pO =
        toLex (0, (↑v : WithTop (ValTy 1))) ∧
      v =
        (invFamily (by decide : 0 < 3) 1).inv (contactMarkedKept L t e (⊤ : Opens M))
          (BlowupTower.refl (X := CMfd.of (n := 3) (⊤ : Opens M))) ⟨pO, mem_univ _⟩ ∧
      fstEntry (k := 0) v = 2 := by
  obtain ⟨_, _, pO, _, _, _, hp, _, hCos, _, hLevel, _, _, _, _, _, _⟩ :=
    joint_positive_nonspecial_first_entries
  obtain ⟨hpW, hEq, hV⟩ := chosen_next_value pO hp hCos hLevel
  let W := maskB L e pO
  let R := invFamily (by decide : 0 < 3) 1
  let v := R.inv (lowerMarkedB L e pO) (BlowupTower.refl (X := CMfd.of (n := 3) W)) ⟨pO, hpW⟩
  have hE : origMembers L e = [] := by simp [origMembers, lower_nil]
  have h0 : level L e pO = 0 := by
    unfold level
    rw [hE]
    simp [boundaryCount]
  have hBar := lower_bar (lower_domain hLevel)
  have hNull := lower_codim_empty pO hp hCos
  have hNS : ¬ IsSpecial L e pO := by
    rintro (⟨_, h⟩ | ⟨h, _⟩)
    · rw [geoTransformAlong_refl, hBar, hNull] at h
      exact h
    · rw [h0] at h
      exact Nat.not_succ_le_zero 0 h
  refine ⟨pO, v, hp, ?_, hEq, hV⟩
  change Seq.StepOneValueMasked.stepOneInvL (X := M) R L (lowerMarkedM L) e pO = _
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R L (lowerMarkedM L) e hNS, h0]
  change toLex (0, Seq.StepOneValueMasked.lowerValueL R L (lowerMarkedM L) 0 e e pO) = _
  unfold Seq.StepOneValueMasked.lowerValueL
  rw [dif_pos (show e.proj pO ∈ lowerMask L 0 e (e.proj pO) from hpW)]
  rfl

end
end Hironaka.HironakaG1CanonicalNormalSelectedExample
