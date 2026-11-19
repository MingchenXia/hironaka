import Hironaka.Resolution.HironakaG1PositiveNormalJointExample
import Hironaka.Invariant.ContactStageKept

/-!
# The normal contact of the finite coordinate example

The actual padded positive lower record has a normal tangent direction.
Its contact record recovers the native order-two trace.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1NormalFiniteRecodingExample

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism GermIdealPullbackCalculus RelativePrincipalizationSpan
  GermIdealOrder IdealWeightPowers IdealOrderArithmetic RestrictedIdealExtension
  HomogenizedIdealAlong HomogenizedGlueingTower CoefficientIdealRestriction
  InvertibleIdealQuotient StepOneValue StepOneValueMasked HironakaG8MixedOrderInvariance
  CanonicalCentres NonmonomialOrderLocal HironakaSharpOriginalProductTraceOrder
  TangentDirectionAlong ContactEquivalenceAlong ContactStageKept
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaActualRelativeNormalGeometry HironakaActualWeightedNormalPadding
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualCentreJointJets HironakaRelativeNormalIdeal HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalContact
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev D : Set U := (Subtype.val : U → ComplexModel 2) ⁻¹' firstCoordinateDivisor
private abbrev H : Set X := projection U ⁻¹' D
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev S : MarkedIdeal 3 X := sectionMarked sourceRecord
private abbrev T : BlowupTower X X := .refl
private abbrev O := lowerMask P 1 T p
private abbrev M := CMfd.of (n := 3) O
private abbrev L : MarkedIdeal 3 M := lowerMarkedM P 1 T p
private abbrev t : X → ℂ := relativeNormalCoordinate U
private abbrev tO : M → ℂ := t ∘ Subtype.val

private theorem normal_zeroPlane : {z : X | t z = 0} = zeroPlane U := by
  ext z
  change t z = 0 ↔ z ∈ liftedCarrier (univ : Set U)
  have hc : t z = actualJointNormalProjection 2 1 z.val (0 : Fin 1) := by
    simp [relativeNormalCoordinate, HironakaActualZeroCoordinateContactSeed.addedCoordinate,
      HironakaActualGraphFunctionalIdeal.graphFunction, HironakaActualZeroCoordinateContactSeed.zeroFunction]
    rfl
  rw [hc]
  constructor
  · intro hz
    refine ⟨mem_univ _, ?_⟩
    ext i
    have h0 : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa only [h0, WithLp.ofLp_zero, Pi.zero_apply] using hz
  · intro hz
    exact congrArg (fun v : ComplexModel 1 => v (0 : Fin 1)) hz.2

private theorem p_mem_H : p ∈ H := by
  change tangentProjection 2 1 (tangentInclusion 2 1 0) ∈ firstCoordinateDivisor
  rw [tangentProjection_tangentInclusion]
  simp [firstCoordinateDivisor]

private theorem P_coherent : P.ideal.IsCoherent :=
  (properNormalMarked_isInvDomain sourceRecord sourceRecord_domain).isWellFormed.isCoherent

private theorem lower_eq :
    L = MarkedIdeal.pullback (Subtype.val : O → X) (⟨H, [], P.ideal, 1⟩ : MarkedIdeal 3 X) := by
  have h := positive_mark_one_single_member_lower_eq (X := X) P rfl P_coherent H rfl p p_mem_H
  have hN : P.N = univ := preimage_univ
  rw [hN, univ_inter] at h
  exact h

private theorem normal_mem (x : X) : P.ideal.mem x t := by
  let J : GermIdeal 3 X := finiteFunctionIdeal (fun _ : Unit => fun z => t z ^ 1)
  change (sumIdeal S.ideal J).mem x t
  have hpol : HolomorphicAt 3 t x := Eventually.of_forall fun z => normalCoordinate_mdifferentiable U z
  apply le_sumIdeal_right' (𝔟 := J) (fun _ _ hg => hg.1) x t
  exact isInSpanAt_self ⟨(), by funext z; simp⟩ hpol

/-- The real independent normal coordinate is a mark-one tangent direction
on the actual selected padded lower carrier, throughout its mask. -/
theorem padded_selected_normal_tangent :
    IsTangentDirectionAlong L.N L.ideal L.d univ tO := by
  have h := normal_tangent_of_power_member U D P.ideal P_coherent 1 (by decide)
    (fun x => by simpa only [pow_one] using normal_mem x)
  have h' := isTangentDirectionAlong_pullback_val O
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem P_coherent hg)
    (show IsTangentDirectionAlong H P.ideal 1 O t from
      ⟨O.isOpen, fun y _ => h.mem y (mem_univ _), fun y _ hy => h.multiplicity_one y (mem_univ _) hy⟩)
  rw [lower_eq]
  exact h'

private theorem cosupport_recoded (q : ℕ) :
    cosupport 3 (zeroPlane U ∩ H) P.ideal q = cosupport 3 (zeroPlane U ∩ H) S.ideal q := by
  have hS := HironakaActualSectionBoundaryGeometry.section_projected_domain 2
    sourceRecord.N sourceRecord.E sourceRecord.ideal sourceRecord.d sourceRecord_domain
  have hSI : S.ideal.IsCoherent := hS.isWellFormed.isCoherent
  let V := zeroPlane U ∩ H
  let J : GermIdeal 3 X := finiteFunctionIdeal (fun _ : Unit => fun z => t z ^ 1)
  change cosupport 3 V (sumIdeal S.ideal J) q = _
  have hHol : ∀ x g, J.mem x g → HolomorphicAt 3 g x := fun _ _ hg => hg.1
  rw [cosupport_sumIdeal (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hSI hg) hHol]
  apply inter_eq_left.mpr
  intro x hx
  refine ⟨hx.1, fun g hg => IsInSpanAt.vanishesToOrderOn hg ?_⟩
  rintro _ ⟨_, rfl⟩
  refine ⟨fun _ => 0, GiraudAlong.zero_mem_idealPow _ _ _, Eventually.of_forall fun y hy => ?_⟩
  have hzero : t y = 0 := by
    have hy0 : y ∈ zeroPlane U := hy.1
    rw [← normal_zeroPlane] at hy0
    exact hy0
  simp [hzero]

private theorem trace_order_recoded :
    ordinaryTraceOrder (X := X) (zeroPlane U ∩ H) P.ideal p = 2 := by
  have hS := HironakaActualSectionBoundaryGeometry.section_projected_domain 2
    sourceRecord.N sourceRecord.E sourceRecord.ideal sourceRecord.d sourceRecord_domain
  have hSI : S.ideal.IsCoherent := hS.isWellFormed.isCoherent
  have hOrd : ordinaryTraceOrder (X := X) (zeroPlane U ∩ H) P.ideal p =
      ordinaryTraceOrder (X := X) (zeroPlane U ∩ H) S.ideal p := by
    apply nmOrd_congr
    intro q
    rw [ordGe_ordinaryTraceMarked_eq_cosupport _ _ P_coherent,
      ordGe_ordinaryTraceMarked_eq_cosupport _ _ hSI, cosupport_recoded]
  exact hOrd.trans section_source_trace_order

private abbrev C : MarkedIdeal 3 (⊤ : Opens M) := contactMarkedKept L tO .refl ⊤
private abbrev A : MarkedIdeal 3 X := ⟨zeroPlane U ∩ H, [], P.ideal, 1⟩

private theorem contact_eq :
    C = MarkedIdeal.pullback (Subtype.val : (⊤ : Opens M) → M)
      (MarkedIdeal.pullback (Subtype.val : O → X) A) := by
  have hI : L.ideal.IsCoherent := by
    rw [lower_eq]
    exact isCoherent_pullback contMDiff_subtype_val P_coherent
  have hd : L.d = 1 := by rw [lower_eq]; rfl
  have hCoeff := coeffMarkedAlong_eq_of_mark_one L hd hI
  change MarkedIdeal.pullback (Subtype.val : (⊤ : Opens M) → M)
    (withN (coeffMarkedAlong (geoTransformAlong (barMarked (X := M) L) .refl))
      (strictAlong (BlowupTower.refl (X := M)) (L.N ∩ {z | tO z = 0}))) = _
  rw [geoTransformAlong_refl, strictAlong_refl]
  change MarkedIdeal.pullback (Subtype.val : (⊤ : Opens M) → M)
    (withN (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong L))) (L.N ∩ {z | tO z = 0})) = _
  rw [homMarkedAlong_eq_of_mark_one L hd hI, hCoeff, hCoeff, lower_eq]
  apply congrArg (MarkedIdeal.pullback (Subtype.val : (⊤ : Opens M) → M))
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change ((Subtype.val : O → X) ⁻¹' H) ∩ {z : O | t z.val = 0} =
      (Subtype.val : O → X) ⁻¹' (zeroPlane U ∩ H)
    change ((Subtype.val : O → X) ⁻¹' H) ∩ ((Subtype.val : O → X) ⁻¹' {z | t z = 0}) = _
    rw [normal_zeroPlane, ← preimage_inter, inter_comm H]
  · rfl
  · rfl
  · rfl

/-- Cutting the actual padded positive lower record by its normal tangent
recovers order two at the same anchor on the actual contact record. -/
theorem padded_selected_normal_contact_fst (pO : O) (hp : pO.val = p) :
    let q : (⊤ : Opens M) := ⟨pO, mem_univ _⟩
    fstEntry ((canonicalInvariant 3).inv C
      (BlowupTower.refl (X := CMfd.of (n := 3) (⊤ : Opens M))) q) = 2 := by
  intro q
  let AO := MarkedIdeal.pullback (Subtype.val : O → X) A
  have hAO : AO.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val P_coherent
  have hOrd := ordinaryTraceOrder_pullback_open (A := M) (⊤ : Opens M) AO.N AO.ideal hAO q
  have hOrd' := ordinaryTraceOrder_pullback_open (A := X) O A.N A.ideal P_coherent pO
  have hq : q.val = pO := rfl
  rw [canonicalInvariant_fst, geoTransformAlong_refl, contact_eq,
    nmOrd_eq_ordinaryTraceOrder_of_nil _ (by rfl)]
  change ordinaryTraceOrder (X := CMfd.of (n := 3) (⊤ : Opens M))
    ((Subtype.val : (⊤ : Opens M) → M) ⁻¹' AO.N)
    (GermIdeal.pullback (m := 3) (Subtype.val : (⊤ : Opens M) → M) AO.ideal) q = 2
  rw [hOrd, hq]
  change ordinaryTraceOrder (X := M) ((Subtype.val : O → X) ⁻¹' A.N)
    (GermIdeal.pullback (m := 3) (Subtype.val : O → X) A.ideal) pO = 2
  rw [hOrd', hp]
  exact trace_order_recoded

open MarkedIdealRestrictOpen

/-- Every order threshold of the actual normal contact is the section ideal's
threshold along the very same member cut, restricted to the padded mask. -/
theorem padded_selected_normal_contact_cosupport (r : ℕ) :
    cosupport 3 C.N C.ideal r =
      (fun q : (⊤ : Opens M) => q.val.val) ⁻¹'
        cosupport 3 (zeroPlane U ∩ H) S.ideal r := by
  let Q : MarkedIdeal 3 X := ⟨A.N, [], A.ideal, r⟩
  let QO := MarkedIdeal.pullback (Subtype.val : O → X) Q
  have hQO : QO.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val P_coherent
  rw [contact_eq]
  change (MarkedIdeal.pullback (Subtype.val : (⊤ : Opens M) → M) QO).cosupp = _
  rw [cosupp_pullback_val QO (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hQO hg)]
  change (Subtype.val : (⊤ : Opens M) → M) ⁻¹'
    (MarkedIdeal.pullback (Subtype.val : O → X) Q).cosupp = _
  rw [cosupp_pullback_val Q (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem P_coherent hg)]
  change (Subtype.val : (⊤ : Opens M) → M) ⁻¹' ((Subtype.val : O → X) ⁻¹'
    cosupport 3 (zeroPlane U ∩ H) P.ideal r) = _
  rw [cosupport_recoded]
  rfl

/-- At the shared origin, the padded lower record has first entry one and
its actual next normal contact has first entry two. -/
theorem padded_selected_normal_contact_at_origin :
    ∃ pO : O, pO.val = p ∧
      fstEntry ((canonicalInvariant 3).inv L
        (BlowupTower.refl (X := M)) pO) = 1 ∧
      fstEntry ((canonicalInvariant 3).inv C
        (BlowupTower.refl (X := CMfd.of (n := 3) (⊤ : Opens M))) ⟨pO, mem_univ _⟩) = 2 := by
  obtain ⟨_, _, pO, _, _, _, hp, _, _, _, _, _, _, _, _, hP, _⟩ :=
    joint_positive_nonspecial_first_entries
  exact ⟨pO, hp, hP, padded_selected_normal_contact_fst pO hp⟩

end
end Hironaka.HironakaG1NormalFiniteRecodingExample
