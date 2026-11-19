import Hironaka.Resolution.HironakaG1PositiveNormalRepairDepth
import Hironaka.Resolution.HironakaSharpActualCurveStageComparison

/-! The padded maximum criterion and section/native depths on one selected repair. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1NormalSpecialStepValues

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres RelativePrincipalizationSpan
  HironakaActualNativeSectionFiniteHistory HironakaActualSectionBoundaryGeometry
  HironakaActualOpenZeroSectionDifferentials HironakaDisjointNativeOpenLift
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1PositiveNormalPhase
  HironakaG1ProperNormalPhaseNative HironakaActualNativeSectionInitialBar
  HironakaG1RecursiveMemberValueTransport HironakaG1PositiveNormalRepairDepth
  HironakaG1PositiveNormalRepairCentres MemberInterLocusAlong BoundaryCount
  StepOneValue StepOneValueMasked InvDomainMemberRestriction
open HomogenizedIdealAlong HomogenizedGlueingTower

private theorem repair_avoidance_of_same_centre {n : ℕ} {X Y Z : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) {D : Set X} (hD : M.IsAdmissibleCentre D)
    {π : Y → X} {ρ : Z → X} (hπ : IsBlowupAlong n D π) (hρ : IsBlowupAlong n D ρ)
    (hAvoid : (M.geoTransform D ρ).cosupp ⊆ ρ ⁻¹' Dᶜ) :
    (M.geoTransform D π).cosupp ⊆ π ⁻¹' Dᶜ := by
  let idX := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞
  have hπ' : IsBlowupAlong n (idX ⁻¹' D) π := hπ
  obtain ⟨e, he, _⟩ :=
    HironakaSharpActualCurveStageComparison.exists_unique_stage_blowup_comparison idX hπ' hρ
  have hComp : ρ ∘ e = π := funext he
  have hNew : (M.geoTransform D ρ).IsWellFormed :=
    GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hM hD hρ
  have hRecord := BlowupBiholomorphismLift.geoTransform_comp_diffeo e M hM.isCoherent D
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hρ.1) hρ.contMDiff hNew.isCoherent
  rw [hComp] at hRecord
  have hCos : (M.geoTransform D π).cosupp = e ⁻¹' (M.geoTransform D ρ).cosupp := by
    rw [hRecord, MarkedIdealTowerTransport.cosupp_pullback_eq hNew.isCoherent]
  intro z hz
  have hz' : e z ∈ (M.geoTransform D ρ).cosupp := (Set.ext_iff.mp hCos z).mp hz
  have hzOff : ρ (e z) ∈ Dᶜ := hAvoid hz'
  change π z ∈ Dᶜ
  have hProj : ρ (e z) = π z := he z
  rwa [hProj] at hzOff

/-- The same actual selected repair supports the padded maximum criterion
and exact adjacent-depth comparison of repaired section/native continuations. -/
theorem positive_normal_special_repair_values {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) H p)
    (hSpecial : IsSpecial (sectionMarked Q) H p) :
    let O := maskA (properNormalMarked Q) H p
    let W := openSection (strictAlong H (zeroPlane U)) O
    let M := MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong (barMarked (sectionMarked Q)) H)
    let J := positiveMemberOn (sectionMarked Q) H p O
    let L := lowerMarkedM (properNormalMarked Q) (s + 1) H p
    ∃ (hWc : IsClosed W) (hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n)
      (q : nativeManifold (Nat.le_succ n) W hW),
      let A := nativePullback (Nat.le_succ n) W hW M
      let E := ((origMembers (sectionMarked Q) H).map ((Subtype.val : O → Y) ⁻¹' ·)).map
        ((Subtype.val : W → O) ⁻¹' ·)
      let C := memberInterLocus A.N E A.cosupp ∩ {z | boundaryCount E z = s + 1}
      let D := (Subtype.val : W → O) '' C
      q.val.val = p ∧ q ∈ C ∧ L.IsAdmissibleCentre D ∧
      ∃ (Z : CMfd.{0} (n + 1)) (π : Z → O) (hπ : IsBlowupAlong (n + 1) D π),
        let V := geoStrictTransform π D W
        let hV := strictRegular hWc hW C π hπ
        let J' := J.geoTransform D π
        let ρ := nativeProjection (Nat.le_succ n) hWc hW C π hπ
        let K := memberRestrict A (membersThrough A.E E q)
        IsBlowupAlong n C ρ ∧
        K.geoTransform C ρ = nativePullback (Nat.le_succ n) V hV J' ∧
        RepairDepthData k (Nat.le_succ n) V hV J' ∧
        RepairCentreComparison k (Nat.succ_pos n) L D q.val π hπ ∧
        π '' ((Subtype.val : V → Z) '' (K.geoTransform C ρ).cosupp) = L.cosupp \ D := by
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let O := maskA P H p
  let W := openSection (strictAlong H (zeroPlane U)) O
  let M := MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong (barMarked Sec) H)
  let J := positiveMemberOn Sec H p O
  let L := lowerMarkedM P (s + 1) H p
  obtain ⟨hWc, hW, q, hqp, hq, hD, Z, π, hπ, hρ, hRecord, hDepth⟩ :=
    positive_normal_repair_depth_data Q hQ H hH p hLevel hNS hSpecial
  let A := nativePullback (Nat.le_succ n) W hW M
  let E := ((origMembers Sec H).map ((Subtype.val : O → Y) ⁻¹' ·)).map
    ((Subtype.val : W → O) ⁻¹' ·)
  let C := memberInterLocus A.N E A.cosupp ∩ {z | boundaryCount E z = s + 1}
  let D := (Subtype.val : W → O) '' C
  obtain ⟨D₀, _, Z₀, π₀, hπ₀, _, _, _, hAvoid₀, _, hCentre₀⟩ :=
    positive_normal_repair_geometry Q hQ H hH p hLevel hNS hSpecial
  have hCentre : D₀ = D := hCentre₀
  have hπ₀' : IsBlowupAlong (n + 1) D π₀ := hCentre ▸ hπ₀
  have hAvoid₀' : (L.geoTransform D π₀).cosupp ⊆ π₀ ⁻¹' Dᶜ := hCentre ▸ hAvoid₀
  have hL : IsInvDomain k L := padded_lower_isInvDomain Q hQ H hH p hLevel
  have hAvoid : (L.geoTransform D π).cosupp ⊆ π ⁻¹' Dᶜ :=
    repair_avoidance_of_same_centre (X := CMfd.of (n := n + 1) O) (Y := Z) (Z := Z₀)
      L hL.isWellFormed (D := D) hD hπ hπ₀' hAvoid₀'
  have hComp : RepairCentreComparison k (Nat.succ_pos n) L D q.val π hπ :=
    repair_centre_criterion (X := CMfd.of (n := n + 1) O) (Z := Z) (Nat.succ_pos n) L hL hD q.val
    (mem_image_of_mem _ hq) π hπ hAvoid
  refine ⟨hWc, hW, q, hqp, hq, hD, Z, π, hπ, hρ, hRecord, hDepth, hComp, ?_⟩
  let V := geoStrictTransform π D W
  let hV := strictRegular hWc hW C π hπ
  let J' := J.geoTransform D π
  have hHol : ∀ x f, J'.ideal.mem x f → HolomorphicAt (n + 1) f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hDepth.ambient_domain.isWellFormed.isCoherent hf
  rw [hRecord, HironakaActualNativeSectionOrderHistory.cosupp_nativePullback
    (Nat.le_succ n) V hV J' hDepth.support hHol, image_preimage_eq_inter_range, Subtype.range_coe,
    inter_eq_left.mpr (J'.cosupp_subset_N.trans hDepth.support)]
  have hClass := (positive_lower_section_class Q hQ H hH p).1
  let T : BlowupTower (CMfd.of (n := n + 1) O) Z := .step .refl D π hπ
  have hCos : (L.geoTransform D π).cosupp = J'.cosupp :=
    (hClass.wEquiv.2 T).2 (show IsGeoTestTower L T from ⟨trivial, hD⟩)
  rw [← hCos]
  exact hComp.cosupport_image

end Hironaka.HironakaG1NormalSpecialStepValues
