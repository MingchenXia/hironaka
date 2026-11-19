import Hironaka.Resolution.HironakaG1AdvancingSupportedContactExponents
import Hironaka.Resolution.HironakaG8ScaledExponentHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1AdvancingBornControlledTrace
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres TangentDirectionAlong
  HomogenizedIdealAlong CoefficientIdealRestriction DivisorExponentAlong GermIdealOrder
  InvDomainTowerAlong ContactStageKept
  StepOneValue HironakaG8LocalHistory HironakaG8GapNormalizedExponent HironakaG8ScaledExponentHistory
  HironakaG1AdvancingSupportedBornContact HironakaG1AdvancingSupportedContactExponents
  RelativePrincipalizationSpan MonomialInvariantFunctorialAlong MarkedIdealOperationsAlong.MarkedIdeal
  MaximalContactAlongTower
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)

set_option maxHeartbeats 1900000 in
/-- Controlled exponent transport of the original bare pair supplies the
born trace condition if the refreshed coefficient germs restrict into the
controlled bare germs on the offending divisor trace. This comparison
uses only their restrictions to that trace, with no equality of marks
or ideals and no advanced supported cosupport gap. -/
theorem advancing_supported_canonical_of_born_controlled_trace {n k l : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K P : MarkedIdeal n X)
    (hK : IsInvDomain k K) (hP : IsInvDomain l P) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = P.N)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked K) H) (O : Opens Y) :
    let A := CMfd.of (n := n) O
    let C := withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})
    let D := contactMarkedKept K u H O
    let C' := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong C H)
    let P' := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong P H)
    IsInvDomain l C → LocWPEquiv C P → HasCosupportGap P →
    (∀ F ∈ C.E, ∀ z ∈ C.cosupp, z ∈ F →
      P.d * divExpAlong n C.N C.ideal F z = C.d * divExpAlong n P.N P.ideal F z) →
    (∀ F ∈ D.E, ∀ z ∈ D.cosupp, z ∈ F →
      (¬ ∃ i : Fin P.E.length, F = (Subtype.val : O → Y) ⁻¹' strictAlong H (P.E.get i)) →
      divExpAlong n D.N D.ideal F z = 0 → 0 < divExpAlong n P'.N P'.ideal F z →
      ∀ᶠ w in 𝓝 z, ∀ g, D.ideal.mem w g →
        IsInSpanOnAt (n := n) (D.N ∩ F) (C'.ideal.mem w) w g) →
    (∀ F ∈ D.E, ∀ z ∈ D.cosupp, z ∈ F →
      P'.d * divExpAlong n D.N D.ideal F z = D.d * divExpAlong n P'.N P'.ideal F z) ∧
    ∀ {Z : CMfd.{0} n} (T : BlowupTower A Z),
      IsCanonical D ((invFamily hn l).inv D) T ↔ IsCanonical P' ((invFamily hn l).inv P') T := by
  intro A C D C' P' hC hClass hGap hInitial hComparison
  obtain ⟨hHP, hD, hP', hDP, hDE, _, hDClass, hDGap⟩ :=
    advancing_kept_contact_supported_stage K P hK hP u hu hTrace hClass H hH O
  have hHC := ((hClass.wEquiv.2 H).1).mpr hHP
  let M := geoTransformAlong C H
  let N := geoTransformAlong P H
  have hM := isInvDomain_geoTransformAlong hC H hHC
  have hN := isInvDomain_geoTransformAlong hP H hHP
  have hCP : C.N = P.N := hTrace
  have hStage := (hClass.geoTransformAlong H hHC).restrict O
  have hCD : C'.N = D.N := by
    have hCP' : C'.N = P'.N := by
      change (Subtype.val : O → Y) ⁻¹' M.N = (Subtype.val : O → Y) ⁻¹' N.N
      rw [show M.N = strictAlong H C.N from N_geoTransformAlong C H,
        show N.N = strictAlong H P.N from N_geoTransformAlong P H, hCP]
    exact hCP'.trans hDP.symm
  have hHistory := scaled_exponents_of_initial_agreement C P hC hP hCP.symm
    hClass.wEquiv.1.symm hClass hInitial H hHC
  have hHolM : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  have hHolN : ∀ x g, N.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hN.isWellFormed.isCoherent hg
  have hHolC' : ∀ x g, C'.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
      (isInvDomain_pullback_val O hM).isWellFormed.isCoherent hg
  apply advancing_supported_canonical_of_new_trace hn K P hK hP u hu hTrace hClass hGap H hH O
  intro F hF z hz hzF hNew hD0 hPosP
  have hFE : F ∈ P'.E := hDE ▸ hF
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hFE
  have hGM : G ∈ M.E := (hClass.geoTransformAlong H hHC).wEquiv.1.symm ▸ hG
  have hzP' : z ∈ P'.cosupp := hDClass.cosupp_eq_base ▸ hz
  have hzC' : z ∈ C'.cosupp := hStage.cosupp_eq_base.symm ▸ hzP'
  have hzM : z.val ∈ M.cosupp :=
    Set.ext_iff.mp (MarkedIdealRestrictOpen.cosupp_pullback_val M hHolM O) z |>.mp hzC'
  have hMap := map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (O : Set Y))
    z.property (O.isOpen.mem_nhds z.property)
  have hExpM : divExpAlong n C'.N C'.ideal ((Subtype.val : O → Y) ⁻¹' G) z =
      divExpAlong n M.N M.ideal G z.val :=
    divExpAlong_pullback (φ := (Subtype.val : O → Y))
      (fun e => MarkedIdealRestrictOpen.cosupp_pullback_val
        (⟨M.N, [], M.ideal, e⟩ : MarkedIdeal n Y) hHolM O) hMap _
  have hExpN : divExpAlong n P'.N P'.ideal ((Subtype.val : O → Y) ⁻¹' G) z =
      divExpAlong n N.N N.ideal G z.val :=
    divExpAlong_pullback (φ := (Subtype.val : O → Y))
      (fun e => MarkedIdealRestrictOpen.cosupp_pullback_val
        (⟨N.N, [], N.ideal, e⟩ : MarkedIdeal n Y) hHolN O) hMap _
  have hScaled := hHistory G hGM z.val hzM hzF
  rw [← hExpM, ← hExpN] at hScaled
  have hPosC : 0 < divExpAlong n C'.N C'.ideal ((Subtype.val : O → Y) ⁻¹' G) z := by
    by_contra! hZero
    rw [Nat.eq_zero_of_le_zero hZero, Nat.mul_zero] at hScaled
    exact (Nat.ne_of_gt (Nat.mul_pos hC.one_le_d hPosP)) hScaled.symm
  have hNear := isDivNearAlong_divExpAlong (N := C'.N) (H := (Subtype.val : O → Y) ⁻¹' G) hHolC' z
  have hInc := hComparison _ hF z hz hzF hNew hD0 hPosP
  filter_upwards [hNear, hInc] with w hw hSpan hwN hwF
  have hwC : w ∈ C'.N := hCD.symm ▸ hwN
  have hwCos := cosupport_anti hPosC (hw hwC hwF)
  apply hDGap w hwN
  refine ⟨hwN, fun g hg => ?_⟩
  have hghol := GermIdeal.IsCoherent.holomorphicAt_mem hD.isWellFormed.isCoherent hg
  apply (vanishesToOrderOn_one_iff hwN hghol).mpr
  exact apply_eq_zero_of_isInSpanOnAt
    (W := D.N ∩ (Subtype.val : O → Y) ⁻¹' G) ⟨hwN, hwF⟩
    (fun s hs => (vanishesToOrderOn_one_iff hwC (hHolC' _ _ hs)).mp (hwCos.2 s hs)) (hSpan g hg)

end
end Hironaka.HironakaG1AdvancingBornControlledTrace
