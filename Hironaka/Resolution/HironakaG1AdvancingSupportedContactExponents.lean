import Hironaka.Resolution.HironakaG1AdvancingSupportedBornContact
import Hironaka.Resolution.HironakaActualOriginalLowerOldExponents
import Hironaka.Resolution.HironakaG8TraceCosuppExponent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1AdvancingSupportedContactExponents
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres TangentDirectionAlong
  HomogenizedIdealAlong CoefficientIdealRestriction DivisorExponentAlong GermIdealOrder
  InvDomainTowerAlong ContactStageKept
  StepOneValue HironakaG8LocalHistory HironakaG8GapNormalizedExponent
  HironakaG8TraceCosuppExponent HironakaG1AdvancingSupportedBornContact
  HironakaG1OriginalUnequalMarkCanonical HironakaG11InvBMClass
  RelativePrincipalizationSpan MonomialInvariantFunctorialAlong
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)

private theorem exponent_pullback_open {n : ℕ} {Y : CMfd.{0} n}
    (M : MarkedIdeal n Y) (hM : M.ideal.IsCoherent) (O : Opens Y)
    (F : Set Y) (z : O) :
    let P := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) M
    divExpAlong n P.N P.ideal ((Subtype.val : O → Y) ⁻¹' F) z =
      divExpAlong n M.N M.ideal F z.val := by
  intro P
  refine divExpAlong_pullback (φ := (Subtype.val : O → Y)) (fun e => ?_) ?_ _
  · exact MarkedIdealRestrictOpen.cosupp_pullback_val
      (⟨M.N, [], M.ideal, e⟩ : MarkedIdeal n Y)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM hg) O
  · exact map_nhds_subtype_coe_eq_nhds
      (p := fun x => x ∈ (O : Set Y)) z.property (O.isOpen.mem_nhds z.property)

set_option maxHeartbeats 1100000 in
/-- A positive exponent on a truly inherited slot of the supported
record is at least its original mark even after a genuine test history.
The initial gap is only used at the projected original trace. -/
theorem inherited_supported_exponent_at_least_mark {n l : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain l P) (hGap : HasCosupportGap P)
    (H : BlowupTower X Y) (hH : IsGeoTestTower P H) (O : Opens Y)
    (i : Fin P.E.length) (z : O) :
    let A := CMfd.of (n := n) O
    let R := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong P H)
    let F := (Subtype.val : O → Y) ⁻¹' strictAlong H (P.E.get i)
    z ∈ R.N → z ∈ F → 0 < divExpAlong n R.N R.ideal F z →
      R.d ≤ divExpAlong n R.N R.ideal F z := by
  intro A R F hzN hzF hPos
  let M := geoTransformAlong P H
  have hM := isInvDomain_geoTransformAlong hP H hH
  have hPull := exponent_pullback_open M hM.isWellFormed.isCoherent O (strictAlong H (P.E.get i)) z
  have hHist := (HironakaActualOriginalLowerOldExponents.Generic.initial_old_strict_trace_exponents
    P hP H hH i).1 z.val hzN hzF
  have hExp : divExpAlong n R.N R.ideal F z =
      divExpAlong n P.N P.ideal (P.E.get i) (H.proj z.val) := hPull.trans hHist
  have hN : H.proj z.val ∈ P.N := by
    have hz : z.val ∈ M.N := hzN
    rw [N_geoTransformAlong] at hz
    exact MemberInterTowerAlong.strictAlong_subset_preimage H hP.isWellFormed.isClosedSubmanifold_N.1 hz
  have hF : H.proj z.val ∈ P.E.get i :=
    MemberInterTowerAlong.strictAlong_subset_preimage H
      (hP.isWellFormed.isSNCDivisor.1 _ (List.get_mem _ i)) hzF
  have hOrigPos : 0 < divExpAlong n P.N P.ideal (P.E.get i) (H.proj z.val) := hExp ▸ hPos
  have hTrace := trace_cosupp_of_gap_pos P hP hGap i hN hF hOrigPos
  have hD := (isDivNearAlong_get_iff_le hP.isWellFormed.isClosedSubmanifold_N
    hP.isWellFormed.isCoherent i hN hF (hP.isNonzeroAlongAt _ hN)).mp
    (show IsDivNearAlong n P.N P.ideal (P.E.get i) P.d (H.proj z.val) from hTrace)
  rw [hExp]
  exact (d_geoTransformAlong P H) ▸ hD

set_option maxHeartbeats 1600000 in
/-- The advancing contact needs a trace condition only at newly born
slots where its own exponent vanishes and the supported exponent is
positive. The full advanced cosupport gap is unnecessary. -/
theorem advancing_supported_canonical_of_new_trace {n k l : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K P : MarkedIdeal n X)
    (hK : IsInvDomain k K) (hP : IsInvDomain l P) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = P.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) P)
    (hGap : HasCosupportGap P)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked K) H) (O : Opens Y) :
    let A := CMfd.of (n := n) O
    let D := contactMarkedKept K u H O
    let R := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong P H)
    (∀ F ∈ D.E, ∀ z ∈ D.cosupp, z ∈ F →
      (¬ ∃ i : Fin P.E.length, F = (Subtype.val : O → Y) ⁻¹' strictAlong H (P.E.get i)) →
      divExpAlong n D.N D.ideal F z = 0 → 0 < divExpAlong n R.N R.ideal F z →
      ∀ᶠ w in 𝓝 z, w ∈ D.N → w ∈ F → w ∈ D.cosupp) →
    (∀ F ∈ D.E, ∀ z ∈ D.cosupp, z ∈ F →
      R.d * divExpAlong n D.N D.ideal F z = D.d * divExpAlong n R.N R.ideal F z) ∧
    ∀ {Z : CMfd.{0} n} (T : BlowupTower A Z),
      IsCanonical D ((invFamily hn l).inv D) T ↔ IsCanonical R ((invFamily hn l).inv R) T := by
  intro A D R hNew
  obtain ⟨hHP, hD, hR, hN, hE, _, hL, hGapD⟩ :=
    advancing_kept_contact_supported_stage K P hK hP u hu hTrace hClass H hH O
  have hDim := SameCarrierDim.of_N_eq (X := A) (A := D) (B := R) hN
  have hExp : ∀ F ∈ D.E, ∀ z ∈ D.cosupp, z ∈ F →
      R.d * divExpAlong n D.N D.ideal F z = D.d * divExpAlong n R.N R.ideal F z := by
    intro F hF z hz hzF
    classical
    have hzN := D.cosupp_subset_N hz
    have hzR : z ∈ R.N := hN ▸ hzN
    have hFR : F ∈ R.E := hE ▸ hF
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hF
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hFR
    have hIJ : D.E.get i = R.E.get j := hi.trans hj.symm
    have hzi : z ∈ D.E.get i := hi.symm ▸ hzF
    have hzj : z ∈ R.E.get j := hj.symm ▸ hzF
    by_cases hPos : 0 < divExpAlong n D.N D.ideal F z
    · have hPosi : 0 < divExpAlong n D.N D.ideal (D.E.get i) z := by simpa only [hi] using hPos
      have hT := trace_cosupp_of_gap_pos (X := A) D hD hGapD i hzN hzi hPosi
      simpa only [hi, hj] using normalized_exponent_of_trace_cosupp hn D R hD hR hN hL i j hIJ hzN hzi hT
    have hD0 : divExpAlong n D.N D.ideal F z = 0 := Nat.eq_zero_of_not_pos hPos
    by_cases hPosR : 0 < divExpAlong n R.N R.ideal F z
    · by_cases hOld : ∃ i : Fin P.E.length, F = (Subtype.val : O → Y) ⁻¹' strictAlong H (P.E.get i)
      · obtain ⟨a, ha⟩ := hOld
        have hAtLeast := inherited_supported_exponent_at_least_mark P hP hGap H hHP O a z hzR
          (ha ▸ hzF) (ha ▸ hPosR)
        have hAtLeast' : R.d ≤ divExpAlong n R.N R.ideal (R.E.get j) z := by
          rw [hj, ha]
          exact hAtLeast
        simpa only [hi, hj] using
          (normalized_exponent_of_mark_le hn R D hR hD hN.symm hL.symm j i hIJ.symm hzR hzj hAtLeast').symm
      · have h := hNew F hF z hz hzF hOld hD0 hPosR
        have hT : ∀ᶠ w in 𝓝 z, w ∈ D.N → w ∈ D.E.get i → w ∈ D.cosupp := by
          simpa only [hi] using h
        simpa only [hi, hj] using normalized_exponent_of_trace_cosupp hn D R hD hR hN hL i j hIJ hzN hzi hT
    · rw [hD0, Nat.eq_zero_of_not_pos hPosR, Nat.mul_zero, Nat.mul_zero]
  exact ⟨hExp, fun T => invFamily_isCanonical_iff_of_local hn D R hD hR hL hDim hExp T⟩

end
end Hironaka.HironakaG1AdvancingSupportedContactExponents
