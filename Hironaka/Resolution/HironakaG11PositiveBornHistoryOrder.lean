import Hironaka.Resolution.HironakaG11PositiveBornCentreOrder
import Hironaka.Resolution.HironakaG11OldBoundaryExponentHistory

set_option autoImplicit false

/-! Positive coefficient exponent at the endpoint of the actual suffix
forces above-mark source order along the birth centre. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11PositiveBornHistoryOrder
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder DivisorExponentAlong
  ResolutionInvariantSpec InvDomainTowerAlong MemberInterTowerAlong
  HironakaG11PositiveBornCentreOrder HironakaG11OldBoundaryExponentHistory

/-- Positive exponent along the literal strict born member after any test
suffix forces the original ideal above its mark near the birth centre. -/
theorem above_mark_on_centre_of_positive_born_history
    {n : ℕ} {X Y Z : CMfd.{0} n} (M : MarkedIdeal n X) {k : ℕ}
    (hM : IsInvDomain k M) {C : Set X} (hC : M.IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong n C π)
    (T : BlowupTower Y Z) (hT : IsGeoTestTower (M.geoTransform C π) T)
    {z : Z} (hzN : z ∈ (geoTransformAlong (M.geoTransform C π) T).N)
    (hzD : z ∈ strictAlong T (π ⁻¹' C))
    (hpos : 0 < divExpAlong n (geoTransformAlong (M.geoTransform C π) T).N
      (geoTransformAlong (M.geoTransform C π) T).ideal (strictAlong T (π ⁻¹' C)) z) :
    ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ cosupport n M.N M.ideal (M.d+1) := by
  have hStep : IsGeoTestTower M (BlowupTower.step (.refl : BlowupTower X X) C π hπ) := ⟨trivial,hC⟩
  have hDom : IsInvDomain k (M.geoTransform C π) := by
    exact isInvDomain_geoTransformAlong hM _ hStep
  have hmem : π ⁻¹' C ∈ (M.geoTransform C π).E := by
    change π ⁻¹' C ∈ M.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    simp
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hmem
  have hNprev : T.proj z ∈ (M.geoTransform C π).N :=
    strictAlong_subset_preimage T (isClosed_closure : IsClosed (M.geoTransform C π).N) (by
      rwa [N_geoTransformAlong] at hzN)
  have hDprev : π (T.proj z) ∈ C :=
    strictAlong_subset_preimage T (hπ.1.1.preimage hπ.contMDiff.continuous) hzD
  have heq := old_exponent_along_test_history (M.geoTransform C π) hDom i T hT hzN (by simpa only [hi] using hzD)
  rw [hi] at heq
  have hb : 0 < divExpAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (π ⁻¹' C) (T.proj z) := by
    rw [← heq]
    exact hpos
  exact above_mark_on_centre_of_positive_born M hM hC hπ hNprev hDprev hb

end Hironaka.HironakaG11PositiveBornHistoryOrder
