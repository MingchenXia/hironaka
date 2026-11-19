import Hironaka.Resolution.HironakaActualPolymorphicBornExponent

set_option autoImplicit false

/-! A positive exponent on the newly born divisor forces above-mark
coefficient order along a neighbourhood of the centre. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11PositiveBornCentreOrder
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  DivisorExponentAlong ResolutionInvariantSpec MarkedIdealOperationsAlong.MarkedIdeal
  HironakaActualPolymorphicBornExponent

/-- If the exponent at a genuine birth is positive, the source ideal has
order at least one above its mark on the centre near the birth projection. -/
theorem above_mark_on_centre_of_positive_born
    {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X) {k : ℕ}
    (hM : IsInvDomain k M) {C : Set X} (hC : M.IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y}
    (hzN : z ∈ (M.geoTransform C π).N) (hzC : π z ∈ C)
    (hpos : 0 < divExpAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (π ⁻¹' C) z) :
    ∀ᶠ x in 𝓝 (π z), x ∈ C → x ∈ cosupport n M.N M.ideal (M.d+1) := by
  have hb := original_history_born_exponent M hM (BlowupTower.refl : BlowupTower X X) trivial hC hπ hzN hzC
  have hgt : M.d + 1 ≤ divExpAlong n M.N M.ideal C (π z) := by
    change M.d ≤ divExpAlong n M.N M.ideal C (π z) ∧
      divExpAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal (π ⁻¹' C) z =
        divExpAlong n M.N M.ideal C (π z)-M.d at hb
    omega
  have hdiv := (isDivNearAlong_divExpAlong (hol_of_isCoherent hM.isWellFormed.isCoherent) (π z)).mono hgt
  filter_upwards [hdiv] with x hx hxC
  exact hx (hC.subset_N hxC) hxC

end Hironaka.HironakaG11PositiveBornCentreOrder
