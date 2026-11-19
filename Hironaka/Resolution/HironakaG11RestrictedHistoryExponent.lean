import Hironaka.Resolution.HironakaG8DomainExponents
import Hironaka.MarkedIdeal.HomogenizedGlueingTower

set_option autoImplicit false

/-! A literal test-tower open restriction preserves endpoint exponents. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11RestrictedHistoryExponent
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealOrder DivisorExponentAlong
  MarkedIdealOperationsAlong.MarkedIdeal

/-- The exponent along a literal strict member at an endpoint is unchanged
by restricting the starting test tower to an open neighbourhood of its
projection. -/
theorem divExpAlong_restricted_test_history
    {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (U : Opens X) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (D : Set X) (y : openPreimage T U) :
    divExpAlong n (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).N
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).ideal
      (strictAlong (restrict U T) ((Subtype.val : U → X) ⁻¹' D)) y =
    divExpAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal (strictAlong T D) y.val := by
  obtain ⟨_,hc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    hM.isClosedSubmanifold_N hM.isCoherent T hT
  let V := openPreimage T U
  have hcos : ∀ e, cosupport n ((Subtype.val : V → Y) ⁻¹' (geoTransformAlong M T).N)
      (GermIdeal.pullback (m := n) (Subtype.val : V → Y) (geoTransformAlong M T).ideal) e =
        (Subtype.val : V → Y) ⁻¹' cosupport n (geoTransformAlong M T).N (geoTransformAlong M T).ideal e := by
    intro e
    exact cosupp_pullback_val (⟨(geoTransformAlong M T).N,[],(geoTransformAlong M T).ideal,e⟩ : MarkedIdeal n Y)
      (hol_of_isCoherent hc) V
  have hmap : Filter.map (Subtype.val : V → Y) (𝓝 y) = 𝓝 (y : Y) :=
    map_nhds_subtype_coe_eq_nhds y.2 (V.isOpen.mem_nhds y.2)
  rw [geoTransformAlong_restrict U hM.isClosedSubmanifold_N hM.isCoherent T hT,
    strictAlong_restrict U T D]
  exact MonomialInvariantFunctorialAlong.divExpAlong_pullback hcos hmap (strictAlong T D)

end Hironaka.HironakaG11RestrictedHistoryExponent
