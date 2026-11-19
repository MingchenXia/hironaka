import Hironaka.Resolution.HironakaG10ArbitraryBaseRecenter

/-! Actual geometric strict carrier at arbitrary tangent base coordinates. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG10ArbitraryBaseStrict
noncomputable section
open Hironaka.BlowupSequences BlowupMonomialCharts BlowupStrictSubmanifold
  HironakaRealOpenGeometricStrictSaturation HironakaG10RecenteredMonomialDomain
  HironakaG10ArbitraryBaseRecenter

variable (d t : ℕ) (j : Fin t) (v : ComplexModel (d+t)) (hvj : v (j.natAdd d) = 0)
variable (U : Opens (ComplexModel (d+t)))

/-- Target translation by the actual base image. -/
def arbitraryBaseTargetMap (x : recenteredTargetOpen d t j v U) : U :=
  ⟨x.val + monomial d (j.natAdd d) v, x.property⟩

include hvj

/-- Translation by the actual base image preserves the original centre. -/
theorem target_translation_centre (x : ComplexModel (d+t)) :
    x + monomial d (j.natAdd d) v ∈ complexCoordinatePlane (d+t) d ↔
      x ∈ complexCoordinatePlane (d+t) d := by
  change (∀ i : Fin (d+t), d ≤ i.val → (x + monomial d (j.natAdd d) v) i = 0) ↔
    ∀ i : Fin (d+t), d ≤ i.val → x i = 0
  constructor
  · intro h i hi
    have hzero := base_image_normal_zero d t j v hvj i hi
    have hh := h i hi
    change x i + monomial d (j.natAdd d) v i = 0 at hh
    rw [hzero,add_zero] at hh
    exact hh
  · intro h i hi
    have hzero := base_image_normal_zero d t j v hvj i hi
    have hh := h i hi
    change x i + monomial d (j.natAdd d) v i = 0
    rw [hzero,add_zero]
    exact hh

/-- The genuine projections intertwine under the two actual translations. -/
theorem arbitraryBase_projection_square
    (w : realOpenChartDomain d t j (fun i => v i) (recenteredTargetOpen d t j v U)) :
    arbitraryBaseTargetMap d t j v U
      (realOpenProjection d t j (fun i => v i) (recenteredTargetOpen d t j v U) w) =
    monomialProjection d t j U (arbitraryBaseSourceHomeomorph d t j v hvj U w) := by
  apply Subtype.ext
  exact (recentered_projection_arbitrary_tangent d t j v hvj w.val).symm

/-- The full strict subsets agree, with closure in their actual source opens. -/
theorem arbitraryBaseStrictTransform (W : Set U) :
    realOpenStrictTransform d t j (fun i => v i) (recenteredTargetOpen d t j v U)
      ((arbitraryBaseTargetMap d t j v U) ⁻¹' W) =
    (arbitraryBaseSourceHomeomorph d t j v hvj U) ⁻¹'
      geoStrictTransform (monomialProjection d t j U)
        ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) W := by
  unfold realOpenStrictTransform geoStrictTransform
  have hpre : (realOpenProjection d t j (fun i => v i) (recenteredTargetOpen d t j v U)) ⁻¹'
      (((arbitraryBaseTargetMap d t j v U) ⁻¹' W) \
       ((Subtype.val : recenteredTargetOpen d t j v U → ComplexModel (d+t)) ⁻¹'
         complexCoordinatePlane (d+t) d)) =
      (arbitraryBaseSourceHomeomorph d t j v hvj U) ⁻¹'
        ((monomialProjection d t j U) ⁻¹'
          (W \ ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d))) := by
    ext w
    change ((arbitraryBaseTargetMap d t j v U
      (realOpenProjection d t j (fun i => v i) (recenteredTargetOpen d t j v U) w) ∈ W) ∧
        ¬ (realOpenProjection d t j (fun i => v i) (recenteredTargetOpen d t j v U) w).val ∈
          complexCoordinatePlane (d+t) d) ↔ _
    rw [arbitraryBase_projection_square d t j v hvj U w]
    have hc := target_translation_centre d t j v hvj
      (realOpenProjection d t j (fun i => v i) (recenteredTargetOpen d t j v U) w).val
    have hs := arbitraryBase_projection_square d t j v hvj U w
    have hv := congrArg Subtype.val hs
    change (realOpenProjection d t j (fun i => v i) (recenteredTargetOpen d t j v U) w).val +
      monomial d (j.natAdd d) v = _ at hv
    rw [hv] at hc
    exact and_congr_right (fun _ => not_congr hc.symm)
  rw [hpre]
  exact ((arbitraryBaseSourceHomeomorph d t j v hvj U).preimage_closure _).symm

end
end Hironaka.HironakaG10ArbitraryBaseStrict
