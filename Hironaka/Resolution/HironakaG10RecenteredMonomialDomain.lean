import Hironaka.Resolution.HironakaRealOpenGeometricStrictSaturation
import Hironaka.Resolution.HironakaActualSmoothCentreBlowupCoordinates

/-! Literal recentering of a monomial chart over its genuine open target. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG10RecenteredMonomialDomain
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupMonomialCharts BlowupStrictSubmanifold HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower
  HironakaActualSmoothCentreBlowupCoordinates HironakaRealOpenGeometricStrictSaturation

variable (d t : ℕ) (j : Fin t) (v : ComplexModel (d+t))
variable (hvt : ∀ i : Fin (d+t), i.val < d → v i = 0) (hvj : v (j.natAdd d) = 0)

private theorem centre_indices : actualTangentCentreVariables d t = {i : Fin (d+t) | d ≤ i.val} := by
  ext i
  simp only [actualTangentCentreVariables, Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, rfl⟩
    simp
  · intro hi
    refine ⟨⟨i.val - d, by omega⟩, ?_⟩
    apply Fin.ext
    simp
    omega

include hvt hvj

/-- The uncentered monomial projection is the literal recentered projection. -/
theorem recentered_projection (w : ComplexModel (d+t)) :
    monomial d (j.natAdd d) (w+v) =
      actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) (fun i => v i) w := by
  have h := actual_smooth_centre_monomial_recentre d (j.natAdd d) v (w+v) hvt hvj
  simpa [centre_indices, add_sub_cancel_right] using h

variable (U : Opens (ComplexModel (d+t)))

/-- Membership uses the entire actual open target, with no global extension. -/
theorem recentered_domain_iff (w : ComplexModel (d+t)) :
    w ∈ realOpenChartDomain d t j (fun i => v i) U ↔
      monomial d (j.natAdd d) (w+v) ∈ U := by
  change actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) (fun i => v i) w ∈ U ↔ _
  rw [← recentered_projection d t j v hvt hvj]

/-- The genuine uncentered source-open over the same target. -/
def monomialSourceOpen : Opens (ComplexModel (d+t)) :=
  ⟨monomial d (j.natAdd d) ⁻¹' U, U.isOpen.preimage (contDiff_monomial d (j.natAdd d)).continuous⟩

/-- Translation is a homeomorphism of the two actual source opens. -/
def recenteredSourceHomeomorph :
    realOpenChartDomain d t j (fun i => v i) U ≃ₜ monomialSourceOpen d t j U where
  toFun w := ⟨w.val+v, (recentered_domain_iff d t j v hvt hvj U w.val).mp w.property⟩
  invFun z := ⟨z.val-v, (recentered_domain_iff d t j v hvt hvj U (z.val-v)).mpr (by simpa [monomialSourceOpen] using z.property)⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

/-- The uncentered monomial chart over the same target. -/
def monomialProjection (z : monomialSourceOpen d t j U) : U :=
  ⟨monomial d (j.natAdd d) z.val, z.property⟩

/-- Both projections are literally equal after the source translation. -/
theorem recentered_projection_square (w : realOpenChartDomain d t j (fun i => v i) U) :
    monomialProjection d t j U (recenteredSourceHomeomorph d t j v hvt hvj U w) =
      realOpenProjection d t j (fun i => v i) U w := by
  apply Subtype.ext
  exact recentered_projection d t j v hvt hvj w.val

/-- The full geometric strict subset transports along the same homeomorphism. -/
theorem recentered_strict_transform (W : Set U) :
    realOpenStrictTransform d t j (fun i => v i) U W =
      (recenteredSourceHomeomorph d t j v hvt hvj U) ⁻¹'
        geoStrictTransform (monomialProjection d t j U)
          ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) W := by
  unfold realOpenStrictTransform geoStrictTransform
  have hfun : realOpenProjection d t j (fun i => v i) U =
      (monomialProjection d t j U) ∘ (recenteredSourceHomeomorph d t j v hvt hvj U) := by
    funext w
    exact (recentered_projection_square d t j v hvt hvj U w).symm
  rw [hfun, preimage_comp]
  exact ((recenteredSourceHomeomorph d t j v hvt hvj U).preimage_closure _).symm

end
end Hironaka.HironakaG10RecenteredMonomialDomain
