import Hironaka.Resolution.HironakaG10RecenteredMonomialDomain
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal

/-! The source translation is biholomorphic, so it is available for native stalk transport. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG10RecenteredMonomialBiholomorph
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupStrictSubmanifold HironakaActualOpenEmbeddingVanishingIdeal
  HironakaG10RecenteredMonomialDomain HironakaRealOpenGeometricStrictSaturation

variable (d t : ℕ) (j : Fin t) (v : ComplexModel (d+t))
variable (hvt : ∀ i : Fin (d+t), i.val < d → v i = 0) (hvj : v (j.natAdd d) = 0)
variable (U : Opens (ComplexModel (d+t)))

/-- The actual recentering homeomorphism is biholomorphic in both directions. -/
def recenteredSourceDiffeomorph :
    realOpenChartDomain d t j (fun i => v i) U ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯
      monomialSourceOpen d t j U where
  toFun := recenteredSourceHomeomorph d t j v hvt hvj U
  invFun := (recenteredSourceHomeomorph d t j v hvt hvj U).symm
  left_inv := (recenteredSourceHomeomorph d t j v hvt hvj U).left_inv
  right_inv := (recenteredSourceHomeomorph d t j v hvt hvj U).right_inv
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
    (contMDiff_subtype_val.add contMDiff_const) (fun w =>
      (recentered_domain_iff d t j v hvt hvj U w.val).mp w.property)
  contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
    (contMDiff_subtype_val.sub contMDiff_const) (fun z =>
      (recentered_domain_iff d t j v hvt hvj U (z.val-v)).mpr (by
        simpa [monomialSourceOpen] using z.property))

/-- The entire geometric strict vanishing ideal is the literal biholomorphic pullback. -/
theorem recentered_strict_ideal (W : Set U) :
    GermIdeal.pullback (m := d+t) (recenteredSourceDiffeomorph d t j v hvt hvj U)
      (vanishingIdeal (n := d+t) (geoStrictTransform (monomialProjection d t j U)
        ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) W)) =
      realOpenStrictIdeal d t j (fun i => v i) U W := by
  rw [pullback_vanishingIdeal_of_biholomorphism]
  change vanishingIdeal (n := d+t)
    ((recenteredSourceHomeomorph d t j v hvt hvj U) ⁻¹' _) = _
  rw [← recentered_strict_transform d t j v hvt hvj U W]
  rfl

end
end Hironaka.HironakaG10RecenteredMonomialBiholomorph
