import Hironaka.Resolution.HironakaG10RecenteredMonomialDomain

/-! Recenter at an actual exceptional point with arbitrary tangent coordinates. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG10ArbitraryBaseRecenter
noncomputable section
open BlowupMonomialCharts HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower
  HironakaG10RecenteredMonomialDomain HironakaRealOpenGeometricStrictSaturation

/-- The target is translated by its actual image; no tangent-zero hypothesis. -/
theorem monomial_recentre_arbitrary_tangent {n : ℕ} (k : ℕ) (j : Fin n)
    (v w : ComplexModel n) (hvj : v j = 0) :
    monomial k j (w+v) - monomial k j v =
      actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j (fun i => v i) w := by
  ext i
  by_cases hi : k ≤ i.val
  · by_cases hij : i = j
    · subst i
      simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi,hvj]
    · simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi,hij,hvj]
      ring
  · simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi]

variable (d t : ℕ) (j : Fin t) (v : ComplexModel (d+t)) (hvj : v (j.natAdd d) = 0)

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

include hvj
/-- The actual chart projection after translating both source and target. -/
theorem recentered_projection_arbitrary_tangent (w : ComplexModel (d+t)) :
    monomial d (j.natAdd d) (w+v) =
      actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) (fun i => v i) w +
        monomial d (j.natAdd d) v := by
  have h := monomial_recentre_arbitrary_tangent d (j.natAdd d) v w hvj
  rw [← centre_indices d t] at h
  exact sub_eq_iff_eq_add.mp h

variable (U : Opens (ComplexModel (d+t)))

/-- The genuine target open translated by the actual image of the chosen point. -/
def recenteredTargetOpen : Opens (ComplexModel (d+t)) :=
  ⟨(fun x : ComplexModel (d+t) => x + monomial d (j.natAdd d) v) ⁻¹' U,
    U.isOpen.preimage (continuous_id.add continuous_const)⟩

/-- Membership for arbitrary tangent coordinates, over the translated actual target. -/
theorem recentered_domain_arbitrary_tangent (w : ComplexModel (d+t)) :
    w ∈ realOpenChartDomain d t j (fun i => v i) (recenteredTargetOpen d t j v U) ↔
      monomial d (j.natAdd d) (w+v) ∈ U := by
  change actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) (fun i => v i) w +
    monomial d (j.natAdd d) v ∈ U ↔ _
  rw [← recentered_projection_arbitrary_tangent d t j v hvj]

/-- Source translation at an arbitrary exceptional point is an actual homeomorphism. -/
def arbitraryBaseSourceHomeomorph :
    realOpenChartDomain d t j (fun i => v i) (recenteredTargetOpen d t j v U) ≃ₜ
      monomialSourceOpen d t j U where
  toFun w := ⟨w.val+v, (recentered_domain_arbitrary_tangent d t j v hvj U w.val).mp w.property⟩
  invFun z := ⟨z.val-v, (recentered_domain_arbitrary_tangent d t j v hvj U (z.val-v)).mpr
    (by simpa [monomialSourceOpen] using z.property)⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

/-- The actual base coordinate has no normal component. -/
theorem base_image_normal_zero (i : Fin (d+t)) (hi : d ≤ i.val) :
    monomial d (j.natAdd d) v i = 0 := by
  by_cases hij : i = j.natAdd d
  · subst i
    simp [monomial_apply,hvj]
  · simp [monomial_apply,hi,hij,hvj]

/-- Source recentering at an arbitrary exceptional point is biholomorphic. -/
def arbitraryBaseSourceDiffeomorph :
    realOpenChartDomain d t j (fun i => v i) (recenteredTargetOpen d t j v U) ≃ₘ⟮
      𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ monomialSourceOpen d t j U where
  toFun := arbitraryBaseSourceHomeomorph d t j v hvj U
  invFun := (arbitraryBaseSourceHomeomorph d t j v hvj U).symm
  left_inv := (arbitraryBaseSourceHomeomorph d t j v hvj U).left_inv
  right_inv := (arbitraryBaseSourceHomeomorph d t j v hvj U).right_inv
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
    (contMDiff_subtype_val.add contMDiff_const) (fun w =>
      (recentered_domain_arbitrary_tangent d t j v hvj U w.val).mp w.property)
  contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
    (contMDiff_subtype_val.sub contMDiff_const) (fun z =>
      (recentered_domain_arbitrary_tangent d t j v hvj U (z.val-v)).mpr (by
        simpa [monomialSourceOpen] using z.property))

end
end Hironaka.HironakaG10ArbitraryBaseRecenter
