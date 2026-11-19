import Hironaka.Geometry.ProjectiveProjectionCenterPoint

/-!
# Original homogeneous evaluation and the actual vector-point prime

The finite-support scaling calculation is adapted from
BingWangEntropy/PolynomialProjectiveCanonical.lean, SHA256
f230ecbe89cd559e8d9a4cb7687561af69d6b237e0795b1ba4f8a0945b6e62d9.
No source-project imports or analytic assumptions are introduced.
-/

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace Hironaka.Geometry.ProjectiveRationalPointCoordinates

open ProjectiveIdeal ProjectiveProjectionCenter

/-- Scaling all original variables scales actual homogeneous evaluation by the degree power. -/
theorem homogeneous_eval₂_scaled {R S I : Type*} [CommSemiring R] [CommSemiring S]
    {F : MvPolynomial I R} {d : ℕ} (hF : F.IsHomogeneous d)
    (f : R →+* S) (g : I → S) (c : S) :
    MvPolynomial.eval₂Hom f (fun i => c * g i) F = c ^ d * MvPolynomial.eval₂Hom f g F := by
  classical
  rw [← F.support_sum_monomial_coeff, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hF.degree_eq_sum_deg_support he]
  ac_rfl

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- Original homogeneous vector substitution is its original scalar value times the actual pure degree term. -/
theorem vectorGradedMap_homogeneous (v : Fin (n + 2) → k)
    {F : MvPolynomial (Fin (n + 2)) k} {d : ℕ} (hF : F.IsHomogeneous d) :
    vectorGradedMap k n v F = C (MvPolynomial.eval v F) * (X () : MvPolynomial Unit k) ^ d := by
  have hmap : MvPolynomial.eval₂Hom (C : k →+* MvPolynomial Unit k) (fun i => C (v i)) =
      (C : k →+* MvPolynomial Unit k).comp (MvPolynomial.eval v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  change MvPolynomial.eval₂Hom C (fun i => C (v i) * X ()) F = _
  calc
    _ = MvPolynomial.eval₂Hom C (fun i => X () * C (v i)) F := by
      apply congrArg (fun g : Fin (n + 2) → MvPolynomial Unit k => MvPolynomial.eval₂Hom C g F)
      funext i
      exact mul_comm _ _
    _ = X () ^ d * MvPolynomial.eval₂Hom C (fun i => C (v i)) F :=
      homogeneous_eval₂_scaled hF _ _ _
    _ = _ := by rw [hmap, RingHom.comp_apply, mul_comm]

/-- The actual vector-point homogeneous prime detects precisely the original homogeneous vector equations. -/
theorem vectorPoint_mem_homogeneous (v : Fin (n + 2) → k) (hv : v ≠ 0)
    {F : MvPolynomial (Fin (n + 2)) k} {d : ℕ} (hF : F.IsHomogeneous d) :
    F ∈ (vectorPoint k n v hv).asHomogeneousIdeal ↔ MvPolynomial.eval v F = 0 := by
  change vectorGradedMap k n v F = 0 ↔ _
  rw [vectorGradedMap_homogeneous k n v hF]
  simp [pow_ne_zero d (MvPolynomial.X_ne_zero ())]

end Hironaka.Geometry.ProjectiveRationalPointCoordinates
