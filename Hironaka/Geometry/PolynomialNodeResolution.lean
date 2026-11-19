import Hironaka.Geometry.NodeBlowupRegular

/-!
# Concrete native resolutions over polynomial bases

Coordinate derivatives supply the local-parameter hypotheses. The resulting
native blowups require no regularity or parameter certificates from callers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial IsLocalRing

namespace Hironaka.PolynomialNodeResolution

universe u v

open Algebra.NodeBlowupChart

variable (K : Type u) [Field K] {ι : Type v}

/-- Every polynomial coordinate is a local parameter at each prime where it vanishes. -/
theorem coordinate_not_mem_square (i : ι) (p : Ideal (MvPolynomial ι K)) [p.IsPrime]
    (hi : X i ∈ p) :
    algebraMap (MvPolynomial ι K) (Localization.AtPrime p) (X i) ∉
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  apply Geometry.RegularNode.not_mem_square_of_derivation p (pderiv i) hi
  rw [pderiv_X_self]
  exact fun h => (inferInstance : p.IsPrime).ne_top (p.eq_top_iff_one.mpr h)

/-- The actual polynomial node `uv=Xᵢ*Xⱼ`, as a native affine scheme. -/
def polynomialNode (i j : ι) : Scheme :=
  Spec (CommRingCat.of (Node (MvPolynomial ι K) ((X i : MvPolynomial ι K) * X j)))

/-- The actual center `(u,Xᵢ)` in the literal polynomial-node quotient. -/
def polynomialNodeCenter (i j : ι) :
    Ideal (Node (MvPolynomial ι K) ((X i : MvPolynomial ι K) * X j)) :=
  centerIdeal (X i : MvPolynomial ι K) (X j)

/-- The native Rees/Proj blowup of the polynomial-node center. -/
def resolvedNode (i j : ι) : Scheme := affineBlowup (polynomialNodeCenter K i j)

/-- The actual structure morphism of the polynomial-node blowup. -/
def resolutionMorphism (i j : ι) : resolvedNode K i j ⟶ polynomialNode K i j :=
  affineBlowupStructure (polynomialNodeCenter K i j)

/-- The polynomial-node blowup is projective, with nonzero coordinates proved internally. -/
theorem resolution_isProjective (i j : ι) :
    IsProjectiveOver (resolutionMorphism K i j) := by
  let : Fact ((X i : MvPolynomial ι K) ≠ 0) := ⟨X_ne_zero i⟩
  let : Fact ((X j : MvPolynomial ι K) ≠ 0) := ⟨X_ne_zero j⟩
  exact NodeBlowupRegular.nodeBlowup_isProjective (X i : MvPolynomial ι K) (X j)

/-- The actual structure morphism is an alteration, without a caller domain or center certificate. -/
theorem resolution_isAlteration (i j : ι) : IsAlteration (resolutionMorphism K i j) := by
  let : Fact ((X i : MvPolynomial ι K) ≠ 0) := ⟨X_ne_zero i⟩
  let : Fact ((X j : MvPolynomial ι K) ≠ 0) := ⟨X_ne_zero j⟩
  exact NodeBlowupRegular.nodeBlowup_isAlteration (X i : MvPolynomial ι K) (X j)

variable [Finite ι]

/-- Both coordinate-parameter hypotheses and regularity of the polynomial base are derived. -/
theorem resolution_isRegular (i j : ι) : IsRegularScheme (resolvedNode K i j) := by
  let : Fact ((X i : MvPolynomial ι K) ≠ 0) := ⟨X_ne_zero i⟩
  let : Fact ((X j : MvPolynomial ι K) ≠ 0) := ⟨X_ne_zero j⟩
  exact NodeBlowupRegular.nodeBlowup_isRegular (X i : MvPolynomial ι K) (X j)
    (fun p _ hp => coordinate_not_mem_square K i p hp)
    (fun p _ hp => coordinate_not_mem_square K j p hp)

/-- A concrete regular projective alteration of `uv=Xᵢ*Xⱼ`, including `i=j`. -/
theorem regular_projective_alteration (i j : ι) :
    IsRegularScheme (resolvedNode K i j) ∧
      IsProjectiveOver (resolutionMorphism K i j) ∧ IsAlteration (resolutionMorphism K i j) :=
  ⟨resolution_isRegular K i j, resolution_isProjective K i j, resolution_isAlteration K i j⟩

omit [Finite ι] in
/-- An explicit crossing-node resolution over the two-variable polynomial ring. -/
theorem crossing_regular_projective_alteration :
    IsRegularScheme (resolvedNode K (0 : Fin 2) 1) ∧
      IsProjectiveOver (resolutionMorphism K (0 : Fin 2) 1) ∧
        IsAlteration (resolutionMorphism K (0 : Fin 2) 1) :=
  regular_projective_alteration K (0 : Fin 2) 1

omit [Finite ι] in
/-- An explicit repeated-coordinate resolution, with original equation `uv=X₀²`. -/
theorem repeated_regular_projective_alteration :
    IsRegularScheme (resolvedNode K (0 : Fin 2) 0) ∧
      IsProjectiveOver (resolutionMorphism K (0 : Fin 2) 0) ∧
        IsAlteration (resolutionMorphism K (0 : Fin 2) 0) :=
  regular_projective_alteration K (0 : Fin 2) 0

end Hironaka.PolynomialNodeResolution
