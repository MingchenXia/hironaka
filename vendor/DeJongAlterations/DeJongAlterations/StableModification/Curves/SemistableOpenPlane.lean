import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Partial derivatives on a surface étale over the affine plane

Let `R` be a ring and `P` an `R`-algebra which is formally étale over the polynomial ring
`R[X₀, X₁]`; write `uᵢ = coord R P i` for the image of `Xᵢ`. Then `Ω_{P/R}` is free on `du₀, du₁`
(`kaehlerBasis`), so `P` carries partial derivatives `∂ᵢ = planeDerivation R P i` with
`∂ᵢ uⱼ = δᵢⱼ`, and every `R`-derivation of `P` is determined by its values on the coordinates
(`derivation_ext`). Partial derivatives are compatible with every coordinate-preserving algebra map
between such algebras (`planeDerivation_map`), in particular with localization and base change, and
so is the Hessian determinant `hessian R P g = ∂₀∂₀g · ∂₁∂₁g - ∂₀∂₁g · ∂₁∂₀g` (`hessian_map`).

These are the relative objects of the openness of the semi-stable locus (M. Temkin, *Stable
modification of relative curves*, Lemma 5.1(i), T:3282–3292): near a node a family of curves is a
hypersurface `g = 0` in a surface étale over the plane, and the nodes of nearby fibres are the
singular points at which the Hessian of `g` is a unit (blueprint `sm-semistable-curves.tex`).
-/

noncomputable section

open KaehlerDifferential

namespace DeJongAlterations.StableModification.Curves.SemistableOpen

universe u v w

section Coordinates

variable (R : Type u) [CommRing R] (P : Type v) [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]

/-- The coordinate functions `u₀, u₁ ∈ P` (images of `X₀, X₁`). -/
abbrev coord (i : Fin 2) : P := algebraMap (MvPolynomial (Fin 2) R) P (MvPolynomial.X i)

variable [Algebra.FormallyEtale (MvPolynomial (Fin 2) R) P]

/-- The differentials of the coordinates span `Ω_{P/R}`. -/
theorem span_D_coord :
    Submodule.span P (Set.range fun i : Fin 2 => D R P (coord R P i)) = ⊤ := by
  set S := Submodule.span P (Set.range fun i : Fin 2 => D R P (coord R P i))
  have hA : ∀ a : MvPolynomial (Fin 2) R,
      D R P (algebraMap (MvPolynomial (Fin 2) R) P a) ∈ S := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C k =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        Derivation.map_algebraMap]
      exact zero_mem _
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | mul_X a i ha =>
      rw [map_mul, Derivation.leibniz]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
        (Submodule.smul_mem _ _ ha)
  rw [eq_top_iff]
  rintro ω -
  obtain ⟨t, rfl⟩ :=
    (tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin 2) R) P).surjective ω
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul p ω' =>
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
    apply Submodule.smul_mem
    have hω' : ω' ∈ Submodule.span (MvPolynomial (Fin 2) R)
        (Set.range (D R (MvPolynomial (Fin 2) R))) := by
      rw [span_range_derivation]; trivial
    induction hω' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [map_D]
      exact hA a
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [LinearMap.map_smul_of_tower]
      have h' := Submodule.smul_mem S (algebraMap (MvPolynomial (Fin 2) R) P a) hx
      rwa [algebraMap_smul] at h'
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- **Derivations of an étale algebra over the plane are determined by the coordinates.** -/
theorem derivation_ext {M : Type w} [AddCommGroup M] [Module P M] [Module R M]
    [IsScalarTower R P M] {D₁ D₂ : Derivation R P M}
    (h : ∀ i, D₁ (coord R P i) = D₂ (coord R P i)) : D₁ = D₂ := by
  have : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    apply LinearMap.ext_on_range (span_D_coord R P)
    intro i
    simp only [Derivation.liftKaehlerDifferential_comp_D, h i]
  rw [← D₁.liftKaehlerDifferential_comp, this, D₂.liftKaehlerDifferential_comp]

/-- The basis `du₀, du₁` of `Ω_{P/R}`. -/
def kaehlerBasis : Module.Basis (Fin 2) P Ω[P⁄R] :=
  ((mvPolynomialBasis R (Fin 2)).baseChange P).map
    (tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin 2) R) P)

theorem kaehlerBasis_apply (i : Fin 2) : kaehlerBasis R P i = D R P (coord R P i) := by
  have hb : mvPolynomialBasis R (Fin 2) i = D R (MvPolynomial (Fin 2) R) (MvPolynomial.X i) := by
    apply (mvPolynomialBasis R (Fin 2)).repr.injective
    rw [Module.Basis.repr_self, mvPolynomialBasis_repr_D_X]
  rw [kaehlerBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, hb,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D]

/-- The partial derivative `∂ᵢ` on `P`: the `i`-th coordinate of `dp` in the basis `du₀, du₁`. -/
def planeDerivation (i : Fin 2) : Derivation R P P :=
  ((kaehlerBasis R P).coord i).compDer (D R P)

theorem planeDerivation_apply (i : Fin 2) (p : P) :
    planeDerivation R P i p = (kaehlerBasis R P).coord i (D R P p) := rfl

@[simp]
theorem planeDerivation_coord (i j : Fin 2) :
    planeDerivation R P i (coord R P j) = if j = i then 1 else 0 := by
  rw [planeDerivation_apply, ← kaehlerBasis_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]

/-- The Hessian determinant `∂₀∂₀g · ∂₁∂₁g - ∂₀∂₁g · ∂₁∂₀g` of `g ∈ P`. -/
def hessian (g : P) : P :=
  planeDerivation R P 0 (planeDerivation R P 0 g) * planeDerivation R P 1 (planeDerivation R P 1 g) -
    planeDerivation R P 0 (planeDerivation R P 1 g) * planeDerivation R P 1 (planeDerivation R P 0 g)

end Coordinates

section Map

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) R) P]
  {R' : Type u} [CommRing R'] [Algebra R R'] {P' : Type w} [CommRing P'] [Algebra R' P']
  [Algebra R P'] [IsScalarTower R R' P']
  [Algebra (MvPolynomial (Fin 2) R') P'] [IsScalarTower R' (MvPolynomial (Fin 2) R') P']
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) R') P']

/-- **Partial derivatives commute with coordinate-preserving maps.** If `φ : P → P'` is an
`R`-algebra map between étale algebras over the planes over `R` and `R'` (with `R → R'`) carrying
coordinates to coordinates, then `∂ᵢ (φ p) = φ (∂ᵢ p)`. -/
theorem planeDerivation_map (φ : P →ₐ[R] P') (hφ : ∀ j, φ (coord R P j) = coord R' P' j)
    (i : Fin 2) (p : P) :
    planeDerivation R' P' i (φ p) = φ (planeDerivation R P i p) := by
  let : Algebra P P' := φ.toRingHom.toAlgebra
  have : IsScalarTower R P P' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let D₁ : Derivation R P P' :=
    ((planeDerivation R' P' i).restrictScalars R).compAlgebraMap P
  let D₂ : Derivation R P P' := (Algebra.linearMap P P').compDer (planeDerivation R P i)
  have h : D₁ = D₂ := by
    apply derivation_ext R P
    intro j
    change planeDerivation R' P' i (φ (coord R P j)) = φ (planeDerivation R P i (coord R P j))
    rw [hφ, planeDerivation_coord, planeDerivation_coord]
    split_ifs <;> simp
  exact Derivation.congr_fun h p

theorem hessian_map (φ : P →ₐ[R] P') (hφ : ∀ j, φ (coord R P j) = coord R' P' j) (g : P) :
    hessian R' P' (φ g) = φ (hessian R P g) := by
  simp only [hessian, planeDerivation_map φ hφ, map_sub, map_mul]

end Map

end DeJongAlterations.StableModification.Curves.SemistableOpen
