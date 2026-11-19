/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CohenIso
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Smooth.Field

/-!
# The Cohen isomorphism over the ground field

Kollár, in the proof of the formal equivalence theorem [Kol07, 95], identifies the completed
local ring `Ô_{p,X}` of a `k`-variety at a point with residue field `K` with `K⟦x₁, …, xₙ⟧` by the
Cohen structure theorem ([Kol07, Definition 55]), so that the computations of Proposition 94
apply to it; and Notation 93 views `R = K⟦x⟧` "as a `k`-algebra" [Kol07, Notation 93].  For the
automorphism of `X̂ = Spec_k Ô_{p,X}` of [Kol07, Definition 91]
(a `k`-algebra automorphism) to be produced by a substitution on `K⟦x⟧`, the Cohen isomorphism
`K⟦x⟧ ≅ Ô_{p,X}` must be `k`-linear: its coefficient field `K → Ô` must be a `k`-algebra map.
`Hironaka/Algebra/Local/CoefficientField.lean` produces a coefficient field over `ℚ`; this file
gives the general form over a ground field `k` of characteristic zero:

* `formallySmooth_of_charZero`: a field extension `K/k` in characteristic zero is formally smooth
  ([Sta, Tag 0322]: separably generated) — `formallySmooth_rat_of_field` with `ℚ` replaced by `k`:
  a transcendence basis, over which `K` is algebraic, hence separable in characteristic zero.
* `exists_coefficientField_over`: a `k`-linear coefficient field `σ : K →ₐ[k] R̂` of the completion
  of a Noetherian local `k`-algebra `R` with residue field `K` — the lift of the (`k`-linear)
  residue isomorphism `K ≅ R̂/𝔪R̂` through the `𝔪R̂`-adically complete `R̂`.
* `cohenAlgEquivOver σ hσ x hx hd : K⟦X₁, …, X_d⟧ ≃ₐ[k] R̂` for a regular system of parameters
  `x`: `cohenEquivOfResidue` of `Hironaka/Algebra/Local/CohenIso.lean` for the coefficient field
  `σ`, which is `k`-linear because the constants go to `σ` (`cohenMap_C`) and `σ` is `k`-linear.
  `cohenAlgEquivOver_X`, `cohenAlgEquivOver_C` are Kollár's `xᵢ ↦ ι(xᵢ)`, constants to the
  coefficient field.
* `exists_algEquiv_of_regularSystems` (Kollár's automorphism `φ^*` with
  `φ^*(x₁', x₂, …, xₙ) = (x₁, x₂, …, xₙ)`, defined because both are coordinate systems,
  [Kol07, 95]): for two regular systems of
  parameters `x, x'` there is a `k`-algebra automorphism `φ` of `R̂` with `φ(ι x'ᵢ) = ι xᵢ` — the
  composite `Φ ∘ Φ'⁻¹` of the Cohen isomorphisms of `x` and `x'` for one and the same coefficient
  field; the criterion of Notation 93 ("the linear parts of the `gᵢ` are linearly independent")
  is not needed, the two coordinate systems supply the two isomorphisms.

The `k`-linear Cohen isomorphism is used for the formal equivalence of points along a
hypersurface of maximal contact
(`Hironaka/Resolution/Algebraic/MaximalContact/FormalEquivExists.lean`).
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

section Field

/-- A field extension of a field of characteristic zero is formally smooth ([Sta, Tag 0322]) —
`formallySmooth_rat_of_field` with `ℚ` replaced by `k`. -/
theorem formallySmooth_of_charZero (k K : Type*) [Field k] [Field K] [CharZero k] [Algebra k K] :
    Algebra.FormallySmooth k K := by
  have : FaithfulSMul k K :=
    (faithfulSMul_iff_algebraMap_injective k K).mpr (algebraMap k K).injective
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' k K
  have : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range v)) K := hv.isAlgebraic_field
  have : CharZero (IntermediateField.adjoin k (Set.range v)) :=
    (algebraMap (IntermediateField.adjoin k (Set.range v)) K).charZero
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hv.1

end Field

section Completion

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (k : Type*) [Field k] [CharZero k] [Algebra k R]

local notation "R̂" => AdicCompletion (maximalIdeal R) R

omit [CharZero k] in
/-- The residue isomorphism `K ≅ R̂/𝔪R̂` is `k`-linear. -/
theorem residueFieldEquiv_algebraMap (a : k) :
    residueFieldEquiv R (algebraMap k (ResidueField R) a) =
      algebraMap k (ResidueField R̂) a := by
  rw [IsScalarTower.algebraMap_apply k R (ResidueField R) a,
    IsScalarTower.algebraMap_apply k R̂ (ResidueField R̂) a]
  change ResidueField.map (algebraMap R R̂) (residue R (algebraMap k R a)) =
    residue R̂ (algebraMap k R̂ a)
  rw [ResidueField.map_residue]
  rfl

/-- A `k`-linear coefficient field of `R̂` exists — a `k`-algebra map `σ : K → R̂` from the residue
field which is a section of the residue map `R̂ → R̂/𝔪R̂ = K`. -/
theorem exists_coefficientField_over :
    ∃ σ : ResidueField R →ₐ[k] R̂, ∀ a, residue R̂ (σ a) = residueFieldEquiv R a := by
  have := formallySmooth_of_charZero k (ResidueField R)
  let f : ResidueField R →ₐ[k] R̂ ⧸ maximalIdeal R̂ :=
    { toRingHom := (residueFieldEquiv R : ResidueField R →+* ResidueField R̂)
      commutes' := fun a => residueFieldEquiv_algebraMap R k a }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (R := k) (A := ResidueField R) (S := R̂) (I := maximalIdeal R̂) f
  exact ⟨g, fun a => congrArg (fun φ => φ a) hg⟩

variable {R k}

/-- The Cohen isomorphism `K⟦X₁, …, X_d⟧ ≃ R̂` ([Kol07, Definition 55]; as used in
[Kol07, 95]) for the `k`-linear coefficient field `σ`, as a `k`-algebra isomorphism. -/
noncomputable def cohenAlgEquivOver (σ : ResidueField R →ₐ[k] R̂)
    (hσ : ∀ a, residue R̂ (σ a) = residueFieldEquiv R a) {d : ℕ} (x : Fin d → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R) :
    MvPowerSeries (Fin d) (ResidueField R) ≃ₐ[k] R̂ :=
  letI : Algebra (ResidueField R) R̂ := σ.toRingHom.toAlgebra
  AlgEquiv.ofRingEquiv (f := cohenEquivOfResidue R x hσ hx hd) fun a => by
    rw [cohenEquivOfResidue_apply, MvPowerSeries.algebraMap_apply, cohenMap_C]
    exact σ.commutes a

omit [CharZero k] in
/-- Kollár's `xᵢ ↦ ι(xᵢ)`. -/
theorem cohenAlgEquivOver_X (σ : ResidueField R →ₐ[k] R̂)
    (hσ : ∀ a, residue R̂ (σ a) = residueFieldEquiv R a) {d : ℕ} (x : Fin d → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R)
    (i : Fin d) : cohenAlgEquivOver σ hσ x hx hd (X i) = algebraMap R R̂ (x i) := by
  let _ : Algebra (ResidueField R) R̂ := σ.toRingHom.toAlgebra
  change cohenEquivOfResidue R x hσ hx hd (X i) = _
  rw [cohenEquivOfResidue_apply, cohenMap_X]

omit [CharZero k] in
/-- The constants go to the coefficient field. -/
theorem cohenAlgEquivOver_C (σ : ResidueField R →ₐ[k] R̂)
    (hσ : ∀ a, residue R̂ (σ a) = residueFieldEquiv R a) {d : ℕ} (x : Fin d → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R)
    (a : ResidueField R) : cohenAlgEquivOver σ hσ x hx hd (C a) = σ a := by
  let _ : Algebra (ResidueField R) R̂ := σ.toRingHom.toAlgebra
  change cohenEquivOfResidue R x hσ hx hd (C a) = σ.toRingHom a
  rw [cohenEquivOfResidue_apply, cohenMap_C]
  rfl

omit [CharZero k] in
/-- The constants of the Cohen isomorphism form a coefficient field: `residue (Φ (C a)) = a`. -/
theorem residue_cohenAlgEquivOver_C (σ : ResidueField R →ₐ[k] R̂)
    (hσ : ∀ a, residue R̂ (σ a) = residueFieldEquiv R a) {d : ℕ} (x : Fin d → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R)
    (a : ResidueField R) :
    residue R̂ (cohenAlgEquivOver σ hσ x hx hd (C a)) = residueFieldEquiv R a := by
  rw [cohenAlgEquivOver_C, hσ]

/-- For a regular system of parameters `x` of the Noetherian local `k`-algebra `R` there is a
`k`-algebra isomorphism `Φ : K⟦X⟧ ≃ₐ[k] R̂` with `Φ(Xᵢ) = ι(xᵢ)` whose constants form a
coefficient field: "`Ô_{p,X} ≅ K⟦x₁, …, xₙ⟧` by (55)" as a `k`-algebra, [Kol07, 95]. -/
theorem exists_cohenAlgEquiv_over {d : ℕ} (x : Fin d → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R) :
    ∃ Φ : MvPowerSeries (Fin d) (ResidueField R) ≃ₐ[k] R̂,
      (∀ i, Φ (X i) = algebraMap R R̂ (x i)) ∧
      ∀ a, residue R̂ (Φ (C a)) = residueFieldEquiv R a := by
  obtain ⟨σ, hσ⟩ := exists_coefficientField_over R k
  exact ⟨cohenAlgEquivOver σ hσ x hx hd, cohenAlgEquivOver_X σ hσ x hx hd,
    residue_cohenAlgEquivOver_C σ hσ x hx hd⟩

/-- For two regular systems of parameters `x`, `x'` of `R` there is a `k`-algebra automorphism `φ`
of `R̂` with `φ(ι x'ᵢ) = ι xᵢ` for every `i` — the composite of the Cohen isomorphisms of `x` and
`x'` for one coefficient field (Kollár's automorphism `φ^*` with
`φ^*(x₁', x₂, …, xₙ) = (x₁, x₂, …, xₙ)`, defined because both are coordinate systems,
[Kol07, 95]). -/
theorem exists_algEquiv_of_regularSystems {d : ℕ} (x x' : Fin d → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hx' : maximalIdeal R = Ideal.span (Set.range x')) (hd : (d : WithBot ℕ∞) = ringKrullDim R) :
    ∃ φ : R̂ ≃ₐ[k] R̂, ∀ i, φ (algebraMap R R̂ (x' i)) = algebraMap R R̂ (x i) := by
  obtain ⟨σ, hσ⟩ := exists_coefficientField_over R k
  refine ⟨(cohenAlgEquivOver σ hσ x' hx' hd).symm.trans (cohenAlgEquivOver σ hσ x hx hd),
    fun i => ?_⟩
  rw [AlgEquiv.trans_apply, ← cohenAlgEquivOver_X σ hσ x' hx' hd i, AlgEquiv.symm_apply_apply,
    cohenAlgEquivOver_X]

end Completion

end IsLocalRing
