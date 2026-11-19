/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Stalk
import Hironaka.Scheme.IdealSheaf.Derivative.StalkCoords
import Hironaka.Scheme.Smooth.DifferentialBasis
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Dual derivations at a closed point span the derivations

At a closed point `x` of a scheme smooth of relative dimension `n` over a field `k` of
characteristic zero, `κ(x) ⊗ Ω_{𝒪_{X,x}/k}` has dimension `n`
(`finrank_residueField_tensor_kaehler_stalk_of_isClosed`,
`Hironaka/Scheme/Smooth/DifferentialBasis.lean`). Hence for any `n` elements `y₁, …, yₙ` of
`𝒪_{X,x}` with `k`-derivations `∂₁, …, ∂ₙ` dual to them (`∂ᵢ yⱼ = δᵢⱼ`), with no assumption that the
`yᵢ` vanish at `x` or generate `𝔪_x`, the `dyᵢ` form a basis of `Ω_{𝒪_{X,x}/k}`: their classes in
`κ(x) ⊗ Ω` are independent, being dual to the `∂ᵢ`, hence a basis by the count, and lift by Nakayama
(Mathlib's `exists_basis_of_basis_baseChange`); so every `k`-derivation is `δ = ∑ᵢ δ(yᵢ) ∂ᵢ`
(`forall_derivation_eq_sum_of_isClosed`).

This is Kollár's "the derivations `∂/∂x₁, …, ∂/∂xₙ` are local generators of `Der_X`"
([Kol07, Definition 73]) at a closed point, for coordinates that need not be centred there. It is
used in the proof of [Kol07, Theorem 88] for one blow-up
(`Hironaka/Resolution/Algebraic/Kol07/Theorem88BlowUp.lean`) at the closed points `q` of a chart of
the blow-up: the chart coordinates `yᵢ/y_ρ, y_ρ, y_l` need not vanish at `q`, but their duals are
the chart derivations `∂'ⱼ` of `Hironaka/Algebra/Local/Chart.lean` (`chartDerivRing_chartYR`), so
the `∂'ⱼ` generate the `k`-derivations of `𝒪_{B,q}`, and the chart derivative ideal `D'` computed
with them is the derivative ideal of the stalk. At a non-closed point the parameters are fewer than
`n` and the spanning by their duals fails
(`Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing KaehlerDifferential TensorProduct

universe u

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n in
/-- Kollár's local generators of `Der_X` ([Kol07, Definition 73]) at a closed point: at a closed
point `x` of a scheme smooth of relative dimension `n` over `k`, `n` elements `yᵢ` of `𝒪_{X,x}`
with dual `k`-derivations `∂ᵢ` (`∂ᵢ yⱼ = δᵢⱼ`) have `δ = ∑ᵢ δ(yᵢ) ∂ᵢ` for every `k`-derivation
`δ`: the `dyᵢ` are a basis of `Ω_{𝒪_{X,x}/k}`, whose rank at a closed point is `n`. -/
theorem forall_derivation_eq_sum_of_isClosed {x : X} (hx : IsClosed ({x} : Set X))
    (y : Fin n → X.presheaf.stalk x)
    (der : letI := f.stalkAlgebra x
      Fin n → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x))
    (hder : letI := f.stalkAlgebra x
      ∀ i j, der i (y j) = if i = j then 1 else 0) :
    letI := f.stalkAlgebra x
    ∀ (δ : Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)) (r : X.presheaf.stalk x),
      δ r = ∑ i, δ (y i) * der i r := by
  classical
  let _ := f.stalkAlgebra x
  have hFS := formallySmooth_stalk f n x
  have hEF := essFiniteType_stalk f n x
  have hfinΩ := finite_kaehlerDifferential_stalk f n x
  -- the classes of the `dy_i` in `κ(x) ⊗ Ω`
  let v : Fin n → Ω[X.presheaf.stalk x⁄k] := fun i => D k (X.presheaf.stalk x) (y i)
  let w : Fin n → ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k] :=
    TensorProduct.mk (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))
      Ω[X.presheaf.stalk x⁄k] 1 ∘ v
  -- the functional `κ(x) ⊗ Ω → κ(x)` induced by `der j` takes `w i` to `δ_ji`
  let φ : Fin n → (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]
      →ₗ[ResidueField (X.presheaf.stalk x)] ResidueField (X.presheaf.stalk x)) := fun j =>
    (TensorProduct.AlgebraTensorModule.rid (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x))).toLinearMap ∘ₗ
      ((der j).liftKaehlerDifferential.baseChange (ResidueField (X.presheaf.stalk x)))
  have hφ : ∀ j i, φ j (w i) = if j = i then 1 else 0 := by
    intro j i
    simp only [φ, w, v, LinearMap.comp_apply, Function.comp_apply, TensorProduct.mk_apply,
      LinearMap.baseChange_tmul, Derivation.liftKaehlerDifferential_comp_D, LinearEquiv.coe_coe,
      TensorProduct.AlgebraTensorModule.rid_tmul, hder]
    split_ifs <;> simp
  have hli : LinearIndependent (ResidueField (X.presheaf.stalk x)) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (φ j) hg
    rw [map_sum, map_zero] at this
    simpa [map_smul, hφ, smul_ite, Finset.sum_ite_eq] using this
  -- the count: `dim κ(x) ⊗ Ω = n` at a closed point, so the `w i` are a basis
  have hfin : Module.finrank (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]) = n :=
    finrank_residueField_tensor_kaehler_stalk_of_isClosed f n hx
  have hsp : Submodule.span (ResidueField (X.presheaf.stalk x)) (Set.range w) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hfin])
  have hinj : Function.Injective
      ((maximalIdeal (X.presheaf.stalk x)).subtype.rTensor Ω[X.presheaf.stalk x⁄k]) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange v hli hsp hinj
  -- `der i` is the `i`-th coordinate functional of the basis `dy`
  have hcoord : ∀ i, (der i).liftKaehlerDifferential = b.coord i := by
    intro i
    refine b.ext fun j => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hb j]
    change (der i).liftKaehlerDifferential (D k (X.presheaf.stalk x) (y j)) = _
    rw [Derivation.liftKaehlerDifferential_comp_D, hder]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  intro δ r
  have hδ : δ.liftKaehlerDifferential = ∑ i, δ (y i) • b.coord i := by
    refine b.ext fun j => ?_
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [Finsupp.single_eq_of_ne hi, mul_zero])
      (fun h => (h (Finset.mem_univ j)).elim), Finsupp.single_eq_same, mul_one, hb j]
    exact Derivation.liftKaehlerDifferential_comp_D δ (y j)
  calc δ r = δ.liftKaehlerDifferential (D k (X.presheaf.stalk x) r) :=
        (Derivation.liftKaehlerDifferential_comp_D δ r).symm
    _ = ∑ i, δ (y i) * der i r := by
        rw [hδ, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.smul_apply, smul_eq_mul, ← hcoord i,
          Derivation.liftKaehlerDifferential_comp_D]

end AlgebraicGeometry
