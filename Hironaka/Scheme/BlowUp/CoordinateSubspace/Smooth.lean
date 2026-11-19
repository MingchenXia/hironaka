/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Hironaka.Scheme.BlowUp.CoordinateSubspace.Charts

/-!
# Smoothness of the model blow-up

The point blow-up of `𝔸ⁿ` is non-singular [Hau14, Example 4.55]; for a general coordinate
subspace `L`, `B_L 𝔸ⁿ_A` is smooth over `A` of relative dimension `n`.  Smoothness of relative
dimension `n` is Zariski-local on the source (Mathlib's `HasRingHomProperty` for
`SmoothOfRelativeDimension n`), the charts `U_j = Spec A[x]` are open immersions covering `B`
(`Hironaka.Scheme.BlowUp.CoordinateSubspace.Charts`), and over the base each chart is `Spec (π_j)`
with `π_j` an `A`-algebra endomorphism of `A[x]`, so `U_j → B → Spec A` is `Spec (A → A[x])`, which
is standard smooth of relative dimension `n`: the polynomial algebra has the submersive presentation
with the `n` variables as generators and no relations (Mathlib's `PreSubmersivePresentation.naive`
with an empty relation index; the Jacobian is the determinant of the endomorphism of the zero
module, `1`).  Mathlib at the pinned version has no instance
`IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R)`;
`mvPolynomial_isStandardSmoothOfRelativeDimension` supplies it, transported from the quotient by
the zero ideal along `RespectsIso`.  The smoothness of affine space and of the model blow-up is
used wherever the model is compared with a blow-up of a smooth centre
(`Hironaka.Scheme.Smooth.BlowUpSmoothChart`,
`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineSpace`,
`Hironaka.Scheme.IdealSheaf.Order.AffineSpace`).
-/

@[expose] public section

universe u v w

open AlgebraicGeometry CategoryTheory MvPolynomial Algebra

namespace AlgebraicGeometry.CoordinateSubspace

/-- Standard smoothness of relative dimension `m` over `A` transports along an `A`-algebra
isomorphism (the ring-hom form, so that the universes of `S` and `T` may differ). -/
theorem isStandardSmoothOfRelativeDimension_algebraMap_of_algEquiv {A : Type u} [CommRing A]
    {S : Type v} {T : Type w} [CommRing S] [CommRing T] [Algebra A S] [Algebra A T] (e : S ≃ₐ[A] T)
    {m : ℕ} (h : RingHom.IsStandardSmoothOfRelativeDimension m (algebraMap A S)) :
    RingHom.IsStandardSmoothOfRelativeDimension m (algebraMap A T) := by
  have := (RingHom.IsStandardSmoothOfRelativeDimension.equiv e.toRingEquiv).comp h
  rw [zero_add] at this
  have hcomp : (e.toRingEquiv : S →+* T).comp (algebraMap A S) = algebraMap A T :=
    RingHom.ext fun a => e.commutes a
  rwa [hcomp] at this

section Polynomial

variable (A : Type u) [CommRing A] (σ : Type v) [Finite σ]

/-- The pre-submersive presentation of `A[x_i : i ∈ σ]` (as the quotient by the zero ideal) with the
variables as generators and no relations. -/
noncomputable def mvPolynomialPreSubmersivePresentation :
    PreSubmersivePresentation A
      (MvPolynomial σ A ⧸ Ideal.span (Set.range (Empty.elim : Empty → MvPolynomial σ A)))
      σ Empty :=
  PreSubmersivePresentation.naive (v := Empty.elim) Empty.elim fun a => a.elim

/-- The ring-level input: the empty-relation presentation is submersive — its
Jacobian is the determinant of the endomorphism of the zero module. -/
noncomputable def mvPolynomialSubmersivePresentation :
    SubmersivePresentation A
      (MvPolynomial σ A ⧸ Ideal.span (Set.range (Empty.elim : Empty → MvPolynomial σ A)))
      σ Empty where
  toPreSubmersivePresentation := mvPolynomialPreSubmersivePresentation A σ
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian, LinearMap.det_eq_one_of_subsingleton, map_one]
    exact isUnit_one

theorem isStandardSmoothOfRelativeDimension_mvPolynomial_quotient :
    IsStandardSmoothOfRelativeDimension (Nat.card σ) A
      (MvPolynomial σ A ⧸ Ideal.span (Set.range (Empty.elim : Empty → MvPolynomial σ A))) :=
  (mvPolynomialSubmersivePresentation A σ).isStandardSmoothOfRelativeDimension (by
    simp [Presentation.dimension])

/-- The ring-level input (absent from Mathlib at the pinned version): `A → A[x_i : i ∈ σ]` is
standard smooth of relative dimension `|σ|`. -/
theorem ringHom_isStandardSmoothOfRelativeDimension_algebraMap_mvPolynomial :
    RingHom.IsStandardSmoothOfRelativeDimension (Nat.card σ) (algebraMap A (MvPolynomial σ A)) := by
  have hJ : Ideal.span (Set.range (Empty.elim : Empty → MvPolynomial σ A)) = ⊥ := by
    rw [Set.range_eq_empty, Ideal.span_empty]
  have h : RingHom.IsStandardSmoothOfRelativeDimension (Nat.card σ) (algebraMap A
      (MvPolynomial σ A ⧸ Ideal.span (Set.range (Empty.elim : Empty → MvPolynomial σ A)))) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := Nat.card σ)).mpr
      (isStandardSmoothOfRelativeDimension_mvPolynomial_quotient A σ)
  have hinj : Function.Injective
      (Ideal.Quotient.mk (Ideal.span (Set.range (Empty.elim : Empty → MvPolynomial σ A)))) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr (by rw [Ideal.mk_ker]; exact hJ)
  let e : MvPolynomial σ A ≃+*
      (MvPolynomial σ A ⧸ Ideal.span (Set.range (Empty.elim : Empty → MvPolynomial σ A))) :=
    RingEquiv.ofBijective _ ⟨hinj, Ideal.Quotient.mk_surjective⟩
  have := (RingHom.IsStandardSmoothOfRelativeDimension.equiv e.symm).comp h
  rw [zero_add] at this
  convert this using 1
  refine RingHom.ext fun a => ?_
  rw [RingHom.comp_apply]
  change algebraMap A (MvPolynomial σ A) a = e.symm (e (algebraMap A (MvPolynomial σ A) a))
  rw [RingEquiv.symm_apply_apply]

/-- `A[x_i : i ∈ σ]` is standard smooth of relative dimension `|σ|` over `A`. -/
instance mvPolynomial_isStandardSmoothOfRelativeDimension :
    IsStandardSmoothOfRelativeDimension (Nat.card σ) A (MvPolynomial σ A) :=
  (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := Nat.card σ)).mp
    (ringHom_isStandardSmoothOfRelativeDimension_algebraMap_mvPolynomial A σ)

/-- `𝔸ⁿ_A → Spec A` is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial (n : ℕ) :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{u} n), CommRingCat.hom_ofHom]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  have := ringHom_isStandardSmoothOfRelativeDimension_algebraMap_mvPolynomial A (Fin n)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

end Polynomial

variable (A : Type u) [CommRing A] (n r : ℕ)

/-- **The model blow-up is smooth** ([Hau14, Example 4.55] for a point; here for any coordinate
subspace): `B_L 𝔸ⁿ_A` is smooth over `A` of relative dimension `n` — Zariski-local on the source,
and on the chart `U_j` the map to `Spec A` is `Spec (A → A[x])`. -/
theorem smoothOfRelativeDimension_modelBlowUp :
    SmoothOfRelativeDimension n (affineBlowUp.π (centerIdeal A n r) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))) := by
  -- Mathlib's instance `HasRingHomProperty.instIsZariskiLocalAtSource` is not found by instance
  -- search at the pinned Mathlib version (the outParam `Q` blocks unification); it is applied by
  -- hand.
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} n) := hloc.toRespects
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{u} n)
    (fun j : {j : Fin n // j.val < r} => (modelChart A n r j.1 j.2).opensRange) ?_ fun j => ?_
  · rw [← iSup_opensRange_modelChart A n r]
    symm
    exact iSup_subtype'
  · have e : Set.range (modelChart A n r j.1 j.2) =
        Set.range (modelChart A n r j.1 j.2).opensRange.ι := by
      rw [Scheme.Opens.range_ι]
      rfl
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (modelChart A n r j.1 j.2) _ e, Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension.{u} n),
      ← Category.assoc, modelChart_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
    exact smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial A n

end AlgebraicGeometry.CoordinateSubspace
