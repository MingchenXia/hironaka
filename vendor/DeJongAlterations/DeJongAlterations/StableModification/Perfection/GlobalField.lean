/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL-GLOBAL)
-/
import DeJongAlterations.StableModification.Perfection.Stabilization
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The compositum `K(X)(E)` of the purely inseparable base change

Blueprint chapter `sm-dj-perfection-global`, node `lem:sm-dj-perfection-global-compositum` (new
route, not in de Jong 1996).

Let `K ⊆ F ⊆ M` be fields (`F` plays the role of the function field `K(X)` of the total space,
`K` that of the base) and `E ⊆ M` an intermediate field of `M / K`, finite over `K`. The
compositum `F(E) = adjoin F E ⊆ M` is the function field of the normalization of the total space
in the purely inseparable base change.

* `finiteDimensional_adjoin_of_finiteDimensional`: `F(E)` is finite over `F`;
* `isPurelyInseparable_adjoin_of_le_perfectClosure`: if `E` lies in the perfect closure of `K`,
  then `F(E)` is purely inseparable over `F`;
* `compositumLift_injective`, `range_compositumLift`: if `E` and `F` are linearly disjoint over
  `K`, multiplication `E ⊗_K F → M` is injective with image `F(E)`;
* `isDomain_adjoin_tensorProduct`: consequently, if `F ⊗_K K'` is a domain for every field
  extension `K'` of `K`, then `F(E) ⊗_E E'` is a domain for every field extension `E'` of `E`:
  `F(E) ⊗_E E' ≅ (E ⊗_K F) ⊗_E E' ≅ E' ⊗_K F`;
* `geometricallyIntegral_specMap_of_forall_isDomain`: a field extension which stays a domain
  after every field extension of the base gives a geometrically integral morphism of spectra.
-/

noncomputable section

open IntermediateField TensorProduct AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.StableModification.Perfection

universe u

variable {K F M : Type u} [Field K] [Field F] [Field M] [Algebra K F] [Algebra F M] [Algebra K M]
  [IsScalarTower K F M] (E : IntermediateField K M)

/-- If `E / K` is finite, the compositum `F(E)` is finite over `F`. -/
theorem finiteDimensional_adjoin_of_finiteDimensional [FiniteDimensional K E] :
    FiniteDimensional F (adjoin F (E : Set M)) := by
  let b := Module.finBasis K E
  let S : Set M := Set.range fun i => (b i : M)
  have hSE : S ⊆ E := by
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  have hES : ∀ e ∈ E, e ∈ adjoin F S := by
    intro e he
    have h1 : e ∈ Submodule.span K S := by
      have := Submodule.apply_mem_span_image_of_mem_span E.val.toLinearMap
        (b.mem_span (⟨e, he⟩ : E))
      rwa [← Set.range_comp] at this
    have h2 : Submodule.span K S ≤
        ((adjoin F S).restrictScalars K).toSubalgebra.toSubmodule :=
      Submodule.span_le.mpr (subset_adjoin F S)
    exact h2 h1
  have heq : adjoin F (E : Set M) = adjoin F S :=
    le_antisymm (adjoin_le_iff.2 fun x hx => hES x hx) (adjoin.mono F _ _ hSE)
  rw [heq]
  have : Finite S := Set.finite_range _
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  have : IsIntegral K x := (Algebra.IsIntegral.isIntegral (R := K) (⟨x, hSE hx⟩ : E)).map E.val
  exact this.tower_top

/-- If `E` lies in the perfect closure of `K` in `M`, the compositum `F(E)` is purely inseparable
over `F`. -/
theorem isPurelyInseparable_adjoin_of_le_perfectClosure (hE : E ≤ perfectClosure K M) :
    IsPurelyInseparable F (adjoin F (E : Set M)) := by
  have : ExpChar F (ringExpChar K) :=
    expChar_of_injective_algebraMap (algebraMap K F).injective (ringExpChar K)
  rw [isPurelyInseparable_adjoin_iff_pow_mem F M (ringExpChar K)]
  intro x hx
  obtain ⟨n, c, hc⟩ := mem_perfectClosure_iff.1 (hE hx)
  exact ⟨n, algebraMap K F c, by rw [← IsScalarTower.algebraMap_apply, hc]⟩

/-- The inclusion `E ⊆ F(E)`. -/
def toAdjoin : E →+* adjoin F (E : Set M) where
  toFun e := ⟨e, subset_adjoin F _ e.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Algebra K F] [IsScalarTower K F M] in
@[simp]
theorem coe_toAdjoin (e : E) : ((toAdjoin (F := F) E e : adjoin F (E : Set M)) : M) = e := rfl

/-- The multiplication map `E ⊗_K F → M`. -/
def compositumLift : E ⊗[K] F →ₐ[E] M :=
  Algebra.TensorProduct.lift (Algebra.ofId E M) (IsScalarTower.toAlgHom K F M)
    fun _ _ => Commute.all _ _

@[simp]
theorem compositumLift_tmul (e : E) (y : F) :
    compositumLift (F := F) E (e ⊗ₜ y) = (e : M) * algebraMap F M y := rfl

/-- **Linear disjointness makes the multiplication map injective.** -/
theorem compositumLift_injective
    (hld : E.LinearDisjoint (IsScalarTower.toAlgHom K F M).fieldRange) :
    Function.Injective (compositumLift (F := F) E) := by
  let b := Module.Basis.ofVectorSpace K F
  let φ := AlgHom.equivFieldRange (IsScalarTower.toAlgHom K F M)
  have hb : LinearIndependent K (φ ∘ b) :=
    b.linearIndependent.map' φ.toLinearEquiv.toLinearMap φ.toLinearEquiv.ker
  refine injective_of_linearIndependent_comp_basis (Algebra.TensorProduct.basis E b)
    (compositumLift (F := F) E).toLinearMap ?_
  have h : (compositumLift (F := F) E).toLinearMap ∘ Algebra.TensorProduct.basis E b =
      (IsScalarTower.toAlgHom K F M).fieldRange.val ∘ (φ ∘ b) := by
    funext i
    simp [Algebra.TensorProduct.basis_apply, φ]
  rw [h]
  exact hld.linearIndependent_right hb

/-- The image of the multiplication map `E ⊗_K F → M` is the compositum `F(E)`, for algebraic
`E / K`. -/
theorem mem_range_compositumLift_iff [Algebra.IsAlgebraic K E] {m : M} :
    m ∈ (compositumLift (F := F) E).range ↔ m ∈ adjoin F (E : Set M) := by
  constructor
  · rintro ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul e y =>
      change (e : M) * algebraMap F M y ∈ _
      exact mul_mem (subset_adjoin F _ e.2) ((adjoin F (E : Set M)).algebraMap_mem y)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · intro hm
    have halg : ∀ x ∈ (E : Set M), IsAlgebraic F x := fun x hx =>
      ((Algebra.IsIntegral.isIntegral (R := K) (⟨x, hx⟩ : E)).map E.val).tower_top.isAlgebraic
    have hm' : m ∈ (adjoin F (E : Set M)).toSubalgebra := hm
    rw [adjoin_toSubalgebra_of_isAlgebraic halg] at hm'
    let R : Subalgebra F M :=
      { (compositumLift (F := F) E).range.toSubring with
        algebraMap_mem' := fun y => ⟨1 ⊗ₜ y, by simp⟩ }
    have hle : Algebra.adjoin F (E : Set M) ≤ R :=
      Algebra.adjoin_le fun e he => ⟨⟨e, he⟩ ⊗ₜ 1, by simp⟩
    exact hle hm'

/-- `E ⊗_K F ≅ F(E)` as `E`-algebras, under linear disjointness. -/
def compositumEquiv [Algebra.IsAlgebraic K E]
    (hld : E.LinearDisjoint (IsScalarTower.toAlgHom K F M).fieldRange) :
    letI : Algebra E (adjoin F (E : Set M)) := (toAdjoin E).toAlgebra
    E ⊗[K] F ≃ₐ[E] adjoin F (E : Set M) :=
  letI : Algebra E (adjoin F (E : Set M)) := (toAdjoin E).toAlgebra
  (AlgEquiv.ofInjective _ (compositumLift_injective E hld)).trans
    { toFun := fun x => ⟨x, (mem_range_compositumLift_iff E).1 x.2⟩
      invFun := fun x => ⟨x, (mem_range_compositumLift_iff E).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

/-- Base change along `E ⊗_K F ≅ L`: if `F ⊗_K E'` is a domain, so is `L ⊗_E E'`. -/
theorem isDomain_tensorProduct_of_algEquiv {K E F L E' : Type u} [Field K] [Field E] [Field F]
    [Field L] [Field E'] [Algebra K E] [Algebra K F] [Algebra E L] [Algebra E E'] [Algebra K E']
    [IsScalarTower K E E'] (e₁ : E ⊗[K] F ≃ₐ[E] L) [IsDomain (F ⊗[K] E')] :
    IsDomain (L ⊗[E] E') := by
  let e₂ : L ⊗[E] E' ≃ₐ[E] (E ⊗[K] F) ⊗[E] E' :=
    Algebra.TensorProduct.congr e₁.symm AlgEquiv.refl
  let e₃ : (E ⊗[K] F) ⊗[E] E' ≃ₐ[E] E' ⊗[E] (E ⊗[K] F) := Algebra.TensorProduct.comm E _ _
  let e₄ : E' ⊗[E] (E ⊗[K] F) ≃ₐ[E'] E' ⊗[K] F :=
    Algebra.TensorProduct.cancelBaseChange K E E' E' F
  let e₅ : E' ⊗[K] F ≃ₐ[K] F ⊗[K] E' := Algebra.TensorProduct.comm K E' F
  let e : L ⊗[E] E' ≃+* F ⊗[K] E' :=
    ((e₂.toRingEquiv.trans e₃.toRingEquiv).trans e₄.toRingEquiv).trans e₅.toRingEquiv
  exact e.toMulEquiv.isDomain

/-- **The compositum is geometrically integral over `E`.** If `E` and `F` are linearly disjoint
over `K`, `E / K` is algebraic and `F ⊗_K K'` is a domain for every field extension `K'` of `K`,
then `F(E) ⊗_E E'` is a domain for every field extension `E'` of `E`. -/
theorem isDomain_adjoin_tensorProduct [Algebra.IsAlgebraic K E]
    (hld : E.LinearDisjoint (IsScalarTower.toAlgHom K F M).fieldRange)
    (hF : ∀ (K' : Type u) [Field K'] [Algebra K K'], IsDomain (F ⊗[K] K'))
    (E' : Type u) [Field E'] [Algebra E E'] :
    letI : Algebra E (adjoin F (E : Set M)) := (toAdjoin E).toAlgebra
    IsDomain (adjoin F (E : Set M) ⊗[E] E') := by
  let : Algebra E (adjoin F (E : Set M)) := (toAdjoin E).toAlgebra
  let : Algebra K E' := ((algebraMap E E').comp (algebraMap K E)).toAlgebra
  have : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := hF E'
  exact isDomain_tensorProduct_of_algEquiv (compositumEquiv E hld)

/-- A field extension `L / E` which stays a domain after every field extension of `E` gives a
geometrically integral morphism `Spec L ⟶ Spec E`. -/
theorem geometricallyIntegral_specMap_of_forall_isDomain {E L : Type u} [Field E] [Field L]
    [Algebra E L] (h : ∀ (E' : Type u) [Field E'] [Algebra E E'], IsDomain (L ⊗[E] E')) :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap E L))) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) IsIntegral :=
    ⟨fun {X Y} e h => by
      let := h
      let : Nonempty Y := Nonempty.map e.hom inferInstance
      exact isIntegral_of_isOpenImmersion (f := e.inv)⟩
  constructor
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro E' _ _
  have := h E'
  have : IsIntegral (Spec (.of (L ⊗[E] E'))) := inferInstance
  exact isIntegral_of_isOpenImmersion (f := (pullbackSpecIso E L E').hom)

end DeJongAlterations.StableModification.Perfection

end
