/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL)
-/
import DeJongAlterations.StableModification.Perfection.Stabilization

/-!
# Level transfer: `B_E = E[T]` for every `E₀ ≤ E ≤ Ω`

Blueprint chapter `sm-dj-perfection`, node `lem:sm-dj-perfection-level-transfer` (new route, not
in de Jong 1996).

In the model of `Perfection/Stabilization.lean`, let `E₀ ≤ Ω` and the finite set `T ⊆ E₀(A)` be as
in `exists_finset_stabilization`: the image of `B_Ω` lies in `Ω[T]`. Then for every `E₀ ≤ E ≤ Ω`
the image `ι(B_E)` of `B_E` in `M` is `E[T]` (`range_normalizationι_subset_adjoin`): the inclusion
`E[T] ⊆ ι(B_E)` becomes surjective after the faithfully flat base change `Ω ⊗_E -` (both sides map
onto `ι(B_Ω)`, and `Ω ⊗_E ι(B_E) → M` is injective), hence is an equality.

This file also introduces the image `normalizationImage A E = ι(B_E)`, an `E`-subalgebra of `M`
isomorphic to `B_E`, the inclusion `A → ι(B_E)` and the inclusions `ι(B_E) ⊆ ι(B_Ω)`.
-/

noncomputable section

open IntermediateField TensorProduct Polynomial

namespace DeJongAlterations.StableModification.Perfection

universe u

variable {K : Type u} {M : Type u} [Field K] [Field M] [Algebra K M] (A : Subalgebra K M)

/-- The image `B_E ≅ ι(B_E) ⊆ M` of the normalization, an `E`-subalgebra of `M`. -/
abbrev normalizationImage (E : IntermediateField K M) : Subalgebra E M := (normalizationι A E).range

/-- The inclusion `A → B_E`. -/
def toNormalization (E : IntermediateField K M) : A →+* normalization A E where
  toFun a := ⟨algebraMap (baseRing A E) (baseField A E) ⟨a, subset_baseRing A E a.2⟩,
    Subalgebra.algebraMap_mem _ _⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem normalizationι_toNormalization (E : IntermediateField K M) (a : A) :
    normalizationι A E (toNormalization A E a) = a := rfl

/-- The inclusion `A → ι(B_E)`. -/
def toNormalizationImage (E : IntermediateField K M) : A →+* normalizationImage A E where
  toFun a := ⟨a, toNormalization A E a, rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_toNormalizationImage (E : IntermediateField K M) (a : A) :
    (toNormalizationImage A E a : M) = a := rfl

variable {A}

/-- The element of `ι(B_E)` given by an element of `E(A)` integral over `A` (`0` otherwise). -/
def imageElem (A : Subalgebra K M) (E : IntermediateField K M) (hE : ∀ x ∈ E, IsIntegral K x)
    (t : M) :
    normalizationImage A E :=
  open Classical in
  if h : t ∈ baseField A E ∧ IsIntegral A t then ⟨t, (mem_range_normalizationι_iff hE).2 h⟩
  else 0

theorem coe_imageElem (E : IntermediateField K M) (hE : ∀ x ∈ E, IsIntegral K x) {t : M}
    (h : t ∈ baseField A E ∧ IsIntegral A t) : (imageElem A E hE t : M) = t := by
  rw [imageElem, dif_pos h]

theorem normalizationImage_le {E Ω : IntermediateField K M} (hEΩ : E ≤ Ω)
    (hΩ : ∀ x ∈ Ω, IsIntegral K x) :
    (normalizationImage A E).toSubring ≤ (normalizationImage A Ω).toSubring := fun _ hx =>
  (mem_range_normalizationι_iff hΩ).2
    ⟨baseField_mono hEΩ ((mem_range_normalizationι_iff fun y hy => hΩ y (hEΩ hy)).1 hx).1,
      ((mem_range_normalizationι_iff fun y hy => hΩ y (hEΩ hy)).1 hx).2⟩

/-- The inclusion `ι(B_E) ⊆ ι(B_Ω)` for `E ≤ Ω`. -/
def imageInclusion {E Ω : IntermediateField K M} (hEΩ : E ≤ Ω)
    (hΩ : ∀ x ∈ Ω, IsIntegral K x) : normalizationImage A E →+* normalizationImage A Ω :=
  Subring.inclusion (normalizationImage_le hEΩ hΩ)

@[simp]
theorem coe_imageInclusion {E Ω : IntermediateField K M} (hEΩ : E ≤ Ω)
    (hΩ : ∀ x ∈ Ω, IsIntegral K x) (x : normalizationImage A E) :
    (imageInclusion hEΩ hΩ x : M) = x :=
  Subring.coe_inclusion (normalizationImage_le hEΩ hΩ) x

theorem imageInclusion_comp_toNormalizationImage {E Ω : IntermediateField K M} (hEΩ : E ≤ Ω)
    (hΩ : ∀ x ∈ Ω, IsIntegral K x) :
    (imageInclusion hEΩ hΩ).comp (toNormalizationImage A E) = toNormalizationImage A Ω :=
  RingHom.ext fun a => Subtype.ext (by
    rw [RingHom.comp_apply, coe_imageInclusion, coe_toNormalizationImage,
      coe_toNormalizationImage])

/-- Over a field, an inclusion of subalgebras which becomes surjective after a field extension
of scalars is surjective (faithful flatness). -/
theorem surjective_of_lTensor_surjective {E Ω N : Type*} [Field E] [Field Ω] [Algebra E Ω]
    [CommRing N] [Algebra E N] (C D : Subalgebra E N) (h : C ≤ D)
    (hs : Function.Surjective ((Subalgebra.inclusion h).toLinearMap.lTensor Ω)) :
    Function.Surjective (Subalgebra.inclusion h).toLinearMap :=
  (Module.FaithfullyFlat.lTensor_surjective_iff_surjective E Ω _).1 hs

/-- **Level transfer.** If the image of `B_Ω` lies in `Ω[T]` with `T ⊆ E₀(A)` integral over `A`,
then for every `E₀ ≤ E ≤ Ω` the image of `B_E` lies in `E[T]`. -/
theorem range_normalizationι_subset_adjoin (Ω : IntermediateField K M) [Algebra.IsAlgebraic K Ω]
    (hld : Ω.LinearDisjoint (fracField A)) {E₀ : IntermediateField K M} {T : Finset M}
    (hT : ∀ t ∈ T, t ∈ baseField A E₀ ∧ IsIntegral A t)
    (hgen : ((normalizationι A Ω).range : Set M) ⊆ Algebra.adjoin Ω (T : Set M))
    (E : IntermediateField K M) (hE₀ : E₀ ≤ E) (hEΩ : E ≤ Ω) :
    ((normalizationι A E).range : Set M) ⊆ Algebra.adjoin E (T : Set M) := by
  let : Algebra E Ω := (IntermediateField.inclusion hEΩ).toAlgebra
  have : IsScalarTower E Ω M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hΩ := forall_isIntegral_of_isAlgebraic Ω
  have hE : ∀ x ∈ E, IsIntegral K x := fun x hx => hΩ x (hEΩ hx)
  have : Algebra.IsAlgebraic K E := ⟨fun x =>
    ((isIntegral_algHom_iff E.val E.val.injective).1 (hE x x.2)).isAlgebraic⟩
  let C := Algebra.adjoin E (T : Set M)
  let R := (normalizationι A E).range
  have hTE : ∀ t ∈ T, t ∈ R := fun t ht =>
    (mem_range_normalizationι_iff hE).2 ⟨baseField_mono hE₀ (hT t ht).1, (hT t ht).2⟩
  have hC : C ≤ R := Algebra.adjoin_le hTE
  let eN := AlgEquiv.ofInjective (normalizationι A E) (normalizationι_injective A E)
  let ψR : Ω ⊗[E] R →ₐ[Ω] M :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω M) R.val fun _ _ => Commute.all _ _
  let ψC : Ω ⊗[E] C →ₐ[Ω] M :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω M) C.val fun _ _ => Commute.all _ _
  have hψR : ∀ w, ψR w = tensorNormalizationLift A Ω E
      (Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[Ω] Ω) eN.symm w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul ω r =>
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        tensorNormalizationLift_tmul]
      have : normalizationι A E (eN.symm r) = r := by
        have := AlgEquiv.ofInjective_apply (normalizationι A E) (normalizationι_injective A E)
          (eN.symm r)
        rw [AlgEquiv.apply_symm_apply] at this
        exact this.symm
      change (ω : M) * (r : M) = ((AlgEquiv.refl : Ω ≃ₐ[Ω] Ω) ω : M) *
        normalizationι A E (eN.symm r)
      rw [this]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hψRinj : Function.Injective ψR := by
    have : ⇑ψR = ⇑(tensorNormalizationLift A Ω E) ∘
        ⇑(Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[Ω] Ω) eN.symm) := funext hψR
    rw [this]
    exact (tensorNormalizationLift_injective hld).comp (AlgEquiv.injective _)
  let i := (Subalgebra.inclusion hC).toLinearMap
  have hfac : ∀ w, ψR (i.lTensor Ω w) = ψC w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul ω c => simp [ψR, ψC, i]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsurj : Function.Surjective (i.lTensor Ω) := by
    intro z
    have hz : ψR z ∈ (normalizationι A Ω).range := by
      rw [hψR]
      exact range_tensorNormalizationLift_le ⟨_, rfl⟩
    have hz' : ψR z ∈ ψC.range := by
      refine Algebra.adjoin_le ?_ (hgen hz)
      intro t ht
      exact ⟨1 ⊗ₜ ⟨t, Algebra.subset_adjoin ht⟩, by simp [ψC]⟩
    obtain ⟨w, hw⟩ := hz'
    exact ⟨w, hψRinj ((hfac w).trans hw)⟩
  have hisurj : Function.Surjective i := surjective_of_lTensor_surjective C R hC hsurj
  intro x hx
  obtain ⟨c, hc⟩ := hisurj ⟨x, hx⟩
  have : (c : M) = x := congrArg Subtype.val hc
  rw [← this]
  exact c.2

end DeJongAlterations.StableModification.Perfection

end
