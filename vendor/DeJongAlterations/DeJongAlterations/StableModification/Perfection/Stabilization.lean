/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL)
-/
import DeJongAlterations.StableModification.Perfection.Normalization
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Stabilization of normalizations under purely inseparable base change

Blueprint chapter `sm-dj-perfection`, nodes `lem:sm-dj-perfection-integral-closure-stabilizes` and
`lem:sm-dj-perfection-smooth-curve` (new route, not in de Jong 1996; it replaces de Jong 4.11 (c),
(d) when generic étaleness of the alteration is not required).

We work in the model of `Perfection/Normalization.lean`: `K ⊆ M` fields, `A ⊆ M` a finitely
generated `K`-algebra of dimension at most one with fraction field `F = K(A)`, and for an
intermediate field `E` the rings `E[A] ⊆ E(A)` and the normalization `B_E` of `E[A]`.

Let `Ω` be an intermediate field which is algebraic over `K` and linearly disjoint from `F`
(e.g. `Ω` purely inseparable over `K` and `F / K` geometrically reduced,
`linearDisjoint_of_isGeometricallyReduced`). For `E ≤ Ω` (given as `[Algebra E Ω]` with
`[IsScalarTower E Ω M]`):

* `algEquivBaseRing`, `algEquivBaseField`: under linear disjointness of `E` and `F`,
  `E ⊗_K A ≅ E[A]` and `E ⊗_K F ≅ E(A)`, so `B_E` is the normalization of `E ⊗_K A`;
* `tensorBaseFieldLift_injective`: `Ω ⊗_E E(A) → M` is injective. A `K`-basis of `F` is an
  `E`-basis of `E(A)` (since `E(A) = E·F` for algebraic `E`) which stays `Ω`-linearly independent;
* `tensorNormalizationLift_injective`: hence `Ω ⊗_E B_E → M` is injective (flatness over `E`);
* `exists_finset_stabilization`, `exists_stabilization`: `B_Ω` is a finite `Ω[A]`-module (Codex
  finiteness of normalization over any field); its finitely many generators lie in `E₀(A)` for some
  `E₀ ≤ Ω` finite over `K` (directed union), and `B_Ω ⊆ Ω[T]` for a finite `T ⊆ E₀(A)`. For
  `E₀ ≤ E ≤ Ω` the image of `Ω ⊗_E B_E` is then all of `B_Ω`, so `Ω ⊗_E B_E ≅ B_Ω`
  (`algEquivNormalization`). This is "`B_m ⊗_{K_m} K^{perf} ≅ B_∞`".
* `exists_smooth_normalization`: if moreover `Ω` is perfect, `B_Ω` is smooth over `Ω`
  (`smooth_normalization_of_perfectField`) and smoothness descends along the faithfully flat
  `E → Ω` (Mathlib, `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`): `B_E` is smooth
  over `E` for every `E₀ ≤ E ≤ Ω`.
* `exists_smooth_normalization_rootField`: with `Ω = perfectClosure K M` (`M` perfect, e.g.
  algebraically closed) and `F / K` geometrically reduced, there is `m` such that for all `m' ≥ m`
  the normalization of `K^{1/q^{m'}} ⊗_K A` is smooth over `K^{1/q^{m'}}`; in characteristic zero
  `K^{1/q^m} = K` for all `m`.
* `smooth_tensor_normalization`: the geometric fibre `Ω' ⊗_E B_E` is smooth over any field
  `Ω' ⊇ E` (e.g. an algebraic closure), by base change.
-/

noncomputable section

open IntermediateField TensorProduct

namespace DeJongAlterations.StableModification.Perfection

universe u

/-- A linear map sending a basis to a linearly independent family is injective. -/
theorem injective_of_linearIndependent_comp_basis {R V W ι : Type*} [Ring R] [AddCommGroup V]
    [Module R V] [AddCommGroup W] [Module R W] (b : Module.Basis ι R V) (f : V →ₗ[R] W)
    (h : LinearIndependent R (f ∘ b)) : Function.Injective f := by
  have hf : f = Finsupp.linearCombination R (f ∘ b) ∘ₗ b.repr.toLinearMap :=
    b.ext fun i => by simp
  rw [hf, LinearMap.coe_comp]
  exact (show Function.Injective (Finsupp.linearCombination R (f ∘ b)) from h).comp
    b.repr.injective

variable {K : Type u} {M : Type u} [Field K] [Field M] [Algebra K M] (A : Subalgebra K M)

/-- The fraction field `F = K(A)` of `A` inside `M`. -/
abbrev fracField : IntermediateField K M := IntermediateField.adjoin K (A : Set M)

/-- A chosen `K`-basis of `F = K(A)`. -/
abbrev fracBasis : Module.Basis (Module.Basis.ofVectorSpaceIndex K (fracField A)) K (fracField A) :=
  Module.Basis.ofVectorSpace K (fracField A)

variable {A}

theorem forall_isIntegral_of_isAlgebraic (E : IntermediateField K M) [Algebra.IsAlgebraic K E] :
    ∀ x ∈ E, IsIntegral K x := fun x hx =>
  (Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : E)).map E.val

theorem fracField_le_baseField (E : IntermediateField K M) {x : M} (hx : x ∈ fracField A) :
    x ∈ baseField A E := by
  have : fracField A ≤ (baseField A E).restrictScalars K :=
    IntermediateField.adjoin_le_iff.2 (subset_baseField A E)
  exact this hx

/-- For algebraic `E / K`, the field `E(A)` is spanned over `E` by `F = K(A)`. -/
theorem mem_span_of_mem_baseField (E : IntermediateField K M) [Algebra.IsAlgebraic K E] {x : M}
    (hx : x ∈ baseField A E) : x ∈ Submodule.span E (fracField A : Set M) := by
  have hx' : x ∈ (E ⊔ fracField A).toSubalgebra := by
    have : x ∈ (baseField A E).restrictScalars K := hx
    rwa [restrictScalars_baseField] at this
  rw [IntermediateField.sup_toSubalgebra_of_isAlgebraic_left, Algebra.sup_def] at hx'
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · have : y = (⟨y, hy⟩ : E) • (1 : M) := by rw [Algebra.smul_def, mul_one]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (one_mem _))
    · exact Submodule.subset_span hy
  | algebraMap c => exact Submodule.subset_span ((fracField A).algebraMap_mem c)
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz =>
    have := Submodule.mul_mem_mul hy hz
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem ha hb

/-- For algebraic `E / K`, the field `E(A)` is spanned over `E` by a `K`-basis of `F`. -/
theorem mem_span_fracBasis_of_mem_baseField (E : IntermediateField K M) [Algebra.IsAlgebraic K E]
    {x : M} (hx : x ∈ baseField A E) :
    x ∈ Submodule.span E (Set.range fun i => (fracBasis A i : M)) := by
  refine Submodule.span_le.2 ?_ (mem_span_of_mem_baseField E hx)
  intro f hf
  have h1 : (⟨f, hf⟩ : fracField A) ∈ Submodule.span K (Set.range (fracBasis A)) :=
    (fracBasis A).mem_span _
  have h2 : f ∈ Submodule.span K (Set.range fun i => (fracBasis A i : M)) := by
    have := Submodule.apply_mem_span_image_of_mem_span (fracField A).val.toLinearMap h1
    rwa [← Set.range_comp] at this
  exact Submodule.span_le_restrictScalars K E _ h2

/-- If `E` and `F = K(A)` are linearly disjoint and `E / K` is algebraic, a `K`-basis of `F` is an
`E`-basis of `E(A)`. -/
def baseFieldBasis (E : IntermediateField K M) [Algebra.IsAlgebraic K E]
    (hld : E.LinearDisjoint (fracField A)) :
    Module.Basis (Module.Basis.ofVectorSpaceIndex K (fracField A)) E (baseField A E) :=
  Module.Basis.mk (v := fun i => ⟨(fracBasis A i : M), fracField_le_baseField E (fracBasis A i).2⟩)
    (LinearIndependent.of_comp (baseField A E).val.toLinearMap
      (hld.linearIndependent_right (fracBasis A).linearIndependent))
    (by
      rintro ⟨y, hy⟩ -
      have h := mem_span_fracBasis_of_mem_baseField E hy
      have heq : (Set.range fun i => (fracBasis A i : M)) = (baseField A E).val.toLinearMap ''
          Set.range (fun i => (⟨(fracBasis A i : M), fracField_le_baseField E (fracBasis A i).2⟩ :
            baseField A E)) := by
        rw [← Set.range_comp]
        rfl
      rw [heq, Submodule.span_image] at h
      obtain ⟨z, hz, hzy⟩ := h
      have : z = ⟨y, hy⟩ := Subtype.ext hzy
      exact this ▸ hz)

@[simp]
theorem baseFieldBasis_apply (E : IntermediateField K M) [Algebra.IsAlgebraic K E]
    (hld : E.LinearDisjoint (fracField A)) (i) :
    ((baseFieldBasis E hld i : baseField A E) : M) = (fracBasis A i : M) := by
  simp [baseFieldBasis]

section TensorModel

/-! ### The model computes the tensor products

Under linear disjointness of `E` and `F`, the subrings `E[A] ⊆ E(A) ⊆ M` are the images of
injective maps from `E ⊗_K A` and `E ⊗_K F`; so `normalization A E` is the normalization of
`E ⊗_K A` (in its fraction field `E ⊗_K F`). -/

variable (A) (E : IntermediateField K M)

/-- The multiplication map `E ⊗_K F → M`. -/
def tensorFracFieldLift : E ⊗[K] fracField A →ₐ[E] M :=
  Algebra.TensorProduct.lift (Algebra.ofId E M) (fracField A).val fun _ _ => Commute.all _ _

/-- The multiplication map `E ⊗_K A → M`. -/
def tensorBaseRingLift : E ⊗[K] A →ₐ[E] M :=
  Algebra.TensorProduct.lift (Algebra.ofId E M) A.val fun _ _ => Commute.all _ _

@[simp]
theorem tensorFracFieldLift_tmul (e : E) (f : fracField A) :
    tensorFracFieldLift A E (e ⊗ₜ f) = (e : M) * f := rfl

@[simp]
theorem tensorBaseRingLift_tmul (e : E) (a : A) :
    tensorBaseRingLift A E (e ⊗ₜ a) = (e : M) * a := rfl

variable {A E}

/-- `E ⊗_K F → M` is injective when `E` and `F` are linearly disjoint. -/
theorem tensorFracFieldLift_injective (hld : E.LinearDisjoint (fracField A)) :
    Function.Injective (tensorFracFieldLift A E) := by
  refine injective_of_linearIndependent_comp_basis (Algebra.TensorProduct.basis E (fracBasis A))
    (tensorFracFieldLift A E).toLinearMap ?_
  have h : ((tensorFracFieldLift A E).toLinearMap ∘ Algebra.TensorProduct.basis E (fracBasis A)) =
      (fracField A).val ∘ fracBasis A := by
    funext i
    simp [Algebra.TensorProduct.basis_apply]
  rw [h]
  exact hld.linearIndependent_right (fracBasis A).linearIndependent

/-- `E ⊗_K A → M` is injective when `E` and `F` are linearly disjoint. -/
theorem tensorBaseRingLift_injective (hld : E.LinearDisjoint (fracField A)) :
    Function.Injective (tensorBaseRingLift A E) := by
  let j : A →ₗ[K] fracField A :=
    { toFun := fun a => ⟨a, IntermediateField.subset_adjoin K _ a.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Function.Injective j := fun a b h =>
    Subtype.ext (congrArg (fun y : fracField A => (y : M)) h)
  have hfac : ∀ x, tensorBaseRingLift A E x = tensorFracFieldLift A E (j.lTensor E x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have : ⇑(tensorBaseRingLift A E) = (tensorFracFieldLift A E) ∘ (j.lTensor E) := funext hfac
  rw [this]
  exact (tensorFracFieldLift_injective hld).comp
    (Module.Flat.lTensor_preserves_injective_linearMap j hj)

/-- The image of `E ⊗_K A` is `E[A]`. -/
theorem range_tensorBaseRingLift : (tensorBaseRingLift A E).range = baseRing A E := by
  refine le_antisymm ?_ (Algebra.adjoin_le fun a ha => ⟨1 ⊗ₜ ⟨a, ha⟩, by simp⟩)
  intro x hx
  rw [AlgHom.mem_range] at hx
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    rw [tensorBaseRingLift_tmul]
    exact mul_mem ((baseRing A E).algebraMap_mem e) (subset_baseRing A E a.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- The image of `E ⊗_K F` is `E(A)`, for algebraic `E / K`. -/
theorem range_tensorFracFieldLift [Algebra.IsAlgebraic K E] :
    (tensorFracFieldLift A E).range = (baseField A E).toSubalgebra := by
  refine le_antisymm ?_ fun x hx => ?_
  · intro x hx
    rw [AlgHom.mem_range] at hx
    obtain ⟨z, rfl⟩ := hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul e f =>
      rw [tensorFracFieldLift_tmul]
      exact mul_mem ((baseField A E).algebraMap_mem e) (fracField_le_baseField E f.2)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · have h := mem_span_of_mem_baseField (A := A) E hx
    clear hx
    induction h using Submodule.span_induction with
    | mem f hf => exact ⟨1 ⊗ₜ ⟨f, hf⟩, by simp⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul e x _ hx =>
      rw [Algebra.smul_def]
      exact mul_mem ⟨algebraMap E _ e, (tensorFracFieldLift A E).commutes e⟩ hx

/-- Under linear disjointness, `E ⊗_K A ≅ E[A]`. -/
def algEquivBaseRing (hld : E.LinearDisjoint (fracField A)) : E ⊗[K] A ≃ₐ[E] baseRing A E :=
  (AlgEquiv.ofInjective _ (tensorBaseRingLift_injective hld)).trans
    (Subalgebra.equivOfEq _ _ range_tensorBaseRingLift)

/-- Under linear disjointness and for algebraic `E / K`, `E ⊗_K F ≅ E(A)`; in particular
`E ⊗_K F` is a field. -/
def algEquivBaseField [Algebra.IsAlgebraic K E] (hld : E.LinearDisjoint (fracField A)) :
    E ⊗[K] fracField A ≃ₐ[E] (baseField A E).toSubalgebra :=
  (AlgEquiv.ofInjective _ (tensorFracFieldLift_injective hld)).trans
    (Subalgebra.equivOfEq _ _ range_tensorFracFieldLift)

end TensorModel

section Pair

variable (A) (Ω E : IntermediateField K M) [Algebra E Ω] [IsScalarTower E Ω M]

theorem le_of_isScalarTower : E ≤ Ω := fun x hx => by
  have : algebraMap Ω M (algebraMap E Ω ⟨x, hx⟩) = x :=
    (IsScalarTower.algebraMap_apply E Ω M ⟨x, hx⟩).symm
  rw [← this]
  exact (algebraMap E Ω ⟨x, hx⟩).2

/-- The multiplication map `Ω ⊗_E E(A) → M`. -/
def tensorBaseFieldLift : Ω ⊗[E] baseField A E →ₐ[Ω] M :=
  Algebra.TensorProduct.lift (Algebra.ofId Ω M) (baseField A E).val fun _ _ => Commute.all _ _

/-- The multiplication map `Ω ⊗_E B_E → M`. -/
def tensorNormalizationLift : Ω ⊗[E] normalization A E →ₐ[Ω] M :=
  Algebra.TensorProduct.lift (Algebra.ofId Ω M) (normalizationι A E) fun _ _ => Commute.all _ _

@[simp]
theorem tensorBaseFieldLift_tmul (ω : Ω) (x : baseField A E) :
    tensorBaseFieldLift A Ω E (ω ⊗ₜ x) = (ω : M) * x := rfl

@[simp]
theorem tensorNormalizationLift_tmul (ω : Ω) (x : normalization A E) :
    tensorNormalizationLift A Ω E (ω ⊗ₜ x) = (ω : M) * normalizationι A E x := rfl

variable {A Ω E}

/-- **Linear disjointness at level `E`.** If `Ω` and `F` are linearly disjoint over `K` and
`E ≤ Ω` is algebraic over `K`, then `Ω ⊗_E E(A) → M` is injective. -/
theorem tensorBaseFieldLift_injective [Algebra.IsAlgebraic K E]
    (hld : Ω.LinearDisjoint (fracField A)) : Function.Injective (tensorBaseFieldLift A Ω E) := by
  have hldE : E.LinearDisjoint (fracField A) := hld.of_le_left (le_of_isScalarTower Ω E)
  let b := baseFieldBasis E hldE
  refine injective_of_linearIndependent_comp_basis (Algebra.TensorProduct.basis Ω b)
    (tensorBaseFieldLift A Ω E).toLinearMap ?_
  have h : ((tensorBaseFieldLift A Ω E).toLinearMap ∘ Algebra.TensorProduct.basis Ω b) =
      (fracField A).val ∘ fracBasis A := by
    funext i
    simp [b, Algebra.TensorProduct.basis_apply]
  rw [h]
  exact hld.linearIndependent_right (fracBasis A).linearIndependent

/-- `Ω ⊗_E B_E → M` is injective. -/
theorem tensorNormalizationLift_injective [Algebra.IsAlgebraic K E]
    (hld : Ω.LinearDisjoint (fracField A)) :
    Function.Injective (tensorNormalizationLift A Ω E) := by
  let j : normalization A E →ₗ[E] baseField A E :=
    { toFun := fun x => (x : baseField A E)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Function.Injective j := Subtype.val_injective
  have hfac : ∀ x, tensorNormalizationLift A Ω E x =
      tensorBaseFieldLift A Ω E (j.lTensor Ω x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have : tensorNormalizationLift A Ω E = (tensorBaseFieldLift A Ω E) ∘ (j.lTensor Ω) :=
    funext hfac
  rw [this]
  exact (tensorBaseFieldLift_injective hld).comp
    (Module.Flat.lTensor_preserves_injective_linearMap j hj)

/-- The image of `Ω ⊗_E B_E` lies in the image of `B_Ω`. -/
theorem range_tensorNormalizationLift_le [Algebra.IsAlgebraic K Ω] :
    (tensorNormalizationLift A Ω E).range ≤ (normalizationι A Ω).range := by
  have hΩ := forall_isIntegral_of_isAlgebraic Ω
  have hE : ∀ x ∈ E, IsIntegral K x := fun x hx => hΩ x (le_of_isScalarTower Ω E hx)
  intro x hx
  rw [AlgHom.mem_range] at hx
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω n =>
    rw [tensorNormalizationLift_tmul]
    refine mul_mem ⟨algebraMap Ω _ ω, rfl⟩ ?_
    obtain ⟨hn₁, hn₂⟩ := (mem_range_normalizationι_iff hE).1 ⟨n, rfl⟩
    exact (mem_range_normalizationι_iff hΩ).2
      ⟨baseField_mono (le_of_isScalarTower Ω E) hn₁, hn₂⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

end Pair

variable (A)

/-- **Stabilization (generators).** There are `E₀ ≤ Ω` finite over `K` and a finite set
`T ⊆ E₀(A)` of elements integral over `A` (generators of `A` together with module generators of
`B_Ω` over `Ω[A]`, Codex finiteness of normalization) such that the image of `B_Ω` in `M` is
contained in `Ω[T]`. -/
theorem exists_finset_stabilization (Ω : IntermediateField K M) [Algebra.IsAlgebraic K Ω]
    [Algebra.FiniteType K A] :
    ∃ E₀ : IntermediateField K M, E₀ ≤ Ω ∧ FiniteDimensional K E₀ ∧
      ∃ T : Finset M, (∀ t ∈ T, t ∈ baseField A E₀ ∧ IsIntegral A t) ∧
        ((normalizationι A Ω).range : Set M) ⊆ Algebra.adjoin Ω (T : Set M) := by
  classical
  have hΩ := forall_isIntegral_of_isAlgebraic Ω
  have := finiteType_baseRing (A := A) (E := Ω)
  have : Module.Finite (baseRing A Ω) (normalization A Ω) :=
    Algebra.IntegralClosureFiniteType.finite_integralClosure Ω (baseRing A Ω) (baseField A Ω)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := baseRing A Ω) (M := normalization A Ω)
  obtain ⟨G, hG⟩ := exists_finset_adjoin_eq A
  have hex : ∀ b : normalization A Ω, ∃ E' : IntermediateField K M, E' ≤ Ω ∧
      FiniteDimensional K E' ∧ normalizationι A Ω b ∈ baseField A E' := fun b =>
    exists_finiteDimensional_of_mem_adjoin Ω (A : Set M) (b : baseField A Ω).2
  choose Eb hEbΩ hEbfin hEbmem using hex
  let E₀ := ⨆ b ∈ s, Eb b
  have hGA : ∀ g ∈ G, g ∈ A := fun g hg => hG ▸ Algebra.subset_adjoin hg
  refine ⟨E₀, iSup₂_le fun b _ => hEbΩ b, inferInstance, G ∪ s.image (normalizationι A Ω), ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_union, Finset.mem_image] at ht
    rcases ht with ht | ⟨b, hb, rfl⟩
    · exact ⟨subset_baseField A E₀ (hGA t ht),
        isIntegral_algebraMap (R := A) (A := M) (x := ⟨t, hGA t ht⟩)⟩
    · exact ⟨baseField_mono (le_iSup₂ (f := fun b _ => Eb b) b hb) (hEbmem b),
        ((mem_range_normalizationι_iff hΩ).1 ⟨b, rfl⟩).2⟩
  · have hR : (baseRing A Ω : Set M) ⊆
        Algebra.adjoin Ω ((G ∪ s.image (normalizationι A Ω) : Finset M) : Set M) := by
      intro x hx
      rw [SetLike.mem_coe, baseRing_eq_adjoin (E := Ω) hG] at hx
      exact Algebra.adjoin_mono (by simp) hx
    intro x hx
    rw [SetLike.mem_coe, AlgHom.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    have hy : y ∈ Submodule.span (baseRing A Ω) (s : Set (normalization A Ω)) := hs ▸ trivial
    induction hy using Submodule.span_induction with
    | mem b hb =>
      exact Algebra.subset_adjoin
        (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r y _ hy =>
      have : normalizationι A Ω (r • y) = (r : M) * normalizationι A Ω y := rfl
      rw [this]
      exact mul_mem (hR r.2) hy

/-- **Stabilization (generators), algebra form.** For every `E₀ ≤ E ≤ Ω`, with `E₀` as in
`exists_finset_stabilization`, the image of `B_Ω` in `M` is generated as an `Ω`-algebra by the
image of `B_E`. -/
theorem exists_stabilization (Ω : IntermediateField K M) [Algebra.IsAlgebraic K Ω]
    [Algebra.FiniteType K A] :
    ∃ E₀ : IntermediateField K M, E₀ ≤ Ω ∧ FiniteDimensional K E₀ ∧
      ∀ E : IntermediateField K M, E₀ ≤ E → E ≤ Ω →
        ((normalizationι A Ω).range : Set M) ⊆
          Algebra.adjoin Ω ((normalizationι A E).range : Set M) := by
  obtain ⟨E₀, hE₀Ω, hfin, T, hT, hgen⟩ := exists_finset_stabilization A Ω
  refine ⟨E₀, hE₀Ω, hfin, fun E hE₀ hEΩ => hgen.trans (Algebra.adjoin_mono fun t ht => ?_)⟩
  have hE : ∀ x ∈ E, IsIntegral K x := fun x hx => forall_isIntegral_of_isAlgebraic Ω x (hEΩ hx)
  exact (mem_range_normalizationι_iff hE).2 ⟨baseField_mono hE₀ (hT t ht).1, (hT t ht).2⟩

section Pair

variable {A} (Ω E : IntermediateField K M) [Algebra E Ω] [IsScalarTower E Ω M]

/-- If the image of `B_Ω` is generated over `Ω` by the image of `B_E`, then `Ω ⊗_E B_E` and `B_Ω`
have the same image in `M`. -/
theorem range_tensorNormalizationLift_eq [Algebra.IsAlgebraic K Ω]
    (hgen : ((normalizationι A Ω).range : Set M) ⊆
      Algebra.adjoin Ω ((normalizationι A E).range : Set M)) :
    (tensorNormalizationLift A Ω E).range = (normalizationι A Ω).range := by
  refine le_antisymm (range_tensorNormalizationLift_le) fun x hx => ?_
  refine Algebra.adjoin_le ?_ (hgen hx)
  rintro _ ⟨n, rfl⟩
  exact ⟨1 ⊗ₜ n, by simp⟩

/-- **Stabilization (isomorphism).** Under linear disjointness and generation,
`Ω ⊗_E B_E ≅ B_Ω` as `Ω`-algebras: "`B_m ⊗_{K_m} K^{perf} ≅ B_∞`". -/
def algEquivNormalization [Algebra.IsAlgebraic K Ω] (hld : Ω.LinearDisjoint (fracField A))
    (hgen : ((normalizationι A Ω).range : Set M) ⊆
      Algebra.adjoin Ω ((normalizationι A E).range : Set M)) :
    Ω ⊗[E] normalization A E ≃ₐ[Ω] normalization A Ω :=
  have : Algebra.IsAlgebraic K E := by
    have hΩ := forall_isIntegral_of_isAlgebraic Ω
    refine ⟨fun x => ?_⟩
    have : IsIntegral K (x : M) := hΩ x (le_of_isScalarTower Ω E x.2)
    exact ((isIntegral_algHom_iff E.val E.val.injective).1 this).isAlgebraic
  (AlgEquiv.ofInjective _ (tensorNormalizationLift_injective hld)).trans
    ((Subalgebra.equivOfEq _ _ (range_tensorNormalizationLift_eq Ω E hgen)).trans
      (AlgEquiv.ofInjective _ (normalizationι_injective A Ω)).symm)

/-- Smoothness descends from `B_Ω` to `B_E` once `Ω ⊗_E B_E ≅ B_Ω`. -/
theorem smooth_of_algEquiv {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] {C D : Type*} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra T D] [Algebra.Smooth T D] (e : T ⊗[R] C ≃ₐ[T] D) : Algebra.Smooth R C := by
  have : Algebra.Smooth T (T ⊗[R] C) := Algebra.Smooth.of_equiv e.symm
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat T

end Pair

/-- **Purely inseparable base change gives a smooth curve.** Let `A ⊆ M` be a finitely generated
`K`-algebra of dimension at most one with fraction field `F = K(A)`, and `Ω ⊆ M` a perfect
intermediate field, algebraic over `K` and linearly disjoint from `F`. Then there is `E₀ ≤ Ω`
finite over `K` such that for every intermediate field `E₀ ≤ E ≤ Ω` the normalization `B_E` of
`E ⊗_K A` is smooth over `E`, and `Ω ⊗_E B_E ≅ B_Ω`. -/
theorem exists_smooth_normalization (Ω : IntermediateField K M) [Algebra.IsAlgebraic K Ω]
    [PerfectField Ω] [Algebra.FiniteType K A] [Ring.DimensionLEOne A]
    (hld : Ω.LinearDisjoint (fracField A)) :
    ∃ E₀ : IntermediateField K M, E₀ ≤ Ω ∧ FiniteDimensional K E₀ ∧
      ∀ E : IntermediateField K M, E₀ ≤ E → (hEΩ : E ≤ Ω) →
        Algebra.Smooth E (normalization A E) ∧
        letI : Algebra E Ω := (IntermediateField.inclusion hEΩ).toAlgebra
        Nonempty (Ω ⊗[E] normalization A E ≃ₐ[Ω] normalization A Ω) := by
  obtain ⟨E₀, hE₀Ω, hfin, hgen⟩ := exists_stabilization A Ω
  refine ⟨E₀, hE₀Ω, hfin, fun E hE₀ hEΩ => ?_⟩
  let : Algebra E Ω := (IntermediateField.inclusion hEΩ).toAlgebra
  have : IsScalarTower E Ω M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hΩ := forall_isIntegral_of_isAlgebraic Ω
  have : Algebra.Smooth Ω (normalization A Ω) := smooth_normalization_of_perfectField (A := A) (E := Ω) hΩ
  let e := algEquivNormalization Ω E hld (hgen E hE₀ hEΩ)
  exact ⟨smooth_of_algEquiv (R := E) (T := Ω) (D := normalization A Ω) e, ⟨e⟩⟩

/-- **The geometric fibre.** If `B_E` is smooth over `E`, then so is its base change to any field
extension `Ω'` of `E`, e.g. an algebraic closure; this is the form consumed by the
geometric-fibre semistability predicate of the Temkin interface (decision D4). -/
theorem smooth_tensor_normalization (E : IntermediateField K M) [Algebra.Smooth E (normalization A E)]
    (Ω' : Type*) [Field Ω'] [Algebra E Ω'] : Algebra.Smooth Ω' (Ω' ⊗[E] normalization A E) :=
  Algebra.Smooth.baseChange E (normalization A E) Ω'

/-- **The `K_m` form.** Let `M` be perfect (e.g. algebraically closed), `A ⊆ M` a finitely
generated `K`-algebra of dimension at most one whose fraction field `F = K(A)` is geometrically
reduced over `K`. Then there is `m` such that for all `m' ≥ m`, the normalization of
`K^{1/q^{m'}} ⊗_K A` is smooth over `K_{m'} = K^{1/q^{m'}}` (`q` the exponential characteristic).
In characteristic zero every `K_m` is `K` (`rootField_eq_bot_of_charZero`). -/
theorem exists_smooth_normalization_rootField [PerfectField M] [Algebra.FiniteType K A]
    [Ring.DimensionLEOne A] [Algebra.IsGeometricallyReduced K (fracField A)] :
    ∃ m : ℕ, ∀ m' ≥ m, Algebra.Smooth (rootField K M m') (normalization A (rootField K M m')) := by
  have hld : (perfectClosure K M).LinearDisjoint (fracField A) :=
    linearDisjoint_of_isGeometricallyReduced K (perfectClosure K M) (fracField A)
  obtain ⟨E₀, hE₀Ω, hfin, h⟩ := exists_smooth_normalization A (perfectClosure K M) hld
  have : IsPurelyInseparable K E₀ := (le_perfectClosure_iff K M E₀).1 hE₀Ω
  refine ⟨IsPurelyInseparable.exponent K E₀, fun m' hm' => ?_⟩
  exact (h _ ((le_rootField_exponent E₀).trans (rootField_mono hm'))
    (rootField_le_perfectClosure m')).1

end DeJongAlterations.StableModification.Perfection

end
