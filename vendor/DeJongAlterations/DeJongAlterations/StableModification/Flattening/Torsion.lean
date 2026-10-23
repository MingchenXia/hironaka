import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.Flat

/-!
# Torsion and strict transforms: the algebra

Let `A` be a domain and `M` an `A`-module. The `A`-torsion `torsion A M` is the kernel of
`M → K ⊗_A M` for the fraction field `K` of `A`; for an `A`-algebra `M` it is an ideal
(`torsionIdeal`). Over an affine open `Spec A` of an integral base and an affine open `Spec M`
of `W ×_S Spec A`, the strict transform of `W` (the scheme-theoretic closure of the generic fibre,
de Jong 2.18, `dejong96-alterations:page-0011`) is cut out by `torsion A M`, and it is flat over
`A` iff `M ⧸ torsion A M` is a flat `A`-module. This file proves the algebra behind the
flattening statement (blueprint chapter `sm-flattening`, Temkin, *Stable modification of
relative curves*, §3.4, with `P` = flatness):

* `eq_zero_iff_mem_torsion_of_isBaseChange` (`lem:sm-flat-torsion-kernel`): if `g : M → N` is a
  base change along `A → k`, where every nonzero element of `A` becomes a unit in the nonzero
  ring `k` (e.g. the residue field of the generic point), then `ker g = torsion A M`;
  `eq_zero_iff_of_isPushout` is the same statement for a pushout square of rings.
* `flat_quotient_torsion_of_flat_quotient` (`lem:sm-flat-torsion-quotient`): if `J ⊆ M` becomes
  torsion in `A ⊗ M` and `A ⊗ (M ⧸ J)` is `A`-flat, then `(A ⊗ M) ⧸ torsion` is `A`-flat (and
  is `A ⊗ (M ⧸ J)`).
* `flat_quotient_torsion_baseChange` (`lem:sm-flat-strict-transform`): if `F → A'` is an injective
  map of domains and `N ⧸ torsion F N` is `F`-flat, then `(A' ⊗_F N) ⧸ torsion` is `A'`-flat;
  i.e. a flat strict transform base changes, along a dominant map of integral bases, to a flat
  strict transform. `flat_quotient_of_isPushout` is the form used on affine charts.
-/

open TensorProduct

universe u

namespace DeJongAlterations.StableModification.Flattening

section TorsionIdeal

variable (A M : Type*) [CommRing A] [CommRing M] [Algebra A M]

/-- The `A`-torsion of an `A`-algebra `M`, as an ideal of `M`. -/
def torsionIdeal : Ideal M where
  carrier := Submodule.torsion A M
  add_mem' := (Submodule.torsion A M).add_mem
  zero_mem' := (Submodule.torsion A M).zero_mem
  smul_mem' c x hx := by
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    refine (Submodule.mem_torsion_iff _).2 ⟨a, ?_⟩
    rw [smul_eq_mul, ← mul_smul_comm, ha, mul_zero]

variable {A M} in
@[simp]
lemma mem_torsionIdeal {x : M} : x ∈ torsionIdeal A M ↔ x ∈ Submodule.torsion A M :=
  Iff.rfl

@[simp]
lemma restrictScalars_torsionIdeal :
    (torsionIdeal A M).restrictScalars A = Submodule.torsion A M :=
  rfl

end TorsionIdeal

/-- Over a domain, torsion elements are those killed by a nonzero scalar. -/
lemma mem_torsion_iff_of_isDomain {A N : Type*} [CommRing A] [IsDomain A] [AddCommGroup N]
    [Module A N] (x : N) : x ∈ Submodule.torsion A N ↔ ∃ a : A, a ≠ 0 ∧ a • x = 0 := by
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, nonZeroDivisors.ne_zero a.2, ha⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, hax⟩

/-- A linear map sends torsion to torsion. -/
lemma map_mem_torsion {A N N' : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') {x : N}
    (hx : x ∈ Submodule.torsion A N) : g x ∈ Submodule.torsion A N' := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
  refine (Submodule.mem_torsion_iff _).2 ⟨a, ?_⟩
  rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, ha, map_zero]

section Kernel

variable {A k N Nk : Type*} [CommRing A] [IsDomain A] [CommRing k] [Nontrivial k] [Algebra A k]
  [AddCommGroup N] [Module A N] [AddCommGroup Nk] [Module A Nk] [Module k Nk]
  [IsScalarTower A k Nk]

/-- **Lemma `lem:sm-flat-torsion-kernel`.** Let `A` be a domain and `A → k` a map to a nonzero
ring under which every nonzero element of `A` becomes a unit (for instance the inclusion into
the fraction field, or into the residue field of the generic point). If `g : N → N_k` is a base
change of `N` along `A → k`, then `g x = 0` iff `x` is `A`-torsion. -/
theorem eq_zero_iff_mem_torsion_of_isBaseChange
    (hk : ∀ a : A, a ≠ 0 → IsUnit (algebraMap A k a)) {g : N →ₗ[A] Nk}
    (hg : IsBaseChange k g) (x : N) : g x = 0 ↔ x ∈ Submodule.torsion A N := by
  constructor
  swap
  · intro hx
    obtain ⟨a, ha, hax⟩ := (mem_torsion_iff_of_isDomain x).1 hx
    have h1 : algebraMap A k a • g x = 0 := by
      rw [algebraMap_smul, ← map_smul, hax, map_zero]
    exact ((hk a ha).smul_eq_zero).1 h1
  · intro hx
    let K := FractionRing A
    have hunit : ∀ y : nonZeroDivisors A, IsUnit (algebraMap A k y) :=
      fun y => hk y (nonZeroDivisors.ne_zero y.2)
    let φ : K →+* k := IsLocalization.lift hunit
    let _ : Algebra K k := φ.toAlgebra
    have _ : IsScalarTower A K k := IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap A k a = φ (algebraMap A K a)
      rw [IsLocalization.lift_eq]
    have _ : FaithfulSMul K k := (faithfulSMul_iff_algebraMap_injective K k).2 φ.injective
    let loc : N →ₗ[A] K ⊗[A] N := TensorProduct.mk A K N 1
    have hloc : IsBaseChange K loc := TensorProduct.isBaseChange A N K
    have _ : IsLocalizedModule (nonZeroDivisors A) loc :=
      (isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) K loc).2 hloc
    let mk₂ : K ⊗[A] N →ₗ[K] k ⊗[K] (K ⊗[A] N) := TensorProduct.mk K k (K ⊗[A] N) 1
    have hmk₂ : IsBaseChange k mk₂ := TensorProduct.isBaseChange K (K ⊗[A] N) k
    have hinj : Function.Injective mk₂ :=
      Module.Flat.tensorProduct_mk_injective K (K ⊗[A] N) k
    have hc := hloc.comp hmk₂
    let e := hg.equiv.symm.trans hc.equiv
    have he : e (g x) = mk₂ (loc x) := by
      have h1 : hg.equiv.symm (g x) = (1 : k) ⊗ₜ[A] x := by
        rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
      change hc.equiv (hg.equiv.symm (g x)) = _
      rw [h1, IsBaseChange.equiv_tmul, one_smul]
      rfl
    rw [hx, map_zero] at he
    have h0 : loc x = 0 := hinj (by rw [← he, map_zero])
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A) loc).1 h0
    exact (Submodule.mem_torsion_iff x).2 ⟨s, hs⟩

end Kernel

/-- **Lemma `lem:sm-flat-torsion-kernel`, pushout form.** In a pushout square of rings
`A → M`, `A → k`, `M → M_k`, `k → M_k` with `A` a domain, `k` nonzero and every nonzero element
of `A` a unit in `k`, an element `x ∈ M` dies in `M_k` iff `a x = 0` for some nonzero `a ∈ A`. -/
theorem eq_zero_iff_of_isPushout {A M k Mk : CommRingCat.{u}} {f₁ : A ⟶ M} {f₂ : A ⟶ k}
    {i₁ : M ⟶ Mk} {i₂ : k ⟶ Mk} (H : CategoryTheory.IsPushout f₁ f₂ i₁ i₂) [IsDomain A]
    [Nontrivial k] (hk : ∀ a : A, a ≠ 0 → IsUnit (f₂ a)) (x : M) :
    i₁ x = 0 ↔ ∃ a : A, a ≠ 0 ∧ f₁ a * x = 0 := by
  let _ : Algebra A M := f₁.hom.toAlgebra
  let _ : Algebra A k := f₂.hom.toAlgebra
  let _ : Algebra M Mk := i₁.hom.toAlgebra
  let _ : Algebra k Mk := i₂.hom.toAlgebra
  let _ : Algebra A Mk := (i₁.hom.comp f₁.hom).toAlgebra
  have _ : IsScalarTower A M Mk := IsScalarTower.of_algebraMap_eq' rfl
  have _ : IsScalarTower A k Mk := IsScalarTower.of_algebraMap_eq' (by
    change i₁.hom.comp f₁.hom = i₂.hom.comp f₂.hom
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, H.w])
  have hP : Algebra.IsPushout A M k Mk := CommRingCat.isPushout_iff_isPushout.1 H
  have hbc : IsBaseChange k (IsScalarTower.toAlgHom A M Mk).toLinearMap := hP.symm.out
  have := eq_zero_iff_mem_torsion_of_isBaseChange (k := k) hk hbc x
  change i₁ x = 0 ↔ _ at this
  rw [this, mem_torsion_iff_of_isDomain]
  simp only [Algebra.smul_def]
  rfl

section Quotient

/-- **Lemma `lem:sm-flat-torsion-quotient`**, for an exact sequence `J → M → Q → 0`. Let `R → A`
be a ring map, `M` an `R`-module, `J ⊆ M` a submodule whose elements become `A`-torsion in
`A ⊗_R M`, and `q : M → Q` surjective with kernel `J`. If `A ⊗_R Q` is flat over `A`, then so is
`(A ⊗_R M) ⧸ torsion`; indeed the kernel of `A ⊗ M → A ⊗ Q` is exactly the `A`-torsion. -/
theorem flat_quotient_torsion_of_exact {R A M Q : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (J : Submodule R M) (q : M →ₗ[R] Q) (hex : Function.Exact J.subtype q)
    (hq : Function.Surjective q)
    (hJ : ∀ x ∈ J, (1 : A) ⊗ₜ[R] x ∈ Submodule.torsion A (A ⊗[R] M))
    [Module.Flat A (A ⊗[R] Q)] :
    Module.Flat A ((A ⊗[R] M) ⧸ Submodule.torsion A (A ⊗[R] M)) := by
  let π : A ⊗[R] M →ₗ[A] A ⊗[R] Q := q.baseChange A
  have hπ' : ⇑π = ⇑(q.lTensor A) := LinearMap.baseChange_eq_ltensor _
  have hπ : Function.Surjective π := by
    rw [hπ']
    exact LinearMap.lTensor_surjective A hq
  have hex' := lTensor_exact A hex hq
  have hrange : ∀ z : A ⊗[R] J,
      (J.subtype.lTensor A) z ∈ Submodule.torsion A (A ⊗[R] M) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a j =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      have : a ⊗ₜ[R] (j : M) = a • ((1 : A) ⊗ₜ[R] (j : M)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (hJ j j.2)
    | add u v hu hv =>
      rw [map_add]
      exact Submodule.add_mem _ hu hv
  have hker : ∀ y, π y = 0 ↔ y ∈ Submodule.torsion A (A ⊗[R] M) := by
    intro y
    constructor
    · intro hy
      rw [hπ'] at hy
      obtain ⟨z, rfl⟩ := (hex' y).1 hy
      exact hrange z
    · intro hy
      have h := map_mem_torsion π hy
      rw [Module.Flat.torsion_eq_bot] at h
      exact h
  have hkerEq : Submodule.torsion A (A ⊗[R] M) = LinearMap.ker π := by
    ext y
    rw [LinearMap.mem_ker, hker]
  let e : ((A ⊗[R] M) ⧸ Submodule.torsion A (A ⊗[R] M)) ≃ₗ[A] A ⊗[R] Q :=
    (Submodule.quotEquivOfEq _ _ hkerEq).trans (π.quotKerEquivOfSurjective hπ)
  exact Module.Flat.of_linearEquiv e

/-- **Lemma `lem:sm-flat-torsion-quotient`.** Let `R → A` be a ring map, `M` an `R`-module and
`J ⊆ M` a submodule whose elements become `A`-torsion in `A ⊗_R M`. If `A ⊗_R (M ⧸ J)` is flat
over `A`, then so is `(A ⊗_R M) ⧸ torsion`. -/
theorem flat_quotient_torsion_of_flat_quotient {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] (J : Submodule R M)
    (hJ : ∀ x ∈ J, (1 : A) ⊗ₜ[R] x ∈ Submodule.torsion A (A ⊗[R] M))
    [Module.Flat A (A ⊗[R] (M ⧸ J))] :
    Module.Flat A ((A ⊗[R] M) ⧸ Submodule.torsion A (A ⊗[R] M)) :=
  flat_quotient_torsion_of_exact J J.mkQ (LinearMap.exact_subtype_mkQ J)
    (Submodule.mkQ_surjective J) hJ

/-- **Lemma `lem:sm-flat-torsion-quotient`**, for a quotient ring `M ⧸ J` of an `R`-algebra. -/
theorem flat_quotient_torsion_of_flat_quotient_ideal {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [CommRing M] [Algebra R M] (J : Ideal M)
    (hJ : ∀ x ∈ J, (1 : A) ⊗ₜ[R] x ∈ Submodule.torsion A (A ⊗[R] M))
    [Module.Flat A (A ⊗[R] (M ⧸ J))] :
    Module.Flat A ((A ⊗[R] M) ⧸ Submodule.torsion A (A ⊗[R] M)) := by
  refine flat_quotient_torsion_of_exact (J.restrictScalars R) (Ideal.Quotient.mkₐ R J).toLinearMap
    (fun y => ?_) (Ideal.Quotient.mkₐ_surjective R J) hJ
  change Ideal.Quotient.mk J y = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact z.2

/-- Flatness of the quotient by torsion is invariant under linear isomorphisms. -/
theorem flat_quotient_torsion_of_linearEquiv {A M M' : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    [Module.Flat A (M ⧸ Submodule.torsion A M)] :
    Module.Flat A (M' ⧸ Submodule.torsion A M') := by
  have h : (Submodule.torsion A M).map (e : M →ₗ[A] M') = Submodule.torsion A M' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact map_mem_torsion (e : M →ₗ[A] M') hx
    · intro hy
      refine ⟨e.symm y, map_mem_torsion (e.symm : M' →ₗ[A] M) hy, ?_⟩
      simp
  exact Module.Flat.of_linearEquiv (Submodule.Quotient.equiv _ _ e h).symm

/-- **Lemma `lem:sm-flat-strict-transform`.** Let `F → A'` be an injective map of domains and
`N` an `F`-module with `N ⧸ torsion F N` flat over `F`. Then `(A' ⊗_F N) ⧸ torsion` is flat over
`A'`: it is `A' ⊗_F (N ⧸ torsion)`. -/
theorem flat_quotient_torsion_baseChange {F A' N : Type*} [CommRing F] [IsDomain F] [CommRing A']
    [IsDomain A'] [Algebra F A'] (h : Function.Injective (algebraMap F A')) [AddCommGroup N]
    [Module F N] [Module.Flat F (N ⧸ Submodule.torsion F N)] :
    Module.Flat A' ((A' ⊗[F] N) ⧸ Submodule.torsion A' (A' ⊗[F] N)) := by
  refine flat_quotient_torsion_of_flat_quotient (Submodule.torsion F N) fun x hx => ?_
  obtain ⟨a, ha, hax⟩ := (mem_torsion_iff_of_isDomain x).1 hx
  refine (mem_torsion_iff_of_isDomain _).2 ⟨algebraMap F A' a, ?_, ?_⟩
  · rw [Ne, ← map_zero (algebraMap F A')]
    exact fun h' => ha (h h')
  · rw [algebraMap_smul, ← TensorProduct.tmul_smul, hax, TensorProduct.tmul_zero]

end Quotient

section Pushout

/-- **Strict flatness on a chart** (`lem:sm-flat-strict-transform`, pushout form). Let
`B ← R → A'` be ring maps with pushout `M`, let `R → F → A'` factor `R → A'` through a domain `F`
with `F → A'` injective and `A'` a domain, and assume `(F ⊗_R B) ⧸ torsion` is `F`-flat. If an
ideal `T ⊆ M` consists exactly of the elements killed by a nonzero element of `A'`, then
`M ⧸ T` is flat over `A'`. -/
theorem flat_quotient_of_isPushout {R B A' M : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ A'}
    {inl : B ⟶ M} {inr : A' ⟶ M} (H : CategoryTheory.IsPushout f g inl inr) [Algebra R B]
    (hf : algebraMap R B = f.hom) {F : Type u} [CommRing F] [IsDomain F] [Algebra R F]
    [IsDomain A'] (σ : F →+* A') (hσ : Function.Injective σ)
    (hσg : σ.comp (algebraMap R F) = g.hom)
    [Module.Flat F ((F ⊗[R] B) ⧸ Submodule.torsion F (F ⊗[R] B))] (T : Ideal M)
    (hT : ∀ x, x ∈ T ↔ ∃ a : A', a ≠ 0 ∧ inr a * x = 0) :
    RingHom.Flat ((Ideal.Quotient.mk T).comp inr.hom) := by
  let _ : Algebra F A' := σ.toAlgebra
  let _ : Algebra R A' := g.hom.toAlgebra
  let _ : Algebra A' M := inr.hom.toAlgebra
  let _ : Algebra B M := inl.hom.toAlgebra
  let _ : Algebra R M := (inr.hom.comp g.hom).toAlgebra
  have _ : IsScalarTower R F A' := IsScalarTower.of_algebraMap_eq' hσg.symm
  have _ : IsScalarTower R A' M := IsScalarTower.of_algebraMap_eq' rfl
  have _ : IsScalarTower R B M := IsScalarTower.of_algebraMap_eq' (by
    change inr.hom.comp g.hom = inl.hom.comp (algebraMap R B)
    rw [hf, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, H.w])
  have H' : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap R A')) (CommRingCat.ofHom (algebraMap B M))
      (CommRingCat.ofHom (algebraMap A' M)) := by
    rw [hf]
    exact H
  have hP : Algebra.IsPushout R B A' M := CommRingCat.isPushout_iff_isPushout.1 H'
  have _ : Algebra.IsPushout R A' B M := hP.symm
  have hinj : Function.Injective (algebraMap F A') := hσ
  have h1 : Module.Flat A' ((A' ⊗[F] (F ⊗[R] B)) ⧸
      Submodule.torsion A' (A' ⊗[F] (F ⊗[R] B))) := flat_quotient_torsion_baseChange hinj
  let e : A' ⊗[F] (F ⊗[R] B) ≃ₗ[A'] M :=
    (AlgebraTensorModule.cancelBaseChange R F A' A' B).trans
      (Algebra.IsPushout.equiv R A' B M).toLinearEquiv
  have h2 : Module.Flat A' (M ⧸ Submodule.torsion A' M) := flat_quotient_torsion_of_linearEquiv e
  have hTt : T.restrictScalars A' = Submodule.torsion A' M := by
    ext x
    rw [Submodule.restrictScalars_mem, hT, mem_torsion_iff_of_isDomain]
    simp only [Algebra.smul_def]
    rfl
  have h3 : Module.Flat A' (M ⧸ T) :=
    Module.Flat.of_linearEquiv ((Submodule.quotEquivOfEq _ _ hTt).symm.trans
      (Submodule.Quotient.restrictScalarsEquiv A' T)).symm
  rw [← RingHom.flat_algebraMap_iff] at h3
  exact h3

end Pushout

end DeJongAlterations.StableModification.Flattening
