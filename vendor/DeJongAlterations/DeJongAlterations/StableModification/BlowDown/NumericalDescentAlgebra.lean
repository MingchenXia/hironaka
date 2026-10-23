/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ComponentGenus

/-!
# Base change of algebras of finite type over an algebraically closed field

Let `k` be an algebraically closed field, `A` a `k`-algebra of finite type and `K / k` any field
extension. This file proves the two facts about `A ⊗_k K` used to compare the fibre of a curve over
a point with algebraically closed residue field with its geometric fibres
(`BlowDown.NoClosedExc.NumericalDescent`; Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), §1.2: "obviously `C → S` is semi-stable iff its geometric fibers are
so"):

* `isDomain_tensorProduct_of_isAlgClosed`: if `A` is a domain, so is `A ⊗_k K` (geometric
  integrality over `k = k̄`);
* `isReduced_tensorProduct_of_isAlgClosed`: if `A` is reduced, so is `A ⊗_k K`.

The proof evaluates at the `k`-points of `A`: writing `f ∈ A ⊗_k K` in a `k`-basis of `K` with
coordinates `f_i ∈ A`, the evaluation `f(x) = ∑ x(f_i) b_i ∈ K` at a `k`-point `x : A → k` vanishes
iff all `f_i` vanish at `x` (`evalTensor_eq_zero_iff`). Every maximal ideal of `A` is the kernel of
a `k`-point (Hilbert's Nullstellensatz, `exists_algHom_ker_eq`) and `A` is a Jacobson ring, so an
element vanishing at all `k`-points is nilpotent (`eq_zero_of_forall_algHom_eq_zero`). If `fg = 0`
then at every `k`-point `f(x) = 0` or `g(x) = 0` (`K` is a field), so `f_i g_j` vanishes at every
`k`-point for all `i, j`; if `f^n = 0` then `f(x) = 0` at every `k`-point.

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-tensor-algclosed`.
-/

noncomputable section

open TensorProduct

namespace DeJongAlterations.StableModification.BlowDown.NumericalDescent

set_option autoImplicit false

section AlgClosed

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] {K : Type*} [Field K]
  [Algebra k K]

/-- Evaluation of `A ⊗_k K` at a `k`-point `x : A → k`: `a ⊗ c ↦ x(a) c`. -/
def evalTensor (x : A →ₐ[k] k) : A ⊗[k] K →ₐ[k] K :=
  Algebra.TensorProduct.lift ((Algebra.ofId k K).comp x) (AlgHom.id k K)
    (fun _ _ => Commute.all _ _)

/-- The evaluation of `f` at a `k`-point in terms of the coordinates of `f` in a `k`-basis of
`K`. -/
theorem evalTensor_eq (x : A →ₐ[k] k) (f : A ⊗[k] K) :
    evalTensor x f = (Module.Basis.ofVectorSpace k K).repr.symm
      (Finsupp.mapRange x (map_zero x)
        ((Algebra.TensorProduct.basis A (Module.Basis.ofVectorSpace k K)).repr f)) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    rw [Algebra.TensorProduct.basis_repr_tmul]
    have h : Finsupp.mapRange x (map_zero x)
        (a • Finsupp.mapRange (algebraMap k A) (map_zero _) ((Module.Basis.ofVectorSpace k K).repr c)) =
        x a • (Module.Basis.ofVectorSpace k K).repr c := by
      ext i
      simp
    rw [h, map_smul, LinearEquiv.symm_apply_apply]
    simp [evalTensor, Algebra.smul_def]
  | add f g hf hg =>
    rw [map_add, hf, hg, map_add, Finsupp.mapRange_add (map_add x), map_add]

/-- **A function on `A ⊗_k K` vanishes at a `k`-point iff all its coordinates do.** -/
theorem evalTensor_eq_zero_iff (x : A →ₐ[k] k) (f : A ⊗[k] K) :
    evalTensor x f = 0 ↔
      ∀ i, x ((Algebra.TensorProduct.basis A (Module.Basis.ofVectorSpace k K)).repr f i) = 0 := by
  rw [evalTensor_eq, LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h i
    have := congrArg (fun g => g i) h
    simpa using this
  · intro h
    ext i
    simpa using h i

variable [IsAlgClosed k] [Algebra.FiniteType k A]

/-- **Hilbert's Nullstellensatz**: over an algebraically closed field, every maximal ideal of an
algebra of finite type is the kernel of a `k`-point. -/
theorem exists_algHom_ker_eq (m : Ideal A) [m.IsMaximal] :
    ∃ x : A →ₐ[k] k, RingHom.ker x = m := by
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (A ⧸ m) := Algebra.FiniteType.trans (S := A) inferInstance
    inferInstance
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hbij : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hbij
  refine ⟨(e.symm : A ⧸ m →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext a
  rw [RingHom.mem_ker]
  change e.symm (Ideal.Quotient.mk m a) = 0 ↔ a ∈ m
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- **An element of a reduced algebra of finite type over `k = k̄` vanishing at all `k`-points is
zero** (`A` is a Jacobson ring). -/
theorem eq_zero_of_forall_algHom_eq_zero [IsReduced A] (a : A) (h : ∀ x : A →ₐ[k] k, x a = 0) :
    a = 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal A).IsRadical := by
    intro b hb
    obtain ⟨n, hn⟩ := hb
    rw [Submodule.mem_bot] at hn ⊢
    exact IsReduced.eq_zero b ⟨n, hn⟩
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out' ⊥ hrad
  have hmem : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨x, hx⟩ := exists_algHom_ker_eq (k := k) m
    rw [← hx, RingHom.mem_ker]
    exact h x
  rw [hjac, Submodule.mem_bot] at hmem
  exact hmem

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
/-- `A ⊗_k K` is nontrivial if `A` is. -/
theorem nontrivial_tensorProduct [Nontrivial A] : Nontrivial (A ⊗[k] K) :=
  inferInstance

/-- **Geometric integrality over an algebraically closed field**: for a domain `A` of finite type
over `k = k̄` and any field extension `K / k`, `A ⊗_k K` is a domain (blueprint
`lem:sm-bdu-tensor-algclosed`). -/
theorem isDomain_tensorProduct_of_isAlgClosed [IsDomain A] : IsDomain (A ⊗[k] K) := by
  have : Nontrivial (A ⊗[k] K) := nontrivial_tensorProduct
  have : NoZeroDivisors (A ⊗[k] K) := by
    refine ⟨fun {f g} hfg => ?_⟩
    set c := (Algebra.TensorProduct.basis A (Module.Basis.ofVectorSpace k K)).repr
    by_contra hne
    push Not at hne
    obtain ⟨hf, hg⟩ := hne
    have hf' : ∃ i, c f i ≠ 0 := by
      by_contra h
      push Not at h
      exact hf (c.injective (by ext i; simpa using h i))
    have hg' : ∃ j, c g j ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (c.injective (by ext j; simpa using h j))
    obtain ⟨i, hi⟩ := hf'
    obtain ⟨j, hj⟩ := hg'
    have h0 : c f i * c g j = 0 := by
      apply eq_zero_of_forall_algHom_eq_zero (k := k)
      intro x
      have hx : evalTensor x f * evalTensor (K := K) x g = 0 := by
        rw [← map_mul, hfg, map_zero]
      rw [map_mul]
      rcases mul_eq_zero.mp hx with h | h
      · rw [(evalTensor_eq_zero_iff x f).mp h i, zero_mul]
      · rw [(evalTensor_eq_zero_iff x g).mp h j, mul_zero]
    exact mul_ne_zero hi hj h0
  exact NoZeroDivisors.to_isDomain _

/-- **Geometric reducedness over an algebraically closed field**: for a reduced algebra `A` of
finite type over `k = k̄` and any field extension `K / k`, `A ⊗_k K` is reduced (blueprint
`lem:sm-bdu-tensor-algclosed`). -/
theorem isReduced_tensorProduct_of_isAlgClosed [IsReduced A] : IsReduced (A ⊗[k] K) := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨n, hn⟩ := hf
  set c := (Algebra.TensorProduct.basis A (Module.Basis.ofVectorSpace k K)).repr
  have hx : ∀ x : A →ₐ[k] k, evalTensor (K := K) x f = 0 := by
    intro x
    have : evalTensor (K := K) x f ^ n = 0 := by rw [← map_pow, hn, map_zero]
    exact IsReduced.eq_zero _ ⟨n, this⟩
  apply c.injective
  ext i
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact eq_zero_of_forall_algHom_eq_zero (k := k) _ fun x => (evalTensor_eq_zero_iff x f).mp (hx x) i

end AlgClosed

section Regular

open IsLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
  [IsLocalHom (algebraMap A B)]

/-- For a flat local homomorphism `A → B` of Noetherian local rings with `𝔪_A B = 𝔪_B`,
`dim A = dim B` (the closed fibre is a field; Mathlib's
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`). -/
theorem ringKrullDim_eq_of_flat (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim A = ringKrullDim B := by
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A)
    (maximalIdeal B)
  rw [hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]

/-- For a flat local homomorphism `A → B` of Noetherian local rings with `𝔪_A B = 𝔪_B`, the
embedding dimension does not drop: a minimal generating family of `𝔪_A` stays minimal in `B`
(if `a_{j₀}` were a `κ_B`-combination of the others modulo `𝔪_B² = 𝔪_A² B`, then by faithful
flatness it would be an `A`-combination of them modulo `𝔪_A²`). -/
theorem spanFinrank_le_of_flat (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    (maximalIdeal A).spanFinrank ≤ (maximalIdeal B).spanFinrank := by
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  set r := Module.finrank (ResidueField A) (CotangentSpace A)
  set n := Module.finrank (ResidueField B) (CotangentSpace B)
  let bA := Module.finBasis (ResidueField A) (CotangentSpace A)
  -- lifts of the basis to `𝔪_A`
  have hlift : ∀ i, ∃ a : maximalIdeal A, (maximalIdeal A).toCotangent a = bA i :=
    fun i => (maximalIdeal A).toCotangent_surjective _
  choose a ha using hlift
  have hmapB : ∀ i, algebraMap A B (a i) ∈ maximalIdeal B := fun i => by
    rw [← hm]; exact Ideal.mem_map_of_mem _ (a i).2
  let a' : Fin r → maximalIdeal B := fun i => ⟨algebraMap A B (a i), hmapB i⟩
  let v : Fin r → CotangentSpace B := fun i => (maximalIdeal B).toCotangent (a' i)
  -- the `a i` generate `𝔪_A`, so the `a' i` generate `𝔪_B`
  have hspanA : Submodule.span A (Set.range a) = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp]
    have : (maximalIdeal A).toCotangent ∘ a = bA := funext ha
    rw [this, bA.span_eq]
  have hspanIdeal : Ideal.span (Set.range fun i => (a i : A)) = maximalIdeal A := by
    have := congrArg (Submodule.map (maximalIdeal A).subtype) hspanA
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have key : Ideal.span (Set.range fun i => algebraMap A B (a i : A)) = maximalIdeal B := by
    calc Ideal.span (Set.range fun i => algebraMap A B (a i : A))
        = Ideal.map (algebraMap A B) (Ideal.span (Set.range fun i => (a i : A))) := by
          rw [Ideal.map_span, ← Set.range_comp]
          rfl
      _ = Ideal.map (algebraMap A B) (maximalIdeal A) := by rw [hspanIdeal]
      _ = maximalIdeal B := hm
  have hspanB : Submodule.span B (Set.range a') = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal B).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact key
  have hv : Submodule.span (ResidueField B) (Set.range v) = ⊤ := by
    have : Set.range v = (maximalIdeal B).toCotangent '' Set.range a' := by
      rw [← Set.range_comp]
      rfl
    rw [this]
    exact CotangentSpace.span_image_eq_top_iff.mpr hspanB
  -- an independent spanning subfamily, indexed by `J`
  obtain ⟨κ, ι, hι, hspanκ, hindκ⟩ := exists_linearIndependent' (ResidueField B) v
  have : Finite κ := Finite.of_injective ι hι
  have : Fintype κ := Fintype.ofFinite κ
  have hcardκ : Fintype.card κ ≤ n := hindκ.fintype_card_le_finrank
  classical
  set J : Finset (Fin r) := Finset.univ.image ι
  have hJ : J.card ≤ n := Finset.card_image_le.trans (by simpa using hcardκ)
  by_contra hlt
  push Not at hlt
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := J) (t := (Finset.univ : Finset (Fin r))) (by simpa using hJ.trans_lt hlt)
  -- `v j₀` is a combination of the `v j`, `j ∈ J`
  have hmem : v j₀ ∈ Submodule.span (ResidueField B) (v '' (J : Set (Fin r))) := by
    have h1 : v j₀ ∈ Submodule.span (ResidueField B) (Set.range (v ∘ ι)) := by
      rw [hspanκ, hv]; trivial
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨c, rfl⟩
    exact ⟨ι c, by simp [J], rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun (ResidueField B)).mp hmem
  choose d hd using fun j : J => IsLocalRing.residue_surjective (c j)
  -- hence `a j₀ ∈ (a_j, j ∈ J) + 𝔪_A²` in `B`, hence in `A`
  set I : Ideal A := Ideal.span ((fun j => (a j : A)) '' (J : Set (Fin r))) ⊔ maximalIdeal A ^ 2
  have hB : algebraMap A B (a j₀) ∈ I.map (algebraMap A B) := by
    have hz : (maximalIdeal B).toCotangent (a' j₀ - ∑ j, d j • a' j) = 0 := by
      rw [map_sub, map_sum, sub_eq_zero,
        show (maximalIdeal B).toCotangent (a' j₀) = v j₀ from rfl, ← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← hd j]
      exact (algebraMap_smul (ResidueField B) (d j) (v j)).symm
    rw [Ideal.toCotangent_eq_zero] at hz
    have hz' : ((a' j₀ - ∑ j, d j • a' j : maximalIdeal B) : B) ∈
        (maximalIdeal A ^ 2).map (algebraMap A B) := by
      rw [Ideal.map_pow, hm]
      exact hz
    have hsum : (∑ j : J, d j * algebraMap A B (a j)) ∈ I.map (algebraMap A B) := by
      refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, j.2, rfl⟩)
    have heq : algebraMap A B (a j₀) = ((a' j₀ - ∑ j, d j • a' j : maximalIdeal B) : B) +
        ∑ j : J, d j * algebraMap A B (a j) := by
      simp [a', smul_eq_mul]
    rw [heq]
    refine Ideal.add_mem _ ?_ hsum
    exact Ideal.map_mono le_sup_right hz'
  have hA : (a j₀ : A) ∈ I := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I]
    exact hB
  -- hence `bA j₀` is a combination of the `bA j`, `j ∈ J`: a contradiction
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hA
  obtain ⟨e, he⟩ := (Submodule.mem_span_image_finset_iff_exists_fun A).mp hy
  have hzm : z ∈ maximalIdeal A := Ideal.pow_le_self two_ne_zero hz
  have hsplit : a j₀ = (∑ j : J, e j • a j) + ⟨z, hzm⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]
    rw [← hyz, ← he]
  have hcomb : bA j₀ = ∑ j : J, IsLocalRing.residue A (e j) • bA j := by
    rw [← ha j₀, hsplit, map_add, ((maximalIdeal A).toCotangent_eq_zero ⟨z, hzm⟩).mpr hz,
      add_zero, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ha]
    exact (algebraMap_smul (ResidueField A) (e j) (bA j)).symm
  apply bA.linearIndependent.notMem_span_image (s := (J : Set (Fin r))) (by simpa using hj₀)
  rw [hcomb]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, j.2, rfl⟩)


/-- **Regularity descends along flat local homomorphisms with trivial closed fibre** (blueprint
`lem:sm-bdu-regular-descent`): if `A → B` is a flat local homomorphism of Noetherian local rings
with `𝔪_A B = 𝔪_B` and `B` is regular, then `A` is regular. -/
theorem isRegularLocalRing_of_flat (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    [IsRegularLocalRing B] : IsRegularLocalRing A := by
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := A) ?_
  calc ((maximalIdeal A).spanFinrank : WithBot ℕ∞)
      ≤ (maximalIdeal B).spanFinrank := by exact_mod_cast spanFinrank_le_of_flat hm
    _ = ringKrullDim B := (isRegularLocalRing_iff B).mp inferInstance
    _ = ringKrullDim A := (ringKrullDim_eq_of_flat hm).symm

end Regular

section TensorRegular

open IsLocalRing

variable {k : Type*} [Field k] [IsAlgClosed k] {A : Type*} [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A] {K : Type*} [Field K] [Algebra k K]

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
/-- The kernel of the evaluation `A ⊗_k K → K` at a `k`-point with kernel `𝔭` is `𝔭 (A ⊗_k K)`. -/
theorem ker_evalTensor (x : A →ₐ[k] k) :
    RingHom.ker (evalTensor (K := K) x) = (RingHom.ker x).map (algebraMap A (A ⊗[k] K)) := by
  ext f
  constructor
  · intro hf
    rw [RingHom.mem_ker, evalTensor_eq_zero_iff] at hf
    set b := Algebra.TensorProduct.basis A (Module.Basis.ofVectorSpace k K)
    rw [← b.linearCombination_repr f, Finsupp.linearCombination_apply]
    refine Ideal.sum_mem _ fun i _ => ?_
    show (b.repr f i) • b i ∈ _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hf i))
  · intro hf
    refine (Ideal.map_le_iff_le_comap.mpr ?_) hf
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.algebraMap_apply]
    rw [RingHom.mem_ker] at ha
    simp [evalTensor, ha]

/-- **The local ring at a closed point of `A` is regular if one point of `A ⊗_k K` over it has a
regular local ring** (blueprint `lem:sm-bdu-regular-descent`): the only prime of `A ⊗_k K` over a
maximal ideal `𝔭` of `A` is `𝔭 (A ⊗_k K)` (`ker_evalTensor`), so `A_𝔭 → (A ⊗_k K)_z` is a flat
local homomorphism with trivial closed fibre (`isRegularLocalRing_of_flat`). -/
theorem isRegularLocalRing_of_tensor (z : Ideal (A ⊗[k] K)) [z.IsPrime]
    (hz : (z.comap (algebraMap A (A ⊗[k] K))).IsMaximal)
    [IsRegularLocalRing (Localization.AtPrime z)] :
    IsRegularLocalRing (Localization.AtPrime (z.comap (algebraMap A (A ⊗[k] K)))) := by
  set p := z.comap (algebraMap A (A ⊗[k] K)) with hp
  obtain ⟨x, hx⟩ := exists_algHom_ker_eq (k := k) p
  have hsurj : Function.Surjective (evalTensor (K := K) x) := fun c =>
    ⟨1 ⊗ₜ c, by simp [evalTensor]⟩
  have hmax : (p.map (algebraMap A (A ⊗[k] K))).IsMaximal := by
    rw [← hx, ← ker_evalTensor]
    exact RingHom.ker_isMaximal_of_surjective _ hsurj
  have hzp : z = p.map (algebraMap A (A ⊗[k] K)) :=
    (hmax.eq_of_le (Ideal.IsPrime.ne_top ‹_›) Ideal.map_comap_le).symm
  -- the local homomorphism `A_𝔭 → (A ⊗_k K)_z`
  let φ := Localization.localRingHom p z (algebraMap A (A ⊗[k] K)) rfl
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime z) := φ.toAlgebra
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime z)) :=
    inferInstanceAs (IsLocalHom φ)
  have hflat0 : (algebraMap A (A ⊗[k] K)).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime z) :=
    RingHom.flat_algebraMap_iff.mp (hflat0.localRingHom z p rfl)
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing (A ⊗[k] K) := by
    have : IsNoetherianRing (K ⊗[k] A) := Algebra.FiniteType.isNoetherianRing K _
    exact isNoetherianRing_of_ringEquiv (K ⊗[k] A) (Algebra.TensorProduct.comm k K A).toRingEquiv
  have hm : (maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime z)) =
        maximalIdeal (Localization.AtPrime z) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map]
    have hcomp : (algebraMap (Localization.AtPrime p) (Localization.AtPrime z)).comp
        (algebraMap A (Localization.AtPrime p)) =
        (algebraMap (A ⊗[k] K) (Localization.AtPrime z)).comp (algebraMap A (A ⊗[k] K)) := by
      ext a
      exact Localization.localRingHom_to_map p z (algebraMap A (A ⊗[k] K)) rfl a
    rw [hcomp, ← Ideal.map_map, ← hzp]
  exact isRegularLocalRing_of_flat hm

/-- `isRegularLocalRing_of_tensor` for `K ⊗_k A` (the order of the tensor charts of
`Curves.SemistableOpen.tensorChart`). -/
theorem isRegularLocalRing_of_tensor_left (z : Ideal (K ⊗[k] A)) [z.IsPrime] (p : Ideal A)
    [p.IsPrime]
    (hp : p = z.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom)
    (hmax : p.IsMaximal) [IsRegularLocalRing (Localization.AtPrime z)] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let e : K ⊗[k] A ≃+* A ⊗[k] K := (Algebra.TensorProduct.comm k K A).toRingEquiv
  let z' : Ideal (A ⊗[k] K) := z.comap e.symm.toRingHom
  have hcomap : z'.comap (algebraMap A (A ⊗[k] K)) = p := by
    rw [hp, Ideal.comap_comap]
    congr 1
  have hM : z.primeCompl.map e.toMonoidHom = z'.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, z', Ideal.mem_comap]
    constructor
    · rintro ⟨w, hw, rfl⟩ hmem
      exact hw (by simpa using hmem)
    · intro hy
      exact ⟨e.symm y, hy, by simp⟩
  let eL : Localization.AtPrime z ≃+* Localization.AtPrime z' :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime z) (Localization.AtPrime z') e hM
  have : IsRegularLocalRing (Localization.AtPrime z') := IsRegularLocalRing.of_ringEquiv eL
  have hmax' : (z'.comap (algebraMap A (A ⊗[k] K))).IsMaximal := by rw [hcomap]; exact hmax
  have h := isRegularLocalRing_of_tensor (K := K) z' hmax'
  subst hcomap
  exact h

end TensorRegular

end DeJongAlterations.StableModification.BlowDown.NumericalDescent
