/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ActualNoetherGeometricDimension
import Hironaka.Analytic.ActualCodimensionOneNoetherIdeal


set_option autoImplicit false

/-! # Genuine local equations for a geometric codimension-one subvariety

The actual local branches and Noether coordinates are internally chosen.
No supplied principal ideal, dimension bridge or local equation is used.
-/

open Hironaka

noncomputable section
open Set Filter Topology
namespace Hironaka.ActualCodimensionOneLocalEquations
open AnalyticGermDecomposition AnalyticDescendingChain
open GermAlgebraicParametrization HolGerm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]

/-- A geometrically codimension-one actual local branch internally has a
prime generator in the ORIGINAL coordinates. -/
theorem exists_prime_branch_generator
    (V : ClosedIrreducibleAnalyticSubvariety (n + 1) M) (hdim : V.dim = n)
    {x : M} {r : ℕ} {A : Fin r → Set (ComplexModel (n + 1))}
    (hA : ∀ i, IsIrreducibleGerm (A i))
    (hcover : chartGerm V.carrier x =ᶠ[𝓝 0] (⋃ i, A i))
    (hpw : Pairwise fun i j => ¬ (A i ≤ᶠ[𝓝 0] A j)) (i : Fin r) :
    ∃ G : HolGerm (ComplexModel (n + 1)), Prime G ∧
      vanishingIdeal (A i) = Ideal.span {G} := by
  have hprime : (vanishingIdeal (A i)).IsPrime :=
    (isIrreducibleGerm_iff_isPrime (hA i).1).mp (hA i)
  let : (vanishingIdeal (A i)).IsPrime := hprime
  obtain ⟨d, L, hN⟩ := exists_isNoetherNormalization
    (vanishingIdeal (A i))
  rw [GermParametrization.map_vanishingIdeal_comapEquiv] at hN
  have hd : d = n :=
    (ActualNoetherGeometricDimension.base_dim_eq_subvariety_dim
      V hA hcover hpw i hN).trans hdim
  subst d
  have htrans : (vanishingIdeal (L ⁻¹' A i)).IsPrime := by
    rw [← GermParametrization.map_vanishingIdeal_comapEquiv]
    exact Ideal.map_isPrime_of_equiv _
  let : (vanishingIdeal (L ⁻¹' A i)).IsPrime := htrans
  obtain ⟨W, _, _, hgen, hG⟩ :=
    ActualCodimensionOneNoetherIdeal.exists_prime_weierstrass_generator
      (vanishingIdeal (L ⁻¹' A i)) hN
  let G := evalGerm (n + 1) W (coord (Fin.last n))
  let e := comapEquiv L
  have heq : vanishingIdeal (A i) = Ideal.span {e.symm G} := calc
    vanishingIdeal (A i) = ((vanishingIdeal (A i)).map e).map e.symm :=
      (Ideal.map_of_equiv e).symm
    _ = (Ideal.span {G}).map e.symm := by
      rw [GermParametrization.map_vanishingIdeal_comapEquiv, hgen]
    _ = Ideal.span {e.symm G} := by
      rw [Ideal.map_span, Set.image_singleton]
  have hne : e.symm G ≠ 0 := by
    intro hz
    apply hG.ne_zero
    apply e.symm.injective
    simpa only [map_zero] using hz
  refine ⟨e.symm G, ?_, heq⟩
  rw [← Ideal.span_singleton_prime hne, ← heq]
  infer_instance

private theorem holomorphic_product {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel d → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using eventually_differentiableAt_const
      (E := ComplexModel d) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem germ_product {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel d → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) (holomorphic_product s f hf) =
      ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have h := map_prod
    (Germ.coeRingHom (𝓝 (0 : ComplexModel d)) :
      (ComplexModel d → ℂ) →+* Germ (𝓝 (0 : ComplexModel d)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.prod_fn]

/-- The complete original chart germ of a geometric codimension-one
subvariety internally has a nonzero holomorphic equation, including at
singular points and points outside its carrier. -/
theorem exists_nonzero_local_equation
    (V : ClosedIrreducibleAnalyticSubvariety (n + 1) M) (hdim : V.dim = n)
    (x : M) :
    ∃ (f : ComplexModel (n + 1) → ℂ)
      (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
      HolGerm.mk f hf ≠ 0 ∧ chartGerm V.carrier x =ᶠ[𝓝 0] {z | f z = 0} := by
  classical
  obtain ⟨r, A, hA, _, hcover, hpw⟩ := exists_irreducible_decomposition_euclidean
    (isAnalyticGerm_chartGerm V.analytic x)
  have hrep : ∀ i : Fin r, ∃ (f : ComplexModel (n + 1) → ℂ)
      (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
      HolGerm.mk f hf ≠ 0 ∧ A i =ᶠ[𝓝 0] {z | f z = 0} := by
    intro i
    obtain ⟨G, hG, hideal⟩ := exists_prime_branch_generator V hdim hA hcover hpw i
    obtain ⟨f, hf, hGF⟩ := HolGerm.exists_eq_mk G
    rw [hGF] at hideal hG
    have hto : A i ≤ᶠ[𝓝 0] {z | f z = 0} :=
      mem_vanishingIdeal_mk.mp (hideal ▸ Ideal.subset_span (Set.mem_singleton _))
    have hfrom : {z | f z = 0} ≤ᶠ[𝓝 0] A i := by
      apply le_of_vanishingIdeal_le (hA i).1
      rw [hideal]
      apply Ideal.span_le.mpr
      rintro _ rfl
      exact mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun _ h => h)
    exact ⟨f, hf, hG.ne_zero, hto.antisymm hfrom⟩
  choose f hf hne hzero using hrep
  let F : ComplexModel (n + 1) → ℂ := fun z => ∏ i : Fin r, f i z
  have hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z :=
    holomorphic_product Finset.univ f hf
  refine ⟨F, hF, ?_, ?_⟩
  · rw [germ_product Finset.univ f hf]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  · apply eventuallyEq_set.mpr
    filter_upwards [eventuallyEq_set.mp hcover,
      eventually_all.mpr fun i => eventuallyEq_set.mp (hzero i)] with z hz hzi
    rw [hz]
    rw [Set.mem_iUnion]
    change (∃ i, z ∈ A i) ↔ ∏ i : Fin r, f i z = 0
    simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    exact exists_congr fun i => hzi i

end Hironaka.ActualCodimensionOneLocalEquations
