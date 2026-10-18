/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.AnalyticSubsetPresentationsExact
import Hironaka.Analytic.RemmertSteinFlatExtension
import Hironaka.Analytic.CoveringSymmetricFunctions
import Hironaka.Analytic.ClosureDifferenceAnalytic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The flat case of the Remmert--Stein theorem

Blueprint `rem:remmert-stein-flat` (Demailly, *Complex analytic and differential geometry*, II.8.7).
Assume `(R_{m-1})`.  Let `Ω ⊆ ℂⁿ` be open, `L = ℂᵖ × {0}`, and `E ⊆ Ω \ L` analytic in `Ω \ L` with
`dim E ≤ m` and `dim_y E ≥ p + 1` at every point.  Then `closure E` is analytic at every point of
`Ω` (`remmertStein_flat`).

* `Wset`: the analytic set `W ⊆ Q` cut out by the extended canonical defining functions
  `P_{λ_i}(π z; λ_i(κ z - κ a))`; on the good base it agrees with `E` (`mem_Wset_iff`), and its
  fibres over `B'` are finite (`finite_Wset_fibre`: roots of monic polynomials, Vandermonde).
* `closure_inter_eq`: `closure E ∩ Q` is the closure of the `s`-dimensional regular stratum of
  `closure (W ∩ X₀)` (the blueprint's `W₁ˢ`), hence analytic in `Q`.
* `remmertStein_flat_pure`: the case of pure dimension `s = p + t`; `remmertStein_flat`: the general
  case, by the dimension strata of `E`.

Sorry-free.
-/

open Set Filter Topology Metric TopologicalSpace Polynomial
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.RemmertSteinFlat

open Hironaka.RegularLocusDense AnalyticDimensionBasics AnalyticSubsetOpens
  RemmertStatements CoveringSymmetricFunctions GermParametrizationData

section W

variable {n p t : ℕ} {Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t))}
  {a : ComplexModel n} {δ ρ : ℝ}

/-- The `i`-th equation of `W`. -/
def eqn (Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t)))
    (a : ComplexModel n) (q : ℕ) (F : ℕ → ℕ → ComplexModel (p + t) → ℂ) (i : ℕ)
    (z : ComplexModel n) : ℂ :=
  form (n - (p + t)) 0 i ((Λ z).2 - (Λ a).2) ^ q +
    ∑ j ∈ Finset.range q, F i j (Λ z).1 * form (n - (p + t)) 0 i ((Λ z).2 - (Λ a).2) ^ j

/-- The set `W ⊆ Q`. -/
def Wset (Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t)))
    (a : ComplexModel n) (δ ρ : ℝ) (q : ℕ) (F : ℕ → ℕ → ComplexModel (p + t) → ℂ) :
    Set (ComplexModel n) :=
  {z | z ∈ polydisc Λ a δ ρ ∧ ∀ i ∈ Finset.range (q * (n - (p + t)) + 1), eqn Λ a q F i z = 0}

theorem differentiableOn_eqn {q : ℕ} {F : ℕ → ℕ → ComplexModel (p + t) → ℂ}
    (hFd : ∀ i j, DifferentiableOn ℂ (F i j) (ball (Λ a).1 δ)) (i : ℕ) :
    DifferentiableOn ℂ (eqn Λ a q F i) (polydisc Λ a δ ρ) := by
  have hform : Differentiable ℂ fun z : ComplexModel n => form (n - (p + t)) 0 i ((Λ z).2 - (Λ a).2) :=
    (form (n - (p + t)) 0 i).differentiable.comp
      ((((ContinuousLinearMap.snd ℂ _ _).comp Λ.toContinuousLinearMap).differentiable).sub_const
        (Λ a).2)
  have hfst : Differentiable ℂ fun z : ComplexModel n => (Λ z).1 :=
    ((ContinuousLinearMap.fst ℂ _ _).comp Λ.toContinuousLinearMap).differentiable
  show DifferentiableOn ℂ (fun z => form (n - (p + t)) 0 i ((Λ z).2 - (Λ a).2) ^ q +
    ∑ j ∈ Finset.range q, F i j (Λ z).1 * form (n - (p + t)) 0 i ((Λ z).2 - (Λ a).2) ^ j) _
  refine (hform.pow q).differentiableOn.add (DifferentiableOn.fun_sum (u := Finset.range q)
    fun j _ => ?_)
  refine DifferentiableOn.mul ?_ (hform.pow j).differentiableOn
  exact (hFd i j).comp hfst.differentiableOn fun z hz => by
    rw [mem_ball, dist_eq_norm]; exact hz.1

/-- `W` has a presentation at every point of `Q`. -/
theorem nonempty_presentation_Wset {q : ℕ} {F : ℕ → ℕ → ComplexModel (p + t) → ℂ}
    (hFd : ∀ i j, DifferentiableOn ℂ (F i j) (ball (Λ a).1 δ)) {x : ComplexModel n}
    (hx : x ∈ polydisc Λ a δ ρ) :
    Nonempty (ComplexAnalyticPresentationAt (n := n) (M := ComplexModel n) (Wset Λ a δ ρ q F) x) :=
  nonempty_presentation_of_eqOn isOpen_polydisc hx
    (fun k : Fin (q * (n - (p + t)) + 1) => eqn Λ a q F k)
    (fun k => differentiableOn_eqn hFd k) fun y hy => by
      simp only [Wset, mem_ofPred_eq, Finset.mem_range, hy, true_and]
      exact ⟨fun h k => h k k.2, fun h i hi => h ⟨i, hi⟩⟩

/-- The canonical polynomial of a finite fibre is monic of degree the cardinality. -/
theorem fibrePoly_monic {s d : ℕ} {E : Set (ComplexModel s × ComplexModel d)}
    (l : ComplexModel d →L[ℂ] ℂ) {w : ComplexModel s} (hfin : (fibreSet E w).Finite) :
    (fibrePoly E l w).Monic ∧ (fibrePoly E l w).natDegree = (fibreSet E w).ncard := by
  classical
  rw [fibrePoly_eq l hfin]
  refine ⟨monic_prod_of_monic _ _ fun x _ => monic_X_sub_C _, ?_⟩
  rw [natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C _]
  simp [Set.ncard_eq_toFinset_card _ hfin]

/-- Evaluation of a monic polynomial of degree `q` through its coefficients. -/
theorem eval_monic_eq {P : ℂ[X]} (hP : P.Monic) {q : ℕ} (hq : P.natDegree = q) (x : ℂ) :
    P.eval x = x ^ q + ∑ j ∈ Finset.range q, P.coeff j * x ^ j := by
  conv_lhs => rw [hP.as_sum]
  simp [hq, eval_finsetSum]

/-- **`W` agrees with `E` over the good base.** -/
theorem mem_Wset_iff {E : Set (ComplexModel n)} {B₀ : Set (ComplexModel (p + t))} {q : ℕ}
    (hq : ∀ w ∈ B₀, (fibreSet (coverSet Λ a δ ρ E B₀) w).Finite ∧
      (fibreSet (coverSet Λ a δ ρ E B₀) w).ncard = q)
    {F : ℕ → ℕ → ComplexModel (p + t) → ℂ}
    (hFeq : ∀ i j, EqOn (F i j)
      (fun w => (fibrePoly (coverSet Λ a δ ρ E B₀) (form (n - (p + t)) 0 i) w).coeff j) B₀)
    {z : ComplexModel n} (hzQ : z ∈ polydisc Λ a δ ρ) (hzB : (Λ z).1 ∈ B₀) :
    z ∈ Wset Λ a δ ρ q F ↔ z ∈ E := by
  set Ê := coverSet Λ a δ ρ E B₀ with hÊ
  set v := (Λ z).2 - (Λ a).2 with hv
  have hmemÊ : ((Λ z).1, v) ∈ Ê ↔ z ∈ E := by
    constructor
    · rintro ⟨y, ⟨⟨hyE, -⟩, -⟩, hyeq⟩
      simp only [Prod.mk.injEq, hv, sub_left_inj] at hyeq
      have : Λ y = Λ z := Prod.ext hyeq.1 hyeq.2
      rwa [Λ.injective this] at hyE
    · intro hzE
      exact ⟨z, ⟨⟨hzE, hzQ⟩, hzB⟩, rfl⟩
  rw [← hmemÊ, exists_forms_mem_iff hq hzB v]
  obtain ⟨hfin, hcard⟩ := hq _ hzB
  simp only [Wset, mem_ofPred_eq, hzQ, true_and]
  refine forall₂_congr fun i _ => ?_
  obtain ⟨hmon, hdeg⟩ := fibrePoly_monic (form (n - (p + t)) 0 i) hfin
  rw [eval_monic_eq hmon (hdeg.trans hcard), eqn]
  have : ∀ j ∈ Finset.range q, F i j (Λ z).1 =
      (fibrePoly Ê (form (n - (p + t)) 0 i) (Λ z).1).coeff j := fun j _ => hFeq i j hzB
  rw [Finset.sum_congr rfl fun j hj => by rw [this j hj]]

/-- **The fibres of `π` on `W` are finite.** -/
theorem finite_Wset_fibre {q : ℕ} {F : ℕ → ℕ → ComplexModel (p + t) → ℂ}
    (w : ComplexModel (p + t)) : (Wset Λ a δ ρ q F ∩ {z | (Λ z).1 = w}).Finite := by
  classical
  -- the polynomials
  set P : ℕ → ℂ[X] := fun i => X ^ q + ∑ j ∈ Finset.range q, C (F i j w) * X ^ j with hP
  have hPeval : ∀ i x, (P i).eval x = x ^ q + ∑ j ∈ Finset.range q, F i j w * x ^ j := by
    intro i x
    simp [hP, eval_finsetSum]
  have hPne : ∀ i, P i ≠ 0 := by
    intro i h
    have := congrArg (fun P => P.coeff q) h
    simp only [hP, coeff_add, coeff_X_pow, if_true, finsetSum_coeff, coeff_C_mul_X_pow,
      coeff_zero] at this
    rw [Finset.sum_eq_zero fun j hj => if_neg (by simp at hj; omega)] at this
    simp at this
  have heqn : ∀ z, (Λ z).1 = w → ∀ i, eqn Λ a q F i z =
      (P i).eval (form (n - (p + t)) 0 i ((Λ z).2 - (Λ a).2)) := by
    intro z hz i
    rw [hPeval, eqn, hz]
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · refine Set.finite_empty.subset fun z hz => ?_
    have := hz.1.2 0 (by simp)
    rw [heqn z hz.2, hPeval] at this
    simp [hq0] at this
  -- the root sets and the Vandermonde map
  set R : Fin (q * (n - (p + t)) + 1) → Set ℂ := fun i => {x | (P i).IsRoot x} with hR
  have hRfin : ∀ i, (R i).Finite := fun i => finite_setOfPred_isRoot (hPne i)
  set Fv : ComplexModel (n - (p + t)) → (Fin (q * (n - (p + t)) + 1) → ℂ) := fun v i => form (n - (p + t)) 0 i v with hFv
  have hFvinj : Function.Injective Fv := by
    intro v v' h
    have h0 : v - v' = 0 := by
      refine eq_zero_of_form_eq_zero (n := n - (p + t)) (d := 0) (I := Finset.range (q * (n - (p + t)) + 1)) ?_
        (Subsingleton.elim _ _) fun i hi => ?_
      · simp only [Finset.card_range, Nat.sub_zero]
        nlinarith
      · have := congrFun h ⟨i, Finset.mem_range.mp hi⟩
        simp only [hFv] at this
        rw [map_sub, this, sub_self]
    exact sub_eq_zero.mp h0
  have hpi : (Fv ⁻¹' Set.pi univ R).Finite :=
    (Set.Finite.pi fun i => hRfin i).preimage hFvinj.injOn
  refine (hpi.image fun v => Λ.symm (w, v + (Λ a).2)).subset fun z hz => ?_
  refine ⟨(Λ z).2 - (Λ a).2, fun i _ => ?_, ?_⟩
  · have := hz.1.2 i (Finset.mem_range.mpr i.2)
    rw [heqn z hz.2] at this
    exact this
  · simp only [sub_add_cancel]
    rw [← hz.2]
    simp

end W

section Pure

variable {n p t : ℕ} {Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t))}
  {a : ComplexModel n} {δ ρ : ℝ}

/-- The coordinate `p`-plane is closed. -/
theorem isClosed_complexCoordinatePlane (n p : ℕ) : IsClosed (complexCoordinatePlane n p) := by
  have : complexCoordinatePlane n p = ⋂ i : Fin n, {z : ComplexModel n | p ≤ i.1 → z i = 0} := by
    ext z
    simp [complexCoordinatePlane]
  rw [this]
  refine isClosed_iInter fun i => ?_
  by_cases h : p ≤ i.1
  · simpa [h] using isClosed_eq (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous
      continuous_const
  · simp [h]

/-- Closures in an open subset are traces of closures. -/
theorem closure_opens_eq {M : Type*} [TopologicalSpace M] (U : Opens M) (T : Set U) :
    closure T = (↑) ⁻¹' closure ((↑) '' T : Set M) := by
  ext x
  exact closure_subtype

/-- **Sets over the bad set have dimension `≤ s - 1`**, when their fibres are finite. -/
theorem dimLE_over_badSet {Sig₀ : Set (coverTarget Λ a δ)}
    (hSiga : IsComplexAnalyticSubset (n := p + t) Sig₀)
    (hSigdim : DimLE (n := p + t) Sig₀ (p + t - 1)) {S : Set (ComplexModel n)}
    (hfin : ∀ w ∈ ball (Λ a).1 δ \ complexCoordinatePlane (p + t) p,
      (S ∩ polydisc Λ a δ ρ ∩ {z | (Λ z).1 = w}).Finite) :
    DimLE (n := n) (S ∩ (coverSource Λ a δ ρ : Set (ComplexModel n)) ∩
      {z | (Λ z).1 ∈ ((↑) '' Sig₀ : Set (ComplexModel (p + t)))}) (p + t - 1) := by
  set X₀ := coverSource Λ a δ ρ with hX₀
  set G := coverMap Λ a δ ρ with hG
  set T : Set X₀ := (↑) ⁻¹' (S ∩ (X₀ : Set (ComplexModel n)) ∩
    {z | (Λ z).1 ∈ ((↑) '' Sig₀ : Set (ComplexModel (p + t)))}) with hT
  have hTdim : DimLE (n := n) T (p + t - 1) := by
    refine FiniteMapDimension.dimLE_of_discrete_fibres (contMDiff_coverMap.mdifferentiable (by simp))
      (fun y _ => ?_) hSiga ?_ hSigdim
    · refine not_accPt_of_finite ?_ y
      have hy := y.2
      refine ((hfin (Λ y).1 ⟨by rw [mem_ball, dist_eq_norm]; exact hy.1.1, hy.2⟩).preimage
        Subtype.val_injective.injOn).subset fun z hz => ?_
      refine ⟨⟨hz.1.1.1, z.2.1⟩, ?_⟩
      have : G z = G y := hz.2
      exact congrArg Subtype.val this
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨σ, hσ, hσy⟩ := hy.2
      have : coverMap Λ a δ ρ y = σ := Subtype.ext hσy.symm
      rw [this]
      exact hσ
  rw [hT, ← dimLE_image_val_iff] at hTdim
  convert hTdim using 1
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hz.1.2⟩, hz, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

end Pure

section PureTheorem

open RemmertSteinCoordinates


variable (probeDim : ℕ)
set_option pp.all true in
#synth TopologicalSpace (ComplexModel probeDim)
set_option pp.all true in
#synth ChartedSpace (ComplexModel probeDim) (ComplexModel probeDim)
end PureTheorem
end Hironaka.RemmertSteinFlat
end
