/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.EquivFin
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Relation sheaves of holomorphic functions and Oka's property

Source: Oka's coherence theorem (K. Oka 1950; Grauert--Remmert, *Coherent analytic sheaves*,
Ch. 2 §5; Demailly, *Complex analytic and differential geometry*, II.3.19--3.20).

Let `F = (F_{ij})` be a finite matrix of holomorphic functions on a complex normed space `X`
(rows `i : κ` are equations, columns `j : ι` unknowns).  A *relation* of `F` at `y` is a
tuple `a = (a_j)` of germs of holomorphic functions at `y` with `∑_j a_j F_{ij} = 0` near `y`
for every `i`.  The relation sheaf is *finitely generated near `x₀`* (`RelationsFGAt`) if
finitely many holomorphic relations `σ_k` on an open `U ∋ x₀` generate the relations at EVERY
point `y ∈ U` (`GeneratesRelationsOn`).  `OkaProperty X`: this holds for every finite matrix
of functions holomorphic near `x₀`.  Oka's coherence theorem is `OkaProperty ℂⁿ`.

Everything is stated with functions and eventual equalities, so that generation at all
points of a neighbourhood (the content of coherence) is part of the statement.

## Main statements

* `relationsFGAt_of_eqOn_zero`: the zero matrix (in particular no equations).
* `relationsFGAt_of_ne_zero`: one equation with an entry that does not vanish on `U`; the
  trivial relations `f_j e_{j₀} - f_{j₀} e_j` generate.
* `RelationsFGAt.of_matrix`: transport along an invertible holomorphic matrix, `F = G A`.
* `RelationsFGAt.comp_homeomorph`: transport along a biholomorphic homeomorphism;
  `OkaProperty.of_homeomorph`.
* `okaProperty_of_scalar`: one equation at a time suffices (induction on the number of
  equations: the relations of the remaining rows are relations among the generators of the
  first row's relations).
-/

open Filter Topology Set

namespace Hironaka.OkaRelationSheaf

section Defs

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `f` is holomorphic on a neighbourhood of `y`. -/
abbrev HolAt (f : X → ℂ) (y : X) : Prop :=
  ∀ᶠ x in 𝓝 y, DifferentiableAt ℂ f x

variable {κ ι μ : Type*} [Fintype κ] [Fintype ι] [Fintype μ]

/-- `a` is a relation at `y` of the system `∑_j a_j F_{ij} = 0` (`i : κ`). -/
def IsRelationAt (F : κ → ι → X → ℂ) (y : X) (a : ι → X → ℂ) : Prop :=
  (∀ j, HolAt (a j) y) ∧ ∀ i, ∀ᶠ x in 𝓝 y, ∑ j, a j x * F i j x = 0

/-- Near `y`, `a` is a combination of the `σ_k` with coefficients holomorphic at `y`. -/
def IsCombinationAt (σ : μ → ι → X → ℂ) (y : X) (a : ι → X → ℂ) : Prop :=
  ∃ c : μ → X → ℂ, (∀ k, HolAt (c k) y) ∧ ∀ j, a j =ᶠ[𝓝 y] fun x => ∑ k, c k x * σ k j x

/-- The holomorphic relations `σ_k` on `U` generate the relations of `F` at every point
of `U`. -/
def GeneratesRelationsOn (F : κ → ι → X → ℂ) (U : Set X) (σ : μ → ι → X → ℂ) : Prop :=
  (∀ k j, DifferentiableOn ℂ (σ k j) U) ∧ (∀ k i, ∀ x ∈ U, ∑ j, σ k j x * F i j x = 0) ∧
    ∀ y ∈ U, ∀ a, IsRelationAt F y a → IsCombinationAt σ y a

/-- The relation sheaf of `F` is finitely generated near `x₀`. -/
def RelationsFGAt (F : κ → ι → X → ℂ) (x₀ : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
    ∃ (μ : Type) (_ : Fintype μ) (σ : μ → ι → X → ℂ), GeneratesRelationsOn F U σ

variable (X) in
/-- **Oka's property**: relation sheaves of finite matrices of holomorphic functions are
finitely generated. -/
def OkaProperty : Prop :=
  ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (F : κ → ι → X → ℂ) (x₀ : X),
    (∀ i j, HolAt (F i j) x₀) → RelationsFGAt F x₀

end Defs

section HolAt

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem holAt_const (c : ℂ) (y : X) : HolAt (fun _ => c) y :=
  Eventually.of_forall fun _ => differentiableAt_const c

theorem HolAt.add {f g : X → ℂ} {y : X} (hf : HolAt f y) (hg : HolAt g y) :
    HolAt (fun x => f x + g x) y :=
  (hf.and hg).mono fun _ h => h.1.add h.2

theorem HolAt.neg {f : X → ℂ} {y : X} (hf : HolAt f y) : HolAt (fun x => -f x) y :=
  hf.mono fun _ h => h.neg

theorem HolAt.mul {f g : X → ℂ} {y : X} (hf : HolAt f y) (hg : HolAt g y) :
    HolAt (fun x => f x * g x) y :=
  (hf.and hg).mono fun _ h => h.1.mul h.2

theorem HolAt.sum {α : Type*} (s : Finset α) {f : α → X → ℂ} {y : X}
    (hf : ∀ i ∈ s, HolAt (f i) y) : HolAt (fun x => ∑ i ∈ s, f i x) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holAt_const (0 : ℂ) y
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem HolAt.fintype_sum {α : Type*} [Fintype α] {f : α → X → ℂ} {y : X}
    (hf : ∀ i, HolAt (f i) y) : HolAt (fun x => ∑ i, f i x) y :=
  HolAt.sum _ fun i _ => hf i

theorem HolAt.differentiableAt {f : X → ℂ} {y : X} (hf : HolAt f y) :
    DifferentiableAt ℂ f y :=
  hf.self_of_nhds

theorem HolAt.continuousAt {f : X → ℂ} {y : X} (hf : HolAt f y) : ContinuousAt f y :=
  hf.differentiableAt.continuousAt

theorem HolAt.eventually {f : X → ℂ} {y : X} (hf : HolAt f y) :
    ∀ᶠ x in 𝓝 y, HolAt f x :=
  eventually_eventually_nhds.2 hf

theorem HolAt.inv {f : X → ℂ} {y : X} (hf : HolAt f y) (hy : f y ≠ 0) :
    HolAt (fun x => (f x)⁻¹) y := by
  have hne : ∀ᶠ x in 𝓝 y, f x ≠ 0 := hf.continuousAt.eventually_ne hy
  exact (hf.and hne).mono fun _ h => h.1.inv h.2

theorem holAt_of_differentiableOn {f : X → ℂ} {U : Set X} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {y : X} (hy : y ∈ U) : HolAt f y :=
  eventually_of_mem (hU.mem_nhds hy) fun _ hx => hf.differentiableAt (hU.mem_nhds hx)

/-- Holomorphy at a point transported along a continuous map that is differentiable
everywhere. -/
theorem HolAt.comp {f : Y → ℂ} {φ : X → Y} {y : X} (hf : HolAt f (φ y))
    (hφc : Continuous φ) (hφ : ∀ x, DifferentiableAt ℂ φ x) : HolAt (f ∘ φ) y :=
  (hφc.continuousAt.eventually hf).mono fun x hx => hx.comp x (hφ x)

/-- A function holomorphic at `y` is holomorphic on an open neighbourhood of `y`. -/
theorem HolAt.exists_isOpen {f : X → ℂ} {y : X} (hf : HolAt f y) :
    ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ DifferentiableOn ℂ f V := by
  obtain ⟨V, hVf, hV, hyV⟩ := eventually_nhds_iff.1 hf
  exact ⟨V, hV, hyV, fun x hx => (hVf x hx).differentiableWithinAt⟩

end HolAt

section Basic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- The relations at `y` of a system whose entries vanish near `y` are all holomorphic
tuples; the unit vectors generate them. -/
theorem relationsFGAt_of_eqOn_zero {F : κ → ι → X → ℂ} {U : Set X} (hU : IsOpen U)
    {x₀ : X} (hx₀ : x₀ ∈ U) (hF : ∀ i j, ∀ x ∈ U, F i j x = 0) {ι' : Type} [Fintype ι']
    (e : ι' ≃ ι) : RelationsFGAt F x₀ := by
  classical
  refine ⟨U, hU, hx₀, ι', inferInstance, fun k j _ => if e k = j then 1 else 0, ?_, ?_, ?_⟩
  · intro k j
    exact differentiableOn_const _
  · intro k i x hx
    simp [hF i _ x hx]
  · intro y _ a ha
    refine ⟨fun k => a (e k), fun k => ha.1 (e k), fun j => Eventually.of_forall fun x => ?_⟩
    show a j x = ∑ k, a (e k) x * (if e k = j then 1 else 0)
    rw [Equiv.sum_comp e (fun j' => a j' x * if j' = j then (1 : ℂ) else 0)]
    simp

/-- **One equation with a nonvanishing entry**: if `f_{j₀}` has no zero on `U`, the trivial
relations `f_j e_{j₀} - f_{j₀} e_j` generate the relations of `f` on `U`. -/
theorem relationsFGAt_of_ne_zero [DecidableEq ι] {f : ι → X → ℂ} {U : Set X} (hU : IsOpen U)
    {x₀ : X} (hx₀ : x₀ ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) (j₀ : ι)
    (hf₀ : ∀ x ∈ U, f j₀ x ≠ 0) {ι' : Type} [Fintype ι'] (e : ι' ≃ ι) :
    RelationsFGAt (fun (_ : Unit) => f) x₀ := by
  classical
  refine ⟨U, hU, hx₀, ι', inferInstance,
    fun k j x => (if j = j₀ then f (e k) x else 0) - (if j = e k then f j₀ x else 0), ?_, ?_, ?_⟩
  · intro k j
    refine DifferentiableOn.sub ?_ ?_
    · split_ifs
      · exact hf _
      · exact differentiableOn_const _
    · split_ifs
      · exact hf _
      · exact differentiableOn_const _
  · intro k _ x _
    simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  · intro y hy a ha
    have hfy : HolAt (f j₀) y := holAt_of_differentiableOn hU (hf j₀) hy
    refine ⟨fun k x => -(a (e k) x) * (f j₀ x)⁻¹,
      fun k => (ha.1 (e k)).neg.mul (hfy.inv (hf₀ y hy)), fun j => ?_⟩
    filter_upwards [ha.2 (), hU.mem_nhds hy] with x hx hxU
    have hne := hf₀ x hxU
    have hx' : ∑ j', a j' x * f j' x = 0 := hx
    show a j x = ∑ k, -a (e k) x * (f j₀ x)⁻¹ *
      ((if j = j₀ then f (e k) x else 0) - (if j = e k then f j₀ x else 0))
    rw [Equiv.sum_comp e (fun j' => -a j' x * (f j₀ x)⁻¹ *
      ((if j = j₀ then f j' x else 0) - (if j = j' then f j₀ x else 0)))]
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    by_cases hj : j = j₀
    · subst hj
      simp only [if_true]
      have : ∑ j', -a j' x * (f j x)⁻¹ * f j' x = -(f j x)⁻¹ * ∑ j', a j' x * f j' x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, hx']
      field_simp
      ring
    · simp only [hj, if_false, Finset.sum_const_zero, zero_sub]
      field_simp

end Basic

section Transport

theorem sum_comm₃ {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c :=
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, f a b c := Finset.sum_comm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- **Transport along an invertible holomorphic matrix**: if `F = G A` on `U` with `A`
invertible (inverse `B`), generators `σ` of the relations of `G` give generators `B σ` of
the relations of `F`. -/
theorem RelationsFGAt.of_matrix [DecidableEq ι] {F G : κ → ι → X → ℂ} {x₀ : X} {U : Set X}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U) (A B : ι → ι → X → ℂ)
    (hA : ∀ k j, DifferentiableOn ℂ (A k j) U) (hB : ∀ k j, DifferentiableOn ℂ (B k j) U)
    (hFGA : ∀ i j, ∀ x ∈ U, F i j x = ∑ k, G i k x * A k j x)
    (hBA : ∀ j l, ∀ x ∈ U, ∑ k, B j k x * A k l x = if j = l then 1 else 0)
    (hAB : ∀ j l, ∀ x ∈ U, ∑ k, A j k x * B k l x = if j = l then 1 else 0)
    (hG : RelationsFGAt G x₀) : RelationsFGAt F x₀ := by
  obtain ⟨V, hV, hx₀V, μ, _, σ, hσd, hσrel, hσgen⟩ := hG
  refine ⟨U ∩ V, hU.inter hV, ⟨hx₀, hx₀V⟩, μ, inferInstance,
    fun l j x => ∑ k, B j k x * σ l k x, ?_, ?_, ?_⟩
  · intro l j
    exact DifferentiableOn.fun_sum fun k _ =>
      ((hB j k).mono inter_subset_left).mul ((hσd l k).mono inter_subset_right)
  · intro l i x hx
    have e1 : ∑ j, (∑ k, B j k x * σ l k x) * F i j x =
        ∑ j, ∑ k, ∑ m, B j k x * σ l k x * (G i m x * A m j x) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hFGA i j x hx.1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
    rw [e1, sum_comm₃]
    rw [← hσrel l i x hx.2]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e2 : ∀ k, ∑ j, B j k x * σ l k x * (G i m x * A m j x) =
        G i m x * σ l k x * (if m = k then 1 else 0) := fun k => by
      rw [← hAB m k x hx.1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  · intro y hy a ha
    have hUy : ∀ᶠ x in 𝓝 y, x ∈ U := hU.mem_nhds hy.1
    have hAy : ∀ k j, HolAt (A k j) y := fun k j => holAt_of_differentiableOn hU (hA k j) hy.1
    have hBy : ∀ k j, HolAt (B k j) y := fun k j => holAt_of_differentiableOn hU (hB k j) hy.1
    -- `A a` is a relation of `G`
    have hAa : IsRelationAt G y fun k x => ∑ j, A k j x * a j x := by
      refine ⟨fun k => HolAt.fintype_sum fun j => (hAy k j).mul (ha.1 j), fun i => ?_⟩
      filter_upwards [ha.2 i, hUy] with x hx hxU
      rw [← hx]
      simp only [hFGA i _ x hxU, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    obtain ⟨c, hc, hcσ⟩ := hσgen y hy.2 _ hAa
    refine ⟨c, hc, fun j => ?_⟩
    have hall : ∀ᶠ x in 𝓝 y, ∀ k, (∑ j, A k j x * a j x) = ∑ l, c l x * σ l k x :=
      eventually_all.2 hcσ
    filter_upwards [hall, hUy] with x hx hxU
    have e1 : ∑ k, B j k x * ∑ j', A k j' x * a j' x = a j x := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ j', ∑ k, B j k x * (A k j' x * a j' x) =
          (if j = j' then 1 else 0) * a j' x := fun j' => by
        rw [← hBA j j' x hxU, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← e1]
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

/-- **Transport along a biholomorphic homeomorphism.** -/
theorem RelationsFGAt.comp_homeomorph {F : κ → ι → Y → ℂ} (φ : X ≃ₜ Y)
    (hφ : ∀ x, DifferentiableAt ℂ φ x) (hφs : ∀ y, DifferentiableAt ℂ φ.symm y) {x₀ : X}
    (hF : RelationsFGAt F (φ x₀)) : RelationsFGAt (fun i j => F i j ∘ φ) x₀ := by
  obtain ⟨V, hV, hx₀V, μ, _, σ, hσd, hσrel, hσgen⟩ := hF
  refine ⟨φ ⁻¹' V, hV.preimage φ.continuous, hx₀V, μ, inferInstance,
    fun k j => σ k j ∘ φ, ?_, ?_, ?_⟩
  · intro k j x hx
    exact ((hσd k j).differentiableAt (hV.mem_nhds hx)).comp x (hφ x) |>.differentiableWithinAt
  · intro k i x hx
    exact hσrel k i (φ x) hx
  · intro y hy a ha
    have hsy : φ.symm (φ y) = y := φ.symm_apply_apply y
    have hφs_t : Tendsto φ.symm (𝓝 (φ y)) (𝓝 y) := by
      have := φ.symm.continuous.tendsto (φ y)
      rwa [hsy] at this
    have hφ_t : Tendsto φ (𝓝 y) (𝓝 (φ y)) := φ.continuous.tendsto y
    -- `a ∘ φ⁻¹` is a relation of `F` at `φ y`
    have ha' : IsRelationAt F (φ y) fun j => a j ∘ φ.symm := by
      refine ⟨fun j => ?_, fun i => ?_⟩
      · have h1 : HolAt (a j) (φ.symm (φ y)) := by rw [hsy]; exact ha.1 j
        exact h1.comp φ.symm.continuous hφs
      · filter_upwards [hφs_t.eventually (ha.2 i)] with z hz
        simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using hz
    obtain ⟨c, hc, hcσ⟩ := hσgen (φ y) hy _ ha'
    refine ⟨fun k => c k ∘ φ, fun k => (hc k).comp φ.continuous hφ, fun j => ?_⟩
    filter_upwards [hφ_t.eventually (hcσ j)] with x hx
    simpa only [Function.comp_apply, Homeomorph.symm_apply_apply] using hx

/-- Oka's property is invariant under biholomorphic homeomorphisms (e.g. linear
equivalences). -/
theorem OkaProperty.of_homeomorph (φ : X ≃ₜ Y) (hφ : ∀ x, DifferentiableAt ℂ φ x)
    (hφs : ∀ y, DifferentiableAt ℂ φ.symm y) (hY : OkaProperty Y) : OkaProperty X := by
  intro κ ι _ _ F x₀ hF
  have hG : ∀ i j, HolAt (F i j ∘ φ.symm) (φ x₀) := fun i j => by
    have h1 : HolAt (F i j) (φ.symm (φ x₀)) := by
      rw [Homeomorph.symm_apply_apply]; exact hF i j
    exact h1.comp φ.symm.continuous hφs
  have := (hY κ ι (fun i j => F i j ∘ φ.symm) (φ x₀) hG).comp_homeomorph φ hφ hφs
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using this

/-- Reindexing the equations. -/
theorem relationsFGAt_reindex {κ' : Type*} [Fintype κ'] (e : κ' ≃ κ) {F : κ → ι → X → ℂ}
    {x₀ : X} (h : RelationsFGAt (fun i => F (e i)) x₀) : RelationsFGAt F x₀ := by
  obtain ⟨V, hV, hx₀V, μ, _, σ, hσd, hσrel, hσgen⟩ := h
  refine ⟨V, hV, hx₀V, μ, inferInstance, σ, hσd, fun k i x hx => ?_, fun y hy a ha => ?_⟩
  · simpa only [Equiv.apply_symm_apply] using hσrel k (e.symm i) x hx
  · exact hσgen y hy a ⟨ha.1, fun i => ha.2 (e i)⟩

end Transport

section Scalar

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The induction step on the number of equations. -/
theorem relationsFGAt_succ {p : ℕ}
    (hscalar : ∀ (ι : Type) [Fintype ι] (f : ι → X → ℂ) (x₀ : X), (∀ j, HolAt (f j) x₀) →
      RelationsFGAt (fun (_ : Unit) => f) x₀)
    (ih : ∀ (ι : Type) [Fintype ι] (F : Fin p → ι → X → ℂ) (x₀ : X),
      (∀ i j, HolAt (F i j) x₀) → RelationsFGAt F x₀)
    {ι : Type} [Fintype ι] (F : Fin (p + 1) → ι → X → ℂ) (x₀ : X)
    (hF : ∀ i j, HolAt (F i j) x₀) : RelationsFGAt F x₀ := by
  obtain ⟨U₁, hU₁, hx₀U₁, μ₁, _, σ, hσd, hσrel, hσgen⟩ := hscalar ι (F 0) x₀ (hF 0)
  set G : Fin p → μ₁ → X → ℂ := fun i k x => ∑ j, σ k j x * F i.succ j x with hGdef
  have hGhol : ∀ i k, HolAt (G i k) x₀ := fun i k =>
    HolAt.fintype_sum fun j => (holAt_of_differentiableOn hU₁ (hσd k j) hx₀U₁).mul (hF _ j)
  obtain ⟨U₂, hU₂, hx₀U₂, μ₂, _, τ, hτd, hτrel, hτgen⟩ := ih μ₁ G x₀ hGhol
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hx₀U₁, hx₀U₂⟩, μ₂, inferInstance,
    fun l j x => ∑ k, τ l k x * σ k j x, ?_, ?_, ?_⟩
  · intro l j
    exact DifferentiableOn.fun_sum fun k _ =>
      ((hτd l k).mono inter_subset_right).mul ((hσd k j).mono inter_subset_left)
  · intro l i x hx
    have key : ∑ j, (∑ k, τ l k x * σ k j x) * F i j x =
        ∑ k, τ l k x * ∑ j, σ k j x * F i j x := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [key]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [hσrel _ () x hx.1]
    · exact hτrel l i x hx.2
  · intro y hy a ha
    obtain ⟨c, hc, hcσ⟩ := hσgen y hy.1 a ⟨ha.1, fun _ => ha.2 0⟩
    have hall : ∀ᶠ x in 𝓝 y, ∀ j, a j x = ∑ k, c k x * σ k j x := eventually_all.2 hcσ
    have hcG : IsRelationAt G y c := by
      refine ⟨hc, fun i => ?_⟩
      filter_upwards [ha.2 i.succ, hall] with x hx hxa
      rw [← hx]
      simp only [hGdef, hxa, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    obtain ⟨e, he, heτ⟩ := hτgen y hy.2 c hcG
    refine ⟨e, he, fun j => ?_⟩
    have hall' : ∀ᶠ x in 𝓝 y, ∀ k, c k x = ∑ l, e l x * τ l k x := eventually_all.2 heτ
    filter_upwards [hall, hall'] with x hx hx'
    rw [hx j]
    simp only [hx', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

/-- **One equation at a time suffices**: if relation sheaves of single rows are finitely
generated, Oka's property holds. -/
theorem okaProperty_of_scalar
    (hscalar : ∀ (ι : Type) [Fintype ι] (f : ι → X → ℂ) (x₀ : X), (∀ j, HolAt (f j) x₀) →
      RelationsFGAt (fun (_ : Unit) => f) x₀) : OkaProperty X := by
  have hfin : ∀ (p : ℕ) (ι : Type) [Fintype ι] (F : Fin p → ι → X → ℂ) (x₀ : X),
      (∀ i j, HolAt (F i j) x₀) → RelationsFGAt F x₀ := by
    intro p
    induction p with
    | zero =>
        intro ι _ F x₀ _
        exact relationsFGAt_of_eqOn_zero isOpen_univ (mem_univ x₀)
          (fun i => Fin.elim0 i) (Equiv.refl ι)
    | succ p ih => exact fun ι _ F x₀ hF => relationsFGAt_succ hscalar ih F x₀ hF
  intro κ ι _ _ F x₀ hF
  exact relationsFGAt_reindex (Fintype.equivFin κ).symm
    (hfin _ ι (fun i => F ((Fintype.equivFin κ).symm i)) x₀ fun i j => hF _ j)

end Scalar

end Hironaka.OkaRelationSheaf
