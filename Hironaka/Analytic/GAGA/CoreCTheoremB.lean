import Hironaka.Analytic.GAGA.CoreCBox
import Hironaka.Analytic.GAGA.CoreBTheoremA
import Hironaka.Analytic.GAGA.CoreOkaModules

/-!
# Cartan's Theorems A and B on compact convex product sets

Infrastructure of lane SERRE-CORE3 (Serre's GAGA, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), steps M2.4--M2.5 of the plan in
`blueprint/src/claude-serre-core.tex` (see `blueprint/src/claude-serre-core3.tex`).
Sources for the mathematics: Cartan's Theorems A and B on closed cubes (Gunning--Rossi,
*Analytic functions of several complex variables*, VIII.A; Grauert--Remmert, *Theory of Stein
spaces*, IV §§1--2), by bisection as in Hörmander, *An introduction to complex analysis in
several variables*, 7.2.

Let `C` be a box (`C_l ⊆ ℂ` compact convex), `Q = boxSet C ⊆ ℂⁿ`, and `M ⊆ 𝒪^ι` a coherent
module (`GermModule.IsCoherentOn`) on an open set containing `Q`.

* `theoremA_box` (**Theorem A**): finitely many sections over a neighbourhood of `Q` generate
  `M` at every point of that neighbourhood (`GenNear`).
* `division_box` (**division by generators**): for generators `σ` of `M` over an open `U ⊇ Q`,
  every section of `M` near `Q` is `∑ c_k σ_k` near `Q` with holomorphic `c_k` (`DivNear`).
* `exists_lift` (**Theorem B in degree one**): a section of the quotient `𝒪^ι / M` near `Q`,
  given by local representatives `s_a` on open sets `U_a` covering `Q` whose differences lie in
  `M`, has a global representative near `Q`.
* `exists_decompose` (**Theorem B for surjections**): for coherent `P ⊆ 𝒪^κ`, `Q ⊆ 𝒪^ι` and a
  holomorphic matrix `A`, every section of `P + A(Q)` near the box is `p + A a` with `p`, `a`
  sections of `P`, `Q` near the box.

The proof of the first two is an induction on the set of non-constant real directions of `C`
(`boxThm`, `Finset.strongInduction`; this is induction on the degree `Box.boxDeg`). In each step
`Box.bisection` reduces to small boxes, where coherence applies, and to the merging of the two
halves of a cut; merging uses division on the face, which has smaller degree, together with
Cartan's lemma (`TheoremA.exists_generatedOn_union`) for Theorem A and Cousin I with Oka's theorem
on the module of relations (`TheoremA.exists_combination_union`) for division.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Metric Complex
open scoped Topology
open Hironaka.OkaRelationSheaf

namespace Hironaka.Analytic.GAGA.Core.TheoremB

open Box GermModule

variable {n : ℕ}

/-! ### Theorem A and division on a set -/

/-- **Theorem A near `K`**: finitely many tuples, holomorphic on an open `U ⊇ K`, generate the
stalk of `M` at every point of `U`. -/
def GenNear {ι : Type} [Fintype ι] (M : GermModule (EuclideanSpace ℂ (Fin n)) ι)
    (K : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∃ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U ∧ K ⊆ U ∧
    ∃ (μ : Type) (_ : Fintype μ) (σ : μ → ι → EuclideanSpace ℂ (Fin n) → ℂ), M.GeneratedOn U σ

/-- **Division near `K`**: for generators `σ` of `M` over an open `U ⊇ K`, every section `f` of
`M` over `U` is a combination `∑ c_k σ_k`, with `c_k` holomorphic, on an open set containing `K`. -/
def DivNear {ι : Type} [Fintype ι] (M : GermModule (EuclideanSpace ℂ (Fin n)) ι)
    (K : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → K ⊆ U →
    ∀ (μ : Type) [Fintype μ] (σ : μ → ι → EuclideanSpace ℂ (Fin n) → ℂ),
    M.GeneratedOn U σ → ∀ f : ι → EuclideanSpace ℂ (Fin n) → ℂ, (∀ y ∈ U, M.mem y f) →
      ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ K ⊆ V ∧
        ∃ c : μ → EuclideanSpace ℂ (Fin n) → ℂ, (∀ k, DifferentiableOn ℂ (c k) V) ∧
        ∀ z ∈ V, ∀ j, f j z = ∑ k, c k z * σ k j z

section Basic

variable {ι : Type} [Fintype ι] {M : GermModule (EuclideanSpace ℂ (Fin n)) ι}

theorem genNear_empty : GenNear M ∅ :=
  ⟨∅, isOpen_empty, subset_rfl, Empty, inferInstance, fun k => k.elim,
    fun k => k.elim, fun _ hy => False.elim hy⟩

theorem divNear_empty : DivNear M ∅ :=
  fun _ _ _ _ _ _ _ _ _ => ⟨∅, isOpen_empty, subset_rfl, fun _ _ => 0,
    fun _ => differentiableOn_empty, fun _ hz => False.elim hz⟩

/-- Division for a section defined on another neighbourhood of `K`. -/
theorem DivNear.of_section {K : Set (EuclideanSpace ℂ (Fin n))} (h : DivNear M K)
    {U V₀ : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hV₀ : IsOpen V₀) (hKU : K ⊆ U) (hKV₀ : K ⊆ V₀) {μ : Type} [Fintype μ]
    {σ : μ → ι → EuclideanSpace ℂ (Fin n) → ℂ} (hσ : M.GeneratedOn U σ)
    {f : ι → EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ∀ y ∈ V₀, M.mem y f) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ K ⊆ V ∧
      ∃ c : μ → EuclideanSpace ℂ (Fin n) → ℂ, (∀ k, DifferentiableOn ℂ (c k) V) ∧
      ∀ z ∈ V, ∀ j, f j z = ∑ k, c k z * σ k j z :=
  h (U ∩ V₀) (hU.inter hV₀) (subset_inter hKU hKV₀) μ σ (hσ.mono inter_subset_left) f
    fun y hy => hf y hy.2

end Basic

/-- The statement proved by induction: Theorem A and division on every box whose non-constant
real directions lie in `F`, for every module coherent near the box. -/
def BoxThm (F : Finset (Fin n × Fin 2)) : Prop :=
  ∀ C : Fin n → Set ℂ, IsBox C → nonconstDirs C ⊆ F →
    ∀ (ι : Type) [Fintype ι] (M : GermModule (EuclideanSpace ℂ (Fin n)) ι)
      (Ω : Set (EuclideanSpace ℂ (Fin n))), IsOpen Ω → boxSet C ⊆ Ω →
      M.IsCoherentOn Ω → GenNear M (boxSet C) ∧ DivNear M (boxSet C)

section Step

variable {F : Finset (Fin n × Fin 2)} (ih : ∀ F' ⊂ F, BoxThm F')
include ih

/-- The induction hypothesis applies to the face of a cut of a sub-box in a non-constant
direction. -/
theorem face_thm {C B : Fin n → Set ℂ} (hF : nonconstDirs C ⊆ F) (hBC : B ≤ C) (hB : IsBox B)
    {i : Fin n} {d : Fin 2} (hc : ¬ ConstDir B (i, d)) (t : ℝ) :
    ∀ (ι : Type) [Fintype ι] (M : GermModule (EuclideanSpace ℂ (Fin n)) ι)
      (Ω : Set (EuclideanSpace ℂ (Fin n))), IsOpen Ω →
      boxSet (cut B i (dirC d) {t}) ⊆ Ω → M.IsCoherentOn Ω →
        GenNear M (boxSet (cut B i (dirC d) {t})) ∧ DivNear M (boxSet (cut B i (dirC d) {t})) := by
  have hpF : (i, d) ∈ F := hF (nonconstDirs_mono hBC (mem_nonconstDirs.2 hc))
  refine ih (F.erase (i, d)) (Finset.erase_ssubset hpF) _ (hB.cut_singleton i _ t) ?_
  exact (nonconstDirs_face_subset B i d t).trans
    (Finset.erase_subset_erase _ ((nonconstDirs_mono hBC).trans hF))

/-- **Theorem A**, induction step. -/
theorem genNear_step {C : Fin n → Set ℂ} (hC : IsBox C) (hF : nonconstDirs C ⊆ F) {ι : Type}
    [Fintype ι] {M : GermModule (EuclideanSpace ℂ (Fin n)) ι} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    (hΩ : IsOpen Ω) (hCΩ : boxSet C ⊆ Ω)
    (hM : M.IsCoherentOn Ω) : GenNear M (boxSet C) := by
  classical
  refine bisection hC (fun B => GenNear M (boxSet B)) ?_ ?_ ?_
  · intro B _ _ he
    simp only [he]
    exact genNear_empty (M := M)
  · intro x hx
    obtain ⟨U, hU, hxU, μ, _, σ, hσ⟩ := hM x (hCΩ hx)
    exact ⟨U, hU.mem_nhds hxU, fun B _ _ hBU => ⟨U, hU, hBU, μ, inferInstance, σ, hσ⟩⟩
  · intro B hBC hB i d t h₁ h₂
    by_cases hc : ConstDir B (i, d)
    · rcases cut_Iic_or_Ici_eq_self hc t with h | h
      · rwa [h] at h₁
      · rwa [h] at h₂
    set θ := dirC d
    have hface : boxSet (cut B i θ {t}) ⊆ Ω :=
      (boxSet_mono ((cut_le B i θ _).trans hBC)).trans hCΩ
    have hS := face_thm ih hF hBC hB hc t ι M Ω hΩ hface hM
    obtain ⟨U₁, hU₁, hQ₁, μ₁, _, σ₁, hσ₁⟩ := h₁
    obtain ⟨U₂, hU₂, hQ₂, μ₂, _, σ₂, hσ₂⟩ := h₂
    have hf₁ : boxSet (cut B i θ {t}) ⊆ U₁ :=
      (boxSet_mono (cut_mono_set B i θ (singleton_subset_iff.2 (mem_Iic.2 le_rfl)))).trans hQ₁
    have hf₂ : boxSet (cut B i θ {t}) ⊆ U₂ :=
      (boxSet_mono (cut_mono_set B i θ (singleton_subset_iff.2 (mem_Ici.2 le_rfl)))).trans hQ₂
    have hT := fun m => hS.2 (U₁ ∩ U₂) (hU₁.inter hU₂) (subset_inter hf₁ hf₂) μ₁ σ₁
      (hσ₁.mono inter_subset_left) (σ₂ m) fun y hy => hσ₂.gen_mem hy.2 m
    have hS' := fun k => hS.2 (U₁ ∩ U₂) (hU₁.inter hU₂) (subset_inter hf₁ hf₂) μ₂ σ₂
      (hσ₂.mono inter_subset_right) (σ₁ k) fun y hy => hσ₁.gen_mem hy.1 k
    choose VT hVT hfVT cT hcT hσT using hT
    choose VS hVS hfVS cS hcS hσS using hS'
    set W := (⋂ m, VT m) ∩ ⋂ k, VS k with hWdef
    have hW : IsOpen W := (isOpen_iInter_of_finite hVT).inter (isOpen_iInter_of_finite hVS)
    have hfW : boxSet (cut B i θ {t}) ⊆ W :=
      subset_inter (subset_iInter hfVT) (subset_iInter hfVS)
    have hWT : ∀ m, W ⊆ VT m := fun m => inter_subset_left.trans (iInter_subset _ m)
    have hWS : ∀ k, W ⊆ VS k := fun k => inter_subset_right.trans (iInter_subset _ k)
    obtain ⟨U, hU, hQU, τ, hτ⟩ := TheoremA.exists_generatedOn_union i θ t hB.isCompact
      hB.convex hU₁ hU₂ hW (fun z hz => hQ₁ (mem_boxSet_cut.2 hz))
      (fun z hz => hQ₂ (mem_boxSet_cut.2 hz)) (fun z hz => hfW (mem_boxSet_cut.2 hz)) hσ₁ hσ₂
      (T := fun z => Matrix.of fun k m => cT m k z) (S := fun z => Matrix.of fun m k => cS k m z)
      (fun k m => by simpa using (hcT m k).mono (hWT m))
      (fun m k => by simpa using (hcS k m).mono (hWS k))
      (fun z hz m j => by simpa using hσT m z (hWT m hz) j)
      (fun z hz k j => by simpa using hσS k z (hWS k hz) j)
    exact ⟨U, hU, hQU, μ₁ ⊕ μ₂, inferInstance, τ, hτ⟩

/-- **Division**, induction step. -/
theorem divNear_step {C : Fin n → Set ℂ} (hC : IsBox C) (hF : nonconstDirs C ⊆ F) {ι : Type}
    [Fintype ι] {M : GermModule (EuclideanSpace ℂ (Fin n)) ι} : DivNear M (boxSet C) := by
  classical
  intro U hU hCU μ _ σ hσ f hf
  -- the module of relations among the generators is coherent (Oka)
  have hR : (relations σ).IsCoherentOn U := fun x hx =>
    CoherentAt.relations (Hironaka.OkaCoherence.okaProperty_euclidean n)
      fun k j => hσ.holAt hU hx k j
  refine bisection hC (fun B => ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ boxSet B ⊆ V ∧
    ∃ c : μ → EuclideanSpace ℂ (Fin n) → ℂ,
    (∀ k, DifferentiableOn ℂ (c k) V) ∧ ∀ z ∈ V, ∀ j, f j z = ∑ k, c k z * σ k j z) ?_ ?_ ?_
  · intro B _ _ he
    exact ⟨∅, isOpen_empty, he.subset, fun _ _ => 0, fun _ => differentiableOn_empty,
      fun _ hz => False.elim hz⟩
  · intro x hx
    obtain ⟨c, hc, hcf⟩ := (hσ.2 x (hCU hx) f).1 (hf x (hCU hx))
    obtain ⟨V, hV, hxV, hcV⟩ := exists_isOpen_differentiableOn hc
    obtain ⟨V', hV'f, hV', hxV'⟩ := _root_.eventually_nhds_iff.1 (eventually_all.2 hcf)
    exact ⟨V ∩ V', (hV.inter hV').mem_nhds ⟨hxV, hxV'⟩, fun B _ _ hBN =>
      ⟨V ∩ V', hV.inter hV', hBN, c, fun k => (hcV k).mono inter_subset_left,
        fun z hz j => hV'f z hz.2 j⟩⟩
  · intro B hBC hB i d t h₁ h₂
    by_cases hc : ConstDir B (i, d)
    · rcases cut_Iic_or_Ici_eq_self hc t with h | h
      · rwa [h] at h₁
      · rwa [h] at h₂
    set θ := dirC d
    obtain ⟨V₁, hV₁, hQ₁, c₁, hc₁, hf₁⟩ := h₁
    obtain ⟨V₂, hV₂, hQ₂, c₂, hc₂, hf₂⟩ := h₂
    have hBU : boxSet B ⊆ U := (boxSet_mono hBC).trans hCU
    have hfB : boxSet (cut B i θ {t}) ⊆ boxSet B := boxSet_mono (cut_le B i θ _)
    have hfV₁ : boxSet (cut B i θ {t}) ⊆ V₁ :=
      (boxSet_mono (cut_mono_set B i θ (singleton_subset_iff.2 (mem_Iic.2 le_rfl)))).trans hQ₁
    have hfV₂ : boxSet (cut B i θ {t}) ⊆ V₂ :=
      (boxSet_mono (cut_mono_set B i θ (singleton_subset_iff.2 (mem_Ici.2 le_rfl)))).trans hQ₂
    -- Theorem A for the relations on `B` (same induction step) and division on the face
    obtain ⟨UR, hUR, hBUR, ν, _, ρ, hρ⟩ :=
      genNear_step ih hB ((nonconstDirs_mono hBC).trans hF) hU hBU hR
    have hS := face_thm ih hF hBC hB hc t μ (relations σ) U hU (hfB.trans hBU) hR
    have hsec : ∀ y ∈ V₁ ∩ V₂, (relations σ).mem y (fun k z => c₁ k z - c₂ k z) := by
      intro y hy
      rw [mem_relations_iff]
      refine ⟨fun k => holAt_of_differentiableOn (hV₁.inter hV₂)
        (((hc₁ k).mono inter_subset_left).sub ((hc₂ k).mono inter_subset_right)) hy,
        fun j => eventually_of_mem ((hV₁.inter hV₂).mem_nhds hy) fun z hz => ?_⟩
      simp only [sub_mul, Finset.sum_sub_distrib, ← hf₁ z hz.1 j, ← hf₂ z hz.2 j, sub_self]
    obtain ⟨W, hW, hfW, e, he, hce⟩ := DivNear.of_section hS.2 hUR (hV₁.inter hV₂)
      (hfB.trans hBUR) (subset_inter hfV₁ hfV₂) hρ hsec
    have hρrel : ∀ z ∈ UR ∩ U, ∀ r j, ∑ k, ρ r k z * σ k j z = 0 := fun z hz r j =>
      ((mem_relations_iff.1 (hρ.gen_mem hz.1 r)).2 j).eq_of_nhds
    obtain ⟨V, hV, hQV, c, hc, hfc⟩ := TheoremA.exists_combination_union i θ t hB.isCompact
      (hUR.inter hU) hV₁ hV₂ hW (subset_inter hBUR hBU)
      (fun z hz => hQ₁ (mem_boxSet_cut.2 hz)) (fun z hz => hQ₂ (mem_boxSet_cut.2 hz))
      (fun z hz => hfW (mem_boxSet_cut.2 hz))
      (fun r k => (hρ.1 r k).mono inter_subset_left) hρrel hc₁ hc₂ hf₁ hf₂ he hce
    exact ⟨V, hV, hQV, c, hc, hfc⟩

end Step

/-- **Theorems A and division on boxes**, by induction on the set of non-constant directions. -/
theorem boxThm (F : Finset (Fin n × Fin 2)) : BoxThm F := by
  induction F using Finset.strongInduction with
  | H F ih =>
    intro C hC hF ι _ M Ω hΩ hCΩ hM
    exact ⟨genNear_step ih hC hF hΩ hCΩ hM, divNear_step ih hC hF⟩

variable {C : Fin n → Set ℂ} {ι : Type} [Fintype ι] {M : GermModule (EuclideanSpace ℂ (Fin n)) ι}
  {Ω : Set (EuclideanSpace ℂ (Fin n))}

/-- **Cartan's Theorem A on compact convex product sets.** If `M ⊆ 𝒪^ι` is coherent on an open
set containing `Q = ∏ C_l` (`C_l ⊆ ℂ` compact convex), then finitely many sections of `M` over
a neighbourhood `U` of `Q` generate the stalk `M_y` at every `y ∈ U`. -/
theorem theoremA_box (hC : IsBox C) (hΩ : IsOpen Ω) (hCΩ : boxSet C ⊆ Ω)
    (hM : M.IsCoherentOn Ω) : GenNear M (boxSet C) :=
  (boxThm _ C hC subset_rfl ι M Ω hΩ hCΩ hM).1

/-- **Division by generators on compact convex product sets** (the form of Theorem B used for
surjections). If `M` is coherent near `Q = ∏ C_l` and `σ` generate `M` over an open `U ⊇ Q`, every
section of `M` over `U` is `∑ c_k σ_k` near `Q` with holomorphic `c_k`. -/
theorem division_box (hC : IsBox C) (hΩ : IsOpen Ω) (hCΩ : boxSet C ⊆ Ω)
    (hM : M.IsCoherentOn Ω) : DivNear M (boxSet C) :=
  (boxThm _ C hC subset_rfl ι M Ω hΩ hCΩ hM).2

/-- **Theorem B in degree one on compact convex product sets**, for arbitrary covers: let `M` be
coherent near `Q = ∏ C_l`, `(U_a)` open sets covering `Q`, and `s_a` tuples holomorphic on `U_a`
with `s_a - s_b ∈ M` on `U_a ∩ U_b` (a section of `𝒪^ι / M` near `Q`). Then there is a tuple `g`
holomorphic on an open `V ⊇ Q` with `g - s_a ∈ M` on `V ∩ U_a` for every `a`. -/
theorem exists_lift (hC : IsBox C) (hΩ : IsOpen Ω) (hCΩ : boxSet C ⊆ Ω)
    (hM : M.IsCoherentOn Ω) {α : Type*} (U : α → Set (EuclideanSpace ℂ (Fin n)))
    (hU : ∀ a, IsOpen (U a))
    (hcov : boxSet C ⊆ ⋃ a, U a) (s : α → ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (hs : ∀ a j, DifferentiableOn ℂ (s a j) (U a))
    (hcoc : ∀ a b, ∀ y ∈ U a ∩ U b, M.mem y (fun j z => s a j z - s b j z)) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ boxSet C ⊆ V ∧
      ∃ g : ι → EuclideanSpace ℂ (Fin n) → ℂ,
      (∀ j, DifferentiableOn ℂ (g j) V) ∧ ∀ a, ∀ y ∈ V ∩ U a,
        M.mem y (fun j z => g j z - s a j z) := by
  classical
  obtain ⟨Uσ, hUσ, hCUσ, μ, _, σ, hσ⟩ := theoremA_box hC hΩ hCΩ hM
  set O : Set (EuclideanSpace ℂ (Fin n)) := (⋃ a, U a) ∩ Ω ∩ Uσ with hOdef
  have hO : IsOpen O := ((isOpen_iUnion hU).inter hΩ).inter hUσ
  suffices h : ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ boxSet C ⊆ V ∧ V ⊆ O ∧
      ∃ g : ι → EuclideanSpace ℂ (Fin n) → ℂ,
      (∀ j, DifferentiableOn ℂ (g j) V) ∧ ∀ a, ∀ y ∈ V ∩ U a,
        M.mem y (fun j z => g j z - s a j z) by
    obtain ⟨V, hV, hCV, -, g, hg, hgs⟩ := h
    exact ⟨V, hV, hCV, g, hg, hgs⟩
  refine bisection hC (fun B => ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ boxSet B ⊆ V ∧
      V ⊆ O ∧ ∃ g : ι → EuclideanSpace ℂ (Fin n) → ℂ,
      (∀ j, DifferentiableOn ℂ (g j) V) ∧ ∀ a, ∀ y ∈ V ∩ U a,
        M.mem y (fun j z => g j z - s a j z)) ?_ ?_ ?_
  · intro B _ _ he
    exact ⟨∅, isOpen_empty, he.subset, empty_subset _, fun _ _ => 0,
      fun _ => differentiableOn_empty, fun _ _ hy => False.elim hy.1⟩
  · intro x hx
    obtain ⟨a₀, hxa₀⟩ := mem_iUnion.1 (hcov hx)
    have hxO : x ∈ O := ⟨⟨hcov hx, hCΩ hx⟩, hCUσ hx⟩
    refine ⟨U a₀ ∩ O, ((hU a₀).inter hO).mem_nhds ⟨hxa₀, hxO⟩, fun B _ _ hBN =>
      ⟨U a₀ ∩ O, (hU a₀).inter hO, hBN, inter_subset_right, s a₀,
        fun j => (hs a₀ j).mono inter_subset_left, fun a y hy => hcoc a₀ a y ⟨hy.1.1, hy.2⟩⟩⟩
  · intro B hBC hB i d t h₁ h₂
    set θ := dirC d
    obtain ⟨V₁, hV₁, hQ₁, hV₁O, g₁, hg₁, hm₁⟩ := h₁
    obtain ⟨V₂, hV₂, hQ₂, hV₂O, g₂, hg₂, hm₂⟩ := h₂
    have hBC' : boxSet B ⊆ boxSet C := boxSet_mono hBC
    have hfB : boxSet (cut B i θ {t}) ⊆ boxSet B := boxSet_mono (cut_le B i θ _)
    have hfV₁ : boxSet (cut B i θ {t}) ⊆ V₁ :=
      (boxSet_mono (cut_mono_set B i θ (singleton_subset_iff.2 (mem_Iic.2 le_rfl)))).trans hQ₁
    have hfV₂ : boxSet (cut B i θ {t}) ⊆ V₂ :=
      (boxSet_mono (cut_mono_set B i θ (singleton_subset_iff.2 (mem_Ici.2 le_rfl)))).trans hQ₂
    -- `g₁ - g₂` is a section of `M` near the face
    have hsec : ∀ y ∈ V₁ ∩ V₂, M.mem y (fun j z => g₁ j z - g₂ j z) := by
      intro y hy
      have hyO := hV₁O hy.1
      obtain ⟨a, hya⟩ := mem_iUnion.1 hyO.1.1
      have h := (hM y hyO.1.2).sub_mem (hm₁ a y ⟨hy.1, hya⟩) (hm₂ a y ⟨hy.2, hya⟩)
      exact (hM y hyO.1.2).congr_mem h fun j => Eventually.of_forall fun z => by ring
    obtain ⟨W, hW, hfW, c, hc, hcW⟩ := DivNear.of_section
      (division_box (hB.cut_singleton i θ t) hΩ (hfB.trans (hBC'.trans hCΩ)) hM)
        hUσ (hV₁.inter hV₂) (hfB.trans (hBC'.trans hCUσ)) (subset_inter hfV₁ hfV₂) hσ hsec
    have hsplit := fun k => Cousin.exists_cousin_split_compact i θ t hB.isCompact hW (hc k)
      (fun z hz => hfW (mem_boxSet_cut.2 hz))
    choose W' W'' hW'o hW''o hQW' hQW'' c' c'' hc' hc'' hcc using hsplit
    set V₁' := V₁ ∩ Uσ ∩ ⋂ k, W' k
    set V₂' := V₂ ∩ Uσ ∩ ⋂ k, W'' k
    set V₀ := W ∩ ⋂ k, (W' k ∩ W'' k)
    have hV₁' : IsOpen V₁' := (hV₁.inter hUσ).inter (isOpen_iInter_of_finite hW'o)
    have hV₂' : IsOpen V₂' := (hV₂.inter hUσ).inter (isOpen_iInter_of_finite hW''o)
    have hV₀ : IsOpen V₀ :=
      hW.inter (isOpen_iInter_of_finite fun k => (hW'o k).inter (hW''o k))
    set h₁' : (EuclideanSpace ℂ (Fin n)) → ι → ℂ := fun z j => g₁ j z - ∑ k, c' k z * σ k j z
    set h₂' : (EuclideanSpace ℂ (Fin n)) → ι → ℂ := fun z j => g₂ j z - ∑ k, c'' k z * σ k j z
    obtain ⟨V, G, hVo, hV1, hV2, hV0, hloc⟩ := TheoremA.exists_glue hV₀ hV₁' hV₂'
      (Cartan.continuous_linForm i θ) t h₁' h₂' (by
        intro z hz
        funext j
        have h1 := hcW z hz.1.1.1 j
        have h2 : ∀ k, c k z = c' k z - c'' k z := fun k =>
          hcc k z ⟨(mem_iInter.1 hz.1.1.2 k).1, (mem_iInter.1 hz.1.1.2 k).2⟩
        simp only [h₁', h₂', h2, sub_mul, Finset.sum_sub_distrib] at h1 ⊢
        linear_combination h1)
    have hQ' : ∀ z, (∀ l, z l ∈ B l) → (θ * z i).re ≤ t → z ∈ V₁' := fun z hz hzt =>
      ⟨⟨hQ₁ (mem_boxSet_cut.2 ⟨hz, hzt⟩), hCUσ (hBC' hz)⟩,
        mem_iInter.2 fun k => hQW' k ⟨hz, hzt⟩⟩
    have hQ'' : ∀ z, (∀ l, z l ∈ B l) → t ≤ (θ * z i).re → z ∈ V₂' := fun z hz hzt =>
      ⟨⟨hQ₂ (mem_boxSet_cut.2 ⟨hz, hzt⟩), hCUσ (hBC' hz)⟩,
        mem_iInter.2 fun k => hQW'' k ⟨hz, hzt⟩⟩
    have hside : ∀ z ∈ V, z ∈ V₁ ∪ V₂ := by
      intro z hz
      obtain ⟨N, hN, hs⟩ := hloc z hz
      rcases hs with ⟨hNV, -⟩ | ⟨hNV, -⟩
      · exact Or.inl (hNV (mem_of_mem_nhds hN)).1.1
      · exact Or.inr (hNV (mem_of_mem_nhds hN)).1.1
    refine ⟨V, hVo, fun z hz => ?_, fun z hz => ?_, fun j z => G z j, fun j => ?_,
      fun a y hy => ?_⟩
    · rcases lt_trichotomy (θ * z i).re t with h | h | h
      · exact hV1 z (hQ' z hz h.le) h
      · refine hV0 ⟨⟨⟨hfW (mem_boxSet_cut.2 ⟨hz, h⟩), mem_iInter.2 fun k =>
          ⟨hQW' k ⟨hz, h.le⟩, hQW'' k ⟨hz, h.ge⟩⟩⟩, hQ' z hz h.le⟩, hQ'' z hz h.ge⟩
      · exact hV2 z (hQ'' z hz h.le) h
    · rcases hside z hz with h | h
      · exact hV₁O h
      · exact hV₂O h
    · intro z hz
      obtain ⟨N, hN, hs⟩ := hloc z hz
      rcases hs with ⟨hNV, hNg⟩ | ⟨hNV, hNg⟩
      · have hzV := hNV (mem_of_mem_nhds hN)
        have hd : DifferentiableAt ℂ (fun y => h₁' y j) z := by
          refine ((hg₁ j).differentiableAt (hV₁.mem_nhds hzV.1.1)).sub ?_
          refine DifferentiableAt.fun_sum fun k _ => ?_
          exact ((hc' k).differentiableAt ((hW'o k).mem_nhds (mem_iInter.1 hzV.2 k))).mul
            ((hσ.1 k j).differentiableAt (hUσ.mem_nhds hzV.1.2))
        exact (hd.congr_of_eventuallyEq (eventually_of_mem hN fun y hy => by
          simp only [hNg y hy])).differentiableWithinAt
      · have hzV := hNV (mem_of_mem_nhds hN)
        have hd : DifferentiableAt ℂ (fun y => h₂' y j) z := by
          refine ((hg₂ j).differentiableAt (hV₂.mem_nhds hzV.1.1)).sub ?_
          refine DifferentiableAt.fun_sum fun k _ => ?_
          exact ((hc'' k).differentiableAt ((hW''o k).mem_nhds (mem_iInter.1 hzV.2 k))).mul
            ((hσ.1 k j).differentiableAt (hUσ.mem_nhds hzV.1.2))
        exact (hd.congr_of_eventuallyEq (eventually_of_mem hN fun y hy => by
          simp only [hNg y hy])).differentiableWithinAt
    · obtain ⟨N, hN, hs⟩ := hloc y hy.1
      have hyN := mem_of_mem_nhds hN
      rcases hs with ⟨hNV, hNg⟩ | ⟨hNV, hNg⟩
      · have hyV := hNV hyN
        have hyΩ : y ∈ Ω := (hV₁O hyV.1.1).1.2
        have hcomb : M.mem y (fun j z => ∑ k, c' k z * σ k j z) :=
          (hσ.2 y hyV.1.2 _).2 ⟨c', fun k => holAt_of_differentiableOn (hW'o k) (hc' k)
            (mem_iInter.1 hyV.2 k), fun _ => EventuallyEq.rfl⟩
        have h := (hM y hyΩ).sub_mem (hm₁ a y ⟨hyV.1.1, hy.2⟩) hcomb
        refine (hM y hyΩ).congr_mem h fun j => eventually_of_mem hN fun z hz => ?_
        show g₁ j z - s a j z - ∑ k, c' k z * σ k j z = G z j - s a j z
        rw [hNg z hz]
        simp only [h₁']
        ring
      · have hyV := hNV hyN
        have hyΩ : y ∈ Ω := (hV₂O hyV.1.1).1.2
        have hcomb : M.mem y (fun j z => ∑ k, c'' k z * σ k j z) :=
          (hσ.2 y hyV.1.2 _).2 ⟨c'', fun k => holAt_of_differentiableOn (hW''o k) (hc'' k)
            (mem_iInter.1 hyV.2 k), fun _ => EventuallyEq.rfl⟩
        have h := (hM y hyΩ).sub_mem (hm₂ a y ⟨hyV.1.1, hy.2⟩) hcomb
        refine (hM y hyΩ).congr_mem h fun j => eventually_of_mem hN fun z hz => ?_
        show g₂ j z - s a j z - ∑ k, c'' k z * σ k j z = G z j - s a j z
        rw [hNg z hz]
        simp only [h₂']
        ring

/-- **Theorem B for surjections on compact convex product sets.** Let `P ⊆ 𝒪^κ`, `Q ⊆ 𝒪^ι` be
coherent on an open `Ω ⊇ ∏ C_l` and `A` a `κ × ι` matrix holomorphic on `Ω`. If `b` is a section
of `P + A(Q)` on a neighbourhood of `∏ C_l`, then `b = p + A a` near `∏ C_l` with `p`, `a`
holomorphic sections of `P`, `Q` there. -/
theorem exists_decompose (hC : IsBox C) (hΩ : IsOpen Ω) (hCΩ : boxSet C ⊆ Ω) {κ : Type}
    [Fintype κ] {P : GermModule (EuclideanSpace ℂ (Fin n)) κ}
    {Q : GermModule (EuclideanSpace ℂ (Fin n)) ι} (hP : P.IsCoherentOn Ω)
    (hQ : Q.IsCoherentOn Ω) {A : κ → ι → EuclideanSpace ℂ (Fin n) → ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (A i j) Ω)
    {b : κ → EuclideanSpace ℂ (Fin n) → ℂ} {V₀ : Set (EuclideanSpace ℂ (Fin n))} (hV₀ : IsOpen V₀)
    (hCV₀ : boxSet C ⊆ V₀)
    (hb : ∀ y ∈ V₀, (P.sup (Q.map A)).mem y b) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ boxSet C ⊆ V ∧
      ∃ (p : κ → EuclideanSpace ℂ (Fin n) → ℂ) (a : ι → EuclideanSpace ℂ (Fin n) → ℂ),
      (∀ j, DifferentiableOn ℂ (p j) V) ∧ (∀ j, DifferentiableOn ℂ (a j) V) ∧
      (∀ y ∈ V, P.mem y p) ∧ (∀ y ∈ V, Q.mem y a) ∧
      ∀ z ∈ V, ∀ j, b j z = p j z + matApply A a j z := by
  classical
  obtain ⟨UP, hUP, hCUP, μ, _, π, hπ⟩ := theoremA_box hC hΩ hCΩ hP
  obtain ⟨UQ, hUQ, hCUQ, ν, _, q, hq⟩ := theoremA_box hC hΩ hCΩ hQ
  set U := UP ∩ UQ ∩ Ω with hUdef
  have hU : IsOpen U := (hUP.inter hUQ).inter hΩ
  have hCU : boxSet C ⊆ U := subset_inter (subset_inter hCUP hCUQ) hCΩ
  have hπU : P.GeneratedOn U π := hπ.mono fun z hz => hz.1.1
  have hqU : Q.GeneratedOn U q := hq.mono fun z hz => hz.1.2
  have hN : (P.sup (Q.map A)).GeneratedOn U (Sum.elim π fun m => matApply A (q m)) :=
    hπU.sup (hqU.map fun i j => (hA i j).mono fun z hz => hz.2)
  have hNc : (P.sup (Q.map A)).IsCoherentOn Ω :=
    hP.sup (hQ.map fun x hx i j => holAt_of_differentiableOn hΩ (hA i j) hx)
  obtain ⟨V, hV, hCV, c, hc, hbc⟩ :=
    DivNear.of_section (division_box hC hΩ hCΩ hNc) hU hV₀ hCU hCV₀ hN hb
  refine ⟨V ∩ U, hV.inter hU, subset_inter hCV hCU,
    fun j z => ∑ k, c (Sum.inl k) z * π k j z, fun i z => ∑ m, c (Sum.inr m) z * q m i z,
    fun j => ?_, fun i => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz j => ?_⟩
  · exact DifferentiableOn.fun_sum fun k _ =>
      ((hc _).mono inter_subset_left).mul ((hπU.1 k j).mono inter_subset_right)
  · exact DifferentiableOn.fun_sum fun m _ =>
      ((hc _).mono inter_subset_left).mul ((hqU.1 m i).mono inter_subset_right)
  · exact (hπU.2 y hy.2 _).2 ⟨fun k => c (Sum.inl k), fun k =>
      holAt_of_differentiableOn (hV.inter hU) ((hc _).mono inter_subset_left) hy,
      fun _ => EventuallyEq.rfl⟩
  · exact (hqU.2 y hy.2 _).2 ⟨fun m => c (Sum.inr m), fun m =>
      holAt_of_differentiableOn (hV.inter hU) ((hc _).mono inter_subset_left) hy,
      fun _ => EventuallyEq.rfl⟩
  · rw [hbc z hz.1 j, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, matApply, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

end Hironaka.Analytic.GAGA.Core.TheoremB
