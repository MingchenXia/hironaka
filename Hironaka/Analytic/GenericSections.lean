/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.AnalyticDimensionCoreExact
import Hironaka.Analytic.ThinDimensionDrop
import Hironaka.Analytic.AnalyticSubsetPreimage

set_option autoImplicit false

/-!
# Generic hyperplane sections

Blueprint `rem:generic-sections` (Demailly, *Complex analytic and differential geometry*, II.5 and
II.8, used in the fibre lower bound and in the flat case of Remmert--Stein).  Let `T` be analytic in
a complex manifold `M` with `dim T ≤ k`, `k ≥ 1`, `g : M → ℂᴺ` holomorphic (an inclusion or a chart,
in the applications), `x₀ ∈ M`, and `Ξ` a space of linear forms on `ℂᴺ` separating every point of
`T \ {x₀}` from `x₀` through `g`.  Then there is a countable set of proper subspaces of `Ξ` such that
for every `ξ ∈ Ξ` outside all of them the section `T ∩ {ξ ∘ g = ξ(g x₀)}` has dimension `≤ k - 1`
(`exists_generic_sections`); and some `ξ ∈ Ξ` avoids any countable set of proper subspaces
(`exists_mem_forall_not_mem`, Baire).

* `lt_of_regularAtDim_of_thin_nhds`: the thin-drop lemma of `ThinDimensionDrop` when thinness is
  known only inside a neighbourhood of the regular point.
* `exists_ne_mem_of_regularAtDim_pos`: a regular point of positive dimension is not isolated.
* `isComplexAnalyticSubset_level`, `isComplexAnalyticSubset_section`: sections are analytic.
-/

open Set Filter Topology Metric
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.GenericSections

open Hironaka.RegularLocusDense AnalyticGermDecomposition RegularPointDimension
  AnalyticDescendingChain AnalyticDimensionBasics FiniteFibrePiece DimensionMonotone
  ThinDimensionDrop

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Thin subsets, locally -/

/-- **Thin-drop, locally**: as `ThinDimensionDrop.lt_of_regularAtDim_of_thin`, with the thinness of
`T'` in `T` required only for open sets inside a neighbourhood `N` of the regular point. -/
theorem lt_of_regularAtDim_of_thin_nhds {T T' : Set M} (hT : IsComplexAnalyticSubset (n := n) T)
    (hT'T : T' ⊆ T) {a : ℕ} (hdim : DimLE (n := n) T a) {y : M} {k : ℕ}
    (hy : RegularAtDim (n := n) T' y k) {N : Set M} (hN : N ∈ 𝓝 y)
    (hthin : ∀ O : Set M, IsOpen O → O ⊆ N → O ∩ T ⊆ T' → O ∩ T = ∅) : k < a := by
  have hka : k ≤ a := DimLE.anti hT hT'T hdim y k hy
  rcases hka.lt_or_eq with h | rfl
  · exact h
  exfalso
  set e := (complexChartAt (n := n) y).val with he
  have hys : y ∈ e.source := mem_complexChartAt_source y
  obtain ⟨U, φ, hUo, hU0, hφ0, hφd, hφi, hφB⟩ :=
    exists_param_of_regularAtDim (regularAtDim_chartGerm_zero hy) (univ_mem (f := 𝓝 0))
  have hφT : MapsTo φ U (chartGerm (n := n) T y) := fun u hu =>
    chartGerm_mono (n := n) hT'T y (hφB hu).1
  have hdim' : ∀ w j, RegularAtDim (n := n) (M := ComplexModel n) (chartGerm (n := n) T y) w j →
      j ≤ k := fun w j hw => hdim _ j (regularAtDim_of_chartGerm hw)
  have hcont : ContinuousAt (fun w : ComplexModel n => e.symm (w + e y)) 0 := by
    have h1 : ContinuousAt e.symm (e y) := e.continuousAt_symm (e.map_source hys)
    have h2 : ContinuousAt (fun w : ComplexModel n => w + e y) 0 :=
      (continuous_id.add continuous_const).continuousAt
    exact ContinuousAt.comp (g := e.symm) (by rw [zero_add]; exact h1) h2
  have hO₀ : (fun w : ComplexModel n => e.symm (w + e y)) ⁻¹' interior N ∈ 𝓝 (0 : ComplexModel n) :=
    hcont.preimage_mem_nhds (by simpa [e.left_inv hys] using interior_mem_nhds.2 hN)
  obtain ⟨W, hWo, hWO, ⟨w, hwW, hwT⟩, hWsub⟩ :=
    exists_isOpen_subset_image_germ (isAnalyticGerm_chartGerm hT y) hdim' hUo hφd hφi hφT hU0 hφ0
      hO₀
  set OM : Set M := e.source ∩ (fun p => e p - e y) ⁻¹' W with hOM
  have hOMo : IsOpen OM := by
    have hc : ContinuousOn (fun p => e p - e y) e.source := e.continuousOn.sub continuousOn_const
    exact hc.isOpen_inter_preimage e.open_source hWo
  have hOMN : OM ⊆ N := by
    rintro p ⟨hps, hpW⟩
    have h := hWO hpW
    simp only [mem_preimage, sub_add_cancel, e.left_inv hps] at h
    exact interior_subset h
  have hsubT' : OM ∩ T ⊆ T' := by
    rintro p ⟨⟨hps, hpW⟩, hpT⟩
    have hpg : e p - e y ∈ chartGerm (n := n) T y := by
      change e p - e y + e y ∈ e.target ∩ e.symm ⁻¹' T
      rw [sub_add_cancel]
      exact ⟨e.map_source hps, by rw [mem_preimage, e.left_inv hps]; exact hpT⟩
    obtain ⟨u, hu, hue⟩ := hWsub ⟨hpW, hpg⟩
    have hT'g := (hφB hu).1
    rw [hue] at hT'g
    change e p - e y + e y ∈ e.target ∩ e.symm ⁻¹' T' at hT'g
    rw [sub_add_cancel] at hT'g
    have := hT'g.2
    rwa [mem_preimage, e.left_inv hps] at this
  have hempty := hthin OM hOMo hOMN hsubT'
  have hwT' : w + e y ∈ e.target ∩ e.symm ⁻¹' T := hwT
  have hpm : e.symm (w + e y) ∈ OM ∩ T := by
    refine ⟨⟨e.map_target hwT'.1, ?_⟩, hwT'.2⟩
    change e (e.symm (w + e y)) - e y ∈ W
    rw [e.right_inv hwT'.1, add_sub_cancel_right]
    exact hwW
  rw [hempty] at hpm
  exact hpm

/-! ### Regular points of positive dimension are not isolated -/

/-- **A regular point of positive dimension is not isolated**: every neighbourhood contains another
point of the set. -/
theorem exists_ne_mem_of_regularAtDim_pos {A : Set M} {x : M} {j : ℕ}
    (hx : RegularAtDim (n := n) A x j) (hj : 0 < j) {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ p ∈ N ∩ A, p ≠ x := by
  set e := (complexChartAt (n := n) x).val with he
  have hxs : x ∈ e.source := mem_complexChartAt_source x
  obtain ⟨U, φ, hUo, hU0, hφ0, hφd, hφi, hφB⟩ :=
    exists_param_of_regularAtDim (regularAtDim_chartGerm_zero hx) (univ_mem (f := 𝓝 0))
  have hcont : ContinuousAt (fun w : ComplexModel n => e.symm (w + e x)) 0 := by
    have h1 : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hxs)
    have h2 : ContinuousAt (fun w : ComplexModel n => w + e x) 0 :=
      (continuous_id.add continuous_const).continuousAt
    exact ContinuousAt.comp (g := e.symm) (by rw [zero_add]; exact h1) h2
  have hO : (fun w : ComplexModel n => e.symm (w + e x)) ⁻¹' N ∈ 𝓝 (0 : ComplexModel n) :=
    hcont.preimage_mem_nhds (by simpa [e.left_inv hxs] using hN)
  have hφc : ContinuousAt φ 0 := (hφd.differentiableAt (hUo.mem_nhds hU0)).continuousAt
  have hev : ∀ᶠ u in 𝓝 (0 : ComplexModel j), u ∈ U ∧ φ u ∈ (fun w => e.symm (w + e x)) ⁻¹' N :=
    Filter.Eventually.and (hUo.mem_nhds hU0) (hφc.preimage_mem_nhds (by rw [hφ0]; exact hO))
  have : Nontrivial (ComplexModel j) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [finrank_euclideanSpace_fin]; exact hj)
  obtain ⟨u, ⟨huU, huN⟩, hu0⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := {(0 : ComplexModel j)}ᶜ))).exists
  have hφu : φ u ∈ chartGerm (n := n) A x := (hφB huU).1
  have hφu' : φ u + e x ∈ e.target ∩ e.symm ⁻¹' A := hφu
  refine ⟨e.symm (φ u + e x), ⟨huN, hφu'.2⟩, fun h => hu0 ?_⟩
  have h1 : e (e.symm (φ u + e x)) = e x := by rw [h]
  rw [e.right_inv hφu'.1] at h1
  have h2 : φ u = φ 0 := by rw [hφ0]; simpa using h1
  exact hφi huU hU0 h2

/-! ### Sections are analytic -/

/-- A level set of a linear form is analytic in `ℂᴺ`. -/
theorem isComplexAnalyticSubset_level {N : ℕ} (ξ : ComplexModel N →L[ℂ] ℂ) (c : ℂ) :
    IsComplexAnalyticSubset (n := N) (M := ComplexModel N) {w | ξ w = c} := by
  intro x
  exact ⟨{ generatorCount := 1
           generator := fun _ w => ξ w - c
           coordinateNeighborhood := (complexChartAt (n := N) x).val.target
           isOpen_coordinateNeighborhood := (complexChartAt (n := N) x).val.open_target
           center_mem_coordinateNeighborhood :=
             (complexChartAt (n := N) x).val.map_source (mem_complexChartAt_source x)
           coordinateNeighborhood_subset_target := Subset.rfl
           generator_holomorphic := fun _ => (ξ.differentiable.sub_const c).differentiableOn
           zeroLocus := by
             intro y _ _
             change ξ y = c ↔ ∀ _ : Fin 1, ξ y - c = 0
             simp [sub_eq_zero] }⟩

/-- A section of an analytic set by a level set of `ξ ∘ g` is analytic. -/
theorem isComplexAnalyticSubset_section {T : Set M} (hT : IsComplexAnalyticSubset (n := n) T)
    {N : ℕ} {g : M → ComplexModel N}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ g)
    (ξ : ComplexModel N →L[ℂ] ℂ) (c : ℂ) :
    IsComplexAnalyticSubset (n := n) (T ∩ {y | ξ (g y) = c}) :=
  hT.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg
    (isComplexAnalyticSubset_level ξ c))

/-! ### Avoiding countably many proper subspaces -/

/-- **A finite-dimensional space is not a countable union of proper subspaces** (Baire): some
`ξ ∈ Ξ` lies in none of countably many submodules not containing `Ξ`. -/
theorem exists_mem_forall_not_mem {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Ξ : Submodule ℂ V) {S : Set (Submodule ℂ V)} (hS : S.Countable)
    (hprop : ∀ H ∈ S, ¬ Ξ ≤ H) : ∃ ξ ∈ Ξ, ∀ H ∈ S, ξ ∉ H := by
  by_contra hcon
  push Not at hcon
  have : CompleteSpace Ξ := FiniteDimensional.complete ℂ Ξ
  have : Countable S := hS.to_subtype
  let f : S → Set Ξ := fun H => ((H.1).comap Ξ.subtype : Set Ξ)
  have hclosed : ∀ H, IsClosed (f H) := fun H =>
    Submodule.closed_of_finiteDimensional ((H.1).comap Ξ.subtype)
  have hcov : ⋃ H, f H = univ := by
    refine eq_univ_of_forall fun ξ => ?_
    obtain ⟨H, hH, hξH⟩ := hcon ξ ξ.2
    exact mem_iUnion.2 ⟨⟨H, hH⟩, hξH⟩
  obtain ⟨H, hH⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcov
  have htop : (H.1).comap Ξ.subtype = ⊤ := Submodule.eq_top_of_nonempty_interior' _ hH
  apply hprop H.1 H.2
  intro v hv
  have : (⟨v, hv⟩ : Ξ) ∈ (H.1).comap Ξ.subtype := by rw [htop]; exact Submodule.mem_top
  exact this

/-! ### Generic sections -/

/-- The forms vanishing along `g` on `T ∩ O` relative to `x₀`, as a submodule. -/
def levelSubmodule {N : ℕ} (g : M → ComplexModel N) (x₀ : M) (S : Set M) :
    Submodule ℂ (ComplexModel N →L[ℂ] ℂ) where
  carrier := {ξ | ∀ y ∈ S, ξ (g y) = ξ (g x₀)}
  add_mem' := by
    intro ξ η hξ hη y hy
    simp [hξ y hy, hη y hy]
  zero_mem' := by
    intro y _
    simp
  smul_mem' := by
    intro c ξ hξ y hy
    simp [hξ y hy]

/-- **Generic hyperplane sections** (`rem:generic-sections`): if `T` is analytic with `dim T ≤ k`,
`k ≥ 1`, and the forms of `Ξ` separate every point of `T \ {x₀}` from `x₀` through `g` (any map), there is a
countable set of submodules not containing `Ξ` such that for every `ξ ∈ Ξ` outside all of them,
`dim (T ∩ {ξ ∘ g = ξ (g x₀)}) ≤ k - 1`. -/
theorem exists_generic_sections {T : Set M} (hT : IsComplexAnalyticSubset (n := n) T) {k : ℕ}
    (hk : 1 ≤ k) (hdim : DimLE (n := n) T k) {N : ℕ} (g : M → ComplexModel N) (x₀ : M)
    (Ξ : Submodule ℂ (ComplexModel N →L[ℂ] ℂ))
    (hsep : ∀ y ∈ T, y ≠ x₀ → ∃ ξ ∈ Ξ, ξ (g y) ≠ ξ (g x₀)) :
    ∃ S : Set (Submodule ℂ (ComplexModel N →L[ℂ] ℂ)), S.Countable ∧ (∀ H ∈ S, ¬ Ξ ≤ H) ∧
      ∀ ξ ∈ Ξ, (∀ H ∈ S, ξ ∉ H) →
        DimLE (n := n) (T ∩ {y | ξ (g y) = ξ (g x₀)}) (k - 1) := by
  classical
  have hBc := TopologicalSpace.countable_countableBasis M
  have hB := TopologicalSpace.isBasis_countableBasis M
  set B := TopologicalSpace.countableBasis M with hBdef
  set I : Set (Set M) := {O | O ∈ B ∧ ∃ y ∈ T ∩ O, y ≠ x₀} with hI
  refine ⟨(fun O => levelSubmodule g x₀ (T ∩ O)) '' I, (hBc.mono fun O hO => hO.1).image _,
    ?_, ?_⟩
  · rintro _ ⟨O, ⟨-, y, hyTO, hyx⟩, rfl⟩ hle
    obtain ⟨ξ, hξΞ, hξ⟩ := hsep y hyTO.1 hyx
    exact hξ (hle hξΞ y hyTO)
  · intro ξ hξΞ hξS
    set T' := T ∩ {y | ξ (g y) = ξ (g x₀)} with hT'
    have hT'T : T' ⊆ T := inter_subset_left
    -- points other than `x₀`
    have hne : ∀ y j, RegularAtDim (n := n) T' y j → y ≠ x₀ → j < k := by
      intro y j hy hyx
      refine lt_of_regularAtDim_of_thin_nhds hT hT'T hdim hy (N := {x₀}ᶜ)
        (isOpen_compl_singleton.mem_nhds hyx) ?_
      intro O hO hON hOT
      by_contra hne
      obtain ⟨y', hy'O, hy'T⟩ := nonempty_iff_ne_empty.mpr hne
      obtain ⟨Ob, hObB, hy'Ob, hObO⟩ := hB.exists_subset_of_mem_open hy'O hO
      have hOb : Ob ∈ I := ⟨hObB, y', ⟨hy'T, hy'Ob⟩, hON hy'O⟩
      have hξnot := hξS _ ⟨Ob, hOb, rfl⟩
      apply hξnot
      intro z hz
      exact (hOT ⟨hObO hz.2, hz.1⟩).2
    intro y j hy
    by_cases hyx : y = x₀
    · rcases Nat.eq_zero_or_pos j with hj | hj
      · omega
      · subst hyx
        have hev := RegularPatchNeighborhood.eventually_regularAtDim hy
        obtain ⟨p, ⟨hpN, hpT⟩, hpx⟩ := exists_ne_mem_of_regularAtDim_pos hy hj hev
        have := hne p j (hpN hpT) hpx
        omega
    · have := hne y j hy hyx
      omega

/-- **Iterated generic sections**: if `T` is analytic with `dim T ≤ k`, `g` holomorphic, and the
forms of `Ξ` separate the points of `T \ {x₀}` from `x₀` through `g`, there are `ξ₁, …, ξ_k ∈ Ξ`
such that `T ∩ {ξ₁ ∘ g = ξ₁(g x₀), …, ξ_k ∘ g = ξ_k(g x₀)}` has no accumulation point in itself
(it is discrete). -/
theorem exists_forms_not_accPt {N : ℕ} {g : M → ComplexModel N}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ g) (x₀ : M)
    (Ξ : Submodule ℂ (ComplexModel N →L[ℂ] ℂ)) :
    ∀ (k : ℕ) {T : Set M}, IsComplexAnalyticSubset (n := n) T → DimLE (n := n) T k →
      (∀ y ∈ T, y ≠ x₀ → ∃ ξ ∈ Ξ, ξ (g y) ≠ ξ (g x₀)) →
      ∃ ξ : Fin k → (ComplexModel N →L[ℂ] ℂ), (∀ i, ξ i ∈ Ξ) ∧
        ∀ y ∈ T ∩ {y | ∀ i, ξ i (g y) = ξ i (g x₀)},
          ¬ AccPt y (𝓟 (T ∩ {y | ∀ i, ξ i (g y) = ξ i (g x₀)})) := by
  intro k
  induction k with
  | zero =>
    intro T hT hdim _
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    have hset : T ∩ {y | ∀ i : Fin 0, (Fin.elim0 i : ComplexModel N →L[ℂ] ℂ) (g y) =
        (Fin.elim0 i : ComplexModel N →L[ℂ] ℂ) (g x₀)} = T := by
      ext y
      simp
    rw [hset]
    intro y hy
    exact not_accPt_of_locDimLE_zero hT hy (DimLE.locDimLE hdim y)
  | succ k ih =>
    intro T hT hdim hsep
    obtain ⟨S, hSc, hSprop, hS⟩ :=
      exists_generic_sections hT (Nat.succ_pos k) hdim g x₀ Ξ hsep
    obtain ⟨ξ₀, hξ₀Ξ, hξ₀S⟩ := exists_mem_forall_not_mem Ξ hSc hSprop
    set T₁ := T ∩ {y | ξ₀ (g y) = ξ₀ (g x₀)} with hT₁
    have hT₁a : IsComplexAnalyticSubset (n := n) T₁ := isComplexAnalyticSubset_section hT hg ξ₀ _
    have hT₁d : DimLE (n := n) T₁ k := by
      have := hS ξ₀ hξ₀Ξ hξ₀S
      simpa using this
    obtain ⟨ξ', hξ'Ξ, hξ'⟩ := ih hT₁a hT₁d fun y hy hyx => hsep y hy.1 hyx
    refine ⟨Fin.cons ξ₀ ξ', fun i => Fin.cases hξ₀Ξ hξ'Ξ i, ?_⟩
    have hset : T ∩ {y | ∀ i, (Fin.cons ξ₀ ξ' : Fin (k + 1) → _) i (g y) =
        (Fin.cons ξ₀ ξ' : Fin (k + 1) → _) i (g x₀)} =
        T₁ ∩ {y | ∀ i, ξ' i (g y) = ξ' i (g x₀)} := by
      ext y
      simp only [hT₁, mem_inter_iff, mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero,
        Fin.cons_succ]
      tauto
    rw [hset]
    exact hξ'

end Hironaka.GenericSections
