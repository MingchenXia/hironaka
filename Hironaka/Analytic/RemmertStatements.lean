/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.AnalyticDimensionCoreExact
import Hironaka.Support.AnalyticSubsetPresentationsExact
import Hironaka.Support.LocalDimensionMonotoneExact
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.AnalyticSubsetPreimage

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Remmert's proper mapping theorem and the Remmert--Stein theorem: the induction statements

Blueprint `blueprint/src/remmert.tex`, the statements `(R_m)` and `(RS_m)` before
`rem:remmert-stein-flat` (Demailly, *Complex analytic and differential geometry*, II.8.7--8.8).
The proof is a simultaneous induction on `m`; every step is an implication between these two
propositions, so they are stated once, for all complex manifolds (of the given universes):

* `ProperImageStatement m` (`(R_m)`): for a holomorphic map `F : X → Y` and an analytic `A ⊆ X` with
  `dim A ≤ m` and `F|_A` proper, `F(A)` is analytic in `Y`;
* `RemmertSteinStatement m` (`(RS_m)`, with `q = p + 1`): for an analytic `B ⊆ Y` all of whose
  regular points have dimension `< q`, and `E ⊆ Y \ B` analytic in `Y \ B` (a local presentation of
  `E` at every point off `B`) with `dim E ≤ m` and `dim_y E ≥ q` at every point of `E`, the closure
  of `E` is analytic in `Y`.

The file also proves the local tools used to move presentations between manifolds:

* `nonempty_presentation_comp`: a presentation of `A` at `g z` pulls back to a presentation at `z`
  of any set agreeing with `g⁻¹(A)` on an open neighbourhood of `z` on which `g` is holomorphic
  (the pointwise form of `AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage`);
* `nonempty_presentation_of_inter_eq`: presentations depend only on the germ of the set;
* `isComplexAnalyticSubset_preimage_val_of_forall`, `nonempty_presentation_of_preimage_val`:
  "analytic in an open set `U`" (as the manifold `U`) is the same as "a presentation in `M` at
  every point of `U`".

Sorry-free.
-/

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.RemmertStatements

open AnalyticDimensionBasics AnalyticSubsetOpens

universe u₁ u₂

/-- **`(R_m)`**: images of analytic sets of dimension `≤ m` under proper holomorphic maps are
analytic (for manifolds `X : Type u₁`, `Y : Type u₂`). -/
def ProperImageStatement (m : ℕ) : Prop :=
  ∀ ⦃n k : ℕ⦄ ⦃X : Type u₁⦄ [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] ⦃Y : Type u₂⦄ [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y]
    [IsComplexManifold k Y] ⦃F : X → Y⦄,
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞ F →
    ∀ ⦃A : Set X⦄, IsComplexAnalyticSubset (n := n) A → DimLE (n := n) A m → ProperOn F A →
      IsComplexAnalyticSubset (n := k) (F '' A)

/-- **`(RS_m)`** (with `q = p + 1`): if `B` is analytic with all regular points of dimension `< q`
and `E ⊆ Y \ B` is analytic in `Y \ B`, of dimension `≤ m`, with `dim_y E ≥ q` at all its points,
then `closure E` is analytic (for manifolds `Y : Type u₂`). -/
def RemmertSteinStatement (m : ℕ) : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃Y : Type u₂⦄ [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y]
    [IsComplexManifold k Y] ⦃B E : Set Y⦄ ⦃q : ℕ⦄,
    IsComplexAnalyticSubset (n := k) B → (∀ y j, RegularAtDim (n := k) B y j → j < q) →
    Disjoint E B → (∀ y, y ∉ B → Nonempty (ComplexAnalyticPresentationAt (n := k) E y)) →
    DimLE (n := k) E m → (∀ y ∈ E, LocDimGE (n := k) E y q) →
    IsComplexAnalyticSubset (n := k) (closure E)

section Presentations

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]
  [IsComplexManifold m Z]

/-- **Pointwise pull-back of a presentation.**  If `g` is holomorphic on an open `O ∋ z` and `S`
agrees with `g⁻¹(A)` on `O`, a presentation of `A` at `g z` gives one of `S` at `z`. -/
theorem nonempty_presentation_comp {g : Z → M} {z : Z} {O : Set Z} (hO : IsOpen O) (hzO : z ∈ O)
    (hg : ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g O) {A : Set M}
    (P : ComplexAnalyticPresentationAt (n := n) A (g z)) {S : Set Z}
    (hS : ∀ y ∈ O, y ∈ S ↔ g y ∈ A) : Nonempty (ComplexAnalyticPresentationAt (n := m) S z) := by
  set e := (complexChartAt (n := m) z).val with he
  set e' := (complexChartAt (n := n) (g z)).val with he'
  have hzs : z ∈ e.source := mem_complexChartAt_source z
  have hgzs : g z ∈ e'.source := mem_complexChartAt_source (g z)
  let U : Set (ComplexModel m) :=
    {w | w ∈ e.target ∧ e.symm w ∈ O ∧ g (e.symm w) ∈ e'.source ∧
      e' (g (e.symm w)) ∈ P.coordinateNeighborhood}
  have hgc : ContinuousOn (fun w => g (e.symm w)) (e.target ∩ e.symm ⁻¹' O) :=
    hg.continuousOn.comp (e.continuousOn_symm.mono inter_subset_left) fun w hw => hw.2
  have hUo : IsOpen U := by
    have h1 : IsOpen (e.target ∩ e.symm ⁻¹' O) :=
      e.continuousOn_symm.isOpen_inter_preimage e.open_target hO
    have := hgc.isOpen_inter_preimage h1
      (e'.isOpen_inter_preimage P.isOpen_coordinateNeighborhood)
    convert this using 1
    ext w
    simp only [U, mem_ofPred_eq, mem_inter_iff, mem_preimage]
    tauto
  have hdiff : ∀ w ∈ U, DifferentiableAt ℂ (fun v => e' (g (e.symm v))) w := by
    intro w hw
    have hws : e.symm w ∈ e.source := e.map_target hw.1
    have hgw : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g (e.symm w) :=
      hg.contMDiffAt (hO.mem_nhds hw.2.1)
    have h1 := (contMDiffAt_iff_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel m)) (n := ∞) z)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (g z))
      hws hw.2.2.1).mp hgw
    have h2 := h1.2
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id,
      contDiffWithinAt_univ] at h2
    have h3 : ContDiffAt ℂ ∞ (fun v => e' (g (e.symm v))) (e (e.symm w)) := h2
    rw [e.right_inv hw.1] at h3
    exact h3.differentiableAt (by simp)
  refine ⟨{ generatorCount := P.generatorCount
            generator := fun i w => P.generator i (e' (g (e.symm w)))
            coordinateNeighborhood := U
            isOpen_coordinateNeighborhood := hUo
            center_mem_coordinateNeighborhood := ?_
            coordinateNeighborhood_subset_target := fun _ hw => hw.1
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · refine ⟨e.map_source hzs, ?_, ?_, ?_⟩
    · rw [e.left_inv hzs]; exact hzO
    · rw [e.left_inv hzs]; exact hgzs
    · rw [e.left_inv hzs]; exact P.center_mem_coordinateNeighborhood
  · intro i w hw
    exact (((P.generator_holomorphic i).differentiableAt
      (P.isOpen_coordinateNeighborhood.mem_nhds hw.2.2.2)).comp w
      (hdiff w hw)).differentiableWithinAt
  · intro y hy hyU
    change y ∈ e.source at hy
    have hyU' : e y ∈ U := hyU
    have hinv : e.symm (e y) = y := e.left_inv hy
    simp only [U, mem_ofPred_eq, hinv] at hyU'
    change y ∈ S ↔ ∀ i, P.generator i (e' (g (e.symm (e y)))) = 0
    rw [hinv, hS y hyU'.2.1, P.zeroLocus hyU'.2.2.1 hyU'.2.2.2]

/-- **Presentations are local**: if `S` agrees with `A` on an open neighbourhood of `x`, a
presentation of `A` at `x` gives one of `S`. -/
theorem nonempty_presentation_of_inter_eq {A S : Set M} {x : M} {O : Set M} (hO : IsOpen O)
    (hxO : x ∈ O) (hSA : S ∩ O = A ∩ O) (P : ComplexAnalyticPresentationAt (n := n) A x) :
    Nonempty (ComplexAnalyticPresentationAt (n := n) S x) :=
  nonempty_presentation_comp (g := id) hO hxO contMDiffOn_id P fun y hy => by
    have := congrArg (y ∈ ·) hSA
    simp only [mem_inter_iff, eq_iff_iff] at this
    simpa [hy] using this

/-- A set with a presentation at every point of an open set `U` is analytic in `U`. -/
theorem isComplexAnalyticSubset_preimage_val_of_forall {A : Set M} {U : Opens M}
    (h : ∀ x ∈ U, Nonempty (ComplexAnalyticPresentationAt (n := n) A x)) :
    IsComplexAnalyticSubset (n := n) ((↑) ⁻¹' A : Set U) :=
  fun x => ⟨presentationPreimageVal x (h x x.2).some⟩

/-- A set analytic in an open set `U` has a presentation in `M` at every point of `U`. -/
theorem nonempty_presentation_of_preimage_val {A : Set M} {U : Opens M}
    (h : IsComplexAnalyticSubset (n := n) ((↑) ⁻¹' A : Set U)) {x : M} (hx : x ∈ U) :
    Nonempty (ComplexAnalyticPresentationAt (n := n) A x) :=
  ⟨presentationOfPreimageVal (⟨x, hx⟩ : U) (h ⟨x, hx⟩).some⟩

/-- A set with a presentation at each point of an open set `U` is closed in `U`: its closure meets
`U` only in the set itself. -/
theorem closure_inter_subset_of_forall {A : Set M} {U : Set M} (hU : IsOpen U)
    (h : ∀ x ∈ U, Nonempty (ComplexAnalyticPresentationAt (n := n) A x)) :
    closure A ∩ U ⊆ A := by
  rintro x ⟨hxc, hxU⟩
  have hana := isComplexAnalyticSubset_preimage_val_of_forall (U := ⟨U, hU⟩) h
  have hcl := hana.isClosed
  by_contra hxA
  have hopen : IsOpen ((↑) ⁻¹' A : Set (⟨U, hU⟩ : Opens M))ᶜ := hcl.isOpen_compl
  obtain ⟨V, hVo, hVeq⟩ := isOpen_induced_iff.mp hopen
  have hxV : x ∈ V := by
    have : (⟨x, hxU⟩ : (⟨U, hU⟩ : Opens M)) ∈ ((↑) ⁻¹' A : Set (⟨U, hU⟩ : Opens M))ᶜ := hxA
    rw [← hVeq] at this
    exact this
  obtain ⟨y, ⟨hyV, hyU⟩, hyA⟩ := mem_closure_iff.mp hxc (V ∩ U) (hVo.inter hU) ⟨hxV, hxU⟩
  have : (⟨y, hyU⟩ : (⟨U, hU⟩ : Opens M)) ∈ ((↑) ⁻¹' A : Set (⟨U, hU⟩ : Opens M))ᶜ := by
    rw [← hVeq]
    exact hyV
  exact this hyA

end Presentations

end Hironaka.RemmertStatements
