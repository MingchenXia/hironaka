/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaAdmissibleCalculus
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.ExceptionalLocus
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.NormalCrossingsInvariance
import Hironaka.Analytic.RegularAtDimTransport
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Base change of admissible blowup sequences along open holomorphic embeddings (Hironaka)

Sources: Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Theorem 1.3 and the paragraph after it (a
resolution sequence pulls back along an open embedding, trivial blowings-up being inserted); Włodarczyk 2005
(`wlodarczyk05-hironaka`), §2.4 (Proposition `pr:funct`, multiple test blow-ups pull back along étale maps, here
open embeddings).

**Open holomorphic embeddings.**  `IsOpenHoloEmbedding n ι` for `ι : B → A`: `ι` is a biholomorphism `Φ : B ≅ O` onto an open
subset `O ⊆ A` followed by the inclusion.  Examples: the inclusion of an open subset (`isOpenHoloEmbedding_val`), its
co-restriction to a larger open subset (`IsOpenHoloEmbedding.codRestrict`).  Such a map is holomorphic, an open embedding, and
has no exceptional points (`exceptionalLocus_eq_empty`, from `exceptionalLocus_val`: the inclusion of an open subset is the
identity in the preferred charts).

**Base change** (`IsAdmissibleBlowupSequence.exists_baseChange`).  Let `f : Y → A` be an admissible blowup sequence of
`(A, E₀)` with centres over `F` and divisor `E`, and `ι : B → A` an open holomorphic embedding.  There are an admissible blowup
sequence `f' : Y' → B` of `(B, ι⁻¹E₀)` with centres over `ι⁻¹F`, with divisor `j⁻¹E`, and an open holomorphic embedding
`j : Y' → Y` with `f ∘ j = ι ∘ f'` and `j(Y') = f⁻¹(ι(B))`.  By induction on the sequence: the empty sequence goes to the
empty sequence over `B` (`j = ι`); a blowup `π : Z → Y` along `C` is restricted to `π⁻¹(j(Y'))`
(`BlowupRestrictOpen.isBlowupAlong_restrict`) and composed with the inverse of `Φ : Y' ≅ j(Y')`
(`MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse`), a blowup along `j⁻¹C`.

**Transport** along a base change: `Exc f' = j⁻¹ Exc f` (`exceptionalLocus_eq_preimage`) and, for every `S ⊆ A`, the strict
transform of `ι⁻¹S` by `f'` is `j⁻¹` of the strict transform of `S` by `f` (`strictTransform_preimage_eq`); regular points,
normal crossings and simple normal crossings divisors pull back along open holomorphic embeddings
(`regularAtDim_preimage`, `hasNormalCrossings_preimage`, `isSNCDivisor_map_preimage`).  The case of the inclusion of an
open subset is `IsAdmissibleBlowupSequence.exists_restrict_opens` (restriction of an admissible sequence to an open subset).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaBaseChange

open Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.NormalCrossingsInvariance Hironaka.HironakaAdmissibleSequence Hironaka.HironakaAdmissibleCalculus

noncomputable section

variable {n : ℕ}

/-! ### The inclusion of an open subset -/

section Val

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The differential of the inclusion of an open subset is bijective**: in the preferred charts the inclusion is the
identity. -/
theorem mfderiv_val_bijective {U : Opens M} (y : U) :
    Function.Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (Subtype.val : U → M) y) := by
  have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (Subtype.val : U → M) y :=
    ((contMDiff_subtype_val (n := ∞)) y).mdifferentiableAt (by simp)
  rw [hd.mfderiv]
  have hne : Nonempty U := ⟨y⟩
  have heq : writtenInExtChartAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) y (Subtype.val : U → M)
      =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ComplexModel n) y) y)] id := by
    have ht : (chartAt (ComplexModel n) y).target ∈ 𝓝 ((extChartAt 𝓘(ℂ, ComplexModel n) y) y) := by
      simpa using (chartAt (ComplexModel n) y).open_target.mem_nhds (mem_chart_target (ComplexModel n) y)
    filter_upwards [ht] with z hz
    have hz' : z ∈ ((chartAt (ComplexModel n) (y : M)).subtypeRestr ⟨y⟩).target := by
      rwa [← TopologicalSpace.Opens.chartAt_eq]
    have h1 := (chartAt (ComplexModel n) (y : M)).subtypeRestr_symm_apply hne hz'
    have h2 : (chartAt (ComplexModel n) (y : M)) ((chartAt (ComplexModel n) (y : M)).symm z) = z :=
      (chartAt (ComplexModel n) (y : M)).right_inv
        ((chartAt (ComplexModel n) (y : M)).subtypeRestr_target_subset ⟨y⟩ hz')
    simp only [Function.comp_apply] at h1
    simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend, mfld_simps,
      TopologicalSpace.Opens.chartAt_eq]
    rw [h1, h2]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  rw [heq.fderiv_eq, fderiv_id]
  exact Function.bijective_id

/-- **The inclusion of an open subset has no exceptional points.** -/
theorem exceptionalLocus_val {U : Opens M} : exceptionalLocus n (Subtype.val : U → M) = ∅ :=
  eq_empty_of_forall_notMem fun y hy => hy (mfderiv_val_bijective y)

end Val

/-! ### Open holomorphic embeddings -/

section Embedding

variable {A B : Type u} [TopologicalSpace A] [ChartedSpace (ComplexModel n) A] [IsComplexManifold n A]
  [TopologicalSpace B] [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B]

variable (n) in
/-- **An open holomorphic embedding** `ι : B → A`: a biholomorphism `Φ : B ≅ O` onto an open subset `O ⊆ A`, followed by the
inclusion. -/
def IsOpenHoloEmbedding (ι : B → A) : Prop :=
  ∃ (O : Opens A) (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ O), ∀ b, ι b = (Φ b : A)

/-- **The inclusion of an open subset is an open holomorphic embedding.** -/
theorem isOpenHoloEmbedding_val (O : Opens A) : IsOpenHoloEmbedding n (Subtype.val : O → A) :=
  ⟨O, Diffeomorph.refl _ _ _, fun _ => rfl⟩

namespace IsOpenHoloEmbedding

variable {ι : B → A}

/-- An open holomorphic embedding is holomorphic. -/
theorem contMDiff (h : IsOpenHoloEmbedding n ι) : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ι := by
  obtain ⟨O, Φ, hΦ⟩ := h
  have : ι = Subtype.val ∘ Φ := funext hΦ
  rw [this]
  exact contMDiff_subtype_val.comp Φ.contMDiff

/-- **An open holomorphic embedding has no exceptional points.** -/
theorem exceptionalLocus_eq_empty (h : IsOpenHoloEmbedding n ι) : exceptionalLocus n ι = ∅ := by
  obtain ⟨O, Φ, hΦ⟩ := h
  have : ι = Subtype.val ∘ Φ := funext hΦ
  rw [this, exceptionalLocus_comp ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp))
    (Φ.contMDiff.mdifferentiable (by simp)), exceptionalLocus_val, preimage_empty, union_empty]
  exact eq_empty_of_forall_notMem (MarkedIdealTowerTransport.notMem_exceptionalLocus Φ)

theorem notMem_exceptionalLocus (h : IsOpenHoloEmbedding n ι) (b : B) : b ∉ exceptionalLocus n ι := by
  rw [h.exceptionalLocus_eq_empty]
  exact notMem_empty b

/-- An open holomorphic embedding is an open embedding. -/
theorem isOpenEmbedding (h : IsOpenHoloEmbedding n ι) : Topology.IsOpenEmbedding ι := by
  obtain ⟨O, Φ, hΦ⟩ := h
  have : ι = Subtype.val ∘ Φ := funext hΦ
  rw [this]
  exact O.isOpen.isOpenEmbedding_subtypeVal.comp Φ.toHomeomorph.isOpenEmbedding

theorem continuous (h : IsOpenHoloEmbedding n ι) : Continuous ι := h.contMDiff.continuous

theorem isOpenMap (h : IsOpenHoloEmbedding n ι) : IsOpenMap ι := h.isOpenEmbedding.isOpenMap

/-- **Closures pull back** along an open holomorphic embedding. -/
theorem preimage_closure (h : IsOpenHoloEmbedding n ι) (S : Set A) : ι ⁻¹' closure S = closure (ι ⁻¹' S) :=
  h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous S

/-- An open holomorphic embedding pulls back adapted coordinates. -/
theorem pullsBackCoordinates (h : IsOpenHoloEmbedding n ι) : PullsBackCoordinates n ι :=
  pullsBackCoordinates_of_forall_notMem_exceptionalLocus h.contMDiff h.notMem_exceptionalLocus

/-- **Regular points pull back** along an open holomorphic embedding. -/
theorem regularAtDim_preimage (h : IsOpenHoloEmbedding n ι) {S : Set A} {b : B} {d : ℕ}
    (hS : RegularAtDim (n := n) S (ι b) d) : RegularAtDim (n := n) (ι ⁻¹' S) b d :=
  RegularAtDimTransport.regularAtDim_of_preimage h.contMDiff (h.notMem_exceptionalLocus b) isOpen_univ (mem_univ b)
    (fun _ _ => Iff.rfl) hS

/-- **Normal crossings pull back** along an open holomorphic embedding. -/
theorem hasNormalCrossings_preimage (h : IsOpenHoloEmbedding n ι) {C : Set A} {E : List (Set A)}
    (hC : HasNormalCrossings n C E) : HasNormalCrossings n (ι ⁻¹' C) (E.map (ι ⁻¹' ·)) :=
  NormalCrossingsInvariance.hasNormalCrossings_preimage h.pullsBackCoordinates hC

/-- **Simple normal crossings divisors pull back** along an open holomorphic embedding. -/
theorem isSNCDivisor_map_preimage (h : IsOpenHoloEmbedding n ι) {E : List (Set A)} (hE : IsSNCDivisor n E) :
    IsSNCDivisor n (E.map (ι ⁻¹' ·)) :=
  NormalCrossingsInvariance.isSNCDivisor_map_preimage h.pullsBackCoordinates h.continuous hE

/-- **Co-restriction to an open subset containing the image** is an open holomorphic embedding. -/
theorem codRestrict (h : IsOpenHoloEmbedding n ι) (U : Opens A) (hU : ∀ b, ι b ∈ U) :
    IsOpenHoloEmbedding n (fun b => (⟨ι b, hU b⟩ : U)) := by
  obtain ⟨O, Φ, hΦ⟩ := h
  let O' : Opens U := ⟨Subtype.val ⁻¹' (O : Set A), O.isOpen.preimage continuous_subtype_val⟩
  have hOU : ∀ p : O, (p : A) ∈ U := fun p => by
    have h := hU (Φ.symm p)
    rwa [hΦ, Φ.apply_symm_apply] at h
  let Ψ : O ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ O' :=
    { toFun := fun p => ⟨⟨p.1, hOU p⟩, p.2⟩
      invFun := fun q => ⟨q.1.1, q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
        (BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val hOU) fun p => p.2
      contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
        (contMDiff_subtype_val.comp contMDiff_subtype_val) fun q => q.2 }
  refine ⟨O', Φ.trans Ψ, fun b => Subtype.ext ?_⟩
  simp only [Diffeomorph.coe_trans, Function.comp_apply]
  exact hΦ b

end IsOpenHoloEmbedding

end Embedding

/-! ### Base change of an admissible blowup sequence -/

section BaseChange

variable {A : Type u} [TopologicalSpace A] [ChartedSpace (ComplexModel n) A] [IsComplexManifold n A]
  {B : Type u} [TopologicalSpace B] [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B]

/-- **Base change of an admissible blowup sequence along an open holomorphic embedding** (`hir:base-change-open`): if
`f : Y → A` is an admissible blowup sequence of `(A, E₀)` with centres over `F` and divisor `E`, and `ι : B → A` is an open
holomorphic embedding, there are an admissible blowup sequence `f' : Y' → B` of `(B, ι⁻¹E₀)` with centres over `ι⁻¹F` and
divisor `j⁻¹E`, and an open holomorphic embedding `j : Y' → Y`, with `f ∘ j = ι ∘ f'` and `j(Y') = f⁻¹(ι(B))`. -/
theorem IsAdmissibleBlowupSequence.exists_baseChange {E₀ : List (Set A)} {F : Set A} {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → A} {E : List (Set Y)}
    (hf : IsAdmissibleBlowupSequence n A E₀ F Y f E) {ι : B → A} (hι : IsOpenHoloEmbedding n ι) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y') (_ : IsComplexManifold n Y')
      (f' : Y' → B) (j : Y' → Y),
      IsAdmissibleBlowupSequence n B (E₀.map (ι ⁻¹' ·)) (ι ⁻¹' F) Y' f' (E.map (j ⁻¹' ·)) ∧
      IsOpenHoloEmbedding n j ∧ (∀ y, f (j y) = ι (f' y)) ∧ range j = f ⁻¹' range ι := by
  induction hf with
  | refl =>
      exact ⟨B, inferInstance, inferInstance, inferInstance, id, ι, IsAdmissibleBlowupSequence.refl, hι,
        fun _ => rfl, by simp⟩
  | @step Y Z _ _ _ _ _ _ f E C π _ hπ hnc hCF ih =>
      obtain ⟨Y', i1, i2, i3, f', j, hadm', hj, hcomm, hrange⟩ := ih
      have hj' := hj
      obtain ⟨O, Φ, hΦ⟩ := hj'
      have hV : IsOpen (π ⁻¹' (O : Set Y)) := O.isOpen.preimage hπ.contMDiff.continuous
      set W : Opens Z := ⟨π ⁻¹' (O : Set Y), hV⟩ with hWdef
      set r : W → O := fun p => (⟨π p.1, p.2⟩ : O) with hrdef
      have hres : IsBlowupAlong n ((↑) ⁻¹' C : Set O) r := BlowupRestrictOpen.isBlowupAlong_restrict hπ O hV
      set σ : W → Y' := Φ.symm ∘ r with hσdef
      have hσ : IsBlowupAlong n (Φ ⁻¹' ((↑) ⁻¹' C : Set O)) σ :=
        MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
          Φ.symm_apply_apply hres
      have hjpre : ∀ S : Set Y, j ⁻¹' S = Φ ⁻¹' ((↑) ⁻¹' S : Set O) := fun S => by
        ext y
        simp [hΦ]
      have hjσ : ∀ p : W, j (σ p) = π p.1 := fun p => by
        rw [hΦ]
        simp [hσdef, hrdef]
      have hσpre : ∀ S : Set Y, σ ⁻¹' (j ⁻¹' S) = (Subtype.val : W → Z) ⁻¹' (π ⁻¹' S) := fun S => by
        ext p
        simp only [mem_preimage, hjσ]
      have hnc' : HasNormalCrossings n (Φ ⁻¹' ((↑) ⁻¹' C : Set O)) (E.map (j ⁻¹' ·)) := by
        rw [← hjpre]
        exact hj.hasNormalCrossings_preimage hnc
      have hCF' : Φ ⁻¹' ((↑) ⁻¹' C : Set O) ⊆ f' ⁻¹' (ι ⁻¹' F) := by
        rw [← hjpre]
        intro y hy
        have := hCF hy
        simp only [mem_preimage] at this ⊢
        rw [← hcomm]
        exact this
      have hstep := IsAdmissibleBlowupSequence.step f' (E.map (j ⁻¹' ·)) _ σ hadm' hσ hnc' hCF'
      have hlist : (E.map (j ⁻¹' ·)).map (fun H => closure (σ ⁻¹' (H \ Φ ⁻¹' ((↑) ⁻¹' C : Set O)))) ++
          [σ ⁻¹' (Φ ⁻¹' ((↑) ⁻¹' C : Set O))] =
          (E.map (fun H => closure (π ⁻¹' (H \ C))) ++ [π ⁻¹' C]).map ((Subtype.val : W → Z) ⁻¹' ·) := by
        rw [← hjpre, List.map_append, List.map_map, List.map_map, List.map_singleton, hσpre]
        congr 1
        refine List.map_congr_left fun H _ => ?_
        simp only [Function.comp_apply]
        rw [← preimage_sdiff, hσpre, (isOpenHoloEmbedding_val (n := n) W).preimage_closure]
      rw [hlist] at hstep
      refine ⟨W, inferInstance, inferInstance, inferInstance, f' ∘ σ, Subtype.val, hstep, isOpenHoloEmbedding_val W,
        fun p => ?_, ?_⟩
      · simp only [Function.comp_apply, ← hjσ, hcomm]
      · rw [Subtype.range_coe, preimage_comp, ← hrange]
        show π ⁻¹' (O : Set Y) = π ⁻¹' range j
        congr 1
        ext y
        constructor
        · intro hy
          exact ⟨Φ.symm ⟨y, hy⟩, by rw [hΦ, Φ.apply_symm_apply]⟩
        · rintro ⟨y', rfl⟩
          rw [hΦ]
          exact (Φ y').2

/-! ### Transport along a base change -/

variable {Y Y' : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Y'] [ChartedSpace (ComplexModel n) Y'] [IsComplexManifold n Y']
  {f : Y → A} {f' : Y' → B} {ι : B → A} {j : Y' → Y}

/-- **The exceptional locus of a base change** is the preimage of the exceptional locus: `Exc f' = j⁻¹ Exc f` when
`f ∘ j = ι ∘ f'` with `ι`, `j` open holomorphic embeddings. -/
theorem exceptionalLocus_eq_preimage (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hf' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f') (hι : IsOpenHoloEmbedding n ι)
    (hj : IsOpenHoloEmbedding n j) (hcomm : ∀ y, f (j y) = ι (f' y)) :
    exceptionalLocus n f' = j ⁻¹' exceptionalLocus n f := by
  have h1 := exceptionalLocus_comp (hf.mdifferentiable (by simp)) (hj.contMDiff.mdifferentiable (by simp))
  have h2 := exceptionalLocus_comp (hι.contMDiff.mdifferentiable (by simp)) (hf'.mdifferentiable (by simp))
  have heq : f ∘ j = ι ∘ f' := funext hcomm
  rw [heq, h2, hι.exceptionalLocus_eq_empty, preimage_empty, union_empty, hj.exceptionalLocus_eq_empty,
    empty_union] at h1
  exact h1

/-- **The strict transform of a base change**: the strict transform of `ι⁻¹S` by `f'` is `j⁻¹` of the strict transform of
`S` by `f`. -/
theorem strictTransform_preimage_eq (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hf' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f') (hι : IsOpenHoloEmbedding n ι)
    (hj : IsOpenHoloEmbedding n j) (hcomm : ∀ y, f (j y) = ι (f' y)) (S : Set A) :
    strictTransform n f' (ι ⁻¹' S) = j ⁻¹' strictTransform n f S := by
  rw [strictTransform, strictTransform, exceptionalLocus_eq_preimage hf hf' hι hj hcomm, hj.preimage_closure,
    preimage_sdiff]
  congr 2
  ext y
  simp [hcomm]

/-- **Restriction of an admissible blowup sequence to an open subset** (`hir:base-change-open`, the case of the inclusion):
if `f : Y → A` is an admissible blowup sequence of `(A, E₀)` with centres over `F` and divisor `E`, and `O ⊆ A` is open, there
are an admissible blowup sequence `f' : Y' → O` of `(O, E₀|O)` with centres over `F ∩ O` and divisor `j⁻¹E`, and a holomorphic
open embedding `j : Y' → Y` without exceptional points onto `f⁻¹(O)`, with `f ∘ j = f'` (as maps to `A`), `Exc f' = j⁻¹ Exc f`,
and, for every `S ⊆ A`, the strict transform of `S ∩ O` by `f'` is `j⁻¹` of the strict transform of `S` by `f`. -/
theorem IsAdmissibleBlowupSequence.exists_restrict_opens {E₀ : List (Set A)} {F : Set A} {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → A} {E : List (Set Y)}
    (hf : IsAdmissibleBlowupSequence n A E₀ F Y f E) (O : Opens A) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y') (_ : IsComplexManifold n Y')
      (f' : Y' → O) (j : Y' → Y),
      IsAdmissibleBlowupSequence n O (E₀.map ((Subtype.val : O → A) ⁻¹' ·)) ((Subtype.val : O → A) ⁻¹' F) Y' f'
        (E.map (j ⁻¹' ·)) ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ j ∧ Topology.IsOpenEmbedding j ∧
      exceptionalLocus n j = ∅ ∧ (∀ y, f (j y) = f' y) ∧ range j = f ⁻¹' O ∧
      exceptionalLocus n f' = j ⁻¹' exceptionalLocus n f ∧
      ∀ S : Set A, strictTransform n f' ((Subtype.val : O → A) ⁻¹' S) = j ⁻¹' strictTransform n f S := by
  have hval := isOpenHoloEmbedding_val (n := n) O
  obtain ⟨Y', i1, i2, i3, f', j, hadm, hj, hcomm, hrange⟩ := IsAdmissibleBlowupSequence.exists_baseChange hf hval
  have hfc := hf.isBlowupSequence.contMDiff
  have hf'c := hadm.isBlowupSequence.contMDiff
  refine ⟨Y', i1, i2, i3, f', j, hadm, hj.contMDiff, hj.isOpenEmbedding, hj.exceptionalLocus_eq_empty, hcomm, ?_,
    exceptionalLocus_eq_preimage hfc hf'c hval hj hcomm, strictTransform_preimage_eq hfc hf'c hval hj hcomm⟩
  rw [hrange, Subtype.range_coe]

end BaseChange

end

end Hironaka.HironakaBaseChange
