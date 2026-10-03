/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.ExceptionalLocus
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.NormalCrossingsInvariance
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Resolution.StrictTransformComposition
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Calculus of admissible blowup sequences (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), (1.1)--(1.2) and Theorem 1.6 (admissible
sequences, the accumulated exceptional divisor, the strict transform); Kollár 2007 (`kollar07-resolution`),
"Principalization III" (the initial divisor is carried along by strict transforms).

Let `f : Y → X` be an admissible blowup sequence of `(X, E₀)` with centres over a set `F`
(`HironakaAdmissibleSequence.IsAdmissibleBlowupSequence`), with accumulated divisor `E`, the members of `E₀` being closed.

* **Composition** (`IsAdmissibleBlowupSequence.comp`): an admissible sequence of `(Y, E)` with centres over `f⁻¹ F` composes with
  `f` to an admissible sequence of `(X, E₀)` with centres over `F`.
* **The accumulated divisor** (`IsAdmissibleBlowupSequence.exists_decomposition`): `E = E₀.map T ++ N`, where `T H` (the
  iterated strict transform of a member) is closed, lies in `f⁻¹ H`, and agrees with `f⁻¹ H` at every point not over `F`; the
  new members `N` are closed and lie over `F`; `f⁻¹ H ⊆ T H ∪ ⋃ N`; and `Exc f ⊆ ⋃ N`.  Hence `f` is an isomorphism over `X \ F`
  (`isIsomorphismOver_compl`) and `⋃ E ⊆ f⁻¹(⋃ E₀ ∪ F)`.
* **Away from the centres** (`hasNormalCrossings_preimage_of_disjoint`, `regularAtDim_preimage_of_disjoint`,
  `strictTransform_eq_preimage_of_disjoint`): for a closed `S` disjoint from a closed `F`, the strict transform of `S` is
  `f⁻¹ S`, it keeps the regular points of `S` with their dimensions, and normal crossings of `S` with `E₀` become normal
  crossings of `f⁻¹ S` with `E`.
* **Strict transforms of analytic sets** (`isComplexAnalyticSubset_strictTransform`, `isCompact_strictTransform`,
  `diff_regularLocus_strictTransform_subset`, `strictTransform_subset_closure_diff`): along any blowup sequence the strict
  transform of an analytic set is analytic, compact if the set is, and over the locus where `f` is an isomorphism it keeps the
  regular points of the set and their density.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaAdmissibleCalculus

open Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.HironakaAdmissibleSequence

noncomputable section

variable {n : ℕ}

/-! ### Blowup sequences: properness and strict transforms -/

section Sequence

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **A blowup sequence is a proper map.** -/
theorem isProperMap_of_isBlowupSequence {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {f : Y → X} (hf : IsBlowupSequence n X Y f) : IsProperMap f := by
  induction hf with
  | refl => exact isProperMap_id
  | step f C g _ hg ih => exact ih.comp (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hg)

/-- **The strict transform of an analytic set along a blowup sequence is analytic.** -/
theorem isComplexAnalyticSubset_strictTransform {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {f : Y → X} (hf : IsBlowupSequence n X Y f) {A : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) : IsComplexAnalyticSubset (n := n) (strictTransform n f A) := by
  induction hf with
  | refl =>
      have : strictTransform n (id : X → X) A = A := by
        rw [strictTransform, exceptionalLocus_id, sdiff_empty, preimage_id]
        exact hA.isClosed.closure_eq
      rw [this]
      exact hA
  | step f C g hf' hg ih =>
      rw [StrictTransformComposition.strictTransform_comp hf'.contMDiff hg.contMDiff]
      exact HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hg ih

/-- The strict transform of a closed set lies in its preimage. -/
theorem strictTransform_subset_preimage {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    {f : Y → X} (hf : Continuous f) {A : Set X} (hA : IsClosed A) : strictTransform n f A ⊆ f ⁻¹' A :=
  closure_minimal sdiff_subset (hA.preimage hf)

/-- **The strict transform of a compact set along a blowup sequence is compact.** -/
theorem isCompact_strictTransform {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {f : Y → X} (hf : IsBlowupSequence n X Y f) {A : Set X} (hA : IsCompact A) :
    IsCompact (strictTransform n f A) :=
  ((isProperMap_of_isBlowupSequence hf).isCompact_preimage hA).of_isClosed_subset isClosed_closure
    (strictTransform_subset_preimage hf.contMDiff.continuous hA.isClosed)

/-- The strict transform of the empty set is empty. -/
@[simp] theorem strictTransform_empty {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] (f : Y → X) :
    strictTransform n f (∅ : Set X) = ∅ := by
  simp [strictTransform]

/-- The strict transform is monotone. -/
theorem strictTransform_mono {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] (f : Y → X)
    {A B : Set X} (hAB : A ⊆ B) : strictTransform n f A ⊆ strictTransform n f B :=
  closure_mono (sdiff_subset_sdiff_left (preimage_mono hAB))

end Sequence

/-! ### Strict transforms over the locus where the map is an isomorphism -/

section Transport

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Off the exceptional locus the strict transform of a closed set is its preimage. -/
theorem mem_strictTransform_iff_of_notMem {f : Y → X} (hf : Continuous f) {A : Set X} (hA : IsClosed A) {u : Y}
    (hu : u ∉ exceptionalLocus n f) : u ∈ strictTransform n f A ↔ f u ∈ A :=
  ⟨fun h => strictTransform_subset_preimage hf hA h, fun h => subset_closure ⟨h, hu⟩⟩

/-- **Regular points survive over the isomorphism locus**: if `Exc f ⊆ f⁻¹ F` and `A` is regular of dimension `d` at each of
its points off `F`, then so is the strict transform of `A` at each of its points not over `F`. -/
theorem diff_regularLocus_strictTransform_subset {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {F : Set X}
    (hexc : exceptionalLocus n f ⊆ f ⁻¹' F) {A : Set X} (hA : IsClosed A) {d : ℕ}
    (hAF : A \ regularLocus (n := n) A d ⊆ F) :
    strictTransform n f A \ regularLocus (n := n) (strictTransform n f A) d ⊆ f ⁻¹' F := by
  rintro z ⟨hzS, hzreg⟩
  by_contra hzF
  have hzE : z ∉ exceptionalLocus n f := fun h => hzF (hexc h)
  have hO : IsOpen (exceptionalLocus n f)ᶜ := StrictTransformComposition.isOpen_compl_exceptionalLocus hf
  have hzA : f z ∈ A := strictTransform_subset_preimage hf.continuous hA hzS
  have hreg : RegularAtDim (n := n) A (f z) d := by
    by_contra h
    exact hzF (hAF ⟨hzA, h⟩)
  exact hzreg (RegularAtDimTransport.regularAtDim_of_preimage hf hzE hO hzE
    (fun u hu => mem_strictTransform_iff_of_notMem hf.continuous hA hu) hreg)

/-- **Density survives**: if no nonempty relatively open subset of `A` lies in `F`, then no nonempty relatively open subset of
the strict transform of `A` lies over `F` (`f` is open off its exceptional locus). -/
theorem strictTransform_subset_closure_diff {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {A F : Set X} (hA : IsClosed A)
    (hAF : A ⊆ closure (A \ F)) :
    strictTransform n f A ⊆ closure (strictTransform n f A \ f ⁻¹' F) := by
  refine closure_minimal ?_ isClosed_closure
  rintro y ⟨hyA, hyE⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  have ht' : t ∩ (exceptionalLocus n f)ᶜ ∈ 𝓝 y :=
    inter_mem ht ((StrictTransformComposition.isOpen_compl_exceptionalLocus hf).mem_nhds hyE)
  have himg : f '' (t ∩ (exceptionalLocus n f)ᶜ) ∈ 𝓝 (f y) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hf hyE]
    exact image_mem_map ht'
  obtain ⟨_, ⟨w, ⟨hwt, hwE⟩, rfl⟩, hwA, hwF⟩ := mem_closure_iff_nhds.mp (hAF hyA) _ himg
  exact ⟨w, hwt, (mem_strictTransform_iff_of_notMem hf.continuous hA hwE).mpr hwA, hwF⟩

/-- **The strict transform of a closed set missing the centres is the preimage**: if `Exc f ⊆ f⁻¹ F` and `S` is closed and
disjoint from `F`, then the strict transform of `S` is `f⁻¹ S`. -/
theorem strictTransform_eq_preimage_of_disjoint {f : Y → X} (hf : Continuous f) {F : Set X}
    (hexc : exceptionalLocus n f ⊆ f ⁻¹' F) {S : Set X} (hS : IsClosed S) (hSF : Disjoint S F) :
    strictTransform n f S = f ⁻¹' S := by
  refine Subset.antisymm (strictTransform_subset_preimage hf hS) fun z hz => ?_
  have hzE : z ∉ exceptionalLocus n f := fun h => disjoint_left.mp hSF hz (hexc h)
  exact subset_closure ⟨hz, hzE⟩

/-- **Regular points of a set missing the centres pull back**: if `Exc f ⊆ f⁻¹ F` and `S` is disjoint from `F`, a regular
point of `S` of dimension `d` pulls back to regular points of `f⁻¹ S` of dimension `d`. -/
theorem regularAtDim_preimage_of_disjoint {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {F : Set X}
    (hexc : exceptionalLocus n f ⊆ f ⁻¹' F) {S : Set X} (hSF : Disjoint S F) {z : Y} {d : ℕ}
    (hz : RegularAtDim (n := n) S (f z) d) : RegularAtDim (n := n) (f ⁻¹' S) z d := by
  have hzE : z ∉ exceptionalLocus n f := fun h => disjoint_left.mp hSF hz.2.1 (hexc h)
  exact RegularAtDimTransport.regularAtDim_of_preimage hf hzE isOpen_univ (mem_univ z) (fun _ _ => Iff.rfl) hz

end Transport

/-! ### Admissible sequences -/

section Admissible

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {E₀ : List (Set X)} {F : Set X}

/-- **Composition of admissible sequences.** -/
theorem IsAdmissibleBlowupSequence.comp {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)} (hf : IsAdmissibleBlowupSequence n X E₀ F Y f E)
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {g : Z → Y}
    {E' : List (Set Z)} (hg : IsAdmissibleBlowupSequence n Y E (f ⁻¹' F) Z g E') :
    IsAdmissibleBlowupSequence n X E₀ F Z (f ∘ g) E' := by
  induction hg with
  | refl => exact hf
  | step g E' C π _ hπ hnc hC ih => exact IsAdmissibleBlowupSequence.step (f ∘ g) E' C π ih hπ hnc hC

/-- **The accumulated divisor of an admissible sequence** (members of `E₀` closed): `E = E₀.map T ++ N`, where for every closed
`H` the transform `T H` is closed, lies in `f⁻¹ H`, agrees with `f⁻¹ H` at the points not over `F`, and `f⁻¹ H ⊆ T H ∪ ⋃ N`;
the new members `N` are closed and lie over `F`; and the exceptional locus of `f` lies in `⋃ N`. -/
theorem IsAdmissibleBlowupSequence.exists_decomposition {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) :
    ∃ (T : Set X → Set Y) (N : List (Set Y)), E = E₀.map T ++ N ∧
      (∀ H : Set X, IsClosed H → IsClosed (T H) ∧ T H ⊆ f ⁻¹' H ∧ f ⁻¹' H ⊆ T H ∪ ⋃ N' ∈ N, N' ∧
        ∀ z, f z ∉ F → (z ∈ T H ↔ f z ∈ H)) ∧
      (∀ N' ∈ N, IsClosed N') ∧ (⋃ N' ∈ N, N') ⊆ f ⁻¹' F ∧ exceptionalLocus n f ⊆ ⋃ N' ∈ N, N' := by
  induction h with
  | refl =>
      refine ⟨id, [], by simp, fun H hH => ⟨hH, subset_rfl, by simp, fun z _ => Iff.rfl⟩, by simp, by simp, by simp⟩
  | step f E C π hf hπ hnc hCF ih =>
      obtain ⟨T, N, rfl, hT, hNcl, hNF, hexc⟩ := ih
      have hC : IsClosed C := hπ.1.1
      have hπc : Continuous π := hπ.contMDiff.continuous
      set tr : Set _ → Set _ := fun H => closure (π ⁻¹' (H \ C)) with htr
      have htr_sub : ∀ H, IsClosed H → tr H ⊆ π ⁻¹' H := fun H hH =>
        closure_minimal (fun z hz => hz.1) (hH.preimage hπc)
      have htr_mem : ∀ H z, π z ∈ H → π z ∉ C → z ∈ tr H := fun H z hz hzC => subset_closure ⟨hz, hzC⟩
      have hExcπ : exceptionalLocus n π ⊆ π ⁻¹' C := by
        intro z hz
        by_contra hzC
        exact disjoint_left.mp (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).2 hzC hz
      -- the preimage of the old new members lies in the new new members
      have hNpre : π ⁻¹' (⋃ N' ∈ N, N') ⊆ ⋃ N' ∈ N.map tr ++ [π ⁻¹' C], N' := by
        intro z hz
        obtain ⟨N₀, hN₀, hzN₀⟩ := mem_iUnion₂.mp hz
        by_cases hzC : π z ∈ C
        · exact mem_iUnion₂.mpr ⟨π ⁻¹' C, List.mem_append_right _ (List.mem_singleton_self _), hzC⟩
        · exact mem_iUnion₂.mpr ⟨tr N₀, List.mem_append_left _ (List.mem_map_of_mem hN₀), htr_mem N₀ z hzN₀ hzC⟩
      refine ⟨fun H => tr (T H), N.map tr ++ [π ⁻¹' C], ?_, fun H hH => ?_, ?_, ?_, ?_⟩
      · simp [List.map_append, List.map_map, Function.comp_def, htr]
      · obtain ⟨hTcl, hTsub, hTcov, hTiff⟩ := hT H hH
        refine ⟨isClosed_closure, (htr_sub _ hTcl).trans (preimage_mono hTsub), fun z hz => ?_, fun z hz => ?_⟩
        · by_cases hzC : π z ∈ C
          · exact Or.inr (mem_iUnion₂.mpr ⟨π ⁻¹' C, List.mem_append_right _ (List.mem_singleton_self _), hzC⟩)
          · rcases hTcov hz with h | h
            · exact Or.inl (htr_mem _ z h hzC)
            · exact Or.inr (hNpre h)
        · have hzC : π z ∉ C := fun h => hz (hCF h)
          constructor
          · intro h
            exact (hTiff (π z) hz).mp (htr_sub _ hTcl h)
          · intro h
            exact htr_mem _ z ((hTiff (π z) hz).mpr h) hzC
      · intro N' hN'
        rcases List.mem_append.mp hN' with h | h
        · obtain ⟨N₀, -, rfl⟩ := List.mem_map.mp h
          exact isClosed_closure
        · rw [List.mem_singleton.mp h]
          exact hC.preimage hπc
      · intro z hz
        obtain ⟨N', hN', hzN'⟩ := mem_iUnion₂.mp hz
        rcases List.mem_append.mp hN' with h | h
        · obtain ⟨N₀, hN₀, rfl⟩ := List.mem_map.mp h
          exact hNF (mem_iUnion₂.mpr ⟨N₀, hN₀, htr_sub N₀ (hNcl N₀ hN₀) hzN'⟩)
        · rw [List.mem_singleton.mp h] at hzN'
          exact hCF hzN'
      · rw [exceptionalLocus_comp (hf.isBlowupSequence.contMDiff.mdifferentiable (by simp))
          (hπ.contMDiff.mdifferentiable (by simp))]
        rintro z (hz | hz)
        · exact mem_iUnion₂.mpr ⟨π ⁻¹' C, List.mem_append_right _ (List.mem_singleton_self _), hExcπ hz⟩
        · exact hNpre (hexc hz)

/-- **The exceptional locus of an admissible sequence lies over the centres.** -/
theorem IsAdmissibleBlowupSequence.exceptionalLocus_subset {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) : exceptionalLocus n f ⊆ f ⁻¹' F := by
  obtain ⟨T, N, -, -, -, hNF, hexc⟩ := IsAdmissibleBlowupSequence.exists_decomposition h
  exact hexc.trans hNF

/-- **An admissible sequence with centres over `F` is an isomorphism over `X \ F`.** -/
theorem IsAdmissibleBlowupSequence.isIsomorphismOver_compl {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) : IsIsomorphismOver n f Fᶜ := by
  refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset h.isBlowupSequence ?_
  rintro x ⟨z, hz, rfl⟩
  exact IsAdmissibleBlowupSequence.exceptionalLocus_subset h hz

/-- **The new members of an admissible sequence** are the members after the first `|E₀|`: they contain the exceptional locus
and lie over the centres. -/
theorem IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) :
    exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧ (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' F := by
  obtain ⟨T, N, rfl, -, -, hNF, hexc⟩ := IsAdmissibleBlowupSequence.exists_decomposition h
  have hdrop : (E₀.map T ++ N).drop E₀.length = N := List.drop_left' (by simp)
  rw [hdrop]
  exact ⟨hexc, hNF⟩

/-- **The members of the accumulated divisor lie over the initial members or the centres.** -/
theorem IsAdmissibleBlowupSequence.biUnion_subset {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) (hE₀ : ∀ H ∈ E₀, IsClosed H) :
    (⋃ H ∈ E, H) ⊆ f ⁻¹' ((⋃ H ∈ E₀, H) ∪ F) := by
  obtain ⟨T, N, rfl, hT, -, hNF, -⟩ := IsAdmissibleBlowupSequence.exists_decomposition h
  intro z hz
  obtain ⟨H', hH', hzH'⟩ := mem_iUnion₂.mp hz
  rcases List.mem_append.mp hH' with h1 | h1
  · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp h1
    exact Or.inl (mem_iUnion₂.mpr ⟨H, hH, (hT H (hE₀ H hH)).2.1 hzH'⟩)
  · exact Or.inr (hNF (mem_iUnion₂.mpr ⟨H', h1, hzH'⟩))

/-- Adapted coordinates only constrain the members through the point: a family each of whose members through `x` is a member
of an adapted family (with the same index set) is adapted. -/
theorem isCoordinateFamilyAt_of_forall_mem {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {ι ι' : Type*} {A : ι → Set M} {S : ι → Finset (Fin n)} {x : M} (h : IsCoordinateFamilyAt n A S x)
    {A' : ι' → Set M} {S' : ι' → Finset (Fin n)} (hmem : ∀ i', x ∈ A' i' → ∃ i, A' i' = A i ∧ S' i' = S i) :
    IsCoordinateFamilyAt n A' S' x := by
  obtain ⟨Φ, h1, h2, h3⟩ := h
  refine ⟨Φ, h1, h2, fun i' hi' y hy hyΦ => ?_⟩
  obtain ⟨i, hA, hS⟩ := hmem i' hi'
  rw [hA, hS]
  rw [hA] at hi'
  exact h3 i hi' hy hyΦ

/-- **Normal crossings are carried along an admissible sequence away from its centres**: if `S` is disjoint from the closed set
`F` over which the centres lie and has only normal crossings with `E₀` (members closed), then `f⁻¹ S` has only normal crossings
with the accumulated divisor `E`. -/
theorem IsAdmissibleBlowupSequence.hasNormalCrossings_preimage_of_disjoint {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) (hE₀ : ∀ H ∈ E₀, IsClosed H) (hF : IsClosed F) {S : Set X}
    (hSF : Disjoint S F) (hS : HasNormalCrossings n S E₀) : HasNormalCrossings n (f ⁻¹' S) E := by
  classical
  obtain ⟨T, N, rfl, hT, -, hNF, hexc⟩ := IsAdmissibleBlowupSequence.exists_decomposition h
  have hfc : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f := h.isBlowupSequence.contMDiff
  intro z hz
  have hzF : f z ∉ F := fun h' => disjoint_left.mp hSF hz h'
  obtain ⟨S₀, S', hcoord, hcard⟩ := hS (f z) hz
  -- the members of `E` through points not over `F`
  have hget_lt : ∀ (i : Fin (E₀.map T ++ N).length) (hi : i.1 < E₀.length),
      (E₀.map T ++ N).get i = T (E₀.get ⟨i.1, hi⟩) := by
    intro i hi
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_left (by simpa using hi), List.getElem_map]
  have hget_ge : ∀ (i : Fin (E₀.map T ++ N).length), E₀.length ≤ i.1 → (E₀.map T ++ N).get i ∈ N := by
    intro i hi
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_right (by simpa using hi)]
    exact List.getElem_mem _
  -- the comparison family on `X`
  let A : Option (Fin (E₀.map T ++ N).length) → Set X := fun o =>
    o.elim S fun i => if hi : i.1 < E₀.length then E₀.get ⟨i.1, hi⟩ else ∅
  let SS : Option (Fin (E₀.map T ++ N).length) → Finset (Fin n) := fun o =>
    o.elim S₀ fun i => if hi : i.1 < E₀.length then S' ⟨i.1, hi⟩ else ∅
  have hA : IsCoordinateFamilyAt n A SS (f z) := by
    refine isCoordinateFamilyAt_of_forall_mem hcoord fun o ho => ?_
    rcases o with _ | i
    · exact ⟨none, rfl, rfl⟩
    · by_cases hi : i.1 < E₀.length
      · exact ⟨some ⟨i.1, hi⟩, by simp [A, hi], by simp [SS, hi]⟩
      · simp [A, hi] at ho
  set O : Set Y := f ⁻¹' Fᶜ with hO
  have hOo : IsOpen O := hF.isOpen_compl.preimage hfc.continuous
  have hzE : z ∉ exceptionalLocus n f := fun h' => hzF (hNF (hexc h'))
  have hAO : ∀ o, ∀ u ∈ O, u ∈ (o.elim (f ⁻¹' S) fun i => (E₀.map T ++ N).get i) ↔ f u ∈ A o := by
    rintro (_ | i) u hu
    · exact Iff.rfl
    · by_cases hi : i.1 < E₀.length
      · simp only [Option.elim, A, hi, dite_true]
        rw [hget_lt i hi]
        exact (hT _ (hE₀ _ (List.get_mem _ _))).2.2.2 u hu
      · simp only [Option.elim, A, hi, dite_false, mem_empty_iff_false, iff_false]
        intro hui
        exact hu (hNF (mem_iUnion₂.mpr ⟨_, hget_ge i (not_lt.mp hi), hui⟩))
  refine ⟨S₀, fun i => if hi : i.1 < E₀.length then S' ⟨i.1, hi⟩ else ∅,
    NormalCrossingsInvariance.isCoordinateFamilyAt_of_preimage hfc hzE hOo hzF hAO hA, fun i hi => ?_⟩
  by_cases hik : i.1 < E₀.length
  · simp only [hik, dite_true]
    rw [hget_lt i hik] at hi
    exact hcard _ (((hT _ (hE₀ _ (List.get_mem _ _))).2.2.2 z hzF).mp hi)
  · exact absurd (hNF (mem_iUnion₂.mpr ⟨_, hget_ge i (not_lt.mp hik), hi⟩)) hzF

end Admissible

end

end Hironaka.HironakaAdmissibleCalculus
