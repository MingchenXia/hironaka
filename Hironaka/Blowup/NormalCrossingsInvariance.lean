/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.LocalHolomorphicInverse
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Normal crossings pull back along local biholomorphisms and open inclusions

Sources: Włodarczyk 2005 §2.4 (functoriality of the resolution under étale maps; here biholomorphisms and open
embeddings, the clauses (2)--(3) of `hir:canonical-resolution`), Bierstone--Milman 2008 Theorem 1.3 (functoriality).

The three normal crossings notions of `Hironaka.NormalCrossings` (`IsSNCDivisor`, `HasNormalCrossings`,
`IsTransverse`) are all built from one local picture, adapted coordinates for a family at a point
(`IsCoordinateFamilyAt`).  This file shows that this picture pulls back

* along a holomorphic map `g` at every point `z` where its differential is bijective, when near `z`
  each member of the new family is the preimage of the corresponding old one
  (`isCoordinateFamilyAt_of_preimage`; the coordinates at `g z` are precomposed with the local
  holomorphic inverse of `g` read in preferred charts, as in `RegularAtDimTransport`);
* along the inclusion of an open subset, in both directions (`isCoordinateFamilyAt_preimage_val_iff`;
  the preferred chart of `U` at `x` is that of `M`, restricted),

and deduces, for every continuous `g` with that pointwise property (`PullsBackCoordinates`), that
preimages of simple normal crossings divisors are simple normal crossings divisors, and that normal
crossings and transversality pull back (`isSNCDivisor_map_preimage`, `hasNormalCrossings_preimage`,
`isTransverse_preimage`).  Instances: maps without exceptional points
(`pullsBackCoordinates_of_forall_notMem_exceptionalLocus`, e.g. biholomorphisms) and open inclusions
(`pullsBackCoordinates_val`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.NormalCrossingsInvariance

open Hironaka.BlowupSequences Hironaka.NormalCrossings Hironaka.AnalyticSubsetOpens

noncomputable section

variable {n : ℕ}

/-! ### Re-indexing -/

section Reindex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **Re-indexing a family with adapted coordinates.** -/
theorem IsCoordinateFamilyAt.reindex {ι ι' : Type*} {A : ι → Set M} {S : ι → Finset (Fin n)}
    {x : M} (h : IsCoordinateFamilyAt n A S x) (e : ι' → ι) {A' : ι' → Set M}
    {S' : ι' → Finset (Fin n)} (hA : ∀ i, A' i = A (e i)) (hS : ∀ i, S' i = S (e i)) :
    IsCoordinateFamilyAt n A' S' x := by
  obtain ⟨Φ, h1, h2, h3⟩ := h
  refine ⟨Φ, h1, h2, fun i hi y hy hyΦ => ?_⟩
  rw [hA, hS]
  rw [hA] at hi
  exact h3 (e i) hi hy hyΦ

end Reindex

/-! ### Along a local biholomorphism -/

section LocalBiholomorphism

variable {Y Z : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Adapted coordinates pull back along a local biholomorphism.**  If `g` is holomorphic with
bijective differential at `z`, and near `z` each `A' i` is the preimage of `A i`, then adapted
coordinates for `A` at `g z` give adapted coordinates for `A'` at `z`, with the same index sets. -/
theorem isCoordinateFamilyAt_of_preimage {ι : Type*} {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ BlowupSequences.exceptionalLocus n g) {A' : ι → Set Z} {A : ι → Set Y} {O : Set Z}
    (hO : IsOpen O) (hzO : z ∈ O) (hAO : ∀ i, ∀ u ∈ O, u ∈ A' i ↔ g u ∈ A i)
    {S : ι → Finset (Fin n)} (hA : IsCoordinateFamilyAt n A S (g z)) :
    IsCoordinateFamilyAt n A' S z := by
  obtain ⟨Φ, hΦt, hΦ0, hΦA⟩ := hA
  set I := 𝓘(ℂ, ComplexModel n) with hI
  have hrange : range I = univ := by simp [hI]
  set e := chartAt (ComplexModel n) z with he
  set e' := chartAt (ComplexModel n) (g z) with he'
  set F : ComplexModel n → ComplexModel n := fun u => e' (g (e.symm u)) with hF
  set N : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' (O ∩ g ⁻¹' e'.source) with hN
  have hNo : IsOpen N :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target
      (hO.inter (hg.continuous.isOpen_preimage _ e'.open_source))
  have hzN : e z ∈ N := ⟨e.map_source (mem_chart_source _ z), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ z)]
    exact ⟨hzO, mem_chart_source _ (g z)⟩⟩
  have hFN : DifferentiableOn ℂ F N := by
    have h := (contMDiffOn_iff.mp (hg.contMDiffOn (s := univ))).2 z (g z)
    refine (h.differentiableOn (by simp)).mono ?_
    intro u hu
    exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _, hu.2.2, mem_univ _⟩
  have hmd : MDifferentiableAt I I g z := (hg z).mdifferentiableAt (by simp)
  have hderiv : mfderiv I I g z = fderiv ℂ F (e z) := by
    rw [hmd.mfderiv, hrange, fderivWithin_univ]
    rfl
  have hinj : Function.Injective (fderiv ℂ F (e z)) := by
    have := hz
    simp only [exceptionalLocus, mem_ofPred_eq, not_not] at this
    rw [hderiv] at this
    exact this.1
  obtain ⟨Ψ, hΨN, hΨF, -⟩ := exists_localHolomorphicEquivAt hNo hzN hFN hinj
  have hFz : F (e z) = e' (g z) := by
    simp only [hF, e.left_inv (mem_chart_source _ z)]
  refine ⟨RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ψ Φ (hΨF ▸ hFz), ?_, ?_, ?_⟩
  · intro u hu
    exact (hΨN hu.1).1
  · change Φ.toFun (Ψ.toFun (e z)) = 0
    rw [hΨF, hFz]
    exact hΦ0
  · intro i hzi y hy hyΘ
    change e y ∈ Ψ.source ∩ Ψ.toFun ⁻¹' Φ.source at hyΘ
    change y ∈ A' i ↔ Φ.toFun (Ψ.toFun (e y)) ∈ coordSubspace (S i)
    have hyN := (hΨN hyΘ.1).2
    rw [mem_preimage, e.left_inv hy] at hyN
    have hFy : F (e y) = e' (g y) := by simp only [hF, e.left_inv hy]
    have hyΦ : e' (g y) ∈ Φ.source := by
      have := hyΘ.2
      rwa [mem_preimage, hΨF, hFy] at this
    rw [hAO i y hyN.1, hΨF, hFy]
    exact hΦA i ((hAO i z hzO).mp hzi) hyN.2 hyΦ

end LocalBiholomorphism

/-! ### Along the inclusion of an open subset -/

section Opens

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {U : Opens M}

/-- **Adapted coordinates on an open subset**: `x ∈ U` has adapted coordinates for the traces
`A i ∩ U` (in `U`) iff it has adapted coordinates for the `A i` (in `M`), with the same index
sets. -/
theorem isCoordinateFamilyAt_preimage_val_iff {ι : Type*} {A : ι → Set M}
    {S : ι → Finset (Fin n)} {x : U} :
    IsCoordinateFamilyAt n (fun i => ((↑) ⁻¹' A i : Set U)) S x ↔
      IsCoordinateFamilyAt n A S (x : M) := by
  constructor
  · rintro ⟨Φ, hΦt, hΦ0, hΦA⟩
    refine ⟨Φ, hΦt.trans (chartAt_opens_target_subset x), hΦ0, ?_⟩
    intro i hxi y hy hyΦ
    have hyU : y ∈ U := mem_opens_of_chart_mem_target hy (hΦt hyΦ)
    exact hΦA i hxi (y := ⟨y, hyU⟩) (mem_chartAt_opens_source.mpr hy) hyΦ
  · rintro ⟨Φ, hΦt, hΦ0, hΦA⟩
    set S' := (chartAt (ComplexModel n) x).target with hS'
    have hxS : chartAt (ComplexModel n) (x : M) x ∈ Φ.source ∩ S' :=
      ⟨Φ.center_mem_source, (chartAt (ComplexModel n) x).map_source
        (mem_chart_source (ComplexModel n) x)⟩
    refine ⟨Φ.restrict S' (isOpen_chartAt_opens_target x) _ hxS, inter_subset_right, hΦ0, ?_⟩
    intro i hxi y hy hyΦ
    exact hΦA i hxi (y := (y : M)) (mem_chartAt_opens_source.mp hy) hyΦ.1

end Opens

/-! ### Families pull back -/

section Pullback

variable {Y Z : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]

variable (n) in
/-- **`g` pulls back adapted coordinates**: adapted coordinates for a family at `g z` give adapted
coordinates, with the same index sets, for the preimages at `z`. -/
def PullsBackCoordinates (g : Z → Y) : Prop :=
  ∀ {ι : Type} (A : ι → Set Y) (S : ι → Finset (Fin n)) (z : Z),
    IsCoordinateFamilyAt n A S (g z) → IsCoordinateFamilyAt n (fun i => g ⁻¹' A i) S z

/-- Maps without exceptional points pull back adapted coordinates (e.g. biholomorphisms). -/
theorem pullsBackCoordinates_of_forall_notMem_exceptionalLocus [IsComplexManifold n Y]
    [IsComplexManifold n Z] {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hexc : ∀ z, z ∉ exceptionalLocus n g) : PullsBackCoordinates n g :=
  fun _ _ z h => isCoordinateFamilyAt_of_preimage hg (hexc z) isOpen_univ (mem_univ z)
    (fun _ _ _ => Iff.rfl) h

/-- **Open inclusions pull back adapted coordinates.** -/
theorem pullsBackCoordinates_val [IsComplexManifold n Y] (U : Opens Y) :
    PullsBackCoordinates n (Subtype.val : U → Y) :=
  fun _ _ _ h => isCoordinateFamilyAt_preimage_val_iff.mpr h

variable {g : Z → Y}

/-- The members of `E.map (g ⁻¹' ·)`, as preimages of the members of `E`. -/
theorem get_map_preimage (E : List (Set Y)) (i : Fin (E.map (g ⁻¹' ·)).length) :
    (E.map (g ⁻¹' ·)).get i = g ⁻¹' E.get (Fin.cast (List.length_map _) i) := by
  simp [List.get_eq_getElem]

/-- **Preimages of simple normal crossings divisors are simple normal crossings divisors.** -/
theorem isSNCDivisor_map_preimage (hg : PullsBackCoordinates n g) (hgc : Continuous g)
    {E : List (Set Y)} (hE : IsSNCDivisor n E) : IsSNCDivisor n (E.map (g ⁻¹' ·)) := by
  refine ⟨fun H hH => ?_, fun z => ?_⟩
  · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact (hE.1 H₀ hH₀).preimage hgc
  · obtain ⟨S, hS, hcard, hinj⟩ := hE.2 (g z)
    set c : Fin (E.map (g ⁻¹' ·)).length → Fin E.length := Fin.cast (List.length_map _)
    refine ⟨fun i => S (c i), IsCoordinateFamilyAt.reindex (hg _ S z hS) c (fun i => get_map_preimage E i)
      (fun _ => rfl), fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · rw [get_map_preimage] at hi
      exact hcard (c i) hi
    · simp only [mem_ofPred_eq, get_map_preimage] at hi hj
      exact Fin.cast_injective _ (hinj hi hj hij)

/-- **Normal crossings pull back.** -/
theorem hasNormalCrossings_preimage (hg : PullsBackCoordinates n g) {C : Set Y}
    {E : List (Set Y)} (h : HasNormalCrossings n C E) :
    HasNormalCrossings n (g ⁻¹' C) (E.map (g ⁻¹' ·)) := by
  intro z hz
  obtain ⟨S₀, S, hS, hcard⟩ := h (g z) hz
  set c : Fin (E.map (g ⁻¹' ·)).length → Fin E.length := Fin.cast (List.length_map _)
  refine ⟨S₀, fun i => S (c i), IsCoordinateFamilyAt.reindex (hg _ _ z hS) (Option.map c) ?_ ?_, fun i hi => ?_⟩
  · rintro (_ | i)
    · rfl
    · exact get_map_preimage E i
  · rintro (_ | i) <;> rfl
  · rw [get_map_preimage] at hi
    exact hcard (c i) hi

/-- **Transversality pulls back.** -/
theorem isTransverse_preimage (hg : PullsBackCoordinates n g) {N : Set Y} {E : List (Set Y)}
    (h : IsTransverse n N E) : IsTransverse n (g ⁻¹' N) (E.map (g ⁻¹' ·)) := by
  intro z hz
  obtain ⟨S₀, S, hS, hcard⟩ := h (g z) hz
  set c : Fin (E.map (g ⁻¹' ·)).length → Fin E.length := Fin.cast (List.length_map _)
  refine ⟨S₀, fun i => S (c i), IsCoordinateFamilyAt.reindex (hg _ _ z hS) (Option.map c) ?_ ?_, fun i hi => ?_⟩
  · rintro (_ | i)
    · rfl
    · exact get_map_preimage E i
  · rintro (_ | i) <;> rfl
  · rw [get_map_preimage] at hi
    exact hcard (c i) hi

end Pullback

end

end Hironaka.NormalCrossingsInvariance
