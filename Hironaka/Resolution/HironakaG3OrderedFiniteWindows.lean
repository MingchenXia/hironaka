import Hironaka.Resolution.HironakaG3IndexedBoundaryFiniteWindow
import Hironaka.Resolution.HironakaG3MixedFilteredComparison
import Mathlib.Data.Finset.Sort
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG3OrderedFiniteWindows
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation
  HironakaOriginalCanonicalSeparationChainChoice HironakaG3MixedOrderedSeparation HironakaG3MixedFilteredComparison
  HironakaG3IndexedBoundaryFiniteWindow
attribute [local instance] Classical.propDecidable

/-- Restriction of a sorted finite index window stays sorted. -/
theorem sort_filter {ι : Type*} [LinearOrder ι] (s : Finset ι) (p : ι → Prop) :
    (s.sort (· ≤ ·)).filter p = (s.filter p).sort (· ≤ ·) := by
  symm
  have hn := (s.sort_nodup (· ≤ ·)).filter p
  have hs := (s.pairwise_sort (· ≤ ·)).filter p
  simpa using (List.toFinset_sort (· ≤ ·) hn).mpr hs

/-- Sorted finite windows have the same surviving labels on a common region,
whenever each window contains every label visible there. -/
theorem sorted_windows_agree {ι : Type*} [LinearOrder ι]
    (s t : Finset ι) (p : ι → Prop)
    (hs : ∀ i, p i → i ∈ s) (ht : ∀ i, p i → i ∈ t) :
    (s.sort (· ≤ ·)).filter p = (t.sort (· ≤ ·)).filter p := by
  rw [sort_filter,sort_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨ht i h.2,h.2⟩,fun h => ⟨hs i h.2,h.2⟩⟩
/-- The geometric component lists obtained from two windows agree after
empty traces are removed, including their dimension labels. -/
theorem sorted_component_traces_agree {ι Z : Type*} [LinearOrder ι]
    (F : ι → Set Z) (d : ι → ℕ) (s t : Finset ι)
    (hs : ∀ i, (F i).Nonempty → i ∈ s) (ht : ∀ i, (F i).Nonempty → i ∈ t) :
    HironakaOriginalCanonicalSeparationChainChoice.nonemptyParts ((s.sort (· ≤ ·)).map (fun i => (F i,d i))) =
    HironakaOriginalCanonicalSeparationChainChoice.nonemptyParts ((t.sort (· ≤ ·)).map (fun i => (F i,d i))) := by
  have h := sorted_windows_agree s t (fun i => (F i).Nonempty) hs ht
  have hm := congrArg (List.map (fun i => (F i,d i))) h
  simpa [HironakaOriginalCanonicalSeparationChainChoice.nonemptyParts,List.filter_map,Function.comp_def] using hm

/-- The same holds for the full boundary lists on an overlap. -/
theorem sorted_boundary_traces_agree {ι Z : Type*} [LinearOrder ι]
    (F : ι → Set Z) (s t : Finset ι)
    (hs : ∀ i, (F i).Nonempty → i ∈ s) (ht : ∀ i, (F i).Nonempty → i ∈ t) :
    ((s.sort (· ≤ ·)).map F).filter (fun H => decide H.Nonempty) =
    ((t.sort (· ≤ ·)).map F).filter (fun H => decide H.Nonempty) := by
  have h := sorted_windows_agree s t (fun i => (F i).Nonempty) hs ht
  have hm := congrArg (List.map F) h
  simpa [List.filter_map,Function.comp_def] using hm
/-- Sorting any finite subset of labels preserves the full SNC property. -/
theorem sorted_boundary_snc {n : ℕ} {X : CMfd.{0} n} {ι : Type*} [LinearOrder ι]
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) (s : Finset ι) :
    IsSNCDivisor n ((s.sort (· ≤ ·)).map D) := by
  let l := s.sort (· ≤ ·)
  let e : Fin l.length ↪ ι := ⟨l.get, (s.sort_nodup (· ≤ ·)).injective_get⟩
  have h := isSNCDivisor_finiteBoundary D hD e
  have heq : finiteBoundary D e = l.map D := by
    simp [finiteBoundary,e]
  rw [heq] at h
  exact h
/-- Local finiteness supplies an actual sorted SNC boundary window. -/
theorem exists_sorted_boundary_window {n : ℕ} {X : CMfd.{0} n} {κ : Type*} [LinearOrder κ]
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) (x : X) :
    ∃ (U : Opens X) (s : Finset κ), x ∈ U ∧
      IsSNCDivisor n ((s.sort (· ≤ ·)).map D) ∧
      ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ s := by
  obtain ⟨U,k,e,hx,_,hhit,_⟩ := exists_finite_boundary_window D hD x
  let s : Finset κ := Finset.univ.image e
  refine ⟨U,s,hx,sorted_boundary_snc D hD s,?_⟩
  intro i hi
  obtain ⟨j,hj⟩ := hhit i hi
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩

/-- Independently chosen finite ordered component and boundary windows have a
unique comparison over the common open when they contain every visible label. -/
theorem sorted_window_mixed_choice {n : ℕ} {X Y Y' : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (F : ι → Set X) (d : ι → ℕ) (G : κ → Set X)
    (s t : Finset ι) (r q : Finset κ)
    (hs : ∀ i, (F i).Nonempty → i ∈ s) (ht : ∀ i, (F i).Nonempty → i ∈ t)
    (hr : ∀ i, (G i).Nonempty → i ∈ r) (hq : ∀ i, (G i).Nonempty → i ∈ q)
    (T : BlowupTower X Y) (S : BlowupTower X Y')
    {Ef : List (Set Y)} {Ef' : List (Set Y')}
    (hT : CanonicalMixedSeparation ((r.sort (· ≤ ·)).map G)
      ((s.sort (· ≤ ·)).map (fun i => (F i,d i))) T Ef)
    (hS : CanonicalMixedSeparation ((q.sort (· ≤ ·)).map G)
      ((t.sort (· ≤ ·)).map (fun i => (F i,d i))) S Ef') :
    ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      (∀ z,T.proj (η z)=S.proj z) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
      ∀ P : Set X,strictTransform n S.proj P=η ⁻¹' strictTransform n T.proj P := by
  have hB := sorted_boundary_traces_agree G r q hr hq
  have hC := sorted_component_traces_agree (fun i => closure (F i)) d s t
    (fun i hi => hs i (closure_nonempty_iff.mp hi))
    (fun i hi => ht i (closure_nonempty_iff.mp hi))
  have h := mixed_choice_over_base_closedParts (Diffeomorph.refl _ _ ∞) hT hS (by simpa using hB.symm)
    (by simpa [closedParts,pulledParts,List.map_map,Function.comp_def] using hC.symm)
  simpa using h
end
end Hironaka.HironakaG3OrderedFiniteWindows
