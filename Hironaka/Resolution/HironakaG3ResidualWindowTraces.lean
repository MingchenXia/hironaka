import Hironaka.Resolution.HironakaG3OrderedFiniteWindows
set_option autoImplicit false
open Set
namespace Hironaka.HironakaG3ResidualWindowTraces
noncomputable section
attribute [local instance] Classical.propDecidable
open HironakaG3OrderedFiniteWindows

/-- Complete finite residual windows have identical nonempty traces. -/
theorem residual_window_traces_agree {ι Z : Type*} [LinearOrder ι]
    (F : ι → Set Z) (S s t : Finset ι)
    (hS : Disjoint S s) (hT : Disjoint S t)
    (hs : ∀ i, i ∉ S → (F i).Nonempty → i ∈ s)
    (ht : ∀ i, i ∉ S → (F i).Nonempty → i ∈ t) :
    ((s.sort (· ≤ ·)).map F).filter (fun H => decide H.Nonempty) =
    ((t.sort (· ≤ ·)).map F).filter (fun H => decide H.Nonempty) := by
  let G : ι → Set Z := fun i => if i ∈ S then ∅ else F i
  have hs' : ∀ i, (G i).Nonempty → i ∈ s := by
    intro i hi
    by_cases hiS : i ∈ S
    · simp [G,hiS] at hi
    · exact hs i hiS (by simpa [G,hiS] using hi)
  have ht' : ∀ i, (G i).Nonempty → i ∈ t := by
    intro i hi
    by_cases hiS : i ∈ S
    · simp [G,hiS] at hi
    · exact ht i hiS (by simpa [G,hiS] using hi)
  have h := sorted_boundary_traces_agree G s t hs' ht'
  have hmap_s : (s.sort (· ≤ ·)).map G = (s.sort (· ≤ ·)).map F := by
    apply List.map_congr_left
    intro i hi
    have his : i ∈ s := by simpa using hi
    have hiS : i ∉ S := fun hiS => (Finset.disjoint_left.mp hS) hiS his
    simp [G,hiS]
  have hmap_t : (t.sort (· ≤ ·)).map G = (t.sort (· ≤ ·)).map F := by
    apply List.map_congr_left
    intro i hi
    have hit : i ∈ t := by simpa using hi
    have hiS : i ∉ S := fun hiS => (Finset.disjoint_left.mp hT) hiS hit
    simp [G,hiS]
  simpa only [hmap_s,hmap_t] using h
end
end Hironaka.HironakaG3ResidualWindowTraces
