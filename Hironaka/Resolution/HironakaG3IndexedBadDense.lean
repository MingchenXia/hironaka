import Hironaka.Resolution.HironakaG3IndexedMixedBad
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedBadDense
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaEmbeddedAnalyticLocal
  HironakaG3FiniteMixedBadLocus HironakaG3MixedOrderedSupport HironakaG3IndexedMixedNonerasure
  HironakaG3IndexedMixedGluing HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaG3IndexedMixedBad HironakaBaseChange RestrictEmptyTower

/-- A window containing every visible component sees the entire indexed bad
locus through its own finite labelled list. -/
theorem indexed_bad_on_complete_window {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} {k : ℕ} (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (e : Fin k ↪ ι) (U : Opens X)
    (hs : ∀ i, ((V i).carrier ∩ (U : Set X)).Nonempty → i ∈ Set.range e) :
    indexedMixedBad V ∩ (U : Set X) ⊆ mixedBadLocus (fun j => V (e j)) := by
  classical
  let W : Fin k → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (e j)
  have hidx : ∀ i, ∀ q ∈ (V i).carrier, q ∈ U → ∃ j : Fin k, e j = i := by
    intro i q hq hqU
    exact hs i ⟨q,hq,hqU⟩
  change indexedMixedBad V ∩ (U : Set X) ⊆ mixedBadLocus W
  rintro q ⟨hqbad,hqU⟩
  rcases hqbad with hsing | hpairs
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hsing
    obtain ⟨j,hj⟩ := hidx i q hi.1 hqU
    left
    apply mem_iUnion₂.mpr
    refine ⟨(W j).carrier \ regularLocus (n := n) (W j).carrier (W j).dim,?_,?_⟩
    · exact List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩
    · simpa [W,hj] using hi
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hpairs
    obtain ⟨k,hk⟩ := mem_iUnion.mp hi
    obtain ⟨hik,hikq⟩ := mem_iUnion.mp hk
    obtain ⟨u,hu⟩ := hidx i q hikq.1 hqU
    obtain ⟨v,hv⟩ := hidx k q hikq.2 hqU
    have huv : u ≠ v := fun he => hik (hu.symm.trans (he ▸ hv))
    apply pair_intersection_subset_mixedBadLocus W huv
    simpa [W,hu,hv] using hikq

/-- No original irreducible component is contained in the actual exceptional
image of its glued indexed mixed separator. -/
theorem original_component_not_subset_exceptional_image {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) {P : Z → X} (h : IsGluedFrom (indexedMixedClass V D) Z P) (a : ι) :
    ¬ (V a).carrier ⊆ P '' exceptionalLocus n P := by
  obtain ⟨x,hx⟩ := (V a).irreducible_carrier.nonempty
  obtain ⟨c,hc⟩ := h.2.2.2 x
  obtain ⟨s,r,Ef,hs,hr,hTree,hOver,hAdm,hSNC,hDis⟩ := c.mem
  let l := s.sort (· ≤ ·)
  let W : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (l.get j)
  have he : Injective l.get := (s.sort_nodup (· ≤ ·)).injective_get
  let e : Fin l.length ↪ ι := ⟨l.get,he⟩
  have hVis : ∀ i, ((V i).carrier ∩ (c.U : Set X)).Nonempty → i ∈ Set.range e := by
    intro i hVisible
    have hi : i ∈ l := by simpa [l] using hs i hVisible
    exact List.mem_iff_get.mp hi
  have hData := mixedBadLocus_closed_and_good W (fun i => hDim (l.get i))
    (fun i j hij => hDistinct (l.get i) (l.get j) (fun heq => hij (he heq)))
  have ha : a ∈ s := hs a ⟨x,hx,hc⟩
  have ha' : a ∈ l := by simpa [l] using ha
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha'
  have hdense : (V a).carrier ⊆ closure ((V a).carrier \ mixedBadLocus W) := by
    simpa only [W,hi] using (hData.2 i).2.2.2.2
  have hmeet : ((V a).carrier \ mixedBadLocus W ∩ (c.U : Set X)).Nonempty := by
    have hclose := c.U.isOpen.closure_inter ⟨hdense hx,hc⟩
    by_contra hn
    have he : ((V a).carrier \ mixedBadLocus W ∩ (c.U : Set X)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he,closure_empty] at hclose
    exact hclose
  obtain ⟨q,⟨hqV,hqNot⟩,hqU⟩ := hmeet
  have hqGlobal : q ∉ indexedMixedBad V := by
    intro hq
    apply hqNot
    exact indexed_bad_on_complete_window V e c.U hVis ⟨hq,hqU⟩
  intro hsub
  obtain ⟨z,hz,rfl⟩ := hsub hqV
  exact hqGlobal (glued_indexed_exceptional_subset V hDim hDistinct D h hz)
end
end Hironaka.HironakaG3IndexedBadDense
