import Hironaka.Resolution.HironakaG3IndexedCanonicalContact
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedResidualFullWindow
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation
  HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact

/-- Adjoining all containing labels after a disjoint residual window gives
an actual finite SNC boundary containing that residual list. -/
theorem residual_then_containing_full_window {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : C.Nonempty) (hD : IsLocallyFiniteSNCDivisor n D) (R : Finset ι)
    (hDis : Disjoint (containingLabels C D hC hD.1) R) :
    let S := containingLabels C D hC hD.1
    let N := canonicalContact C D hC hD.1
    let B := (R.sort (· ≤ ·)).map D
    let E := B ++ (S.sort (· ≤ ·)).map D
    IsSNCDivisor n E ∧ B.Sublist E ∧ ∀ H ∈ E, H ∉ B → N ⊆ H := by
  let S := containingLabels C D hC hD.1
  let N := canonicalContact C D hC hD.1
  let B := (R.sort (· ≤ ·)).map D
  let E := B ++ (S.sort (· ≤ ·)).map D
  let l := R.sort (· ≤ ·) ++ S.sort (· ≤ ·)
  have hdis : List.Disjoint (R.sort (· ≤ ·)) (S.sort (· ≤ ·)) := by
    apply List.disjoint_left.mpr
    intro i hiR hiS
    have hiR' : i ∈ R := by simpa using hiR
    have hiS' : i ∈ S := by simpa using hiS
    exact (Finset.disjoint_left.mp hDis) hiS' hiR'
  have hl : l.Nodup := (R.sort_nodup (· ≤ ·)).append (S.sort_nodup (· ≤ ·)) hdis
  let e : Fin l.length ↪ ι := ⟨l.get,hl.injective_get⟩
  have hsnc := isSNCDivisor_finiteBoundary D hD e
  have heq' : finiteBoundary D e = l.map D := by
    simp [finiteBoundary,e]
  have heq : finiteBoundary D e = E := by
    rw [heq']
    simp [l,E,B]
  rw [heq] at hsnc
  refine ⟨hsnc,List.sublist_append_left B _,?_⟩
  intro H hH hnot
  have hHS : H ∈ (S.sort (· ≤ ·)).map D := by
    rcases List.mem_append.mp hH with hb | hs
    · exact False.elim (hnot hb)
    · exact hs
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hHS
  have hiS : i ∈ S := by simpa using hi
  intro x hx
  change x ∈ ⋂ i ∈ S, D i at hx
  exact (mem_iInter.mp (mem_iInter.mp hx i)) hiS
end
end Hironaka.HironakaG3IndexedResidualFullWindow
