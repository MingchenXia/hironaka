import Hironaka.Resolution.HironakaG3RBoundaryEmbedded
import Hironaka.Resolution.HironakaG3OrderedFiniteWindows
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BoundaryStoppingOpenRestriction
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3RBoundaryEmbedded

/-- Removing empty indexed boundary slots does not change their support. -/
theorem biUnion_nonempty_filter {X : Type*} (E : List (Set X)) :
    (⋃ H ∈ E.filter (fun H => decide H.Nonempty), H) = ⋃ H ∈ E, H := by
  ext x
  simp only [mem_iUnion, exists_prop, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨H,⟨hH,_⟩,hx⟩
    exact ⟨H,hH,hx⟩
  · rintro ⟨H,hH,hx⟩
    exact ⟨H,⟨hH,⟨x,hx⟩⟩,hx⟩

/-- The literal stopping open is unchanged when the ordered nonempty
boundary slots agree. -/
theorem bdryOpen_eq_of_nonempty_filter {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (r : ℕ) (E F : List (Set X))
    (h : E.filter (fun H => decide H.Nonempty) = F.filter (fun H => decide H.Nonempty)) :
    bdryOpen W r E = bdryOpen W r F := by
  have hUnion : (⋃ H ∈ E, H) = ⋃ H ∈ F, H := by
    calc
      _ = ⋃ H ∈ E.filter (fun H => decide H.Nonempty), H := (biUnion_nonempty_filter E).symm
      _ = ⋃ H ∈ F.filter (fun H => decide H.Nonempty), H := by rw [h]
      _ = ⋃ H ∈ F, H := biUnion_nonempty_filter F
  apply Opens.ext
  change interior (W \ regularLocus (n := n) W r ∪ ⋃ H ∈ E, H)ᶜ =
    interior (W \ regularLocus (n := n) W r ∪ ⋃ H ∈ F, H)ᶜ
  rw [hUnion]

/-- Native stopping opens commute with literal open restriction, even when
the local ordered boundary differs by empty slots. -/
theorem bdryOpen_restrict_of_nonempty_filter {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsClosed W) (r : ℕ) (E : List (Set X))
    (hE : ∀ H ∈ E, IsClosed H) (U : Opens X) (F : List (Set U))
    (hfilter : F.filter (fun H => decide H.Nonempty) =
      (E.map ((Subtype.val : U → X) ⁻¹' ·)).filter (fun H => decide H.Nonempty)) :
    (bdryOpen (n := n) (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W) r F : Set U) =
      (Subtype.val : U → X) ⁻¹' (bdryOpen W r E : Set X) := by
  have hOpen := bdryOpen_eq_of_nonempty_filter (n := n) (X := CMfd.of (n := n) U)
    ((Subtype.val : U → X) ⁻¹' W) r F (E.map ((Subtype.val : U → X) ⁻¹' ·)) hfilter
  rw [hOpen]
  have hEC : ∀ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·), IsClosed H := by
    intro H hH
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
    exact (hE K hK).preimage continuous_subtype_val
  rw [coe_bdryOpen (hW.preimage continuous_subtype_val) r hEC, coe_bdryOpen hW r hE]
  rw [← HironakaEmbeddedReducible.preimage_val_diff_regularLocus U W r,
    ← HironakaEmbeddedBoundary.preimage_biUnion_list (Subtype.val : U → X) E,
    ← preimage_union, ← preimage_compl]
/-- Complete ordered windows determine the same literal stopping open on
    their common carrier, with no supplied stopping-open equality. -/
theorem sorted_windows_stopping_opens_agree {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (W : Set X) (r : ℕ) (D : ι → Set X)
    (s t : Finset ι) (hs : ∀ i, (D i).Nonempty → i ∈ s)
    (ht : ∀ i, (D i).Nonempty → i ∈ t) :
    bdryOpen W r ((s.sort (· ≤ ·)).map D) = bdryOpen W r ((t.sort (· ≤ ·)).map D) :=
  bdryOpen_eq_of_nonempty_filter W r _ _
    (HironakaG3OrderedFiniteWindows.sorted_boundary_traces_agree D s t hs ht)
end
end Hironaka.HironakaG3BoundaryStoppingOpenRestriction
