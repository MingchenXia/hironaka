/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsLabelledBoundary

/-!
# Original labelled boundaries from genuine disjoint branch groups

Actual finite position groups retain their original labels, even for an
empty group. One genuine shared NC coordinate system proves every local
equation and the disjointness of all regrouped branch sets.
Blueprint: `hironaka-normal-crossings-labelled-boundary-regrouping-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaNormalCrossingsLabelledBoundaryRegrouping
noncomputable section
open NormalCrossings BlowupFlatCoordinates HironakaNormalCrossingsLabelledBoundary
variable {n q : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y]

/-- Finite disjoint groups of original positions give the actual entire labelled list. -/
theorem isNormalCrossingsBoundary_grouped {F : List (Set Y)}
    (hF : IsNormalCrossingsBoundary (n := n) F)
    (G : Fin q → Finset (Fin F.length))
    (hG : ∀ i j, i ≠ j → Disjoint (G i) (G j)) :
    IsNormalCrossingsBoundary (n := n) (List.ofFn fun i => ⋃ j ∈ G i, F.get j) := by
  let L := List.ofFn fun i => ⋃ j ∈ G i, F.get j
  let c : Fin L.length → Fin q := Fin.cast List.length_ofFn
  have hget (i : Fin L.length) : L.get i = ⋃ j ∈ G (c i), F.get j :=
    List.get_ofFn _ i
  refine ⟨?_, fun x => ?_⟩
  · intro H hH
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    rw [hget]
    exact (G (c i)).finite_toSet.isClosed_biUnion (fun j _ => hF.1 _ (List.get_mem _ _))
  · obtain ⟨Φ, S, hsrc, h0, hdis, hEq⟩ := hF.2 x
    refine ⟨Φ, (fun i => (G (c i)).biUnion S), hsrc, h0, ?_, ?_⟩
    · intro i k hne
      apply Finset.disjoint_left.mpr
      intro a hai hak
      obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp hai
      obtain ⟨l, hl, hal⟩ := Finset.mem_biUnion.mp hak
      have hci : c i ≠ c k := fun he => hne (Fin.cast_injective _ he)
      have hjl : j ≠ l := by
        intro he
        exact Finset.disjoint_left.mp (hG _ _ hci) hj (he ▸ hl)
      exact Finset.disjoint_left.mp (hdis j l hjl) haj hal
    · intro i y hy
      rw [hget]
      constructor
      · intro hyH
        obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hyH
        obtain ⟨a, ha, hya⟩ := (hEq j y hy).mp hyj
        exact ⟨a, Finset.mem_biUnion.mpr ⟨j, hj, ha⟩, hya⟩
      · rintro ⟨a, ha, hya⟩
        obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp ha
        exact mem_iUnion₂.mpr ⟨j, hj, (hEq j y hy).mpr ⟨a, haj, hya⟩⟩

/-- Genuine SNC branches can be regrouped, retaining original and singleton born labels. -/
theorem isNormalCrossingsBoundary_grouped_of_snc {F : List (Set Y)}
    (hF : IsSNCDivisor n F) (G : Fin q → Finset (Fin F.length))
    (hG : ∀ i j, i ≠ j → Disjoint (G i) (G j)) :
    IsNormalCrossingsBoundary (n := n) (List.ofFn fun i => ⋃ j ∈ G i, F.get j) :=
  isNormalCrossingsBoundary_grouped (isNormalCrossingsBoundary_of_snc hF) G hG

/-- Every injective finite ordered selection retains every chosen original member literally. -/
theorem isNormalCrossingsBoundary_reindex {F : List (Set Y)}
    (hF : IsNormalCrossingsBoundary (n := n) F) (σ : Fin q → Fin F.length)
    (hσ : Function.Injective σ) :
    IsNormalCrossingsBoundary (n := n) (List.ofFn fun i => F.get (σ i)) := by
  have h := isNormalCrossingsBoundary_grouped hF (fun i => {σ i}) (by
    intro i j hne
    exact Finset.disjoint_singleton.mpr (fun he => hne (hσ he)))
  have he : (List.ofFn fun i => ⋃ j ∈ ({σ i} : Finset (Fin F.length)), F.get j) =
      List.ofFn (fun i => F.get (σ i)) := by
    apply congrArg List.ofFn
    funext i
    ext y
    simp
  rwa [he] at h

end
end Hironaka.HironakaNormalCrossingsLabelledBoundaryRegrouping
