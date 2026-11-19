import Hironaka.Resolution.HironakaG4ToricCentreNC
import Hironaka.Blowup.NormalCrossingsInvariance

/-! An invariant ambient toric state supplies normal crossings on a window. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricCentreLocalNC
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings NormalCrossingsInvariance
  HironakaG4LocalToricDivisors HironakaG4ToricCentreNC
  HironakaSharpNormalCrossingsOpenLocus

variable {n : ℕ} {X : CMfd.{u} n} {A : Type*} {F : Filter A}

/-- Toric states at the points of the centre in an open window give normal
crossings of the restricted centre with the restricted ordered boundary. -/
theorem normalCrossings_on_open_of_invariant_toric_states
    {N C : Set X} {E : List (Set X)} (V : Opens X) {act : A → X → X}
    (hCN : C ⊆ N) (hCan : IsComplexAnalyticSubset (n := n) C)
    (hCreg : ∀ x ∈ C, ∃ k, RegularAtDim (n := n) C x k)
    (hstate : ∀ x ∈ C, x ∈ V → LocalToricDivisorState (n := n) F N
      (fun i : Fin E.length => E.get i) x act)
    (hpres : ∀ x ∈ C, x ∈ V → ∀ᶠ p in F ×ˢ 𝓝 x, p.2 ∈ C → act p.1 p.2 ∈ C) :
    HasNormalCrossings n ((Subtype.val : V → X) ⁻¹' C)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) := by
  intro z hz
  obtain ⟨k, hk⟩ := hCreg z hz
  obtain ⟨S₀, S, hS, hcard⟩ := normalCrossingsAt_of_invariant_toric_state
    hCN hCan hk (hstate z hz z.property) (hpres z hz z.property)
  let c : Fin (E.map ((Subtype.val : V → X) ⁻¹' ·)).length → Fin E.length :=
    Fin.cast (List.length_map _)
  refine ⟨S₀, fun i => S (c i), IsCoordinateFamilyAt.reindex
    ((pullsBackCoordinates_val V) _ _ z hS) (Option.map c) ?_ ?_, fun i hi => ?_⟩
  · rintro (_ | i)
    · rfl
    · exact get_map_preimage E i
  · rintro (_ | i) <;> rfl
  · rw [get_map_preimage] at hi
    exact hcard (c i) hi

end
end Hironaka.HironakaG4ToricCentreLocalNC
