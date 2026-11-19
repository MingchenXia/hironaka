import Hironaka.Resolution.HironakaG8FiniteParallelReadback

/-! Construct the actual selected/empty tape from the trace data. -/
set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SelectedParallelTapeProducer
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HironakaG8FiniteParallelReadback

variable {n : ℕ} {X : CMfd.{0} n}

/-- Each specified parallel round has a selected member or an empty
trace on the same fixed original saturated open. -/
inductive SelectedParallelPlan (U : Opens X) {A : CMfd.{0} n} (P₀ : BlowupTower X A) :
    {Y : CMfd.{0} n} → BlowupTower X Y → Prop
  | start : SelectedParallelPlan U P₀ P₀
  | round {Y Y' : CMfd.{0} n} {P : BlowupTower X Y}
      (hPrev : SelectedParallelPlan U P₀ P)
      {ι : Type} {C : ι → Set Y} {π : Y' → Y} (hπ : IsBlowupAlong n (⋃ i, C i) π)
      (selected : Option ι)
      (hTrace : (Subtype.val : openPreimage P U → Y) ⁻¹' (⋃ i, C i) =
        selected.elim ∅ (fun i => (Subtype.val : openPreimage P U → Y) ⁻¹' C i)) :
      SelectedParallelPlan U P₀ (.step P (⋃ i, C i) π hπ)

/-- The parallel plan produces an actual local tape. An empty trace is
realized by an actual identity blowup at that round. -/
theorem SelectedParallelPlan.exists_local_tape
    {U : Opens X} {A Y : CMfd.{0} n} {P₀ : BlowupTower X A} {P : BlowupTower X Y}
    (h : SelectedParallelPlan U P₀ P) :
    ∃ (Z : CMfd.{0} n) (S : BlowupTower (CMfd.of (n := n) U) Z),
      SelectedParallelTape U P₀ P S := by
  induction h with
  | start => exact ⟨_,restrict U P₀,.start⟩
  | @round Y Y' P hPrev ι C π hπ selected hTrace ih =>
    obtain ⟨Z,S,hS⟩ := ih
    obtain ⟨e,hIso⟩ := hS.exists_strict_comparison
    cases selected with
    | none =>
      let hρ : IsBlowupAlong n (∅ : Set Z) (id : Z → Z) :=
        BlowupExistenceCodimOne.isBlowupAlong_id_empty
      exact ⟨Z,.step S ∅ id hρ,hS.round_of_known_prefix hπ none hTrace hρ hIso (preimage_empty)⟩
    | some j =>
      let V := openPreimage P U
      let R := BlowupTower.step P (⋃ i, C i) π hπ
      let f : openPreimage R U → V := fun z => ⟨π z.val,z.property⟩
      let D := e.symm ⁻¹' ((Subtype.val : V → Y) ⁻¹' C j)
      have hf : IsBlowupAlong n ((Subtype.val : V → Y) ⁻¹' C j) f := by
        rw [show ((Subtype.val : V → Y) ⁻¹' C j) =
          (Subtype.val : V → Y) ⁻¹' (⋃ i, C i) from hTrace.symm]
        exact BlowupRestrictOpen.isBlowupAlong_restrict hπ V
          (V.isOpen.preimage hπ.contMDiff.continuous)
      have hρ : IsBlowupAlong n D (e ∘ f) :=
        MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse e.symm.contMDiff e.contMDiff
          e.symm_apply_apply e.apply_symm_apply hf
      refine ⟨CMfd.of (n := n) (openPreimage R U),.step S D (e ∘ f) hρ,
        hS.round_of_known_prefix hπ (some j) hTrace hρ hIso ?_⟩
      ext z
      change e.symm (e z) ∈ (Subtype.val : V → Y) ⁻¹' C j ↔ z ∈ (Subtype.val : V → Y) ⁻¹' C j
      rw [e.symm_apply_apply]

end Hironaka.HironakaG8SelectedParallelTapeProducer
