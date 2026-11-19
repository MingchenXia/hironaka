import Hironaka.Resolution.HironakaG4ToricCentreNC
import Hironaka.Resolution.HironakaG34LowerCleanupLift
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Invariant.MaxLocusLocal

/-! An invariant toric state supplies the full protected window. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricProtectedWindow
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaG4LocalToricDivisors HironakaG4ToricDivisorRecognition HironakaG4ToricCentreNC
  HironakaSharpNormalCrossingsOpenLocus HironakaG34LowerCleanupLift
  NormalCrossingsInvariance HironakaBaseChange

variable {n : ℕ} {X : CMfd.{u} n} {A : Type*} {G : Filter A}

/-- A local toric divisor state, invariant smooth centre and local slice
identity imply the complete protected-window certificate. -/
theorem protectedWindowAt_of_invariant_toric_state {N S H C : Set X} {F : List (Set X)}
    {x : X} {act : A → X → X} (hCclosed : IsClosed C)
    (hEclosed : ∀ K ∈ H :: F, IsClosed K) (hCN : C ⊆ N)
    (hCan : IsComplexAnalyticSubset (n := n) C) {k : ℕ} (hreg : RegularAtDim (n := n) C x k)
    (hstate : LocalToricDivisorState (n := n) G N (fun i : Fin (H :: F).length => (H :: F).get i) x act)
    (hpreserve : ∀ᶠ p in G ×ˢ 𝓝 x, p.2 ∈ C → act p.1 p.2 ∈ C)
    (hslice : ∀ᶠ y in 𝓝 x, y ∈ S ↔ y ∈ N ∩ H) :
    ProtectedWindowAt N S F C x := by
  obtain ⟨V, hxV, hSNC, hTr⟩ := exists_snc_transverse_neighborhood hEclosed hstate
  have hNCx := normalCrossingsAt_of_invariant_toric_state hCN hCan hreg hstate hpreserve
  have hNCnear := eventually_normalCrossingsAt hCclosed hEclosed hNCx
  obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.mp (hNCnear.and hslice)
  let W : Opens X := ⟨O, hOopen⟩
  let U : Opens X := V ⊓ W
  let i : U → V := fun z => ⟨z.val, z.property.1⟩
  have hOpen : IsOpenHoloEmbedding n i :=
    ⟨MaxLocusLocal.nestedOpens V U, (MaxLocusLocal.nestedOpensDiffeo (n := n) inf_le_left).symm, fun _ => rfl⟩
  have hSNC' := isSNCDivisor_map_preimage hOpen.pullsBackCoordinates hOpen.continuous hSNC
  have hTr' := isTransverse_preimage hOpen.pullsBackCoordinates hTr
  refine ⟨U, ⟨hxV, hxO⟩, (Subtype.val : U → X) ⁻¹' H, ?_, ?_, ?_, ?_⟩
  · ext y
    exact (hOsub y.property.2).2
  · simpa only [List.map_cons, List.map_map, Function.comp_def, Set.preimage_preimage] using hSNC'
  · simpa only [List.map_cons, List.map_map, Function.comp_def, Set.preimage_preimage] using hTr'
  · intro y hyC
    let E := H :: F
    have hlocal : normalCrossingsAt (n := n) C E y := (hOsub y.property.2).1
    obtain ⟨S₀, R, hcoord, hcard⟩ := hlocal
    let R' : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length → Finset (Fin n) :=
      fun j => R ⟨j.val, by simpa using j.isLt⟩
    have hget (j : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length) :
        (E.map ((Subtype.val : U → X) ⁻¹' ·)).get j =
          (Subtype.val : U → X) ⁻¹' (E.get ⟨j.val, by simpa using j.isLt⟩) := by
      simp [List.get_eq_getElem]
    change ∃ (T₀ : Finset (Fin n)) (T : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option (Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length) => o.elim ((Subtype.val : U → X) ⁻¹' C)
        (fun j => (E.map ((Subtype.val : U → X) ⁻¹' ·)).get j)) (fun o => o.elim T₀ T) y ∧
      ∀ j, y ∈ (E.map ((Subtype.val : U → X) ⁻¹' ·)).get j → (T j).card = 1
    refine ⟨S₀, R', ?_, ?_⟩
    · have hA : (fun o : Option (Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length) =>
          o.elim ((Subtype.val : U → X) ⁻¹' C) (fun j => (E.map ((Subtype.val : U → X) ⁻¹' ·)).get j)) =
          (fun o => (Subtype.val : U → X) ⁻¹' (o.elim C (fun j => E.get ⟨j.val, by simpa using j.isLt⟩))) := by
        funext o
        cases o with
        | none => rfl
        | some j => exact hget j
      rw [hA]
      apply isCoordinateFamilyAt_preimage_val_iff.mpr
      obtain ⟨Ψ, hsrc, hzero, hflat⟩ := hcoord
      refine ⟨Ψ, hsrc, hzero, ?_⟩
      intro o ho z hz hzΨ
      cases o with
      | none => exact hflat none ho hz hzΨ
      | some j => exact hflat (some ⟨j.val, by simpa using j.isLt⟩) ho hz hzΨ
    · intro j hj
      rw [hget] at hj
      exact hcard ⟨j.val, by simpa using j.isLt⟩ hj

end
end Hironaka.HironakaG4ToricProtectedWindow
