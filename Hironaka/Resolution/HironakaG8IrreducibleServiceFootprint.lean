import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaG8ClosedNativeTestGlobalization
import Hironaka.Analytic.StrictTransformLocus
import Hironaka.Analytic.ProperMappingTheorem

/-! A global serving block must contain full analytic continuations of its centres. -/
set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8IrreducibleServiceFootprint
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  RestrictEmptyTower HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaG8FirstFootprintOrder HironakaG8OccupiedSlotComparison
  HironakaG8ClosedNativeTestGlobalization HironakaClosedFootprintOpenTowerExtension

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- Every actual raw centre image is analytic by proper mapping. -/
theorem slotFootprint_analytic (T : BlowupTower X Y) (i : ℕ) :
    IsComplexAnalyticSubset (n := n) (slotFootprint T i) := by
  induction T with
  | refl => exact isComplexAnalyticSubset_empty
  | step T C π hπ ih =>
    by_cases hi : i = T.length
    · rw [slotFootprint,if_pos hi]
      have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
      exact ProperMappingTheorem.isComplexAnalyticSubset_image T.contMDiff_proj hC
        (fun K hK => ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).inter_left hC.isClosed)
    · rw [slotFootprint,if_neg hi]
      exact ih

/-- Any global finite tower clearing a neighbourhood-sized part of an
irreducible singular subvariety must hit the entire subvariety in one
projected physical centre. -/
theorem irreducible_carrier_subset_one_serving_slot
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (K U : Set X)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hOpen : IsOpen U) (hMeet : (V.carrier ∩ U).Nonempty)
    (hInside : V.carrier ∩ U ⊆ singularSet (n := n) W ∩ K)
    (T : BlowupTower X Y)
    (hClear : Disjoint (singularSet (n := n) (strictTransform n T.proj W)) (T.proj ⁻¹' K)) :
    ∃ i < T.length, V.carrier ⊆ slotFootprint T i := by
  have hSurj : Surjective T.proj := by
    clear hClear
    induction T with
    | refl => exact surjective_id
    | step T C π hπ ih =>
      rw [BlowupTower.proj_step]
      exact ih.comp (HironakaLocalPrincipalization.surjective_of_isBlowupAlong hπ)
  have hHit : singularSet (n := n) W ∩ K ⊆ ⋃ i, slotFootprint T i := by
    intro x hx
    by_contra hMiss
    obtain ⟨y,hy⟩ := hSurj x
    have hNo : ∀ i, T.proj y ∉ slotFootprint T i :=
      fun i hi => hMiss (mem_iUnion.mpr ⟨i,hy ▸ hi⟩)
    have hSing := (untouched_fibre_intrinsic W hW T y hNo).1.mpr (hy ▸ hx.1)
    exact disjoint_left.mp hClear hSing (show T.proj y ∈ K from hy.symm ▸ hx.2)
  obtain ⟨i,hi⟩ := StrictTransformLocus.exists_subset_of_inter_isOpen_subset_iUnion
    V (slotFootprint_analytic T) hOpen hMeet (hInside.trans hHit)
  obtain ⟨x,hx,_⟩ := hMeet
  exact ⟨i,hit_slot_lt_length T (hi hx),hi⟩

/-- Even a possibly noncompact closed footprint inside a proposed
window cannot globalize its finite clearing if that window omits part
of the irreducible singular subvariety met by the task. -/
theorem no_closed_footprint_extension_omitting_irreducible_carrier
    {m : ℕ} {X S : CMfd.{0} (m+1)}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := m+1) W)
    (K U : Set X) (V : ClosedIrreducibleAnalyticSubvariety (m+1) X)
    (hOpen : IsOpen U) (hMeet : (V.carrier ∩ U).Nonempty)
    (hInside : V.carrier ∩ U ⊆ singularSet (n := m+1) W ∩ K)
    (O : Opens X) (hKO : K ⊆ O) (hOmit : ¬ V.carrier ⊆ O)
    (T : BlowupTower (CMfd.of (n := m+1) O) S)
    (hClear : Disjoint (T.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' K))
      (singularSet (n := m+1) (strictTransform (m+1) T.proj ((Subtype.val : O → X) ⁻¹' W)))) :
    ¬ ∃ F : Set X, IsClosed F ∧ F ⊆ O ∧ CentresOver ((Subtype.val : O → X) ⁻¹' F) T := by
  rintro ⟨F,hF,hFO,hOver⟩
  obtain ⟨Y,Q,hQ,e,he,_,hProj⟩ := exists_closed_footprint_extension O F hF hFO T hOver
  have hClearQ := singular_fibre_clear_of_extension_iso W hW.isClosed K O hKO Q T e he hProj hClear
  obtain ⟨i,_,hi⟩ := irreducible_carrier_subset_one_serving_slot W hW K U V hOpen hMeet hInside Q hClearQ
  exact hOmit (hi.trans ((slotFootprint_subset_of_centresOver Q hQ i).trans hFO))

end Hironaka.HironakaG8IrreducibleServiceFootprint
