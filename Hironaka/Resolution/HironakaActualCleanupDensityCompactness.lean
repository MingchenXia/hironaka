import Hironaka.Resolution.HironakaG4RecordedTowerResidualCompatibility
import Hironaka.Resolution.HironakaLocalPrincipalization

/-! Actual density and compactness transport for repeated cleanup, retaining
the SAME original old boundary list. Source-first chapter:
hironaka-actual-cleanup-density-compactness.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCleanupDensityCompactness
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MemberInterTowerAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings
  HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualFirstAmbientStrictExponent
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry
  HironakaG4RecordedTowerResidualCompatibility
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem dense_diff_union {Z : Type*} [TopologicalSpace Z] {N D F : Set Z}
    (hD : IsClosed D) (hd : N ⊆ closure (N \ D)) (hf : N ⊆ closure (N \ F)) :
    N ⊆ closure (N \ (D ∪ F)) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro U hU hxU
  obtain ⟨y,hyU,hyN,hyD⟩ := mem_closure_iff.mp (hd hx) U hU hxU
  obtain ⟨z,⟨hzU,hzD⟩,hzN,hzF⟩ := mem_closure_iff.mp (hf hyN)
    (U ∩ Dᶜ) (hU.inter hD.isOpen_compl) ⟨hyU,hyD⟩
  exact ⟨z,hzU,hzN,fun h => h.elim hzD hzF⟩

private theorem dense_diff_list {Z : Type*} [TopologicalSpace Z] {N : Set Z}
    (L : List (Set Z)) (hC : ∀ H ∈ L,IsClosed H)
    (hD : ∀ H ∈ L,N ⊆ closure (N \ H)) : N ⊆ closure (N \ ⋃ H ∈ L,H) := by
  induction L with
  | nil => simpa using (subset_closure : N ⊆ closure N)
  | cons H L ih =>
    have hTail := ih (fun K hK => hC K (List.mem_cons_of_mem H hK))
      (fun K hK => hD K (List.mem_cons_of_mem H hK))
    simpa only [List.mem_cons,Set.iUnion_iUnion_eq_or_left] using
      dense_diff_union (hC H (by simp)) (hD H (by simp)) hTail

/-- Source transversality to the entire born list supplies its true missing
density, which combines with density off the SAME old list. -/
theorem actual_cleanup_source_full_density (hn : 0<n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O++B))
    (hTrans : IsTransverse n N B) (hOld : N ⊆ closure (N \ ⋃ H ∈ O,H)) :
    N ⊆ closure (N \ ⋃ H ∈ O++B,H) := by
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right O B)
  have hBDense : N ⊆ closure (N \ ⋃ H ∈ B,H) := by
    apply dense_diff_list B hBorn.1
    intro H hH
    have hSingle : IsSNCDivisor n [H] := isSNCDivisor_of_sublist hBorn
      (List.singleton_sublist.mpr hH)
    have hT : IsTransverse n N [H] := by
      apply isTransverse_of_forall_mem hTrans
      intro K hK
      rw [List.mem_singleton.mp hK]
      exact hH
    exact actual_density_of_nonzero_normalized_vanishing
      (actual_normalized_transverse_member_geometry hn hN hSingle hT).2.1
  have hOC : IsClosed (⋃ H ∈ O,H) :=
    HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed
      (fun H hH => hE.1 H (List.mem_append_left B hH))
  have hUnion : (⋃ H ∈ O++B,H)=(⋃ H ∈ O,H) ∪ ⋃ H ∈ B,H := by
    ext x
    simp only [mem_iUnion,List.mem_append,mem_union]
    constructor
    · rintro ⟨H,hH,hxH⟩
      exact hH.elim (fun h => Or.inl ⟨H,h,hxH⟩) (fun h => Or.inr ⟨H,h,hxH⟩)
    · rintro (⟨H,hH,hxH⟩ | ⟨H,hH,hxH⟩)
      · exact ⟨H,Or.inl hH,hxH⟩
      · exact ⟨H,Or.inr hH,hxH⟩
  rw [hUnion]
  exact dense_diff_union hOC hOld hBDense

/-- The actual endpoint is compact and remains dense off the strict transforms
of the SAME fixed original OLD list. No endpoint certificate is an input. -/
theorem actual_cleanup_density_compactness_transport (hn : 0<n) {N : Set X}
    {O B : List (Set X)} (hN : IsClosedSubmanifold n N) (hK : IsCompact N)
    (hE : IsSNCDivisor n (O++B)) (hTrans : IsTransverse n N B)
    (hOld : N ⊆ closure (N \ ⋃ H ∈ O,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate N []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (O++B)) T) :
    IsCompact (strictAlong T N) ∧
      strictAlong T N ⊆ closure (strictAlong T N \ ⋃ H ∈ O.map (strictAlong T),H) := by
  have hDense := actual_cleanup_source_full_density hn hN hE hTrans hOld
  obtain ⟨hNT,_hSNC,_hTr,hCurrent,_hRows⟩ :=
    actual_recorded_tower_residual_dictionary hn hN hE hDense T hT hFull
  have hNid : (geoTransformAlong (geometricTemplate N []) T).N=strictAlong T N :=
    N_geoTransformAlong _ T
  rw [hNid] at hNT hCurrent
  refine ⟨((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    hNT.1 (strictAlong_subset_preimage T hN.1),hCurrent.trans (closure_mono ?_)⟩
  intro y hy
  refine ⟨hy.1,fun hyOld => hy.2 ?_⟩
  obtain ⟨H,hHO,hyH⟩ := mem_iUnion₂.mp hyOld
  obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hHO
  exact mem_iUnion₂.mpr ⟨strictAlong T H₀,
    List.mem_append_left _ (List.mem_map.mpr ⟨H₀,List.mem_append_left B hH₀,rfl⟩),hyH⟩

end
end Hironaka.HironakaActualCleanupDensityCompactness
