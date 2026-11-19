import Hironaka.Resolution.HironakaG8TerminalNativeSNC
import Hironaka.Resolution.HironakaOriginalBoundaryCanonicalPrincipalization
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix
import Hironaka.Resolution.HironakaG8BFamilyPad
import Hironaka.Resolution.HironakaG3SNCListPermutation

/-! The whole ordered boundary and SNC geometry on an untouched current open. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CleanOpenProtection
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaEmbeddedBoundary RestrictEmptyTower ResolutionInvariantExt
  HironakaOriginalBoundaryCanonicalPrincipalization HironakaOriginalEmptyHeadPrefix
  HironakaG3BoundaryRestrictInitialList MarkedIdealTowerTransport
  NormalCrossings NormalCrossingsInvariance HironakaG8BFamilyPad HironakaG3SNCListPermutation
  HironakaOriginalStoppedBoundaryTransport HironakaNormalCrossingsTransversality
  HironakaStageCenters HironakaG8IntrinsicSingularBlockSchedule HironakaActualSmoothBoundaryCleanup
  HironakaNormalCrossingsOpenRestrictionSeparation

/-- A later history missing the open has one actual local biholomorphism
for the strict carrier and every boundary position, including empty births. -/
theorem clean_open_of_avoiding_history {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (O : Opens X) (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (hAvoid : CentresAvoid O T)
    (hW : IsClosedSubmanifold n ((Subtype.val : O → X) ⁻¹' W))
    (hE : IsSNCDivisor n (M.E.map ((Subtype.val : O → X) ⁻¹' ·)))
    (hNC : HasNormalCrossings n ((Subtype.val : O → X) ⁻¹' W)
      (M.E.map ((Subtype.val : O → X) ⁻¹' ·)))
    (hDense : ((Subtype.val : O → X) ⁻¹' W) ⊆ closure
      (((Subtype.val : O → X) ⁻¹' W) \ ⋃ H ∈ M.E.map ((Subtype.val : O → X) ⁻¹' ·), H)) :
    let Q := openPreimage T O
    let WO := (Subtype.val : O → X) ⁻¹' W
    let EO := M.E.map ((Subtype.val : O → X) ⁻¹' ·)
    let V := (Subtype.val : Q → Y) ⁻¹' strictTransform n T.proj W
    let F := (geoTransformAlong M T).E.map ((Subtype.val : Q → Y) ⁻¹' ·)
    ∃ β : CMfd.of (n := n) Q ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) O,
      (∀ z, β z = (restrict O T).proj z) ∧ V = β ⁻¹' WO ∧
      F = EO.map (β ⁻¹' ·) ++ List.replicate T.length ∅ ∧
      IsClosedSubmanifold n V ∧ IsSNCDivisor n F ∧ HasNormalCrossings n V F ∧ IsTransverse n V F := by
  classical
  intro Q WO EO V F
  let P := restrict O T
  let M₀ := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → X) M
  have hEmpty : IsEmptyTower P := (isEmptyTower_restrict_iff O T).mpr hAvoid
  obtain ⟨β,hβ⟩ := HironakaOriginalEmptyHeadPrefix.exists_empty_tower_projection P hEmpty
  have hProj : (β : Q → O) = P.proj := funext hβ
  have hExc (z : Q) : z ∉ exceptionalLocus n β :=
    MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
      β.contMDiff β.symm.contMDiff β.apply_symm_apply β.symm_apply_apply z
  have hExcEmpty : exceptionalLocus n β = ∅ := eq_empty_iff_forall_notMem.mpr hExc
  have hV : V = β ⁻¹' WO := by
    change ((Subtype.val : Q → Y) ⁻¹' strictTransform n T.proj W) = _
    rw [← strictTransform_restricted_tower O T W,← show (β : Q → O) = (restrict O T).proj from hProj]
    simp only [strictTransform,hExcEmpty,sdiff_empty,(hW.1.preimage β.continuous).closure_eq]
    rfl
  have hB := boundary_restrict_of_initial_eq M O M₀ rfl T
  have hClosed : ∀ H ∈ M₀.E, IsClosed H := hE.1
  rw [boundary_of_all_empty_tower M₀ hClosed P hEmpty,← hProj,
    show P.length = T.length from length_restrict O T] at hB
  have hF : F = EO.map (β ⁻¹' ·) ++ List.replicate T.length ∅ := hB.symm
  have hCoord : PullsBackCoordinates n (β : Q → O) :=
    pullsBackCoordinates_of_forall_notMem_exceptionalLocus β.contMDiff hExc
  have hNC₁ : HasNormalCrossings n (β ⁻¹' WO) (EO.map (β ⁻¹' ·)) :=
    hasNormalCrossings_preimage hCoord hNC
  have hNC₂ : HasNormalCrossings n V F := by
    rw [hV,hF]
    apply (hasNormalCrossings_filter_nonempty_iff _ _).mp
    simpa using (hasNormalCrossings_filter_nonempty_iff _ _).mpr hNC₁
  have hSNC₁ : IsSNCDivisor n (EO.map (β ⁻¹' ·)) :=
    isSNCDivisor_map_preimage hCoord β.continuous hE
  have hSNC₂ : IsSNCDivisor n F := by
    rw [hF]
    exact isSNCDivisor_of_perm ((isSNCDivisor_replicate_empty_append_iff T.length).mpr hSNC₁)
      List.perm_append_comm
  have hDense₂ : V ⊆ closure (V \ ⋃ H ∈ F, H) := by
    have hUnion : (⋃ H ∈ F, H) = ⋃ H ∈ EO.map (β ⁻¹' ·), H := by
      rw [hF]
      ext x
      simp only [mem_iUnion, List.mem_append]
      constructor
      · rintro ⟨H,hH,hx⟩
        rcases hH with hH | hH
        · exact ⟨H,hH,hx⟩
        · have he : H = ∅ := (List.mem_replicate.mp hH).2
          exact (he ▸ hx).elim
      · rintro ⟨H,hH,hx⟩
        exact ⟨H,Or.inl hH,hx⟩
    rw [hV,hUnion,← preimage_biUnion_list,← preimage_sdiff]
    have hCl : β ⁻¹' closure (WO \ ⋃ H ∈ EO, H) = closure (β ⁻¹' (WO \ ⋃ H ∈ EO, H)) :=
      β.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage β.continuous _
    rw [← hCl]
    exact preimage_mono hDense
  have hSmooth : IsClosedSubmanifold n V := by
    rw [hV]
    exact (isClosedSubmanifold_preimage_iff β).mpr hW
  exact ⟨β,hβ,hV,hF,hSmooth,hSNC₂,hNC₂,
    isTransverse_of_hasNormalCrossings_of_subset_closure_diff hNC₂ hDense₂⟩

/-- Intrinsic singular centres miss every previously cleaned smooth open;
no additional avoidance hypothesis is needed for such later stages. -/
theorem clean_open_of_singular_history {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (hAnalytic : IsComplexAnalyticSubset (n := n) W) (O : Opens X) (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hW : IsClosedSubmanifold n ((Subtype.val : O → X) ⁻¹' W))
    (hE : IsSNCDivisor n (M.E.map ((Subtype.val : O → X) ⁻¹' ·)))
    (hNC : HasNormalCrossings n ((Subtype.val : O → X) ⁻¹' W)
      (M.E.map ((Subtype.val : O → X) ⁻¹' ·)))
    (hDense : ((Subtype.val : O → X) ⁻¹' W) ⊆ closure
      (((Subtype.val : O → X) ⁻¹' W) \ ⋃ H ∈ M.E.map ((Subtype.val : O → X) ⁻¹' ·), H)) :
    let Q := openPreimage T O
    let WO := (Subtype.val : O → X) ⁻¹' W
    let EO := M.E.map ((Subtype.val : O → X) ⁻¹' ·)
    let V := (Subtype.val : Q → Y) ⁻¹' strictTransform n T.proj W
    let F := (geoTransformAlong M T).E.map ((Subtype.val : Q → Y) ⁻¹' ·)
    ∃ β : CMfd.of (n := n) Q ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) O,
      (∀ z, β z = (restrict O T).proj z) ∧ V = β ⁻¹' WO ∧
      F = EO.map (β ⁻¹' ·) ++ List.replicate T.length ∅ ∧
      IsClosedSubmanifold n V ∧ IsSNCDivisor n F ∧ HasNormalCrossings n V F ∧ IsTransverse n V F := by
  have hReg : Disjoint (singularSet (n := n) W) (O : Set X) := by
    apply disjoint_left.mpr
    intro x hx hO
    let z : O := ⟨x,hO⟩
    obtain ⟨d,hd⟩ := hW.2 z (mem_singularSet_iff.mp hx).1
    exact (mem_singularSet_iff.mp hx).2 d (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hd)
  exact clean_open_of_avoiding_history W O M T
    (intrinsic_singular_history_avoids_regular_open hAnalytic O hReg T hStage) hW hE hNC hDense

/-- A clean open on an actual accumulated prefix remains clean after
any subsequent intrinsic-singular block, with the full original ordered
boundary computed on the appended physical tower. -/
theorem clean_open_after_original_append {n : ℕ} {X Y Z : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (M : MarkedIdeal n X)
    (P : BlowupTower X Y) (O : Opens Y) (T : BlowupTower Y Z) :
    let U := strictTransform n P.proj W
    let B := (geoTransformAlong M P).E.map ((Subtype.val : O → Y) ⁻¹' ·)
    let C := (Subtype.val : O → Y) ⁻¹' U
    StageCentres (fun S K => K ⊆ singularSet (n := n) (strictTransform n S.proj U)) T →
    IsClosedSubmanifold n C → IsSNCDivisor n B → HasNormalCrossings n C B →
    C ⊆ closure (C \ ⋃ H ∈ B, H) →
    let Q := openPreimage T O
    let F := (geoTransformAlong M (P.append T)).E.map ((Subtype.val : Q → Z) ⁻¹' ·)
    let V := (Subtype.val : Q → Z) ⁻¹' strictTransform n (P.append T).proj W
    ∃ β : CMfd.of (n := n) Q ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) O,
      (∀ z, β z = (restrict O T).proj z) ∧ V = β ⁻¹' C ∧
      F = B.map (β ⁻¹' ·) ++ List.replicate T.length ∅ ∧
      IsClosedSubmanifold n V ∧ IsSNCDivisor n F ∧ HasNormalCrossings n V F ∧ IsTransverse n V F := by
  intro U B C hStages hClean hSNC hNC hDense Q F V
  have hA := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW P
  have hResult := clean_open_of_singular_history U hA O (geoTransformAlong M P) T
    hStages hClean hSNC hNC hDense
  simpa only [F,V,geoTransformAlong_append,BlowupTower.proj_append,
    StrictTransformComposition.strictTransform_comp P.contMDiff_proj T.contMDiff_proj] using hResult

#print axioms clean_open_after_original_append
#print axioms clean_open_of_singular_history
#print axioms clean_open_of_avoiding_history

end
end Hironaka.HironakaG8CleanOpenProtection
