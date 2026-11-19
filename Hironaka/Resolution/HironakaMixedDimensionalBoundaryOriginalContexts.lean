import Hironaka.Resolution.HironakaOriginalNCMarkedStratumBranchHistory
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.NormalCrossingsInvariance

/-!
# Returning a nested joint chart to the same original branch context

One fixed original U/B is rebased along an actual head. Its legitimate current
branch context is derived from the actual terminal-datum and union identities.
An actual restriction-concatenation tower isomorphism then transports the whole
joint chart back to the direct original open. No all-current-context packet is
inferred from an original-context family.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaMixedDimensionalBoundaryOriginalContexts

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings NormalCrossingsInvariance HironakaOriginalOldBranchOpenHistory
  GermIdealPullbackCalculus MemberInterTowerAlong MemberInterLocusAlong HomogenizedGlueingTower

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The exact single original branch context, with every ordered boundary entry,
is retained through the actual restriction-concatenation isomorphism. -/
theorem original_branch_joint_chart_append
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (H : Set X) (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hP : IsGeoTestTower M P) (hHistoryP : IsOriginalBranchTestTower M H P)
    (hHistoryQ : IsOriginalBranchTestTower (geoTransformAlong M P) (strictAlong P H) Q)
    (U : Opens X) (B : List (Set U))
    (hB : IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E))
    (hUnion : (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A)) (S : Set Z)
    (hJoint :
      let V := openPreimage P U
      let BP := B.map (strictAlong (restrict U P))
      let MP := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong M P)
      HasNormalCrossings n ((Subtype.val : openPreimage Q V → Z) ⁻¹' S)
        (BP.map (strictAlong (restrict V Q)) ++ (geoTransformAlong MP (restrict V Q)).E)) :
    HasNormalCrossings n ((Subtype.val : openPreimage (P.append Q) U → Z) ⁻¹' S)
      (B.map (strictAlong (restrict U (P.append Q))) ++
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M)
          (restrict U (P.append Q))).E) := by
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let A : MarkedIdeal n U := { MU with E := B ++ MU.E }
  let PU := restrict U P
  let V := openPreimage P U
  let BP := B.map (strictAlong PU)
  let MP := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong M P)
  let QV := restrict V Q
  have hAP : IsGeoTestTower A PU := hHistoryP U B hB hUnion
  have hAN : A.N = univ := by
    change (Subtype.val : U → X) ⁻¹' M.N = univ
    rw [hN, preimage_univ]
  have hAI : A.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hM.isCoherent
  have hAWF : A.IsWellFormed := by
    refine ⟨?_, hAI, hB, ?_⟩
    · rw [hAN]
      exact ⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
    · rw [hAN]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hB
  have hCurrent : geoTransformAlong A PU = ({ MP with E := BP ++ MP.E } : MarkedIdeal n V) :=
    original_branch_terminal_datum M hM.isClosedSubmanifold_N hM.isCoherent P hP U B
  have hSNCP : IsSNCDivisor n (BP ++ MP.E) := by
    have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hAWF PU hAP
    have hSNC := hWF.isSNCDivisor
    rw [hCurrent] at hSNC
    exact hSNC
  have hUnionP : (Subtype.val : V → Y) ⁻¹' strictAlong P H = (⋃ C ∈ BP, C) := by
    rw [← strictAlong_restrict U P H, hUnion]
    exact strictAlong_original_branch_union PU B
  have hTail := hHistoryQ V BP hSNCP hUnionP
  rw [← hCurrent] at hTail
  have hConcat : IsGeoTestTower A (PU.append QV) :=
    (isGeoTestTower_append_iff A PU QV).mpr ⟨hAP, hTail⟩
  let χ := opensCongr (n := n) (openPreimage_append P Q U).symm
  have hIso := isTowerIso_restrict_append U P Q
  have hDatum := BlowupTowerIsomorphism.IsTowerIso.geoTransformAlong_eq
    (X := CMfd.of (n := n) U) (X' := CMfd.of (n := n) U) (𝔪 := A)
    (T := PU.append QV) (T' := restrict U (P.append Q)) (χ := χ)
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) U ∞) hAWF.isClosedSubmanifold_N hAI hIso hConcat
  change geoTransformAlong (MarkedIdeal.pullback (id : U → U) A) (restrict U (P.append Q)) =
    MarkedIdeal.pullback χ (geoTransformAlong A (PU.append QV)) at hDatum
  have hId : MarkedIdeal.pullback (id : U → U) A = A :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl
      (show A.E.map (fun C => (id : U → U) ⁻¹' C) = A.E by simp)
      (BlowupControlledTransform.pullback_id hAI) rfl
  rw [hId] at hDatum
  have hEIso := congrArg (fun L : MarkedIdeal n (openPreimage (P.append Q) U) => L.E) hDatum
  have hDirect := entire_original_old_retained_boundary MU B (restrict U (P.append Q))
  have hNested : (geoTransformAlong A (PU.append QV)).E =
      BP.map (strictAlong QV) ++ (geoTransformAlong MP QV).E := by
    rw [geoTransformAlong_append, hCurrent]
    exact entire_original_old_retained_boundary MP BP QV
  change (geoTransformAlong A (restrict U (P.append Q))).E =
    (geoTransformAlong A (PU.append QV)).E.map (χ ⁻¹' ·) at hEIso
  rw [hDirect, hNested] at hEIso
  change HasNormalCrossings n ((Subtype.val : openPreimage Q V → Z) ⁻¹' S)
    (BP.map (strictAlong QV) ++ (geoTransformAlong MP QV).E) at hJoint
  have hχ : PullsBackCoordinates n χ :=
    pullsBackCoordinates_of_forall_notMem_exceptionalLocus χ.contMDiff
      (fun z => MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
        χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply z)
  have hPull := NormalCrossingsInvariance.hasNormalCrossings_preimage hχ hJoint
  have hSet : χ ⁻¹' ((Subtype.val : openPreimage Q V → Z) ⁻¹' S) =
      (Subtype.val : openPreimage (P.append Q) U → Z) ⁻¹' S := by
    ext z
    rfl
  rw [hSet, ← hEIso] at hPull
  exact hPull

end

end Hironaka.HironakaMixedDimensionalBoundaryOriginalContexts
