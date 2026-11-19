import Hironaka.Resolution.HironakaOriginalOldBranchOpenTransport
import Hironaka.Blowup.BlowupTowerIsoTail

set_option autoImplicit false

/-!
# Concatenating actual original-branch histories

The current presentation passed to the second phase is the literal strict
transform of the first phase's original branch list. The controlled ideal,
marking, retained boundary and every born slot belong to the SAME towers.
The first tower's ordinary testness is an actual algorithm output, explicitly
retained rather than inferred from a potentially vacuous universal predicate.

Blueprint: `hir:original-old-branch-append-universal-history`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalOldBranchOpenHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealPullbackCalculus HomogenizedGlueingTower MemberInterTowerAlong DropMembers

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

private theorem strictAlong_empty_original :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → strictAlong T (∅ : Set X) = ∅
  | _, .refl => rfl
  | _, .step T C π hπ => by
    rw [strictAlong_step, strictAlong_empty_original T]
    exact geoStrictTransform_eq_empty_of_subset (empty_subset C)

/-- Literal finite original branch unions commute with the actual strict transform. -/
theorem strictAlong_original_branch_union {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (B : List (Set X)) : strictAlong T (⋃ A ∈ B, A) = ⋃ A ∈ B.map (strictAlong T), A := by
  have hcons (A : Set X) (L : List (Set X)) : (⋃ C ∈ A :: L, C) = A ∪ (⋃ C ∈ L, C) := by
    ext x
    simp
  have hconsY (A : Set Y) (L : List (Set Y)) : (⋃ C ∈ A :: L, C) = A ∪ (⋃ C ∈ L, C) := by
    ext y
    simp
  induction B with
  | nil => simpa using strictAlong_empty_original T
  | cons A B ih =>
    rw [hcons, MemberInterTowerAlong.strictAlong_union, ih, List.map_cons, hconsY]

/-- The actual terminal augmented datum of the first tower has the literal transformed
original branch block followed by the entire current retained/born boundary. -/
theorem original_branch_terminal_datum (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    {Y : CMfd.{u} n} (P : BlowupTower X Y) (hP : IsGeoTestTower M P)
    (W : Opens X) (B : List (Set W)) :
    let MU := MarkedIdeal.pullback (Subtype.val : W → X) M
    let PW := restrict W P
    let U := openPreimage P W
    geoTransformAlong ({ MU with E := B ++ MU.E } : MarkedIdeal n W) PW =
      ({ MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong M P) with
        E := B.map (strictAlong PW) ++
          (MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong M P)).E } :
            MarkedIdeal n U) := by
  dsimp only
  let MU := MarkedIdeal.pullback (Subtype.val : W → X) M
  have hBase := geoTransformAlong_restrict W hN hI P hP
  obtain ⟨hSameN, hSameI, hSameD⟩ :=
    geoTransformAlong_withE (X := CMfd.of (n := n) W) MU (B ++ MU.E) (restrict W P)
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (hSameN.trans (congrArg (fun A => A.N) hBase)) ?_
    (hSameI.trans (congrArg (fun A => A.ideal) hBase))
    (hSameD.trans (congrArg (fun A => A.d) hBase))
  rw [entire_original_old_retained_boundary (X := CMfd.of (n := n) W) MU B (restrict W P), hBase]

/-- The second phase tests the actual strict transforms of the SAME original branches.
Consequently the actual concatenated tower retains the universal original-branch property. -/
theorem isOriginalBranchTestTower_append (M : MarkedIdeal n X) (hN : M.N = univ)
    (hI : M.ideal.IsCoherent) {H : Set X} {Y Z : CMfd.{u} n}
    (P : BlowupTower X Y) (Q : BlowupTower Y Z) (hP : IsGeoTestTower M P)
    (hHistoryP : IsOriginalBranchTestTower M H P)
    (hHistoryQ : IsOriginalBranchTestTower (geoTransformAlong M P) (strictAlong P H) Q) :
    IsOriginalBranchTestTower M H (P.append Q) := by
  intro W B hSNC hUnion
  let MU := MarkedIdeal.pullback (Subtype.val : W → X) M
  let A : MarkedIdeal n W := { MU with E := B ++ MU.E }
  let PW := restrict W P
  let U := openPreimage P W
  let BP := B.map (strictAlong PW)
  let MP := MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong M P)
  have hNM : IsClosedSubmanifold n M.N := by
    rw [hN]
    exact HomogenizedGlueingTower.isClosedSubmanifold_univ
  have hAP : IsGeoTestTower A PW := hHistoryP W B hSNC hUnion
  have hWFA : A.IsWellFormed := by
    refine ⟨?_, isCoherent_pullback contMDiff_subtype_val hI, hSNC, ?_⟩
    · change IsClosedSubmanifold n ((Subtype.val : W → X) ⁻¹' M.N)
      rw [hN, preimage_univ]
      exact HomogenizedGlueingTower.isClosedSubmanifold_univ
    · change IsTransverse n ((Subtype.val : W → X) ⁻¹' M.N) (B ++ MU.E)
      rw [hN, preimage_univ]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hSNC
  have hCurrent : geoTransformAlong A PW = ({ MP with E := BP ++ MP.E } : MarkedIdeal n U) :=
    original_branch_terminal_datum M hNM hI P hP W B
  have hWFCurrent := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWFA PW hAP
  have hSNCP : IsSNCDivisor n (BP ++ MP.E) := by
    have hBoundary : (geoTransformAlong A PW).E = BP ++ MP.E :=
      congrArg (fun L => L.E) hCurrent
    exact hBoundary ▸ hWFCurrent.isSNCDivisor
  have hUnionP : (Subtype.val : U → Y) ⁻¹' strictAlong P H = ⋃ C ∈ BP, C := by
    rw [← strictAlong_restrict W P H, hUnion]
    exact strictAlong_original_branch_union PW B
  have hTail := hHistoryQ U BP hSNCP hUnionP
  rw [← hCurrent] at hTail
  have hConcat : IsGeoTestTower A (PW.append (restrict U Q)) :=
    (isGeoTestTower_append_iff A PW (restrict U Q)).mpr ⟨hAP, hTail⟩
  have hIso := isTowerIso_restrict_append W P Q
  have hLeft := (IsTowerIso.isGeoTestTower_iff
    (X := CMfd.of (n := n) W) (X' := CMfd.of (n := n) W) (𝔪 := A)
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞)
    hWFA.isClosedSubmanifold_N hWFA.isCoherent hIso).mpr hConcat
  change IsGeoTestTower (MarkedIdeal.pullback (id : W → W) A) (restrict W (P.append Q)) at hLeft
  have hId : MarkedIdeal.pullback (id : W → W) A = A :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl
      (show A.E.map (fun C => (id : W → W) ⁻¹' C) = A.E by simp)
      (BlowupControlledTransform.pullback_id hWFA.isCoherent) rfl
  rw [hId] at hLeft
  exact hLeft

end

end Hironaka.HironakaOriginalOldBranchOpenHistory
