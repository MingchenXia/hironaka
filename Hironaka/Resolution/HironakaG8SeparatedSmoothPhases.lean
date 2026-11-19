import Hironaka.Resolution.HironakaG8SeparatedSmoothGeometry
import Hironaka.Resolution.HironakaSaturatedMarkedPhase
import Hironaka.Resolution.HironakaG3BoundaryRestrictInitialList

/-! Full smooth-boundary centre positions on literal towers, preserved on
adjoining a disjoint protected carrier or joining successive phases. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe u

namespace Hironaka.HironakaG8SeparatedSmoothPhases

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaEmbeddedAnalytic HironakaStageCenters NormalCrossings RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaSharpActualFiniteChronologicalHistory
  HironakaG8SeparatedSmoothGeometry HironakaAdmissibleCalculus HironakaG8UniverseBMTransport
  HironakaCoherentTransformExtension HironakaG4CompactWholeMonomialMaskPhase
  HironakaG3BoundaryRestrictInitialList HironakaG3CentresOverGenericFactor
  HironakaActualProcessedAllMasksDrop HironakaEmbeddedBoundary

/-- The whole current carrier is smooth and the actual centre lies in it
and the full current boundary at each literal prefix. -/
def SmoothBoundaryStages {n : ℕ} {X Y : CMfd.{u} n}
    (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) : Prop :=
  StageCentres (fun P C =>
    (IsClosedSubmanifold n (strictTransform n P.proj W) ∧
      C ⊆ strictTransform n P.proj W ∩ ⋃ H ∈ (geoTransformAlong (geometricTemplate (univ : Set X) E) P).E, H) ∧
    HasNormalCrossings n C (geoTransformAlong (geometricTemplate (univ : Set X) E) P).E) T

/-- The endpoint of a finite smooth-boundary tower with its actual
centre footprint and full ordered transformed boundary. -/
structure SmoothBoundaryTower {n : ℕ} {X Y : CMfd.{u} n}
    (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) : Prop where
  test : IsGeoTestTower (geometricTemplate (univ : Set X) E) T
  footprint : CentresOver (W ∩ ⋃ H ∈ E, H) T
  stages : SmoothBoundaryStages W E T
  smooth : IsClosedSubmanifold n (strictTransform n T.proj W)
  snc : IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
  nc : HasNormalCrossings n (strictTransform n T.proj W)
    (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E

theorem smoothBoundaryStages_bmStages {n : ℕ} {X Y : CMfd.{u} n}
    {W : Set X} {E : List (Set X)} {T : BlowupTower X Y} (h : SmoothBoundaryStages W E T) : BMStages W E T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih => exact ⟨ih h.1, Or.inr h.2.1, h.2.2⟩

/-- A phase on one closed component retains the full smooth centre law
when the disjoint smooth component is adjoined. -/
theorem smoothBoundaryStages_union_of_protected {n : ℕ} {X : CMfd.{u} n} {A B F : Set X}
    (hA : IsClosed A) (hB : IsClosedSubmanifold n B) (hAB : Disjoint A B)
    (hF : IsClosed F) (hFA : F ⊆ A) (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T → CentresOver F T →
      SmoothBoundaryStages A E T → SmoothBoundaryStages (A ∪ B) E T
  | _, .refl, _, _, _ => trivial
  | _, .step P C π hπ, hT, hOver, hStage => by
    refine ⟨smoothBoundaryStages_union_of_protected hA hB hAB hF hFA E hE P hT.1 hOver.1 hStage.1, ?_⟩
    obtain ⟨_, hBP, hSep, _, _, _⟩ := protected_smooth_part hA hB hAB hF hFA
      (geometricTemplate (univ : Set X) E) hE.1 P hT.1 hOver.1
    change (IsClosedSubmanifold n (strictTransform n P.proj (A ∪ B)) ∧
      C ⊆ strictTransform n P.proj (A ∪ B) ∩ ⋃ H ∈
        (geoTransformAlong (geometricTemplate (univ : Set X) E) P).E, H) ∧
      HasNormalCrossings n C (geoTransformAlong (geometricTemplate (univ : Set X) E) P).E
    rw [strictTransform_union]
    exact ⟨⟨closedSubmanifold_union_disjoint hStage.2.1.1 hBP hSep,
      fun y hy => ⟨Or.inl (hStage.2.1.2 hy).1, (hStage.2.1.2 hy).2⟩⟩, hStage.2.2⟩

/-- A terminal phase on one part yields a terminal phase on its union
with a disjoint part already in normal crossings with the boundary. -/
theorem SmoothBoundaryTower.union_of_protected {n : ℕ} {X Y : CMfd.{u} n} {A B : Set X}
    (hA : IsClosed A) (hB : IsClosedSubmanifold n B) (hAB : Disjoint A B)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hBN : HasNormalCrossings n B E)
    {T : BlowupTower X Y} (h : SmoothBoundaryTower A E T) : SmoothBoundaryTower (A ∪ B) E T := by
  let F := A ∩ ⋃ H ∈ E, H
  have hF : IsClosed F := hA.inter (isClosed_biUnion_of_forall_isClosed hE.1)
  obtain ⟨_, hBP, hSep, _, _, hNCB⟩ := protected_smooth_part hA hB hAB hF inter_subset_left
    (geometricTemplate (univ : Set X) E) hE.1 T h.test h.footprint
  have hSmooth : IsClosedSubmanifold n (strictTransform n T.proj (A ∪ B)) := by
    rw [strictTransform_union]
    exact closedSubmanifold_union_disjoint h.smooth hBP hSep
  have hNC : HasNormalCrossings n (strictTransform n T.proj (A ∪ B))
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E := by
    rw [strictTransform_union]
    exact normalCrossings_union_disjoint isClosed_closure isClosed_closure hSep h.nc (hNCB hBN)
  have hFsub : F ⊆ (A ∪ B) ∩ ⋃ H ∈ E, H := fun _ h => ⟨Or.inl h.1, h.2⟩
  exact ⟨h.test, centresOver_mono_local hFsub T h.footprint,
    smoothBoundaryStages_union_of_protected hA hB hAB hF inter_subset_left E hE T h.test h.footprint h.stages,
    hSmooth, h.snc, hNC⟩

/-- Concatenating two actual smooth phases retains every literal centre
condition and carries the full ordered boundary through their join. -/
theorem smoothBoundaryStages_append {n : ℕ} {X Y : CMfd.{u} n}
    (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (hT : SmoothBoundaryStages W E T) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),
      SmoothBoundaryStages (strictTransform n T.proj W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E S →
      SmoothBoundaryStages W E (T.append S)
  | _, .refl, _ => hT
  | _, .step S C π hπ, hS => by
    refine ⟨smoothBoundaryStages_append W E T hT S hS.1, ?_⟩
    let M := geometricTemplate (univ : Set X) E
    let N := geometricTemplate (univ : Set Y) (geoTransformAlong M T).E
    change (IsClosedSubmanifold n (strictTransform n (T.append S).proj W) ∧
      C ⊆ strictTransform n (T.append S).proj W ∩ ⋃ H ∈ (geoTransformAlong M (T.append S)).E, H) ∧
      HasNormalCrossings n C (geoTransformAlong M (T.append S)).E
    rw [BlowupTower.proj_append, StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj,
      geoTransformAlong_append, geoTransformAlong_E_eq_of_E_eq (𝔍 := geoTransformAlong M T) (𝔪 := N) rfl S]
    exact hS.2

end Hironaka.HironakaG8SeparatedSmoothPhases
