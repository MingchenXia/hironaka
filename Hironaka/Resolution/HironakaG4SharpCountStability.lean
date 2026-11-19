import Hironaka.Resolution.HironakaG4CompactOpenServicePrefix
import Hironaka.Analytic.TowerPreimageCompact
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4SharpCountStability
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower MemberInterTowerAlong MemberInterLocusAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower TowerPreimageCompact
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4SharpBadFootprint
open ResolutionInvariantSpec (countCentresMeeting)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Any final sharp condition restricts to the actual appended tail. -/
theorem sharp_tail_of_append (N : Set X) (E : List (Set X)) (T : BlowupTower X Y) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z), CurrentSharpCentres N E (T.append S) →
      CurrentSharpCentres (strictAlong T N)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E S
  | _, .refl, _ => trivial
  | _, .step S C π hπ, h => by
    refine ⟨sharp_tail_of_append N E T S h.1, ?_⟩
    have hstep := h.2
    rw [strictAlong_append T N S,geoTransformAlong_append,
      template_current (univ : Set X) E T,strict_univ T] at hstep
    exact hstep

theorem count_zero_of_centresOver_disjoint {A B : Set X} (hAB : Disjoint A B) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver B T → countCentresMeeting A T = 0
  | _,.refl,_ => rfl
  | _,.step T C π hπ,h => by
    classical
    have hc : ¬ (C ∩ T.proj ⁻¹' A).Nonempty := by
      rintro ⟨z,hzC,hzA⟩
      exact (disjoint_left.mp hAB) hzA (h.2 hzC)
    change countCentresMeeting A T + (if (C ∩ T.proj ⁻¹' A).Nonempty then 1 else 0) = 0
    rw [count_zero_of_centresOver_disjoint hAB T h.1,if_neg hc]

/-- Once a compact task is resolved, no later sharp tail adds centres over it. -/
theorem count_append_eq_of_sharp_resolved
    {W : Set X} {E : List (Set X)} (hW : IsClosed W) (hE : ∀ H ∈ E, IsClosed H)
    (T : BlowupTower X Y) (S : BlowupTower Y Z) (hSharp : CurrentSharpCentres W E (T.append S))
    (L : Set X) (hGood : ∀ z ∈ strictAlong T W, T.proj z ∈ L →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z) :
    countCentresMeeting L (T.append S) = countCentresMeeting L T := by
  let N := strictAlong T W
  let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
  have hN : IsClosed N := isClosed_strictAlong T hW
  have hF : ∀ H ∈ F, IsClosed H :=
    HironakaPrincipalization.isClosed_of_mem_E_geoTransformAlong
      (geometricTemplate (univ : Set X) E) hE T
  have hS := sharp_tail_of_append W E T S hSharp
  obtain ⟨_,hOver⟩ := currentSharpCentres_original_footprint hN hF S hS
  have hDis : Disjoint (T.proj ⁻¹' L) (originalSharpBadLocus (n := n) N F) := by
    apply disjoint_left.mpr
    intro z hzL hzBad
    exact hzBad.2 (hGood z hzBad.1 hzL)
  rw [countCentresMeeting_append, count_zero_of_centresOver_disjoint hDis S hOver, add_zero]
end
end Hironaka.HironakaG4SharpCountStability
