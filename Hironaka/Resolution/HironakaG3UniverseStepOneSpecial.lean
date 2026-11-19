import Hironaka.Resolution.HironakaG3UniverseStepOneLevel
import Hironaka.Resolution.HironakaG3UniverseCodimOne
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.Invariant.CanonicalCentres
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseStepOneSpecial
open Set Function TopologicalSpace Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneLowerDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseMarkedCosupport G3UniverseCodimOne G3UniverseStepOneLevel MemberInterLocusAlong
  CodimOneSupportAlong MarkedIdealRestrictOpen
open scoped Topology Manifold ContDiff
noncomputable section

/-- Special-locus transport assuming the literal transformed bar-record dictionary. -/
theorem isSpecial_liftTower_of_bar_history {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (hbar : geoTransformAlong (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T) =
      markedPullback (m := n) (liftDiffeomorph.{u} Y).symm (geoTransformAlong (barMarked M) T))
    (y : liftCMfd.{u} Y) :
    IsSpecial (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y ↔
      IsSpecial M T ((liftDiffeomorph.{u} Y).symm y) := by
  have hJ := StepOneLowerDomain.isWellFormed_barMarked M hM
  obtain ⟨_,hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  have hl := level_liftTower_barTest M hM T hT y
  have hO := origMembers_liftTower_barTest M hM T hT
  have hc := markedPullback_cosupp_diffeo (liftDiffeomorph.{u} Y).symm (geoTransformAlong (barMarked M) T) hcT
  have hcod := codimOne_lifted_record Y (geoTransformAlong (barMarked M) T) hcT
  have hmem := memberInterLocus_preimage ((liftDiffeomorph.{u} Y).symm : liftCMfd.{u} Y → Y)
    (fun z => (liftDiffeomorph.{u} Y).symm.toHomeomorph.map_nhds_eq z)
    (geoTransformAlong (barMarked M) T).N (origMembers M T) (geoTransformAlong (barMarked M) T).cosupp
  unfold IsSpecial
  rw [hl,hO,hbar]
  refine or_congr (and_congr_right fun _ => ?_) (and_congr_right fun _ => ?_)
  · change y ∈ codimOnePartAlong (markedPullback (m := n) (liftDiffeomorph.{u} Y).symm (geoTransformAlong (barMarked M) T)).N
      (markedPullback (m := n) (liftDiffeomorph.{u} Y).symm (geoTransformAlong (barMarked M) T)).ideal
      (geoTransformAlong (barMarked M) T).d ↔ _
    rw [hcod]
    rfl
  · rw [hc]
    change y ∈ memberInterLocus ((liftDiffeomorph.{u} Y).symm ⁻¹' (geoTransformAlong (barMarked M) T).N)
      ((origMembers M T).map ((liftDiffeomorph.{u} Y).symm ⁻¹' ·))
      ((liftDiffeomorph.{u} Y).symm ⁻¹' (geoTransformAlong (barMarked M) T).cosupp) ↔ _
    rw [hmem]
    rfl

/-- Base bar-record naturality supplies its actual transformed history identity. -/
theorem bar_history_of_base {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (hbar : barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) =
      markedPullback (m := n) (liftDiffeomorph.{u} X).symm (barMarked M)) :
    geoTransformAlong (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T) =
      markedPullback (m := n) (liftDiffeomorph.{u} Y).symm (geoTransformAlong (barMarked M) T) := by
  rw [hbar]
  exact HironakaG3UniverseLiftedMarkedHistory.liftTower_geoTransformAlong (barMarked M)
    (StepOneLowerDomain.isWellFormed_barMarked M hM) T hT

/-- Step One's full regime agrees, conditional only on base bar-record naturality. -/
theorem stepRegime_liftTower_of_bar_base {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (hbar : barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) =
      markedPullback (m := n) (liftDiffeomorph.{u} X).symm (barMarked M))
    (s : ℕ) (y : liftCMfd.{u} Y) :
    stepRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) s (liftTower.{u} T) y ↔
      stepRegime M s T ((liftDiffeomorph.{u} Y).symm y) := by
  unfold stepRegime
  rw [level_liftTower_barTest M hM T hT y,
    isSpecial_liftTower_of_bar_history M hM T hT (bar_history_of_base M hM T hT hbar) y]

/-- At a special point Step One values agree, conditional on base bar-record naturality. -/
theorem stepOneInvM_lifted_special_of_bar_base {n r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (hbar : barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) =
      markedPullback (m := n) (liftDiffeomorph.{u} X).symm (barMarked M))
    (y : liftCMfd.{u} Y) (hs : IsSpecial M T ((liftDiffeomorph.{u} Y).symm y)) :
    Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily.{u} hn r)
      (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y =
    Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily.{0} hn r) M T ((liftDiffeomorph.{u} Y).symm y) := by
  classical
  have hs' : IsSpecial (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y :=
    (isSpecial_liftTower_of_bar_history M hM T hT (bar_history_of_base M hM T hT hbar) y).mpr hs
  simp only [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL, if_pos hs', if_pos hs,
    level_liftTower_barTest M hM T hT y]
end
end Hironaka.G3UniverseStepOneSpecial

