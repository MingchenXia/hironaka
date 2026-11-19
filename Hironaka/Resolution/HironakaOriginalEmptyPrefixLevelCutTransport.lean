/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteLevelCutLowerTests
import Hironaka.Invariant.StepOneEmptyPrefix
/-! Original level-cut transport constructs actual source current lower
geometry before any empty-prefix numeric or canonicality comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalEmptyPrefixLevelCutTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneEmptyPrefix StepOneValue
  StepOneValueMasked StepOneLowerDomain StepOneRegime StepOneCanonicalTail
  InvDomainTowerAlong CanonicalCentres HironakaOriginalFrozenRecursiveLower
  HironakaOriginalFiniteLevelCutLowerTests
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Real source admissibility and ONLY true original levels construct
all source recipe steps, before any FULL-value or CAN transport. -/
theorem level_cut_tail_of_empty_prefix (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hd : 1≤M.d) (P : BlowupTower X A) (hP : IsEmptyTower P)
    (T : BlowupTower A Y) (hT : IsLevelCutTower M (P.append T)) :
    IsLevelCutTower (geoTransformAlong M P) T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    have hPrev : IsLevelCutTower M (P.append T) := hT.1
    have hOldTest := levelCutTower_geoTest M (P.append T) hPrev
    have he := coeff_homAlong_wEquiv M hM.isClosedSubmanifold_N hM.isCoherent hd
    have hBar := (he.2 (P.append T)).1.mpr hOldTest
    refine ⟨ih hPrev,?_,?_⟩
    · simpa only [geoTransformAlong_append] using hT.2.1
    · intro y hy hns hp c hc
      have hyOld : y∈(geoTransformAlong M (P.append T)).cosupp := by
        simpa only [geoTransformAlong_append] using hy
      have hnsOld : ¬IsSpecial M (P.append T) y :=
        fun h => hns ((isSpecial_emptyPrefix_iff M hM hd P hP T hBar y).mpr h)
      have hpOld : 0<level M (P.append T) y := by
        rwa [level_emptyPrefix M P hP T y] at hp
      rw [level_emptyPrefix M P hP T y,level_emptyPrefix M P hP T c]
      exact hT.2.2 y hyOld hnsOld hpOld c hc

/-- The actual computed source lower DOMAIN/TEST/point/whole cosupport
are internally supplied from ONLY original level cuts and geometry. -/
theorem empty_prefix_current_lower_data (hn : 0<n) (b : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (b+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (T : BlowupTower A Y)
    (hT : IsLevelCutTower M (P.append T)) (z : Y)
    (hz : z∈(geoTransformAlong M (P.append T)).cosupp) (hns : ¬IsSpecial M (P.append T) z) :
    let MP := geoTransformAlong M P
    IsInvDomain (b+1) MP ∧ IsMaximalOrderAlong MP.N MP.ideal MP.d ∧ IsLevelCutTower MP T ∧
      IsInvDomain b (lowerAt MP T z) ∧ IsGeoTestTower (lowerAt MP T z) (lowerTailAt MP T z) ∧
      IsInvDomain b (geoTransformAlong (lowerAt MP T z) (lowerTailAt MP T z)) ∧
      ∃ hp : z∈patchAt MP T z,
        (⟨z,hp⟩ : patchAt MP T z)∈(geoTransformAlong (lowerAt MP T z) (lowerTailAt MP T z)).cosupp ∧
        ∀ p : patchAt MP T z,p∈(geoTransformAlong (lowerAt MP T z) (lowerTailAt MP T z)).cosupp ↔
          p.val∈(geoTransformAlong MP T).cosupp ∧ level MP T p.val=level MP T z := by
  have hPt : IsGeoTestTower M P := isGeoTestTower_of_isEmptyTower M P hP
  have hDom := isInvDomain_geoTransformAlong hM P hPt
  have hMax := isMaximalOrderAlong_geoTransformAlong hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hmax P hPt
  have hLevel := level_cut_tail_of_empty_prefix M hM.isWellFormed hM.one_le_d P hP T hT
  have hzSource : z∈(geoTransformAlong (geoTransformAlong M P) T).cosupp := by
    simpa only [geoTransformAlong_append] using hz
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar := (he.2 (P.append T)).1.mpr (levelCutTower_geoTest M (P.append T) hT)
  have hnsSource : ¬IsSpecial (geoTransformAlong M P) T z :=
    fun h => hns ((isSpecial_emptyPrefix_iff M hM.isWellFormed hM.one_le_d P hP T hBar z).mp h)
  exact ⟨hDom,hMax,hLevel,levelCutTower_current_lower_data hn _ hDom hMax T hLevel z hzSource hnsSource⟩

end
end Hironaka.HironakaOriginalEmptyPrefixLevelCutTransport
