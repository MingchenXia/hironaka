/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPositiveEmptyPrefixHeadValues
import Hironaka.Resolution.HironakaOriginalFiniteLevelCutLowerTests
import Hironaka.Invariant.StepOneRepresentative
/-! Genuine whole relative-ideal geometry precedes all positive head values.
No second cut/TEST, lower DOMAIN, CAN or numerical certificate is input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalRelativeIdealLevelCut
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  MarkedIdealEquivalence.MarkedIdeal ContactRepresentative
  HomogenizedIdealAlong HomogenizedIdealAlongTower InvDomainMemberRestriction
  StepOneValue StepOneValueMasked StepOneLowerDomain StepOneRegime StepOneRepresentative CanonicalCentres
  HironakaOriginalFiniteLevelCutLowerTests HironakaOriginalPositiveEmptyPrefixHeadValues
variable {n : ℕ} {X B Y : CMfd.{u} n}

/-- Actual centre admissibility is transported before ordinary level cuts. -/
theorem level_cut_of_restrictEquiv (M N : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : N.ideal.IsCoherent) (hEq : RestrictEquiv M N)
    (T : BlowupTower X Y) (hT : IsLevelCutTower M T) : IsLevelCutTower N T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    have hWhole := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEq hM.isClosedSubmanifold_N.1 hM.isCoherent hN T
    have hFacts := restrictEquiv_facts hM hN hEq T
    refine ⟨ih hT.1,(hWhole.2 C).mp hT.2.1,?_⟩
    intro y hy hns hp c hc
    have hyM : y∈(geoTransformAlong M T).cosupp := by rw [hWhole.1];exact hy
    have hnsM : ¬IsSpecial M T y := fun h => hns ((hFacts.2.2.2 y).2.1.mp h)
    have hlY := (hFacts.2.2.2 y).1
    have hlC := (hFacts.2.2.2 c).1
    rw [←hlY,←hlC]
    exact hT.2.2 y hyM hnsM (by rwa [hlY]) c hc

/-- Equality concerns the ENTIRE true positive mask, at all actual points. -/
theorem maskA_of_restrictEquiv (M N : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : N.ideal.IsCoherent) (hEq : RestrictEquiv M N)
    (H : BlowupTower X B) (z : B) : maskA M H z=maskA N H z := by
  have hFacts := restrictEquiv_facts hM hN hEq H
  have hO := ContactLowerValue.origMembers_restrictEquiv hEq H
  apply Opens.ext
  show interior _=interior _
  congr 1
  ext y
  simp only [mem_ofPred_eq]
  rw [hO,(hFacts.2.2.2 y).1,(hFacts.2.2.2 z).1,(hFacts.2.2.2 y).2.1]

/-- Genuine member-reference equivalence gives ALL-depth positive lower
values on ANY actual tail, with no lower TEST or canonicality assumption. -/
theorem positive_lower_values_of_restrictEquiv (hn : 0<n) (q s : ℕ)
    (M N : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : N.ideal.IsCoherent)
    (hEq : RestrictEquiv M N) (H : BlowupTower X B)
    (hHead : IsGeoTestTower (barMarked M) H) (T : BlowupTower B Y) (z : Y) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn q) M (lowerMarkedM M) (s+1) H T z=
      Seq.StepOneValueMasked.lowerValueL (invFamily hn q) N (lowerMarkedM N) (s+1) H T z := by
  have hNWF : N.IsWellFormed := by
    refine ⟨hEq.N_eq ▸ hM.isClosedSubmanifold_N,hN,hEq.E_eq ▸ hM.isSNCDivisor,?_⟩
    rw [←hEq.N_eq,←hEq.E_eq]
    exact hM.isTransverse
  have hFacts := restrictEquiv_facts hM hN hEq H
  have hHeadN := hFacts.2.2.1.mp hHead
  have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked M hM) H hHead
  have hWFN := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked N hNWF) H hHeadN
  have hMember := MemberRestrictTowerIso.restrictEquiv_memberRestrict_membersThrough hM hN hEq H (T.proj z)
  exact masked_full_values_congr hn q _ _ (isWellFormed_memberRestrict hn hWF _)
    (isWellFormed_memberRestrict hn hWFN _) hMember (maskA_of_restrictEquiv M N hM hN hEq H (T.proj z)) T z

end
end Hironaka.HironakaOriginalRelativeIdealLevelCut
