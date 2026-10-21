/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOpenCarrierTestTowerExtension
import Hironaka.Resolution.HironakaOriginalWholeContactRemainderDomain
import Hironaka.Resolution.HironakaNormalCrossingsIntrinsicStratumCentre
import Hironaka.MarkedIdeal.CoefficientRestrictionTower

/-!
# A genuine finite nonzero coefficient-stratum remainder phase

Actual original data internally produce a canonical terminal remainder tower.
The SAME tower is proved to be a true parent coefficient test history and a
true ORIGINAL marked test history; no parent-test/terminal/history certificate
is an input. Entire final original controlled cosupport avoids the literal
strict nonzero remainder. The initial selected zero components and whole old
NC/born-boundary admissibility/progress remain separate obligations.
Blueprint: `hironaka-normal-crossings-coefficient-remainder-phase-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsCoefficientRemainderPhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower MemberInterTowerAlong
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaStepOneZeroContactRemainderExtension HironakaCoherentTransformExtension
  HironakaOpenCarrierTestTowerExtension CanonicalCentres HironakaAdmissibleSequence
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- All domain fields and the whole ORIGINAL open record are derived internally. -/
theorem contactRemainder_original_domain (L : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1≤L.d) (hE : L.E=[]) :
    let A := contactRemainderMarked L 0
    let F := selectedComponents (n := n) L.N L.cosupp
    let G : Opens X := ⟨Fᶜ,(isClosedSubmanifold_selectedComponents hN L.cosupp).1.isOpen_compl⟩
    IsInvDomain n A ∧ A.cosupp=L.cosupp∩A.N ∧ A.N⊆G ∧
      MarkedIdeal.pullback (Subtype.val : G→X) A=
        MarkedIdeal.pullback (Subtype.val : G→X) L := by
  dsimp only
  let A := contactRemainderMarked L 0
  let F := selectedComponents (n := n) L.N L.cosupp
  let G : Opens X := ⟨Fᶜ,(isClosedSubmanifold_selectedComponents hN L.cosupp).1.isOpen_compl⟩
  have hDim : ResolutionInvariantSpec.DimLE n L.N n := by
    intro x hx
    obtain ⟨j,hj⟩ := hN.2 x hx
    exact ⟨j,BlowupStrictSubmanifold.le_of_regularAtDim_subset hj
      (AnalyticIrreducibleComponents.regularAtDim_univ x) (subset_univ _),hj⟩
  obtain ⟨hR,hAI,hADim,hnz,hcs⟩ :=
    HironakaOriginalWholeContactRemainderDomain.contactRemainder_geometry_and_nonzero L 0 hN hI hd hDim
  have hAE : A.E=[] := hE
  have hAG : A.N⊆G := by
    change remainingComponents (n := n) L.N L.cosupp⊆Fᶜ
    rw [remainingComponents_eq_diff_selected hN]
    exact fun _ hx=>hx.2
  refine ⟨⟨⟨hR,hAI,?_,?_⟩,hADim,hd,hnz⟩,hcs,hAG,?_⟩
  · rw [hAE]
    exact isSNCDivisor_nil
  · rw [hAE]
    exact isTransverse_nil_of_isClosedSubmanifold hR
  · apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext x
      change ((x:X)∈remainingComponents (n := n) L.N L.cosupp↔(x:X)∈L.N)
      rw [remainingComponents_eq_diff_selected hN]
      exact ⟨fun hx=>hx.1,fun hx=>⟨hx,x.2⟩⟩
    · rfl
    · rfl
    · rfl

/-- SAME internally chosen actual terminal tower, with true parent testness and
whole parent final-cosupport avoidance, including exceptional points. -/
theorem exists_canonical_remainder_parent_phase (L : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1≤L.d) (hE : L.E=[]) (hK : IsCompact L.cosupp) :
    let A := contactRemainderMarked L 0
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical A ((canonicalInvariant n).inv A) T ∧ IsGeoResolution A T ∧
      IsGeoTestTower L T ∧ CentresIn A.N T ∧
      (geoTransformAlong L T).cosupp∩strictAlong T A.N=∅ := by
  dsimp only
  let A := contactRemainderMarked L 0
  let F := selectedComponents (n := n) L.N L.cosupp
  let G : Opens X := ⟨Fᶜ,(isClosedSubmanifold_selectedComponents hN L.cosupp).1.isOpen_compl⟩
  obtain ⟨hA,hcs,hAG,heq⟩ := contactRemainder_original_domain L hN hI hd hE
  have hKA : IsCompact A.cosupp := by
    rw [hcs]
    exact hK.inter_right hA.isWellFormed.isClosedSubmanifold_N.1
  obtain ⟨Y,T,hcan,hres⟩ := exists_isGeoResolution_isCanonical_of_isCompact (canonicalInvariant n) hA hKA
  have hTL : IsGeoTestTower L T := isGeoTestTower_parent A L G
    hA.isWellFormed.isClosedSubmanifold_N hN hA.isWellFormed.isCoherent hI heq hAG rfl T hres.1
  refine ⟨Y,T,hcan,hres,hTL,?_,?_⟩
  · exact centresIn_of_isGeoTestTower_withN A A.N T hres.1
  · apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyL,hyR⟩
    have hyG : T.proj y∈G := hAG
      (strictAlong_subset_preimage T hA.isWellFormed.isClosedSubmanifold_N.1 hyR)
    let p : openPreimage T G := ⟨y,hyG⟩
    have hcohL := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hTL).2
    have hcohA := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent T hres.1).2
    have hp : p∈(MarkedIdeal.pullback (Subtype.val : openPreimage T G→Y) (geoTransformAlong L T)).cosupp := by
      rw [cosupp_pullback_val (geoTransformAlong L T)
        (fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcohL hg)]
      exact hyL
    rw [←current_open_record_eq A L G hA.isWellFormed.isClosedSubmanifold_N hN
      hA.isWellFormed.isCoherent hI heq T hres.1 hTL,
      cosupp_pullback_val (geoTransformAlong A T)
        (fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcohA hg)] at hp
    have hyA : y∈(geoTransformAlong A T).cosupp := hp
    rw [hres.2] at hyA
    exact hyA

/-- Original-only finite coefficient-remainder phase. Every literal controlled
original centre condition is DERIVED from the full coefficient tower theorem. -/
theorem exists_original_nc_coefficient_remainder_phase
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ x : X,branchMultiplicity hH x≤r) :
    let M : MarkedIdeal n X := ⟨univ,[],I,d⟩
    let Z := {x : X | r≤branchMultiplicity hH x}
    let L := withN (coeffMarked M) Z
    let A := contactRemainderMarked L 0
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical A ((canonicalInvariant n).inv A) T ∧ IsGeoResolution A T ∧
      IsGeoTestTower L T ∧ IsGeoTestTower M T ∧
      CentresIn A.N T ∧ CentresIn Z T ∧
      (geoTransformAlong L T).cosupp=(geoTransformAlong M T).cosupp∩strictAlong T Z ∧
      (geoTransformAlong M T).cosupp∩strictAlong T A.N=∅ := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,[],I,d⟩
  let Z := {x : X | r≤branchMultiplicity hH x}
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
  have hZ := isClosedSubmanifold_highest_superlevel hH hbound
  have hL : L.ideal.IsCoherent := isCoherent_coeffMarked (𝔪:=M) rfl hI
  have hLd : 1≤L.d := by
    change 1≤(Finset.range d).prod (fun i=>d-i)
    have hp : 0<(Finset.range d).prod (fun i=>d-i) := Finset.prod_pos fun i hi=> by
      have hi' := Finset.mem_range.mp hi
      omega
    omega
  have hcs : L.cosupp=M.cosupp∩Z := cosupp_coeff_withN M rfl hI hd Z
  have hKL : IsCompact L.cosupp := by
    rw [hcs]
    exact hK.inter_right hZ.1
  obtain ⟨Y,T,hcan,hres,hTL,hTR,hclear⟩ := exists_canonical_remainder_parent_phase L hZ hL hLd rfl hKL
  obtain ⟨hTM,hTZ⟩ := (coeff_restrict_tower_iff M rfl hI hd hZ T).1.mp hTL
  have hcsT := (coeff_restrict_tower_iff M rfl hI hd hZ T).2 hTL
  refine ⟨Y,T,hcan,hres,hTL,hTM,hTR,hTZ,hcsT,?_⟩
  have hRZ : A.N⊆Z := by
    change remainingComponents (n := n) Z L.cosupp⊆Z
    rw [remainingComponents_eq_diff_selected hZ]
    exact sdiff_subset
  apply eq_empty_iff_forall_notMem.mpr
  rintro y ⟨hyM,hyR⟩
  have hyL : y∈(geoTransformAlong L T).cosupp := by
    rw [hcsT]
    exact ⟨hyM,strictAlong_mono T hRZ hyR⟩
  have hy := show y∈(geoTransformAlong L T).cosupp∩strictAlong T A.N from ⟨hyL,hyR⟩
  rw [hclear] at hy
  exact hy

end
end Hironaka.HironakaNormalCrossingsCoefficientRemainderPhase
