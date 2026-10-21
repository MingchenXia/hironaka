/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsHighestStratumBlowup
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.Resolution.HironakaLocalPrincipalization

/-!
# Actual local marked admissibility of highest-NC-stratum subcentres

A smooth subcentre of the intrinsic highest multiplicity stratum lies in EVERY
actual local old branch. The genuine drop-containing-members theorem supplies
its whole local NC geometry, independently of ordering those branches. A true
blowup keeps the ORIGINAL off-cosupport locus and actual local SNC transforms.
No canonical subcentre, invariant symmetry or strict-progress claim is made.
Blueprint: `hironaka-normal-crossings-highest-subcentre-admissibility-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsHighestSubcentreAdmissibility
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup BlowupFlatCoordinates NormalCrossings
  NormalCrossingsInvariance NormalCrossingsComparison BlowupRestrictOpen
  BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealRestrictOpen MarkedIdealBiholomorphism GermIdealPullbackCalculus
  BlowupTowers GermIdealOrder
variable {n : ℕ} {X : CMfd.{u} n}

/-- Literal branches of the actual flattening on its WHOLE actual flat domain. -/
def flatBranches {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (S : Finset (Fin n)) : List (Set (⟨flatDomain Φ,isOpen_flatDomain Φ⟩ : Opens X)) :=
  S.toList.map fun j => {p | flatCoord Φ j p.1=0}

/-- The genuine flat-domain biholomorphism pulls the actual coordinate SNC list back. -/
theorem isSNCDivisor_flatBranches {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) (S : Finset (Fin n)) :
    IsSNCDivisor n (flatBranches Φ S) := by
  let T : Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  let χ := flatDomainDiffeomorph Φ hsrc
  let F := (coordinateHyperplanes.{u} S).map
    ((Subtype.val : LiftedOpen.{u} T → LiftedModel.{u} n) ⁻¹' ·)
  let B := F.map (χ ⁻¹' ·)
  have hF : IsSNCDivisor n F := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (liftedOpens.{u} T)) continuous_subtype_val
    (isSNCDivisor_coordinateHyperplanes S)
  have hB : IsSNCDivisor n B := isSNCDivisor_map_preimage
    (MarkedIdealTowerTransport.pullsBackCoordinates χ) χ.contMDiff.continuous hF
  have heq : B=flatBranches Φ S := by
    simp only [B,F,coordinateHyperplanes,flatBranches,List.map_map]
    apply List.map_congr_left
    intro j _hj
    rfl
  exact heq ▸ hB

/-- The intrinsic maximum stratum puts the actual subcentre in EVERY branch,
without global labels or any branch-selection certificate. -/
theorem exists_highest_subcentre_branches {H C : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ y : X,branchMultiplicity hH y≤r)
    (hC : C ⊆ {y | r≤branchMultiplicity hH y}) {x : X} (hx : x∈C) :
    ∃ (U : Opens X) (B : List (Set U)),x∈U ∧ IsSNCDivisor n B ∧
      (Subtype.val : U → X) ⁻¹' H=(⋃ A∈B,A) ∧
      ∀ A∈B,(Subtype.val : U → X) ⁻¹' C ⊆ A := by
  obtain ⟨Φ,hsrc,h0,S,hflat⟩ := hH.2 x
  obtain ⟨_hcard,hlevel⟩ := highest_superlevel_flattening hH hbound (hC hx) Φ h0 S hflat
  let U : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let B : List (Set U) := flatBranches Φ S
  refine ⟨U,B,mem_flatDomain_self Φ,isSNCDivisor_flatBranches Φ hsrc S,?_,?_⟩
  · ext p
    change p.1∈H ↔ p∈⋃ A∈B,A
    rw [hflat p.1 p.2]
    constructor
    · rintro ⟨j,hj,hzero⟩
      exact mem_iUnion₂.mpr ⟨{p : U | flatCoord Φ j p.1=0},
        List.mem_map.mpr ⟨j,Finset.mem_toList.mpr hj,rfl⟩,hzero⟩
    · intro hp
      obtain ⟨A,hA,hpA⟩ := mem_iUnion₂.mp hp
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hA
      exact ⟨j,Finset.mem_toList.mp hj,hpA⟩
  · intro A hA p hpC
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hA
    exact ((hlevel p.1 p.2).mp (hC hpC)) j (Finset.mem_toList.mp hj)

/-- The unchanged original marked data on an actual branch neighbourhood. -/
def localBranchMarked (U : Opens X) (B : List (Set U)) (N : Set X)
    (I : GermIdeal n X) (d : ℕ) : MarkedIdeal n U :=
  ⟨(Subtype.val : U → X) ⁻¹' N,B,GermIdeal.pullback (m := n) (Subtype.val : U → X) I,d⟩

/-- Actual original cosupport and smooth subcentre geometry give local marked
admissibility for EVERY permutation of the constructed WHOLE branch list. -/
theorem exists_highest_subcentre_local_admissibility {H C : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ y : X,branchMultiplicity hH y≤r)
    (hCtop : C ⊆ {y | r≤branchMultiplicity hH y})
    (hC : IsClosedSubmanifold n C) (N : Set X) (I : GermIdeal n X)
    (hI : I.IsCoherent) (d : ℕ) (hcos : C ⊆ cosupport n N I d) {x : X} (hx : x∈C) :
    ∃ (U : Opens X) (B : List (Set U)),x∈U ∧ IsSNCDivisor n B ∧
      (Subtype.val : U → X) ⁻¹' H=(⋃ A∈B,A) ∧
      HasNormalCrossings n ((Subtype.val : U → X) ⁻¹' C) B ∧
      ∀ F : List (Set U),B.Perm F →
        (localBranchMarked U F N I d).IsAdmissibleCentre ((Subtype.val : U → X) ⁻¹' C) := by
  obtain ⟨U,B,hxU,hB,hunion,hcontain⟩ := exists_highest_subcentre_branches hH hbound hCtop hx
  have hCU := isClosedSubmanifold_preimage_val hC U
  have hNC : HasNormalCrossings n ((Subtype.val : U → X) ⁻¹' C) B :=
    (hasNormalCrossings_iff_of_forall_mem hB (E' := []) (by simp)
      (fun A hA _ => hcontain A hA)).mp (hasNormalCrossings_nil_of_isClosedSubmanifold hCU)
  let M : MarkedIdeal n X := ⟨N,[],I,d⟩
  have hM : M.IsAdmissibleCentre C := ⟨hC,hcos,hasNormalCrossings_nil_of_isClosedSubmanifold hC⟩
  have hMU := MarkedIdealRestrictOpen.IsAdmissibleCentre.pullback_val
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hM U
  refine ⟨U,B,hxU,hB,hunion,hNC,?_⟩
  intro F hF
  exact ⟨hCU,hMU.2.1,hasNormalCrossings_of_forall_mem hNC
    (fun A hA => hF.mem_iff.mpr hA)⟩

/-- The actual smooth subcentre has a true blowup preserving the ORIGINAL good
locus, with actual local SNC strict branches and the literal new exceptional. -/
theorem exists_highest_subcentre_blowup {H C : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0<r)
    (hbound : ∀ y : X,branchMultiplicity hH y≤r)
    (hCtop : C ⊆ {y | r≤branchMultiplicity hH y})
    (hC : IsClosedSubmanifold n C) (N : Set X) (I : GermIdeal n X)
    (hI : I.IsCoherent) (d : ℕ) (hcos : C ⊆ cosupport n N I d) :
    ∃ (Y : CMfd.{u} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      IsIsomorphismOver n π (cosupport n N I d)ᶜ ∧
      ∀ x∈C,∃ (U : Opens X) (B : List (Set U)),x∈U ∧ IsSNCDivisor n B ∧
        (Subtype.val : U → X) ⁻¹' H=(⋃ A∈B,A) ∧
        (localBranchMarked U B N I d).IsAdmissibleCentre ((Subtype.val : U → X) ⁻¹' C) ∧
        let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
        let πU : V → U := fun p => ⟨π p.1,p.2⟩
        IsBlowupAlong n ((Subtype.val : U → X) ⁻¹' C) πU ∧
        IsSNCDivisor n (B.map (geoStrictTransform πU ((Subtype.val : U → X) ⁻¹' C)) ++
          [πU ⁻¹' ((Subtype.val : U → X) ⁻¹' C)]) ∧
        (N=univ → (localBranchMarked U B N I d).IsWellFormed) := by
  have hInt : interior C=∅ := subset_empty_iff.mp
    ((interior_mono hCtop).trans_eq (interior_highest_superlevel_eq_empty hH hr hbound))
  obtain ⟨Y,tY,cY,mY,π,hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC hInt
  let Y' : CMfd.{u} n := {carrier := Y,topologicalSpace := tY,chartedSpace := cY,isComplexManifold := mY}
  refine ⟨Y',π,hπ,?_,?_⟩
  · exact HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      (.step id C π .refl hπ) (by
        rintro _ ⟨y,hy,rfl⟩
        exact hcos (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hy))
  · intro x hx
    obtain ⟨U,B,hxU,hB,hunion,hNC,hadm⟩ :=
      exists_highest_subcentre_local_admissibility hH hbound hCtop hC N I hI d hcos hx
    let V : Opens Y' := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
    let πU : V → U := fun p => ⟨π p.1,p.2⟩
    have hπU : IsBlowupAlong n ((Subtype.val : U → X) ⁻¹' C) πU :=
      isBlowupAlong_restrict hπ U _
    refine ⟨U,B,hxU,hB,hunion,hadm B (.refl B),hπU,
      SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπU hB hNC,?_⟩
    intro hN
    have hcoh : (GermIdeal.pullback (m := n) (Subtype.val : U → X) I).IsCoherent :=
      isCoherent_pullback contMDiff_subtype_val hI
    have hNloc : (Subtype.val : U → X) ⁻¹' N=univ := by rw [hN,preimage_univ]
    change (⟨(Subtype.val : U → X) ⁻¹' N,B,
      GermIdeal.pullback (m := n) (Subtype.val : U → X) I,d⟩ : MarkedIdeal n U).IsWellFormed
    rw [hNloc]
    exact ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hcoh,hB,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hB⟩

end
end Hironaka.HironakaNormalCrossingsHighestSubcentreAdmissibility
