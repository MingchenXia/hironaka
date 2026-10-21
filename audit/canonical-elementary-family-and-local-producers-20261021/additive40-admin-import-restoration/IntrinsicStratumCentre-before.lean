/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsHighestSubcentreAdmissibility
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Invariant.OrderTaylor

/-!
# An intrinsic first old-NC-stratum centre from original marked data

The actual derivative-stratum ideal detects the ORIGINAL marked cosupport.
Its actual canonical initial maximum selects a nonempty smooth centre without
branch labels or a supplied centre/maximum/history. The original mark and ideal
are retained in the actual NC-admissible blowup. No iteration or equality with
the old ordered invariant is claimed.
Blueprint: `hironaka-normal-crossings-intrinsic-stratum-centre-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsIntrinsicStratumCentre
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates BlowupStrictSubmanifold NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder RestrictedIdealExtension
  DerivativeIdeal HironakaEmbeddedReducible HironakaAdmissibleSequence
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsHighestSubcentreAdmissibility
  CanonicalCentres
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.ResolutionDriver (maxLocus)
variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual intrinsic stratum ideal plus actual original derivative ideal. -/
def stratumDetectionIdeal (I : GermIdeal n X) (j : ℕ) (Z : Set X) : GermIdeal n X :=
  sumIdeal (vanishingIdeal (n := n) Z) (iterDerivIdeal I j)

/-- An auxiliary original marking-one datum, used only to select the first centre. -/
def stratumDetectionMarked (I : GermIdeal n X) (j : ℕ) (Z : Set X) : MarkedIdeal n X :=
  ⟨univ,[],stratumDetectionIdeal I j Z,1⟩

private theorem zeroLocus_sumIdeal {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    (sumIdeal I J).zeroLocus=I.zeroLocus ∩ J.zeroLocus := by
  ext x
  constructor
  · intro hx
    exact ⟨fun g hg => hx g (le_sumIdeal_left hI x g hg),
      fun g hg => hx g (le_sumIdeal_right hJ x g hg)⟩
  · rintro ⟨hxI,hxJ⟩ g hg
    obtain ⟨_,N,s,a,hs,_,he⟩ := hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    rcases hs i with hi | hi
    · rw [hxI _ hi,mul_zero]
    · rw [hxJ _ hi,mul_zero]

/-- WHOLE original derivative-stratum ideal, coherence and exact original marked locus. -/
theorem stratumDetectionIdeal_geometry (I : GermIdeal n X) (hI : I.IsCoherent) (j : ℕ)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ x : X,branchMultiplicity hH x≤r) :
    let Z := {x : X | r≤branchMultiplicity hH x}
    (stratumDetectionIdeal I j Z).IsCoherent ∧
      (stratumDetectionIdeal I j Z).zeroLocus=Z ∩ cosupport n univ I (j+1) := by
  dsimp only
  have hZ := isClosedSubmanifold_highest_superlevel hH hbound
  have hZI := VanishingIdealCoherent.isCoherent_vanishingIdeal hZ
  have hD := isCoherent_iterDerivIdeal hI j
  refine ⟨isCoherent_sumIdeal hZI hD,?_⟩
  rw [stratumDetectionIdeal,zeroLocus_sumIdeal hZI hD,
    BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hZ.1,
    ← OrderTaylor.cosupport_succ_eq_zeroLocus_iterDerivIdeal
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg) j]

/-- Positive-codimension old stratum internally supplies every actual domain field. -/
theorem stratumDetectionMarked_isInvDomain (I : GermIdeal n X) (hI : I.IsCoherent) (j : ℕ)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0<r)
    (hbound : ∀ x : X,branchMultiplicity hH x≤r) :
    IsInvDomain n (stratumDetectionMarked I j {x : X | r≤branchMultiplicity hH x}) := by
  let Z := {x : X | r≤branchMultiplicity hH x}
  have hZ := isClosedSubmanifold_highest_superlevel hH hbound
  have hZI := VanishingIdealCoherent.isCoherent_vanishingIdeal hZ
  have hZa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hZ
  have hZint := interior_highest_superlevel_eq_empty hH hr hbound
  have hK := (stratumDetectionIdeal_geometry I hI j hH hbound).1
  refine ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hK,isSNCDivisor_nil,
    isTransverse_nil_of_isClosedSubmanifold HomogenizedGlueingTower.isClosedSubmanifold_univ⟩,
    fun x _ => ⟨n,le_rfl,AnalyticIrreducibleComponents.regularAtDim_univ x⟩,le_rfl,?_⟩
  intro x _hx
  obtain ⟨g,hg,hfreq⟩ := isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty hZa hZint x
  exact ⟨g,le_sumIdeal_left hZI x g hg,hfreq⟩

/-- Only ORIGINAL compact cosupport and a nonempty intrinsic-stratum intersection
supply the actual smooth centre, whole maximum and genuine permitted NC blowup. -/
theorem exists_intrinsic_original_marked_nc_blowup
    (I : GermIdeal n X) (hI : I.IsCoherent) (j : ℕ)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0<r)
    (hbound : ∀ x : X,branchMultiplicity hH x≤r)
    (hK : IsCompact (cosupport n univ I (j+1)))
    (hne : ({x : X | r≤branchMultiplicity hH x} ∩ cosupport n univ I (j+1)).Nonempty) :
    let Z := {x : X | r≤branchMultiplicity hH x}
    let M := stratumDetectionMarked I j Z
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C=maxLocus ((canonicalInvariant n).inv M (.refl : BlowupTower X X)) M.cosupp ∧
      C ⊆ Z ∧ C ⊆ cosupport n univ I (j+1) ∧
      IsIsomorphismOver n π (cosupport n univ I (j+1))ᶜ ∧
      ∀ x∈C,∃ (U : Opens X) (B : List (Set U)),x∈U ∧ IsSNCDivisor n B ∧
        (Subtype.val : U → X) ⁻¹' H=(⋃ A∈B,A) ∧
        (localBranchMarked U B univ I (j+1)).IsAdmissibleCentre ((Subtype.val : U → X) ⁻¹' C) ∧
        let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
        let πU : V → U := fun p => ⟨π p.1,p.2⟩
        IsBlowupAlong n ((Subtype.val : U → X) ⁻¹' C) πU ∧
        IsSNCDivisor n (B.map (geoStrictTransform πU ((Subtype.val : U → X) ⁻¹' C)) ++
          [πU ⁻¹' ((Subtype.val : U → X) ⁻¹' C)]) ∧
        (localBranchMarked U B univ I (j+1)).IsWellFormed := by
  dsimp only
  let Z := {x : X | r≤branchMultiplicity hH x}
  let M := stratumDetectionMarked I j Z
  obtain ⟨hcoh,hzero⟩ := stratumDetectionIdeal_geometry I hI j hH hbound
  have hdom := stratumDetectionMarked_isInvDomain I hI j hH hr hbound
  have hcos : M.cosupp=Z ∩ cosupport n univ I (j+1) :=
    (cosupp_univ_one hcoh).trans hzero
  have hcompact : IsCompact M.cosupp := by
    rw [hcos]
    exact hK.inter_left (isClosed_branchMultiplicity_superlevel hH r)
  have hnonempty : M.cosupp.Nonempty := hcos.symm ▸ hne
  have husc := (canonicalInvariant n).isInvValue.usc M hdom (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at husc
  obtain ⟨a,ha,hmax⟩ := husc.exists_isMaxOn hcompact hnonempty
  let C := maxLocus ((canonicalInvariant n).inv M (.refl : BlowupTower X X)) M.cosupp
  have hCne : C.Nonempty := ⟨a,ha,hmax⟩
  have hCadm : M.IsAdmissibleCentre C := by
    simpa only [geoTransformAlong_refl] using
      (canonicalInvariant n).isInvValue.isAdmissibleCentre_maxLocus hdom
        (.refl : BlowupTower X X) trivial trivial
  have hCZ : C ⊆ Z := fun x hx => (hcos ▸ hx.1).1
  have hCcos : C ⊆ cosupport n univ I (j+1) := fun x hx => (hcos ▸ hx.1).2
  obtain ⟨Y,π,hπ,hiso,hLocal⟩ := exists_highest_subcentre_blowup
    hH hr hbound hCZ hCadm.1 univ I hI (j+1) hCcos
  refine ⟨C,Y,π,hπ,hCne,rfl,hCZ,hCcos,hiso,?_⟩
  intro x hx
  obtain ⟨U,B,hxU,hB,hunion,hadm,hπU,hnew,hwell⟩ := hLocal x hx
  exact ⟨U,B,hxU,hB,hunion,hadm,hπU,hnew,hwell rfl⟩

end
end Hironaka.HironakaNormalCrossingsIntrinsicStratumCentre
