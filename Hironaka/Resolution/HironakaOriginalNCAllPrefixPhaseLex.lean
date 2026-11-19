import Hironaka.Resolution.HironakaOriginalNCCurrentCount
import Hironaka.Resolution.HironakaCanonicalPrincipalization

set_option autoImplicit false

/-!
# Every unfinished prefix of the SAME canonical remainder phase is phase-lex maximal

The phase datum A is formed once from the natural original coefficient stratum.
Current adapted old carriers and both count assertions are actually produced
from A-testness, not supplied as history/count certificates. The canonical
value is inv_A(T) on the SAME original phase history T, without a reset.

The final producer internally selects an entire real canonical resolving
A-phase and exports its actual prefix dictionaries. Selected-zero priority,
phase resets and a single original general-NC invariant remain open.

Blueprint: hironaka-original-nc-all-prefix-phase-lex-extension.tex.
Source-only proof-body draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCAllPrefixPhaseLex

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower MemberInterTowerAlong
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneZeroContactRemainderExtension
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaBoundaryCoefficientStratumResolution
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCPhaseLex
open ResolutionDriver (maxLocus IsCanonicalSegment)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Current old geometry and exact cosupports at any SAME actual A-test prefix.
Parent testness, universal branch histories and current count assertions are outputs. -/
theorem exists_remainder_prefix_current_geometry
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower
      (contactRemainderMarked (withN (coeffMarked (⟨univ, E, I, d⟩ : MarkedIdeal n X))
        {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) 0) T) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    let A := contactRemainderMarked L 0
    ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E,
      IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
      (∀ y : Y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ r) ∧
      (∀ y ∈ strictAlong T A.N,
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y = r) ∧
      (geoTransformAlong L T).cosupp =
        (geoTransformAlong M T).cosupp ∩ strictAlong T Z ∧
      (geoTransformAlong A T).cosupp =
        (geoTransformAlong M T).cosupp ∩ strictAlong T A.N := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
  obtain ⟨_hLT, hMT, hTZ, hLCos, hACos⟩ :=
    original_remainder_cosupport_dictionary I hI d hd h hBound T hT
  obtain ⟨hc, hCurrentBound, hCurrentTop⟩ :=
    exists_highest_history_current_pair_counts I hI d h hr hBound T hMT hTZ
  have hZ := isClosedSubmanifold_highest_superlevel
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  have hRZ : A.N ⊆ Z := by
    change remainingComponents (n := n) Z L.cosupp ⊆ Z
    rw [remainingComponents_eq_diff_selected hZ]
    exact fun _ hx => hx.1
  have hHistory := isOriginalBranchTestTower_of_centresIn_highest_stratum
    I hI d h hr hBound T hMT hTZ
  exact ⟨hc, hMT, hHistory, hCurrentBound,
    fun y hy => hCurrentTop y (strictAlong_mono T hRZ hy), hLCos, hACos⟩

/-- The actual same-prefix A whole maximum equals the entire M-cosupport
maximum of its explicit CURRENT phase lex value, whenever A is unfinished. -/
theorem exists_remainder_prefix_current_lex_dictionary
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower
      (contactRemainderMarked (withN (coeffMarked (⟨univ, E, I, d⟩ : MarkedIdeal n X))
        {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) 0) T) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    let A := contactRemainderMarked L 0
    let f := (CanonicalCentres.canonicalInvariant n).inv A T
    ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E,
      (∀ y : Y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ r) ∧
      (∀ y ∈ strictAlong T A.N,
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y = r) ∧
      (geoTransformAlong L T).cosupp =
        (geoTransformAlong M T).cosupp ∩ strictAlong T Z ∧
      (geoTransformAlong A T).cosupp =
        (geoTransformAlong M T).cosupp ∩ strictAlong T A.N ∧
      ((geoTransformAlong A T).cosupp.Nonempty →
        maxLocus f (geoTransformAlong A T).cosupp =
          maxLocus (remainderPhaseLex
            (branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc))
            (strictAlong T A.N) f) (geoTransformAlong M T).cosupp) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
  let f := (CanonicalCentres.canonicalInvariant n).inv A T
  obtain ⟨hc, _hMT, _hHistory, hCurrentBound, hCurrentTop, hLCos, hACos⟩ :=
    exists_remainder_prefix_current_geometry I hI d hd h hr hBound T hT
  refine ⟨hc, hCurrentBound, hCurrentTop, hLCos, hACos, ?_⟩
  intro hNe
  have hNe' : ((geoTransformAlong M T).cosupp ∩ strictAlong T A.N).Nonempty := by
    rw [← hACos]
    exact hNe
  have hMax := maxLocus_remainderPhaseLex
    (geoTransformAlong M T).cosupp (strictAlong T A.N)
    (branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc))
    f hCurrentBound hCurrentTop hNe'
  rw [← hACos] at hMax
  exact hMax.symm

/-- Natural original data internally select a genuine COMPLETE canonical
resolving remainder phase. Every literal prefix has internally derived current
counts and both exact cosupports; each unfinished prefix has the phase-lex
whole-maximum equality for the SAME original A-history invariant. -/
theorem exists_original_canonical_remainder_all_prefix_phase_lex
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    let A := contactRemainderMarked L 0
    let V := CanonicalCentres.canonicalInvariant n
    ∃ (Y : CMfd.{u} n) (P : BlowupTower X Y),
      IsCanonicalSegment A (V.inv A) P ∧ IsGeoResolution A P ∧
      IsGeoTestTower M P ∧ IsOriginalBranchTestTower M H P ∧
      ∀ j : ℕ,
        let T := head P j
        let f := V.inv A T
        IsCanonicalSegment A (V.inv A) T ∧
        ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E,
          (∀ y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ r) ∧
          (∀ y ∈ strictAlong T A.N,
            branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y = r) ∧
          (geoTransformAlong L T).cosupp =
            (geoTransformAlong M T).cosupp ∩ strictAlong T Z ∧
          (geoTransformAlong A T).cosupp =
            (geoTransformAlong M T).cosupp ∩ strictAlong T A.N ∧
          ((geoTransformAlong A T).cosupp.Nonempty →
            maxLocus f (geoTransformAlong A T).cosupp =
              maxLocus (remainderPhaseLex
                (branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc))
                (strictAlong T A.N) f) (geoTransformAlong M T).cosupp) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
  let V := CanonicalCentres.canonicalInvariant n
  have hZ := isClosedSubmanifold_highest_superlevel
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  have hLI : L.ideal.IsCoherent := isCoherent_coeffMarked (𝔪 := M) rfl hI
  have hLW : L.IsWellFormed :=
    ⟨hZ, hLI, isSNCDivisor_of_boundaryAdapted h, highest_stratum_isTransverse h hBound⟩
  have hLd : 1 ≤ L.d := by
    change 1 ≤ (Finset.range d).prod (fun i => d - i)
    have hp : 0 < (Finset.range d).prod (fun i => d - i) :=
      Finset.prod_pos fun i hi => by
        have hi' := Finset.mem_range.mp hi
        omega
    omega
  obtain ⟨hA, hACos, _hAG, _hEq⟩ := contactRemainder_boundary_domain L hLW hLd
  have hLCos : L.cosupp = M.cosupp ∩ Z := cosupp_coeff_withN M rfl hI hd Z
  have hKL : IsCompact L.cosupp := by
    rw [hLCos]
    exact hK.inter_right hZ.1
  have hKA : IsCompact A.cosupp := by
    rw [hACos]
    exact hKL.inter_right hA.isWellFormed.isClosedSubmanifold_N.1
  obtain ⟨Y, P, hCan, hRes⟩ :=
    HironakaCanonicalPrincipalization.exists_canonical_segment_of_isCompact V hA hKA
  obtain ⟨_hc, hMP, hHistory, _hb, _ht, _hL, _hC⟩ :=
    exists_remainder_prefix_current_geometry I hI d hd h hr hBound P hRes.1
  refine ⟨Y, P, hCan, hRes, hMP, hHistory, ?_⟩
  intro j
  have hHeadCan : IsCanonicalSegment A (V.inv A) (head P j) :=
    CanonicalResolution.isCanonicalSegment_of_append A (V.inv A) (head P j) (tail P j)
      (by rw [head_append_tail]; exact hCan)
  have hHead := ((isGeoTestTower_iff_head_tail A P j).mp hRes.1).1
  exact ⟨hHeadCan,
    exists_remainder_prefix_current_lex_dictionary I hI d hd h hr hBound (head P j) hHead⟩

end
end Hironaka.HironakaOriginalNCAllPrefixPhaseLex

