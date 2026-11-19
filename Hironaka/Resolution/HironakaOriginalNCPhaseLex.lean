import Hironaka.Resolution.HironakaOriginalOldBranchHighestPhase
import Hironaka.Resolution.HironakaBoundaryCoefficientStratumResolution
import Hironaka.Invariant.MaxLocusLocal

set_option autoImplicit false

/-!
# An actual first canonical remainder centre is an explicit phase-lex maximum

The actual contact remainder A omits the selected zero components F of the
whole coefficient stratum L. Its correct cosupport is the current original
cosupport intersected with the strict remainder R, not the whole strict Z.
The exact dictionary is proved on the SAME A-test tower, deriving all parent
testness internally.

Natural original data and a nonempty natural remainder internally construct a
genuine first A-canonical successor. Its centre is the entire original-cosupport
maximum of the explicit old-count/remainder-invariant lex value. No output tower
is used to define that value; the initial phase prefix is genuinely refl.
The bottom extension outside R retains and defers the selected zero components.

This is not the full original general-NC history-invariant identification.
Blueprint: hironaka-original-nc-phase-lex-extension.tex.
Source-only proof-body draft; no kernel or axiom-check claim.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaOriginalNCPhaseLex

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower MemberInterTowerAlong
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaStepOneZeroContactRemainderExtension HironakaCoherentTransformExtension
  HironakaOpenCarrierTestTowerExtension HironakaBoundaryCoefficientStratumResolution
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaOriginalOldBranchOpenHistory
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionDriver (maxLocus IsCanonicalSegment)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Parent testness and the correct full remainder cosupport are derived from
the same actual A-test history. Zero components of L are not discarded. -/
theorem remainder_parent_cosupport (L : MarkedIdeal n X) (hw : L.IsWellFormed)
    (hd : 1 ≤ L.d) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (contactRemainderMarked L 0) T) :
    let A := contactRemainderMarked L 0
    IsGeoTestTower L T ∧
      (geoTransformAlong A T).cosupp =
        (geoTransformAlong L T).cosupp ∩ strictAlong T A.N := by
  dsimp only
  let A := contactRemainderMarked L 0
  let F := selectedComponents (n := n) L.N L.cosupp
  let G : Opens X := ⟨Fᶜ,
    (isClosedSubmanifold_selectedComponents hw.isClosedSubmanifold_N L.cosupp).1.isOpen_compl⟩
  obtain ⟨hA, _hInitial, hAG, hEq⟩ := contactRemainder_boundary_domain L hw hd
  have hLT : IsGeoTestTower L T := isGeoTestTower_parent A L G
    hA.isWellFormed.isClosedSubmanifold_N hw.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent hw.isCoherent hEq hAG rfl T hT
  have hCurrent := current_open_record_eq A L G
    hA.isWellFormed.isClosedSubmanifold_N hw.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent hw.isCoherent hEq T hT hLT
  have hIA := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent T hT).2
  have hIL := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    hw.isClosedSubmanifold_N hw.isCoherent T hLT).2
  have hMem (y : Y) (hyR : y ∈ strictAlong T A.N) :
      y ∈ (geoTransformAlong A T).cosupp ↔ y ∈ (geoTransformAlong L T).cosupp := by
    have hyG : T.proj y ∈ G :=
      hAG (strictAlong_subset_preimage T hA.isWellFormed.isClosedSubmanifold_N.1 hyR)
    let p : openPreimage T G := ⟨y, hyG⟩
    have hp : p ∈ (MarkedIdeal.pullback (Subtype.val : openPreimage T G → Y)
        (geoTransformAlong A T)).cosupp ↔
        p ∈ (MarkedIdeal.pullback (Subtype.val : openPreimage T G → Y)
          (geoTransformAlong L T)).cosupp := by rw [hCurrent]
    rw [cosupp_pullback_val _ (fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIA hg),
      cosupp_pullback_val _ (fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIL hg)] at hp
    exact hp
  refine ⟨hLT, ?_⟩
  ext y
  constructor
  · intro hy
    have hyR : y ∈ strictAlong T A.N := by
      rw [← N_geoTransformAlong A T]
      exact (geoTransformAlong A T).cosupp_subset_N hy
    exact ⟨(hMem y hyR).mp hy, hyR⟩
  · rintro ⟨hy, hyR⟩
    exact (hMem y hyR).mpr hy

/-- The exact A/L/M dictionaries hold along the same actual history, deriving
parent testness and centres in the original highest stratum, with all E retained. -/
theorem original_remainder_cosupport_dictionary
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ}
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
    IsGeoTestTower L T ∧ IsGeoTestTower M T ∧ CentresIn Z T ∧
      (geoTransformAlong L T).cosupp =
        (geoTransformAlong M T).cosupp ∩ strictAlong T Z ∧
      (geoTransformAlong A T).cosupp =
        (geoTransformAlong M T).cosupp ∩ strictAlong T A.N := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
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
  obtain ⟨hLT, hACos⟩ := remainder_parent_cosupport L hLW hLd T hT
  obtain ⟨hMT, hTZ⟩ := (coeff_restrict_tower_iff M rfl hI hd hZ T).1.mp hLT
  have hLCos := (coeff_restrict_tower_iff M rfl hI hd hZ T).2 hLT
  have hRZ : A.N ⊆ Z := by
    change remainingComponents (n := n) Z L.cosupp ⊆ Z
    rw [remainingComponents_eq_diff_selected hZ]
    exact fun _ hx => hx.1
  have hStrict := strictAlong_mono T hRZ
  refine ⟨hLT, hMT, hTZ, hLCos, ?_⟩
  rw [hACos, hLCos]
  ext y
  constructor
  · rintro ⟨⟨hyM, _hyZ⟩, hyR⟩
    exact ⟨hyM, hyR⟩
  · rintro ⟨hyM, hyR⟩
    exact ⟨⟨hyM, hStrict hyR⟩, hyR⟩

/-- The original old count and actual remainder invariant, with an explicit
bottom extension on deferred selected-zero components and all other points. -/
def remainderPhaseLex {A : Type u} {Λ : Type v} [LinearOrder Λ]
    (b : A → ℕ) (R : Set A) (f : A → Λ) (x : A) : ℕ ×ₗ WithBot Λ := by
  classical
  exact toLex (b x, if x ∈ R then (f x : WithBot Λ) else ⊥)

/-- Nonempty remainder maxima are exactly the WHOLE parent cosupport maxima
of the explicit lex value. No desired maximum or centre is a premise. -/
theorem maxLocus_remainderPhaseLex {A : Type u} {Λ : Type v} [LinearOrder Λ]
    (S R : Set A) (b : A → ℕ) (f : A → Λ) {r : ℕ}
    (hBound : ∀ x, b x ≤ r) (hTop : ∀ x ∈ R, b x = r)
    (hNe : (S ∩ R).Nonempty) :
    maxLocus (remainderPhaseLex b R f) S = maxLocus f (S ∩ R) := by
  classical
  ext x
  constructor
  · intro hx
    have hxR : x ∈ R := by
      by_contra hxR
      obtain ⟨y, hyS, hyR⟩ := hNe
      have hCmp := hx.2 y hyS
      rw [remainderPhaseLex, remainderPhaseLex, if_pos hyR, if_neg hxR,
        hTop y hyR, Prod.Lex.toLex_le_toLex] at hCmp
      rcases hCmp with hLt | ⟨_hEq, hBot⟩
      · exact (not_lt_of_ge (hBound x)) hLt
      · exact (not_le_of_gt (WithBot.bot_lt_coe (f y))) hBot
    refine ⟨⟨hx.1, hxR⟩, ?_⟩
    intro y hy
    have hCmp := hx.2 y hy.1
    simpa only [remainderPhaseLex, if_pos hy.2, if_pos hxR, hTop y hy.2,
      hTop x hxR, Prod.Lex.toLex_le_toLex, lt_self_iff_false, eq_self_iff_true,
      false_or, true_and, WithBot.coe_le_coe] using hCmp
  · rintro ⟨⟨hxS, hxR⟩, hMax⟩
    refine ⟨hxS, ?_⟩
    intro y hy
    by_cases hyR : y ∈ R
    · have hf := hMax y ⟨hy, hyR⟩
      simpa only [remainderPhaseLex, if_pos hyR, if_pos hxR, hTop y hyR,
        hTop x hxR, Prod.Lex.toLex_le_toLex, lt_self_iff_false, eq_self_iff_true,
        false_or, true_and, WithBot.coe_le_coe] using hf
    · rw [remainderPhaseLex, remainderPhaseLex, if_neg hyR, if_pos hxR,
        hTop x hxR, Prod.Lex.toLex_le_toLex]
      rcases (hBound y).lt_or_eq with hLt | hEq
      · exact Or.inl hLt
      · exact Or.inr ⟨hEq, bot_le⟩

/-- A natural nonempty highest-stratum remainder internally yields an actual
first A-canonical blowup. Its SAME centre is the maximum of an explicit phase
lex value on the whole original cosupport. There is no supplied history/T. -/
theorem exists_original_first_remainder_phase_lex_step
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let b := branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h)
    let Z := {x | r ≤ b x}
    let L := withN (coeffMarked M) Z
    let A := contactRemainderMarked L 0
    let f := (CanonicalCentres.canonicalInvariant n).inv A (BlowupTower.refl : BlowupTower X X)
    A.cosupp.Nonempty →
      ∃ (C : Set X), C.Nonempty ∧ C = maxLocus f A.cosupp ∧
        C = maxLocus (remainderPhaseLex b A.N f) M.cosupp ∧
        ∃ (Y : CMfd.{u} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
          let S : BlowupTower X Y := .step .refl C π hπ
          IsCanonicalSegment A ((CanonicalCentres.canonicalInvariant n).inv A) S ∧
          IsGeoTestTower M S ∧ IsOriginalBranchTestTower M H S ∧
          ∀ j : ℕ,
            (geoTransformAlong L (head S j)).cosupp =
              (geoTransformAlong M (head S j)).cosupp ∩ strictAlong (head S j) Z ∧
            (geoTransformAlong A (head S j)).cosupp =
              (geoTransformAlong M (head S j)).cosupp ∩ strictAlong (head S j) A.N := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let b := branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h)
  let Z := {x | r ≤ b x}
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
  let V := CanonicalCentres.canonicalInvariant n
  let f := V.inv A (BlowupTower.refl : BlowupTower X X)
  intro hNe
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
  have hUSC := V.isInvValue.usc A hA (BlowupTower.refl : BlowupTower X X) trivial
  obtain ⟨x, hx, hMax⟩ := hUSC.exists_isMaxOn hKA hNe
  let C := maxLocus f A.cosupp
  have hCNe : C.Nonempty := ⟨x, hx, hMax⟩
  have hAdm : A.IsAdmissibleCentre C :=
    V.isInvValue.isAdmissibleCentre_maxLocus hA .refl trivial trivial
  have hInt : interior C = ∅ :=
    ResolutionInvariantDriver.interior_maxLocus_eq_empty hA .refl trivial f
  have hRZ : A.N ⊆ Z := by
    change remainingComponents (n := n) Z L.cosupp ⊆ Z
    rw [remainingComponents_eq_diff_selected hZ]
    exact fun _ hx => hx.1
  have hTop : ∀ y ∈ A.N, b y = r := by
    intro y hy
    exact le_antisymm (hBound y) (hRZ hy)
  obtain ⟨_hL0, _hM0, _hZ0, _hLCos0, hACos0⟩ :=
    original_remainder_cosupport_dictionary I hI d hd h hBound
      (BlowupTower.refl : BlowupTower X X) trivial
  change A.cosupp = M.cosupp ∩ A.N at hACos0
  have hLex : C = maxLocus (remainderPhaseLex b A.N f) M.cosupp := by
    have he := maxLocus_remainderPhaseLex M.cosupp A.N b f hBound hTop
      (by rw [← hACos0]; exact hNe)
    rw [← hACos0] at he
    exact he.symm
  obtain ⟨Y, tY, cY, mY, π, hπ⟩ := BlowupExistence.exists_isBlowupAlong C hAdm.1 hInt
  let := tY
  let := cY
  let := mY
  let S : BlowupTower X (CMfd.of (n := n) Y) := .step .refl C π hπ
  have hAS : IsGeoTestTower A S := ⟨trivial, hAdm⟩
  have hCanS : IsCanonicalSegment A (V.inv A) S := ⟨trivial, hCNe, rfl⟩
  obtain ⟨_hLS, hMS, hZS, _hLCosS, _hACosS⟩ :=
    original_remainder_cosupport_dictionary I hI d hd h hBound S hAS
  have hHistory : IsOriginalBranchTestTower M H S :=
    isOriginalBranchTestTower_of_centresIn_highest_stratum I hI d h hr hBound S hMS hZS
  refine ⟨C, hCNe, rfl, hLex, CMfd.of (n := n) Y, π, hπ, hCanS, hMS, hHistory, ?_⟩
  intro j
  have hHead := ((isGeoTestTower_iff_head_tail A S j).mp hAS).1
  obtain ⟨_hLJ, _hMJ, _hZJ, hLCosJ, hACosJ⟩ :=
    original_remainder_cosupport_dictionary I hI d hd h hBound (head S j) hHead
  exact ⟨hLCosJ, hACosJ⟩

end
end Hironaka.HironakaOriginalNCPhaseLex

