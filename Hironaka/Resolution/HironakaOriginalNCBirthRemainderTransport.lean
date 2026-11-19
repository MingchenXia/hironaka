import Hironaka.Resolution.HironakaOriginalNCBirthPhaseTail
import Hironaka.Invariant.ContactEmptyPrefix
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderGlueing

set_option autoImplicit false

/-!
# Actual birth remainders and freshly formed current intrinsic-count data

An empty history is a genuine pullback with its SAME whole current boundary.
For an ambient parent this is literal record equality. Actual coefficient and
remainder pullback then identify the current datum, while restricted equivalence
compares its ideal representative with the actual transformed birth datum.

The final producer chooses its completed r-phase and birth suffix internally.
It identifies the endpoint parent with the SAME original current parent on the
actual endpoint open. It chooses no finite local q-phase on a possibly
noncompact open and claims no full original general-NC driver identification.

Blueprint: hironaka-original-nc-birth-remainder-transport-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCBirthRemainderTransport

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower HomogenizedIdealAlong MemberInterTowerAlong
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneZeroContactRemainderExtension
  HironakaStepOneZeroContactRemainderGlueing
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsGlobalPhaseCarrier HironakaBoundaryCoefficientStratumResolution
  HironakaOriginalOldBranchOpenHistory HironakaOriginalOldBranchEmptyProjection
  HironakaOriginalOldBranchCountDrop HironakaOriginalNCCountHistory HironakaOriginalNCBirthPhaseTail
open MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
open ResolutionDriver (IsCanonicalSegment)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem restrictEquiv_symm {D : Type u} [TopologicalSpace D]
    [ChartedSpace (ComplexModel n) D] [IsComplexManifold n D]
    {J K : MarkedIdeal n D} (h : RestrictEquiv J K) : RestrictEquiv K J :=
  ⟨h.N_eq.symm, h.E_eq.symm, h.d_eq.symm,
    h.N_eq ▸ h.ge, h.N_eq ▸ h.le⟩

private theorem empty_step_whole_pullback
    {Z : CMfd.{u} n} (L : MarkedIdeal n Y) (hN : IsClosed L.N)
    {π : Z → Y} (hπ : IsBlowupAlong n (∅ : Set Y) π) :
    RestrictEquiv (L.geoTransform ∅ π)
      ({ MarkedIdeal.pullback π L with E := (L.geoTransform ∅ π).E } : MarkedIdeal n Z) := by
  refine ⟨ContactCanonicalAlong.geoStrictTransform_empty hπ.contMDiff.continuous hN,
    rfl, rfl, ContactCanonicalAlong.restrictLe_geoTransform_empty_le_pullback hπ L, ?_⟩
  exact ContactCanonicalAlong.restrictLe_pullback_le_geoTransform ∅ L

/-- The pullback is given the exact boundary of the SAME actual history.
Empty born entries and every intermediate empty step are retained literally. -/
theorem empty_transform_restrictEquiv_whole_pullback
    (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower X Y), IsEmptyTower S →
      RestrictEquiv (geoTransformAlong L S)
        ({ MarkedIdeal.pullback S.proj L with E := (geoTransformAlong L S).E } : MarkedIdeal n Y)
  | _, .refl, _ => by
      have hId : ({ MarkedIdeal.pullback id L with E := L.E } : MarkedIdeal n X) = L := by
        apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
        · rfl
        · rfl
        · exact BlowupControlledTransform.pullback_id hI
        · rfl
      change RestrictEquiv L ({ MarkedIdeal.pullback id L with E := L.E } : MarkedIdeal n X)
      rw [hId]
      exact RestrictEquiv.refl hI
  | _, .step S C π hπ, he => by
      obtain ⟨heS, rfl⟩ := he
      let J := geoTransformAlong L S
      let P : MarkedIdeal n _ := { MarkedIdeal.pullback S.proj L with E := J.E }
      have hJ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI S
        (isGeoTestTower_of_isEmptyTower L S heS)
      have hPI : P.ideal.IsCoherent :=
        GermIdealPullbackCalculus.isCoherent_pullback S.contMDiff_proj hI
      have hPN : IsClosed P.N := hN.1.preimage S.contMDiff_proj.continuous
      have hEq : J.geoTransform ∅ π = P.geoTransform ∅ π :=
        (empty_transform_restrictEquiv_whole_pullback L hN hI S heS).geoTransform_eq
          hJ.1.1 hJ.2 hPI hπ.contMDiff
      have hOne := empty_step_whole_pullback P hPN hπ
      have hPB :
          ({ MarkedIdeal.pullback π P with E := (P.geoTransform ∅ π).E } : MarkedIdeal n _) =
          ({ MarkedIdeal.pullback (S.proj ∘ π) L with E := (J.geoTransform ∅ π).E } : MarkedIdeal n _) := by
        apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
        · rfl
        · exact (congrArg MarkedIdeal.E hEq).symm
        · exact (GermIdealTotalTransform.pullback_comp S.contMDiff_proj hπ.contMDiff hI).symm
        · rfl
      have hRight : RestrictEquiv (P.geoTransform ∅ π)
          ({ MarkedIdeal.pullback (S.proj ∘ π) L with E := (J.geoTransform ∅ π).E } : MarkedIdeal n _) :=
        (congrArg (fun K : MarkedIdeal n _ => RestrictEquiv (P.geoTransform ∅ π) K) hPB).mp hOne
      exact (congrArg (fun K : MarkedIdeal n _ => RestrictEquiv K
        ({ MarkedIdeal.pullback (S.proj ∘ π) L with E := (J.geoTransform ∅ π).E } : MarkedIdeal n _))
          hEq).mpr hRight

/-- For an ambient carrier, the restricted ideal comparison is a genuine
equality of entire marked records, retaining the actual appended boundary. -/
theorem ambient_empty_transform_eq_whole_pullback
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    (S : BlowupTower X Y) (he : IsEmptyTower S) :
    geoTransformAlong M S =
      ({ MarkedIdeal.pullback S.proj M with E := (geoTransformAlong M S).E } : MarkedIdeal n Y) := by
  have hNS : IsClosedSubmanifold n M.N := hN ▸ isClosedSubmanifold_univ
  have hEq := empty_transform_restrictEquiv_whole_pullback M hNS hI S he
  have hCurrentN : (geoTransformAlong M S).N = univ := by
    calc
      _ = (MarkedIdeal.pullback S.proj M).N := hEq.N_eq
      _ = univ := by change S.proj ⁻¹' M.N = univ; rw [hN, preimage_univ]
  have hCurrentI := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hNS hI S
    (isGeoTestTower_of_isEmptyTower M S he)).2
  have hPullI := GermIdealPullbackCalculus.isCoherent_pullback S.contMDiff_proj hI
  have hLe : RestrictedIdealWeight.RestrictLe univ (geoTransformAlong M S).ideal
      (GermIdeal.pullback (m := n) S.proj M.ideal) := hCurrentN ▸ hEq.le
  have hGe : RestrictedIdealWeight.RestrictLe univ (GermIdeal.pullback (m := n) S.proj M.ideal)
      (geoTransformAlong M S).ideal := hCurrentN ▸ hEq.ge
  have hIdeal := restrictOn_eq_of_restrictLe isClosed_univ hLe hGe
  rw [restrictOn_univ hCurrentI, restrictOn_univ hPullI] at hIdeal
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hEq.N_eq hEq.E_eq hIdeal hEq.d_eq

private theorem coeffMarked_with_boundary (M : MarkedIdeal n X) (E : List (Set X)) :
    coeffMarked ({ M with E := E } : MarkedIdeal n X) = { coeffMarked M with E := E } := rfl

private theorem coefficient_positive (M : MarkedIdeal n X) : 1 ≤ (coeffMarked M).d := by
  change 1 ≤ (Finset.range M.d).prod (fun i => M.d - i)
  have hp : 0 < (Finset.range M.d).prod (fun i => M.d - i) :=
    Finset.prod_pos fun i hi => by
      have hi' := Finset.mem_range.mp hi
      omega
  omega

private theorem coefficient_pullback_diffeo
    (χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d) :
    coeffMarked (MarkedIdeal.pullback χ M) = MarkedIdeal.pullback χ (coeffMarked M) := by
  have hPN : (MarkedIdeal.pullback χ M).N = univ := by
    change χ ⁻¹' M.N = univ
    rw [hN, preimage_univ]
  have hPI := GermIdealPullbackCalculus.isCoherent_pullback χ.contMDiff hI
  have h := pullback_coeffMarkedAlong_of_inverse χ.contMDiff χ.symm.contMDiff
    χ.apply_symm_apply χ.symm_apply_apply M hI (hN ▸ isClosedSubmanifold_univ) hd
  rw [coeffMarkedAlong_eq_coeffMarked hN
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg),
    coeffMarkedAlong_eq_coeffMarked hPN
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hPI hg)] at h
  exact h.symm

/-- The freshly formed current coefficient remainder has the exact carrier,
marking and WHOLE current boundary of the actual transformed birth remainder.
Only its ideal representative is compared by restricted equivalence. -/
theorem coefficient_remainder_empty_transport
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    {Z : Set X} (hZ : IsClosedSubmanifold n Z)
    (S : BlowupTower X Y) (he : IsEmptyTower S) :
    let A := contactRemainderMarked (withN (coeffMarked M) Z) 0
    let A' := contactRemainderMarked (withN (coeffMarked (geoTransformAlong M S)) (strictAlong S Z)) 0
    RestrictEquiv A' (geoTransformAlong A S) ∧ A'.E = (geoTransformAlong M S).E := by
  dsimp only
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
  let MS := geoTransformAlong M S
  let A' := contactRemainderMarked (withN (coeffMarked MS) (strictAlong S Z)) 0
  obtain ⟨χ, hχ⟩ := exists_empty_tower_projection S he
  have hProj : (χ : Y → X) = S.proj := funext hχ
  have hMS : MS = ({ MarkedIdeal.pullback χ M with E := MS.E } : MarkedIdeal n Y) := by
    rw [hProj]
    exact ambient_empty_transform_eq_whole_pullback M hN hI S he
  have hStrict : strictAlong S Z = χ ⁻¹' Z := by
    rw [ContactEmptyPrefix.strictAlong_of_isEmptyTower hZ.1 S he, hProj]
  have hL : withN (coeffMarked MS) (strictAlong S Z) =
      ({ MarkedIdeal.pullback χ L with E := MS.E } : MarkedIdeal n Y) := by
    calc
      _ = withN (coeffMarked ({ MarkedIdeal.pullback χ M with E := MS.E } : MarkedIdeal n Y))
          (strictAlong S Z) := congrArg (fun J : MarkedIdeal n Y => withN (coeffMarked J) (strictAlong S Z)) hMS
      _ = _ := by
        rw [coeffMarked_with_boundary, coefficient_pullback_diffeo χ M hN hI hd, hStrict]
        rfl
  have hLI : L.ideal.IsCoherent := isCoherent_coeffMarked (𝔪 := M) hN hI
  have hA' : A' = ({ MarkedIdeal.pullback χ A with E := MS.E } : MarkedIdeal n Y) := by
    calc
      _ = contactRemainderMarked ({ MarkedIdeal.pullback χ L with E := MS.E } : MarkedIdeal n Y) 0 :=
        congrArg (fun J : MarkedIdeal n Y => contactRemainderMarked J 0) hL
      _ = ({ contactRemainderMarked (MarkedIdeal.pullback χ L) 0 with E := MS.E } : MarkedIdeal n Y) := rfl
      _ = _ := by
        rw [contactRemainderMarked_pullback_diffeo χ L 0 hZ hLI (coefficient_positive M)]
  have hAN : IsClosedSubmanifold n A.N := isClosedSubmanifold_remainingComponents hZ L.cosupp
  have hAT := empty_transform_restrictEquiv_whole_pullback A hAN hLI S he
  have hE : (geoTransformAlong A S).E = MS.E :=
    HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq (𝔍 := A) (𝔪 := M) rfl S
  have hPB : ({ MarkedIdeal.pullback S.proj A with E := (geoTransformAlong A S).E } : MarkedIdeal n Y) = A' := by
    rw [hE, ← hProj, hA']
  have hAT' : RestrictEquiv (geoTransformAlong A S) A' :=
    (congrArg (fun J : MarkedIdeal n Y => RestrictEquiv (geoTransformAlong A S) J) hPB).mp hAT
  exact ⟨restrictEquiv_symm hAT', rfl⟩

/-- The endpoint stratum is the actual intrinsic q-superlevel, including q=0.
The current remainder domain, whole boundary, cosupport and admissible-centre
comparison are produced from the actual empty history itself. -/
theorem intrinsic_remainder_empty_transport
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) {q : ℕ}
    (hBound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ q)
    (S : BlowupTower X Y) (he : IsEmptyTower S) :
    let Z := {x | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let A := contactRemainderMarked (withN (coeffMarked M) Z) 0
    ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong S H) (geoTransformAlong M S).E,
      (∀ y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y =
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (S.proj y)) ∧
      {y | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y} = strictAlong S Z ∧
      let A' := contactRemainderMarked (withN (coeffMarked (geoTransformAlong M S))
        {y | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y}) 0
      IsInvDomain n A' ∧ RestrictEquiv A' (geoTransformAlong A S) ∧
        A'.E = (geoTransformAlong M S).E ∧ A'.cosupp = (geoTransformAlong A S).cosupp ∧
        ∀ C, A'.IsAdmissibleCentre C ↔ (geoTransformAlong A S).IsAdmissibleCentre C := by
  dsimp only
  let Z := {x | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let A := contactRemainderMarked (withN (coeffMarked M) Z) 0
  let MS := geoTransformAlong M S
  let hc := boundaryAdapted_empty_tower M h S he
  have hCount : ∀ y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y =
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (S.proj y) :=
    branchMultiplicity_empty_tower (isNormalCrossingsCarrier_of_boundaryAdapted h) S he
      (isNormalCrossingsCarrier_of_boundaryAdapted hc)
  have hZ := isClosedSubmanifold_highest_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  have hCurrentZ : {y | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y} =
      strictAlong S Z := by
    rw [ContactEmptyPrefix.strictAlong_of_isEmptyTower hZ.1 S he]
    ext y
    change (q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y) ↔
      q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (S.proj y)
    rw [hCount]
  have hCurrentBound : ∀ y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ q :=
    fun y => (hCount y).trans_le (hBound _)
  let Z' := {y | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y}
  let L' := withN (coeffMarked MS) Z'
  let A' := contactRemainderMarked L' 0
  have hMSN : MS.N = univ := by
    have hh := congrArg MarkedIdeal.N (ambient_empty_transform_eq_whole_pullback M hN hI S he)
    exact hh.trans (by change S.proj ⁻¹' M.N = univ; rw [hN, preimage_univ])
  have hMSI : MS.ideal.IsCoherent := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := M) (hN ▸ isClosedSubmanifold_univ) hI S (isGeoTestTower_of_isEmptyTower M S he)).2
  have hZ' : IsClosedSubmanifold n Z' :=
    isClosedSubmanifold_highest_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted hc) hCurrentBound
  have hL'I : L'.ideal.IsCoherent := isCoherent_coeffMarked (𝔪 := MS) hMSN hMSI
  have hL'W : L'.IsWellFormed :=
    ⟨hZ', hL'I, isSNCDivisor_of_boundaryAdapted hc, highest_stratum_isTransverse hc hCurrentBound⟩
  obtain ⟨hA', _hCos, _hAG, _hEq⟩ := contactRemainder_boundary_domain L' hL'W (coefficient_positive MS)
  obtain ⟨hTransport, _hE⟩ := coefficient_remainder_empty_transport M hN hI hd hZ S he
  have hCompare : RestrictEquiv A' (geoTransformAlong A S) := by
    change RestrictEquiv (contactRemainderMarked (withN (coeffMarked MS)
      {y | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y}) 0) _
    rw [hCurrentZ]
    exact hTransport
  exact ⟨hc, hCount, hCurrentZ, hA', hCompare, rfl, hCompare.cosupp_eq,
    fun C => hCompare.isAdmissibleCentre_iff⟩

/-- Original natural data select their SAME completed phase and causal birth
suffix internally. The freshly formed endpoint q-remainder uses the literal
original current parent restricted to the actual endpoint open. No caller
history, empty suffix, phase, transport or test certificate is assumed. -/
theorem exists_original_birth_current_remainder_transport
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hCompact : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoResolution L T ∧ IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
      ∀ y ∈ (geoTransformAlong M T).cosupp,
        let β := birthYear H T y
        let K := head T (T.length - β)
        let Q := tail T (T.length - β)
        let q := oldCount H T y
        q < r ∧ ∃ (hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong K H) (geoTransformAlong M K).E)
          (W : Opens (split T (T.length - β)).1),
          (W : Set (split T (T.length - β)).1) =
            {z | q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z}ᶜ ∧
          Q.proj y ∈ W ∧ IsEmptyTower (restrict W Q) ∧ (restrict W Q).length = T.length - β ∧
          let MW := MarkedIdeal.pullback (Subtype.val : W → (split T (T.length - β)).1)
            (geoTransformAlong M K)
          let HW := (Subtype.val : W → (split T (T.length - β)).1) ⁻¹' strictAlong K H
          let hW := boundaryAdapted_open W hc
          let S := restrict W Q
          let Zq := {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z}
          let Aq := contactRemainderMarked (withN (coeffMarked MW) Zq) 0
          geoTransformAlong MW S = MarkedIdeal.pullback (Subtype.val : openPreimage Q W → Y)
            (geoTransformAlong M T) ∧
          strictAlong S HW = (Subtype.val : openPreimage Q W → Y) ⁻¹' strictAlong T H ∧
          ∃ hcS : IsBoundaryAdaptedCarrier (n := n) (strictAlong S HW) (geoTransformAlong MW S).E,
            let A' := contactRemainderMarked (withN (coeffMarked (geoTransformAlong MW S))
              {z | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcS) z}) 0
            IsInvDomain n A' ∧ RestrictEquiv A' (geoTransformAlong Aq S) ∧
              A'.E = (geoTransformAlong MW S).E ∧ A'.cosupp = (geoTransformAlong Aq S).cosupp ∧
              ∀ C, A'.IsAdmissibleCentre C ↔ (geoTransformAlong Aq S).IsAdmissibleCentre C := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  obtain ⟨Y₀, P, _hCan, _hARes, Y, π, hπ, hResL, hMT, hHistory, hBirths⟩ :=
    exists_original_completed_phase_birth_remainder_tail I hI d hd hCompact h hr hBound
  let T : BlowupTower X Y := .step P
    (strictAlong P (selectedComponents (n := n) L.N L.cosupp)) π hπ
  refine ⟨Y, T, hResL, hMT, hHistory, ?_⟩
  intro y hy
  let β := birthYear H T y
  let k := T.length - β
  let K := head T k
  let Q := tail T k
  let q := oldCount H T y
  obtain ⟨_hβ, _hKLen, _hQLen, hqr, hc, W, hWSet, _hAtBirth, hyW, hCountW, _hDis,
      hEmpty, hLen, _hAq, _hAqTest, _hAqE, _hAqET, _hAqLen⟩ := hBirths y hy
  let MW := MarkedIdeal.pullback (Subtype.val : W → (split T k).1) (geoTransformAlong M K)
  let HW := (Subtype.val : W → (split T k).1) ⁻¹' strictAlong K H
  let hW := boundaryAdapted_open W hc
  let S := restrict W Q
  have hMK := ((isGeoTestTower_iff_head_tail M T k).mp hMT).1
  have hMQ := ((isGeoTestTower_iff_head_tail M T k).mp hMT).2
  have hKI := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := M) isClosedSubmanifold_univ hI K hMK).2
  have hKN : (geoTransformAlong M K).N = univ :=
    (DerivativeIdealTower.inclusions_tower M rfl hI (j := 0) (Nat.zero_le _) K hMK).2.1
  have hMWN : MW.N = univ := by
    change (Subtype.val : W → (split T k).1) ⁻¹' (geoTransformAlong M K).N = univ
    rw [hKN, preimage_univ]
  have hMWI : MW.ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hKI
  have hMWd : 1 ≤ MW.d := by
    change 1 ≤ (geoTransformAlong M K).d
    rw [d_geoTransformAlong]
    exact hd
  have hWBound : ∀ z : W, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z ≤ q := by
    intro z
    exact (branchMultiplicity_open W (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) z).trans_le (hCountW z)
  have hParent : geoTransformAlong MW S =
      MarkedIdeal.pullback (Subtype.val : openPreimage Q W → Y) (geoTransformAlong M T) := by
    rw [geoTransformAlong_restrict W (𝔪 := geoTransformAlong M K)
      (hKN ▸ isClosedSubmanifold_univ) hKI Q hMQ]
    rw [← geoTransformAlong_head_tail M T k]
  have hOld : strictAlong S HW =
      (Subtype.val : openPreimage Q W → Y) ⁻¹' strictAlong T H := by
    rw [strictAlong_restrict W Q (strictAlong K H)]
    have hCompose : strictAlong Q (strictAlong K H) = strictAlong T H := by
      rw [← MemberInterLocusAlong.strictAlong_append, head_append_tail T k]
    rw [hCompose]
  obtain ⟨hcS, _hCounts, _hStratum, hDomain, hCompare, hE, hCosupp, hCentres⟩ :=
    intrinsic_remainder_empty_transport (X := CMfd.of (n := n) W) MW hMWN hMWI hMWd
      hW hWBound S hEmpty
  exact ⟨hqr, hc, W, hWSet, hyW, hEmpty, hLen, hParent, hOld,
    hcS, hDomain, hCompare, hE, hCosupp, hCentres⟩

end
end Hironaka.HironakaOriginalNCBirthRemainderTransport
