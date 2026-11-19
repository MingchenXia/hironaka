import Hironaka.Resolution.HironakaOriginalNCZeroPriority
import Hironaka.Resolution.HironakaOriginalOldBranchCompactExtension

set_option autoImplicit false

/-!
# Internally selected next global highest-count canonical remainder phase

The next count is maximized on the WHOLE current parent cosupport. Its actual
phase open contains that entire compact cosupport. Natural original data
internally select the completed phase, the next count/open, the fresh actual
coefficient/remainder data, and a real canonical resolving remainder tower.
At positive next count the SAME tower has the actual selected-zero append
and a whole-cosupport-containing strict successor bound. At zero next count
only the canonical remainder resolution is asserted, without a selected
append of a possibly whole ambient component.

There is no caller history/canonical/value certificate, no independent finite
phase choice on a point-local birth open, and no original parent invariant or
general-NC canonical-driver identification.

Blueprint: hironaka-original-nc-next-highest-phase-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCNextHighestPhase

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower MemberInterTowerAlong
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneZeroContactRemainderExtension
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaBoundaryCoefficientStratumResolution HironakaOriginalOldBranchOpenHistory
  HironakaOriginalNCPhaseLex HironakaOriginalNCAllPrefixPhaseLex HironakaOriginalNCZeroPriority
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X : CMfd.{u} n}

/-- Output data for a genuinely selected fresh highest phase. The actual
canonical Q is a witness, not an input. Its SAME selected append and strict
whole-cosupport reset are retained at positive q; q=0 has no such append. -/
def HasCanonicalHighestRemainderPhase (M : MarkedIdeal n X) {H : Set X}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) (q : ℕ) : Prop :=
  let Z := {x | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
  let V := CanonicalCentres.canonicalInvariant n
  L.IsWellFormed ∧ 1 ≤ L.d ∧ IsCompact L.cosupp ∧
    IsInvDomain n A ∧ IsCompact A.cosupp ∧ A.E = M.E ∧
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y),
      IsCanonical A (V.inv A) Q ∧ IsGeoResolution A Q ∧
      IsGeoTestTower L Q ∧ IsGeoTestTower M Q ∧ CentresIn A.N Q ∧ CentresIn Z Q ∧
      (q = 0 ∨ 0 < q ∧
        ∃ (Y' : CMfd.{u} n) (π : Y' → Y)
          (hπ : IsBlowupAlong n (strictAlong Q (selectedComponents (n := n) L.N L.cosupp)) π),
          let S : BlowupTower X Y' := .step Q
            (strictAlong Q (selectedComponents (n := n) L.N L.cosupp)) π hπ
          IsGeoResolution L S ∧ IsGeoTestTower M S ∧ IsOriginalBranchTestTower M H S ∧
            ∃ (hcS : IsBoundaryAdaptedCarrier (n := n) (strictAlong S H) (geoTransformAlong M S).E)
              (U : Opens Y'),
              (U : Set Y') = (strictAlong S Z)ᶜ ∧ (geoTransformAlong M S).cosupp ⊆ U ∧
              ∀ y : U, branchMultiplicity
                (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U hcS)) y ≤ q - 1)

/-- A maximum on the WHOLE actual cosupport selects a genuine open containing
that whole compact set. This is not compactness of an arbitrary birth-open
intersection. The count may be zero, and is attained on the true restricted
cosupport without any caller maximum certificate. -/
theorem exists_whole_cosupport_highest_cut (M : MarkedIdeal n X)
    (hI : M.ideal.IsCoherent) (hK : IsCompact M.cosupp)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    {r : ℕ}
    (hLow : ∀ y ∈ M.cosupp, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) y < r)
    (hNe : M.cosupp.Nonempty) :
    ∃ (q : ℕ) (V : Opens X), q < r ∧
      (V : Set X) = {x | q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}ᶜ ∧
      M.cosupp ⊆ V ∧
      (∀ z : V, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open V h)) z ≤ q) ∧
      (∃ z ∈ (MarkedIdeal.pullback (Subtype.val : V → X) M).cosupp,
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open V h)) z = q) ∧
      IsCompact (MarkedIdeal.pullback (Subtype.val : V → X) M).cosupp := by
  let b := branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h)
  let J := b '' M.cosupp
  have hJFinite : J.Finite := (finite_Iic n).subset (by
    rintro v ⟨x, _hx, rfl⟩
    exact branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
  have hJNe : J.Nonempty := by
    obtain ⟨x, hx⟩ := hNe
    exact ⟨b x, x, hx, rfl⟩
  obtain ⟨q, hq, hMax⟩ := Set.exists_max_image J id hJFinite hJNe
  obtain ⟨x, hx, hxq⟩ := hq
  have hqr : q < r := hxq ▸ hLow x hx
  have hBound : ∀ y ∈ M.cosupp, b y ≤ q := fun y hy => hMax _ ⟨y, hy, rfl⟩
  let V : Opens X := ⟨{y | q + 1 ≤ b y}ᶜ,
    (isClosed_branchMultiplicity_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted h) (q + 1)).isOpen_compl⟩
  have hCover : M.cosupp ⊆ V := by
    intro y hy
    change ¬ q + 1 ≤ b y
    have hb := hBound y hy
    omega
  have hVBound : ∀ z : V,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open V h)) z ≤ q := by
    intro z
    have hz : ¬ q + 1 ≤ b z.val := z.property
    have hb : b z.val ≤ q := by omega
    exact (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted h)
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open V h)) z).trans_le hb
  let p : V := ⟨x, hCover hx⟩
  have hp : p ∈ (MarkedIdeal.pullback (Subtype.val : V → X) M).cosupp := by
    rw [cosupp_pullback_val M
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact hx
  have hpq : branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open V h)) p = q :=
    (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted h)
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open V h)) p).trans hxq
  exact ⟨q, V, hqr, rfl, hCover, hVBound, ⟨p, hp, hpq⟩,
    HironakaOriginalOldBranchCompactExtension.restricted_cosupport_compact M hI hK V hCover⟩

/-- Genuine current natural data internally select their fresh canonical
remainder phase. At q>0 the selected append uses the SAME resolving Q and
produces the strict successor bound; q=0 keeps only the valid remainder phase. -/
theorem exists_canonical_highest_remainder_phase (M : MarkedIdeal n X)
    (hN : M.N = univ) (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    (hK : IsCompact M.cosupp) {H : Set X}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) (q : ℕ)
    (hBound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ q) :
    HasCanonicalHighestRemainderPhase M h q := by
  rcases M with ⟨N, E, I, d⟩
  change N = univ at hN
  subst N
  dsimp only [HasCanonicalHighestRemainderPhase]
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
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
  have hLCos : L.cosupp = M.cosupp ∩ Z := cosupp_coeff_withN M rfl hI hd Z
  have hKL : IsCompact L.cosupp := by
    rw [hLCos]
    exact hK.inter_right hZ.1
  obtain ⟨hA, hACos, _hAG, _hEq⟩ := contactRemainder_boundary_domain L hLW hLd
  have hKA : IsCompact A.cosupp := by
    rw [hACos]
    exact hKL.inter_right hA.isWellFormed.isClosedSubmanifold_N.1
  refine ⟨hLW, hLd, hKL, hA, hKA, rfl, ?_⟩
  by_cases hq : q = 0
  · obtain ⟨Y, Q, hCan, hRes, hLQ, hRQ, _hClear⟩ :=
      exists_boundary_remainder_parent_phase L hLW hLd hKL
    obtain ⟨hMQ, hZQ⟩ := (coeff_restrict_tower_iff M rfl hI hd hZ Q).1.mp hLQ
    exact ⟨Y, Q, hCan, hRes, hLQ, hMQ, hRQ, hZQ, Or.inl hq⟩
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    obtain ⟨Y, Q, hCan, hResA, Y', π, hπ, hResL, hMS, hHistory,
        _hPrefixes, _hcQ, _hTop, _hMax, hcS, U, hU, hCover, _hcU, hReset⟩ :=
      exists_original_remainder_zero_append_permitted_reset I hI d hd hK h hqpos hBound
    obtain ⟨hLQ, hMQ, hZQ, _hLCosQ, _hACosQ⟩ :=
      original_remainder_cosupport_dictionary I hI d hd h hBound Q hResA.1
    have hRQ : CentresIn A.N Q := centresIn_of_isGeoTestTower_withN A A.N Q hResA.1
    have hCanonical : IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) Q :=
      ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment
        ((CanonicalCentres.canonicalInvariant n).inv A) Q hCan
    exact ⟨Y, Q, hCanonical, hResA, hLQ, hMQ, hRQ, hZQ,
      Or.inr ⟨hqpos, Y', π, hπ, hResL, hMS, hHistory, hcS, U, hU, hCover, hReset⟩⟩

/-- Original natural input internally chooses a completed r-phase, then its
next attained WHOLE-cosupport maximum q<r, the actual compact phase open and
the genuine fresh canonical remainder phase. No caller history or canonical
future is an input. The empty-parent and q=0 cases remain explicit. -/
theorem exists_original_next_highest_phase
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoResolution L T ∧ IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
      ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E,
        (geoTransformAlong M T).cosupp = ∅ ∨
          ∃ (q : ℕ) (V : Opens Y), q < r ∧
            (V : Set Y) = {y | q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y}ᶜ ∧
            (geoTransformAlong M T).cosupp ⊆ V ∧
            let MV := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong M T)
            let hV := boundaryAdapted_open V hc
            (∀ z : V, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hV) z ≤ q) ∧
            (∃ z ∈ MV.cosupp,
              branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hV) z = q) ∧
            IsCompact MV.cosupp ∧ HasCanonicalHighestRemainderPhase (X := CMfd.of (n := n) V) MV hV q := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  obtain ⟨Y, P, _hCan, _hResA, Y', π, hπ, hResL, hMT, hHistory,
      _hPrefixes, _hcP, _hTop, _hMax, hcT, U, _hU, hCover, hcU, hReset⟩ :=
    exists_original_remainder_zero_append_permitted_reset I hI d hd hK h hr hBound
  let T : BlowupTower X Y' := .step P (strictAlong P (selectedComponents (n := n) L.N L.cosupp)) π hπ
  refine ⟨Y', T, hResL, hMT, hHistory, hcT, ?_⟩
  by_cases hEmpty : (geoTransformAlong M T).cosupp = ∅
  · exact Or.inl hEmpty
  · have hNe : (geoTransformAlong M T).cosupp.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    have hTI : (geoTransformAlong M T).ideal.IsCoherent :=
      (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
        (𝔪 := M) isClosedSubmanifold_univ hI T hMT).2
    have hTN : (geoTransformAlong M T).N = univ :=
      (DerivativeIdealTower.inclusions_tower M rfl hI (j := 0) (Nat.zero_le _) T hMT).2.1
    have hKT : IsCompact (geoTransformAlong M T).cosupp :=
      HironakaOriginalOldBranchCompactExtension.current_cosupport_compact M
        isClosedSubmanifold_univ hI hK T hMT
    have hLow : ∀ y ∈ (geoTransformAlong M T).cosupp,
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) y < r := by
      intro y hy
      let p : U := ⟨y, hCover hy⟩
      have hb := hReset p
      have he := branchMultiplicity_open U (isNormalCrossingsCarrier_of_boundaryAdapted hcT)
        (isNormalCrossingsCarrier_of_boundaryAdapted hcU) p
      have hg : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) y ≤ r - 1 :=
        he.symm.trans_le hb
      omega
    obtain ⟨q, V, hqr, hVSet, hVCover, hVBound, hVAttained, hKV⟩ :=
      exists_whole_cosupport_highest_cut (geoTransformAlong M T) hTI hKT hcT hLow hNe
    let MV := MarkedIdeal.pullback (Subtype.val : V → Y') (geoTransformAlong M T)
    have hMVN : MV.N = univ := by
      change (Subtype.val : V → Y') ⁻¹' (geoTransformAlong M T).N = univ
      rw [hTN, preimage_univ]
    have hMVI : MV.ideal.IsCoherent :=
      GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hTI
    have hMVd : 1 ≤ MV.d := by
      change 1 ≤ (geoTransformAlong M T).d
      rw [d_geoTransformAlong]
      exact hd
    have hPhase := exists_canonical_highest_remainder_phase (X := CMfd.of (n := n) V) MV hMVN hMVI hMVd hKV
      (boundaryAdapted_open V hcT) q hVBound
    exact Or.inr ⟨q, V, hqr, hVSet, hVCover, hVBound, hVAttained, hKV, hPhase⟩

end
end Hironaka.HironakaOriginalNCNextHighestPhase
