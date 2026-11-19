import Hironaka.Resolution.HironakaOriginalNCNextHighestPhase
import Hironaka.Resolution.HironakaOriginalNCBirthPhaseTail

set_option autoImplicit false

/-!
# The SAME completed history has entire birth windows inside the next phase

The next global phase cut is the exact low-count open. Every point's SAME
completed-history birth suffix is actually empty on its entire birth open;
the true empty-count dictionary and whole old-carrier trace show that the
ENTIRE endpoint birth window has count at most that point's terminal count.
It is therefore contained in the next global cut. No second completed tower
is chosen and no local compactness hypothesis is introduced.

The old coefficient-resolution interface is used only at the SAME completed
T. It is not applied to a later nonempty composite. This module does not
treat the selected-F append as a high-remainder test, or identify a zero-count
parent canonical tail with a coefficient/remainder canonical tail.

Blueprint: hironaka-original-nc-next-highest-birth-window-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCNextHighestBirthWindows

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower MemberInterTowerAlong
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneZeroContactRemainderExtension
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalOldBranchCountDrop
  HironakaOriginalNCCountHistory HironakaOriginalNCBirthPhaseTail
  HironakaOriginalNCNextHighestPhase
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionInvariantExt (IsEmptyTower)

private theorem count_eq_of_carrier_eq
    {n : ℕ} {D : Type u} [TopologicalSpace D] [ChartedSpace (ComplexModel n) D]
    {A B : Set D} (hA : IsNormalCrossingsCarrier (n := n) A)
    (hB : IsNormalCrossingsCarrier (n := n) B) (hEq : A = B) (p : D) :
    branchMultiplicity hA p = branchMultiplicity hB p := by
  subst B
  rfl

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Output data of a SAME completed-history birth window. Its ENTIRE endpoint
open is nested in the next actual global count cut; all old/born slots and
actual empty years are retained with true parent/remainder records. -/
def HasNestedBirthWindow (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y)
    (hcT : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E)
    (qmax : ℕ) (V : Opens Y) (y : Y) : Prop :=
  let β := birthYear H T y
  let K := head T (T.length - β)
  let Q := tail T (T.length - β)
  let q := oldCount H T y
  β ≤ T.length ∧ K.length = β ∧ Q.length = T.length - β ∧ q ≤ qmax ∧
    ∃ (hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong K H) (geoTransformAlong M K).E)
      (W : Opens (split T (T.length - β)).1),
      (W : Set (split T (T.length - β)).1) =
        {z | q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z}ᶜ ∧
      Q.proj y ∈ W ∧ IsEmptyTower (restrict W Q) ∧ (restrict W Q).length = T.length - β ∧
      let MW := MarkedIdeal.pullback (Subtype.val : W → (split T (T.length - β)).1)
        (geoTransformAlong M K)
      let HW := (Subtype.val : W → (split T (T.length - β)).1) ⁻¹' strictAlong K H
      let hW := boundaryAdapted_open W hc
      let S := restrict W Q
      let J := openPreimage Q W
      let Zq := {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z}
      let Aq := contactRemainderMarked (withN (coeffMarked MW) Zq) 0
      geoTransformAlong MW S = MarkedIdeal.pullback (Subtype.val : J → Y) (geoTransformAlong M T) ∧
      strictAlong S HW = (Subtype.val : J → Y) ⁻¹' strictAlong T H ∧
      IsInvDomain n Aq ∧ IsGeoTestTower Aq S ∧ Aq.E = MW.E ∧
      (geoTransformAlong Aq S).E = (geoTransformAlong MW S).E ∧
      (geoTransformAlong Aq S).E.length = MW.E.length + (T.length - β) ∧
      J ≤ V ∧ ∀ p : J, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) p.val ≤ q

/-- The actual generic completed-phase birth producer is used on THIS T.
The empty suffix gives a bound on its whole endpoint open, which proves
nesting into the actual next low-count cut without a caller birth certificate. -/
theorem same_completed_phase_birth_window_inside_count_cut
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hRes : IsGeoResolution
      (withN (coeffMarked (⟨univ, E, I, d⟩ : MarkedIdeal n X))
        {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) T)
    (hcT : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H)
      (geoTransformAlong (⟨univ, E, I, d⟩ : MarkedIdeal n X) T).E)
    (qmax : ℕ) (V : Opens Y)
    (hVSet : (V : Set Y) =
      {z | qmax + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) z}ᶜ)
    (hCover : (geoTransformAlong (⟨univ, E, I, d⟩ : MarkedIdeal n X) T).cosupp ⊆ V)
    (y : Y) (hy : y ∈ (geoTransformAlong (⟨univ, E, I, d⟩ : MarkedIdeal n X) T).cosupp) :
    HasNestedBirthWindow (⟨univ, E, I, d⟩ : MarkedIdeal n X) H T hcT qmax V y := by
  dsimp only [HasNestedBirthWindow]
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let β := birthYear H T y
  let k := T.length - β
  let K := head T k
  let Q := tail T k
  let q := oldCount H T y
  obtain ⟨hβ, hKLen, hQLen, _hqr, hc, W, hWSet, _hAtBirth, hyW, hCountW, _hDis,
      hEmpty, hLen, hAq, hAqTest, hAqE, hAqET, hAqLen⟩ :=
    completed_phase_birth_remainder_tail_test I hI d hd h hr hBound T hRes y hy
  let MW := MarkedIdeal.pullback (Subtype.val : W → (split T k).1) (geoTransformAlong M K)
  let HW := (Subtype.val : W → (split T k).1) ⁻¹' strictAlong K H
  let hW := boundaryAdapted_open W hc
  let S := restrict W Q
  let J := openPreimage Q W
  have hZ := isClosedSubmanifold_highest_superlevel
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  have hMT : IsGeoTestTower M T :=
    ((coeff_restrict_tower_iff M rfl hI hd hZ T).1.mp hRes.1).1
  have hMK := ((isGeoTestTower_iff_head_tail M T k).mp hMT).1
  have hMQ := ((isGeoTestTower_iff_head_tail M T k).mp hMT).2
  have hKI := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := M) isClosedSubmanifold_univ hI K hMK).2
  have hKN : (geoTransformAlong M K).N = univ :=
    (DerivativeIdealTower.inclusions_tower M rfl hI (j := 0) (Nat.zero_le _) K hMK).2.1
  have hParent : geoTransformAlong MW S =
      MarkedIdeal.pullback (Subtype.val : J → Y) (geoTransformAlong M T) := by
    rw [geoTransformAlong_restrict W (𝔪 := geoTransformAlong M K)
      (hKN ▸ isClosedSubmanifold_univ) hKI Q hMQ]
    rw [← geoTransformAlong_head_tail M T k]
  have hOld : strictAlong S HW = (Subtype.val : J → Y) ⁻¹' strictAlong T H := by
    rw [strictAlong_restrict W Q (strictAlong K H)]
    have hCompose : strictAlong Q (strictAlong K H) = strictAlong T H := by
      rw [← MemberInterLocusAlong.strictAlong_append, head_append_tail T k]
    rw [hCompose]
  have hWBound : ∀ p : W,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) p ≤ q := by
    intro p
    exact (branchMultiplicity_open W (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) p).trans_le (hCountW p)
  let hNCJ := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open J hcT)
  have hNCS : IsNormalCrossingsCarrier (n := n) (strictAlong S HW) := hOld.symm ▸ hNCJ
  have hEmptyCount := branchMultiplicity_empty_tower
    (isNormalCrossingsCarrier_of_boundaryAdapted hW) S hEmpty hNCS
  have hCurrentBound : ∀ p : J,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) p.val ≤ q := by
    intro p
    calc
      _ = branchMultiplicity hNCJ p :=
        (branchMultiplicity_open J (isNormalCrossingsCarrier_of_boundaryAdapted hcT) hNCJ p).symm
      _ = branchMultiplicity hNCS p := (count_eq_of_carrier_eq hNCS hNCJ hOld p).symm
      _ = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) (S.proj p) := hEmptyCount p
      _ ≤ q := hWBound (S.proj p)
  have hPointCount : q = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) y :=
    oldCount_eq T (isNormalCrossingsCarrier_of_boundaryAdapted hcT) y
  have hqmax : q ≤ qmax := by
    have hyV : y ∈ (V : Set Y) := hCover hy
    rw [hVSet] at hyV
    change ¬ qmax + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) y at hyV
    omega
  have hJV : J ≤ V := by
    intro z hz
    let p : J := ⟨z, hz⟩
    have hb := (hCurrentBound p).trans hqmax
    change branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) z ≤ qmax at hb
    change z ∈ (V : Set Y)
    rw [hVSet]
    change ¬ qmax + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) z
    omega
  exact ⟨hβ, hKLen, hQLen, hqmax, hc, W, hWSet, hyW, hEmpty, hLen,
    hParent, hOld, hAq, hAqTest, hAqE, hAqET, hAqLen, hJV, hCurrentBound⟩

/-- Natural original input chooses the completed T and next phase ONCE. The
generic birth theorem is then applied to that SAME T at every point; no
independently selected birth tower, window, count, domain or empty suffix is
supplied by the caller. -/
theorem exists_original_next_highest_phase_with_nested_birth_windows
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
          ∃ (qmax : ℕ) (V : Opens Y), qmax < r ∧
            (V : Set Y) = {z | qmax + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z}ᶜ ∧
            (geoTransformAlong M T).cosupp ⊆ V ∧
            let MV := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong M T)
            let hV := boundaryAdapted_open V hc
            (∀ z : V, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hV) z ≤ qmax) ∧
            (∃ z ∈ MV.cosupp,
              branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hV) z = qmax) ∧
            IsCompact MV.cosupp ∧ HasCanonicalHighestRemainderPhase (X := CMfd.of (n := n) V) MV hV qmax ∧
            ∀ y ∈ (geoTransformAlong M T).cosupp, HasNestedBirthWindow M H T hc qmax V y := by
  dsimp only
  obtain ⟨Y, T, hResL, hMT, hHistory, hc, hNext⟩ :=
    exists_original_next_highest_phase I hI d hd hK h hr hBound
  refine ⟨Y, T, hResL, hMT, hHistory, hc, ?_⟩
  rcases hNext with hEmpty | ⟨qmax, V, hqr, hVSet, hCover, hVBound, hAttained, hKV, hPhase⟩
  · exact Or.inl hEmpty
  · refine Or.inr ⟨qmax, V, hqr, hVSet, hCover, hVBound, hAttained, hKV, hPhase, ?_⟩
    intro y hy
    exact same_completed_phase_birth_window_inside_count_cut I hI d hd h hr hBound
      T hResL hc qmax V hVSet hCover y hy

end
end Hironaka.HironakaOriginalNCNextHighestBirthWindows
