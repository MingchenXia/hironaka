import Hironaka.Resolution.HironakaOriginalNCCountHistory
import Hironaka.Resolution.HironakaOriginalNCZeroPriority

set_option autoImplicit false

/-!
# Actual causal birth tails inside a naturally completed highest-count phase

The natural producer internally chooses the SAME canonical A-resolution and
selected-zero append already supplied by ZeroPriority. At each terminal M
cosupport point, the causal birth split has a genuine low-count open avoiding
the current strict original highest stratum. The SAME literal restricted
suffix has only empty centres, retains every year, and is a true test tower
of the internally formed birth remainder datum with its whole boundary.

This is one completed-phase comparison, not a subsequent nonempty phase
interpreter or an identification with the original canonical general-NC driver.
Blueprint: hironaka-original-nc-birth-phase-empty-tail-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCBirthPhaseTail

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower MemberInterTowerAlong RestrictEmptyTower
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneZeroContactRemainderExtension
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaBoundaryCoefficientStratumResolution HironakaCoherentTransformExtension
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCAllPrefixPhaseLex
  HironakaOriginalNCCountHistory HironakaOriginalNCZeroPriority
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
open ResolutionDriver (IsCanonicalSegment)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem centresOver_of_centresIn_closed {F : Set X} (hF : IsClosed F) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresIn F T → CentresOver F T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, hT =>
      ⟨centresOver_of_centresIn_closed hF T hT.1,
        fun _ hx => strictAlong_subset_preimage T hF (hT.2 hx)⟩

private theorem ambient_N_geoTransformAlong (M : MarkedIdeal n X) (hN : M.N = univ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), (geoTransformAlong M T).N = univ
  | _, .refl => hN
  | _, .step T C π hπ => by
      rw [N_geoTransformAlong_step, ambient_N_geoTransformAlong M hN T,
        MarkedIdeals.MarkedIdeal.geoStrictTransform_univ hπ]

/-- A real completed coefficient-stratum phase lowers the original old count
at every point of the SAME current original cosupport. No history/count
certificate is an additional premise. -/
theorem completed_phase_terminal_oldCount_lt
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hRes : IsGeoResolution
      (withN (coeffMarked (⟨univ, E, I, d⟩ : MarkedIdeal n X))
        {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (⟨univ, E, I, d⟩ : MarkedIdeal n X) T).cosupp) :
    oldCount H T y < r := by
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  have hZ := isClosedSubmanifold_highest_superlevel
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  obtain ⟨hMT, hTZ⟩ := (coeff_restrict_tower_iff M rfl hI hd hZ T).1.mp hRes.1
  have hLCos := (coeff_restrict_tower_iff M rfl hI hd hZ T).2 hRes.1
  obtain ⟨hc, _hUpper, _hTop, hHigh⟩ :=
    exists_highest_history_current_pair_high_locus I hI d h hr hBound T hMT hTZ
  rw [oldCount_eq T (isNormalCrossingsCarrier_of_boundaryAdapted hc) y]
  apply lt_of_not_ge
  intro hyHigh
  have hyZ : y ∈ strictAlong T Z := hHigh ▸ hyHigh
  have hyL : y ∈ (geoTransformAlong L T).cosupp := hLCos.symm ▸ ⟨hy, hyZ⟩
  rw [hRes.2] at hyL
  exact hyL

/-- The SAME causal split of a real completed r-phase produces its actual
low-count birth open and a genuinely empty, uncompressed restricted suffix.
The legal phase domain here is supplied internally by the natural theorem. -/
theorem completed_phase_birth_empty_tail
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hRes : IsGeoResolution
      (withN (coeffMarked (⟨univ, E, I, d⟩ : MarkedIdeal n X))
        {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (⟨univ, E, I, d⟩ : MarkedIdeal n X) T).cosupp) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let β := birthYear H T y
    let K := head T (T.length - β)
    let Q := tail T (T.length - β)
    let q := oldCount H T y
    β ≤ T.length ∧ K.length = β ∧ Q.length = T.length - β ∧ q < r ∧
      ∃ (hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong K H) (geoTransformAlong M K).E)
        (W : Opens (split T (T.length - β)).1),
        (W : Set (split T (T.length - β)).1) =
          {z | q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z}ᶜ ∧
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) (Q.proj y) = q ∧
        Q.proj y ∈ W ∧
        (∀ z : W, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z.val ≤ q) ∧
        Disjoint (W : Set (split T (T.length - β)).1) (strictAlong K Z) ∧
        IsEmptyTower (restrict W Q) ∧ (restrict W Q).length = T.length - β := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  let β := birthYear H T y
  let k := T.length - β
  let K := head T k
  let Q := tail T k
  let q := oldCount H T y
  have hβ : β ≤ T.length := birthYear_le_length H T y
  have hKLen : K.length = β := by
    rw [length_head]
    omega
  have hQLen : Q.length = T.length - β := by
    rw [length_tail]
    omega
  have hqr : q < r := completed_phase_terminal_oldCount_lt I hI d hd h hr hBound T hRes y hy
  have hZ := isClosedSubmanifold_highest_superlevel
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  obtain ⟨hLK, hLQ⟩ := (isGeoTestTower_iff_head_tail L T k).mp hRes.1
  obtain ⟨hMK, hKZ⟩ := (coeff_restrict_tower_iff M rfl hI hd hZ K).1.mp hLK
  obtain ⟨hc, _hUpper, _hTop, hHigh⟩ :=
    exists_highest_history_current_pair_high_locus I hI d h hr hBound K hMK hKZ
  let b := branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc)
  have hBirth : b (Q.proj y) = q := by
    calc
      b (Q.proj y) = oldCount H K (Q.proj y) := (oldCount_eq K _ _).symm
      _ = countAt H T y β := (countAt_eq_prefix_count H T y β).symm
      _ = q := birthYear_spec H T y
  let W : Opens (split T k).1 :=
    ⟨{z | q + 1 ≤ b z}ᶜ,
      (isClosed_branchMultiplicity_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted hc)
        (q + 1)).isOpen_compl⟩
  have hyW : Q.proj y ∈ W := by
    change ¬ q + 1 ≤ b (Q.proj y)
    rw [hBirth]
    omega
  have hBoundW : ∀ z : W, b z.val ≤ q := by
    intro z
    have hz : ¬ q + 1 ≤ b z.val := z.property
    omega
  have hDis : Disjoint (W : Set (split T k).1) (strictAlong K Z) := by
    apply Set.disjoint_left.mpr
    intro z hzW hzZ
    have hzBound : b z ≤ q := hBoundW ⟨z, hzW⟩
    have hzTop : r ≤ b z := by
      have hzHigh : z ∈ {w | r ≤ branchMultiplicity
          (isNormalCrossingsCarrier_of_boundaryAdapted hc) w} := hHigh.symm ▸ hzZ
      exact hzHigh
    omega
  have hQIn : CentresIn (strictAlong K Z) Q := by
    have hQIn' := centresIn_of_isGeoTestTower_withN (geoTransformAlong L K)
      (geoTransformAlong L K).N Q hLQ
    have hKN : (geoTransformAlong L K).N = strictAlong K Z := N_geoTransformAlong L K
    rwa [hKN] at hQIn'
  have hEmpty : IsEmptyTower (restrict W Q) :=
    isEmptyTower_restrict_of_centresOver W hDis Q
      (centresOver_of_centresIn_closed (isClosed_strictAlong K hZ.1) Q hQIn)
  refine ⟨hβ, hKLen, hQLen, hqr, hc, W, rfl, hBirth, hyW, hBoundW, hDis, hEmpty, ?_⟩
  rw [length_restrict]
  exact hQLen

/-- The birth remainder is formed from the actual local current parent data.
Its domain and SAME uncompressed suffix testness are real outputs, with all
retained and newly born boundary slots, including empty slots. -/
theorem completed_phase_birth_remainder_tail_test
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hRes : IsGeoResolution
      (withN (coeffMarked (⟨univ, E, I, d⟩ : MarkedIdeal n X))
        {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (⟨univ, E, I, d⟩ : MarkedIdeal n X) T).cosupp) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let β := birthYear H T y
    let K := head T (T.length - β)
    let Q := tail T (T.length - β)
    let q := oldCount H T y
    β ≤ T.length ∧ K.length = β ∧ Q.length = T.length - β ∧ q < r ∧
      ∃ (hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong K H) (geoTransformAlong M K).E)
        (W : Opens (split T (T.length - β)).1),
        (W : Set (split T (T.length - β)).1) =
          {z | q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z}ᶜ ∧
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) (Q.proj y) = q ∧
        Q.proj y ∈ W ∧
        (∀ z : W, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z.val ≤ q) ∧
        Disjoint (W : Set (split T (T.length - β)).1) (strictAlong K Z) ∧
        IsEmptyTower (restrict W Q) ∧ (restrict W Q).length = T.length - β ∧
        let MW := MarkedIdeal.pullback (Subtype.val : W → (split T (T.length - β)).1)
          (geoTransformAlong M K)
        let hW := boundaryAdapted_open W hc
        let Zq := {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z}
        let Aq := contactRemainderMarked (withN (coeffMarked MW) Zq) 0
        IsInvDomain n Aq ∧ IsGeoTestTower Aq (restrict W Q) ∧ Aq.E = MW.E ∧
          (geoTransformAlong Aq (restrict W Q)).E = (geoTransformAlong MW (restrict W Q)).E ∧
          (geoTransformAlong Aq (restrict W Q)).E.length = MW.E.length + (T.length - β) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  let β := birthYear H T y
  let k := T.length - β
  let K := head T k
  let Q := tail T k
  let q := oldCount H T y
  obtain ⟨hβ, hKLen, hQLen, hqr, hc, W, hWSet, hBirth, hyW, hBoundW, hDis, hEmpty, hLen⟩ :=
    completed_phase_birth_empty_tail I hI d hd h hr hBound T hRes y hy
  let MW := MarkedIdeal.pullback (Subtype.val : W → (split T k).1) (geoTransformAlong M K)
  let hW := boundaryAdapted_open W hc
  let Zq := {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z}
  let Lq := withN (coeffMarked MW) Zq
  let Aq := contactRemainderMarked Lq 0
  have hLocalBound : ∀ z : W,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z ≤ q := by
    intro z
    exact (branchMultiplicity_open W (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) z).trans_le (hBoundW z)
  have hZ := isClosedSubmanifold_highest_superlevel
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  have hLK := ((isGeoTestTower_iff_head_tail L T k).mp hRes.1).1
  have hMK := ((coeff_restrict_tower_iff M rfl hI hd hZ K).1.mp hLK).1
  have hKI := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := M) isClosedSubmanifold_univ hI K hMK).2
  have hMWI : MW.ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hKI
  have hMWN : MW.N = univ := by
    change (Subtype.val : W → (split T k).1) ⁻¹' (geoTransformAlong M K).N = univ
    rw [ambient_N_geoTransformAlong M rfl K, preimage_univ]
  have hZq : IsClosedSubmanifold n Zq :=
    isClosedSubmanifold_highest_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted hW) hLocalBound
  have hLqI : Lq.ideal.IsCoherent := by
    change (coeffMarked MW).ideal.IsCoherent
    exact CoefficientIdealRestriction.isCoherent_coeffMarked
      (X := CMfd.of (n := n) W) (𝔪 := MW) hMWN hMWI
  have hZqE : IsTransverse n Zq MW.E :=
    highest_stratum_isTransverse (X := CMfd.of (n := n) W) hW hLocalBound
  have hLqW : Lq.IsWellFormed :=
    ⟨hZq, hLqI, isSNCDivisor_of_boundaryAdapted hW, hZqE⟩
  have hLqd : 1 ≤ Lq.d := by
    change 1 ≤ (Finset.range MW.d).prod (fun i => MW.d - i)
    have hp : 0 < (Finset.range MW.d).prod (fun i => MW.d - i) :=
      Finset.prod_pos fun i hi => by
        have hi' := Finset.mem_range.mp hi
        omega
    omega
  obtain ⟨hAq, _hCos, _hAG, _hEq⟩ :=
    contactRemainder_boundary_domain (X := CMfd.of (n := n) W) Lq hLqW hLqd
  have hTestAq : IsGeoTestTower Aq (restrict W Q) := isGeoTestTower_of_isEmptyTower Aq _ hEmpty
  have hE : Aq.E = MW.E := rfl
  have hET : (geoTransformAlong Aq (restrict W Q)).E = (geoTransformAlong MW (restrict W Q)).E :=
    geoTransformAlong_E_eq_of_E_eq hE (restrict W Q)
  refine ⟨hβ, hKLen, hQLen, hqr, hc, W, hWSet, hBirth, hyW, hBoundW, hDis, hEmpty,
    hLen, hAq, hTestAq, hE, hET, ?_⟩
  rw [length_E_geoTransformAlong, hE, hLen]

/-- Only natural original data are inputs. The SAME canonical A-phase and its
actual selected-zero append are chosen internally; every endpoint birth
remainder then has a genuine SAME uncompressed suffix test on its actual open.
No caller T, phase, history, count, empty-tower or A-test certificate is used. -/
theorem exists_original_completed_phase_birth_remainder_tail
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hCompact : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    let A := contactRemainderMarked L 0
    ∃ (Y : CMfd.{u} n) (P : BlowupTower X Y),
      IsCanonicalSegment A ((CanonicalCentres.canonicalInvariant n).inv A) P ∧ IsGeoResolution A P ∧
      ∃ (Y' : CMfd.{u} n) (π : Y' → Y)
        (hπ : IsBlowupAlong n (strictAlong P (selectedComponents (n := n) L.N L.cosupp)) π),
        let T : BlowupTower X Y' := .step P
          (strictAlong P (selectedComponents (n := n) L.N L.cosupp)) π hπ
        IsGeoResolution L T ∧ IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
        ∀ y ∈ (geoTransformAlong M T).cosupp,
          let β := birthYear H T y
          let K := head T (T.length - β)
          let Q := tail T (T.length - β)
          let q := oldCount H T y
          β ≤ T.length ∧ K.length = β ∧ Q.length = T.length - β ∧ q < r ∧
            ∃ (hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong K H) (geoTransformAlong M K).E)
              (W : Opens (split T (T.length - β)).1),
              (W : Set (split T (T.length - β)).1) =
                {z | q + 1 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z}ᶜ ∧
              branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) (Q.proj y) = q ∧
              Q.proj y ∈ W ∧
              (∀ z : W, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) z.val ≤ q) ∧
              Disjoint (W : Set (split T (T.length - β)).1) (strictAlong K Z) ∧
              IsEmptyTower (restrict W Q) ∧ (restrict W Q).length = T.length - β ∧
              let MW := MarkedIdeal.pullback (Subtype.val : W → (split T (T.length - β)).1)
                (geoTransformAlong M K)
              let hW := boundaryAdapted_open W hc
              let Zq := {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z}
              let Aq := contactRemainderMarked (withN (coeffMarked MW) Zq) 0
              IsInvDomain n Aq ∧ IsGeoTestTower Aq (restrict W Q) ∧ Aq.E = MW.E ∧
                (geoTransformAlong Aq (restrict W Q)).E = (geoTransformAlong MW (restrict W Q)).E ∧
                (geoTransformAlong Aq (restrict W Q)).E.length = MW.E.length + (T.length - β) := by
  dsimp only
  obtain ⟨Y, P, hCan, hResA, Y', π, hπ, hResL, hMT, hHistory, _hPrefixes,
      _hcP, _hTop, _hMax, _hcT, _U, _hU, _hCover, _hcU, _hReset⟩ :=
    exists_original_remainder_zero_append_permitted_reset I hI d hd hCompact h hr hBound
  refine ⟨Y, P, hCan, hResA, Y', π, hπ, hResL, hMT, hHistory, ?_⟩
  intro y hy
  exact completed_phase_birth_remainder_tail_test I hI d hd h hr hBound _ hResL y hy

end
end Hironaka.HironakaOriginalNCBirthPhaseTail
