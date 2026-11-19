import Hironaka.Resolution.HironakaOriginalNCNextHighestPhase
import Hironaka.Resolution.HironakaOriginalOldBranchAppend
import Hironaka.Invariant.DropMembers

set_option autoImplicit false

/-!
# The zero old-count phase selects the actual parent canonical resolution

The ordinary pointwise nonzero hypothesis is already an original general-NC
resolution input. It internally supplies the actual parent invariant domain,
which is preserved by the actual history. At zero old count on the WHOLE
cosupport the old carrier misses it, so the actual ordinary parent canonical
resolution retains every original branch history by the real drop-members
theorem. No selected-zero blowup of a whole ambient component is used.

The natural final theorem internally retains the SAME completed phase and
next-highest selection. It proves original resolution/history for its literal
zero-count completion, and asserts canonicality only for the actual current
parent tail. It does not rebase canonicality through a nonempty old phase or
identify the original general-NC invariant.

Blueprint: hironaka-original-nc-zero-count-parent-completion-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCZeroCountCompletion

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  GermIdealOrder NormalCrossings DropMembers GermIdealPullbackCalculus
  DivisorExponentAlong BlowupRestrictOpen
  CoefficientIdeal CoefficientIdealRestriction MemberInterTowerAlong
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalOldBranchCompactExtension
  HironakaOriginalNCNextHighestPhase
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X : CMfd.{u} n}

private theorem ambient_domain (M : MarkedIdeal n X) (hN : M.N = univ)
    (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    (hne : ∀ x, IsNonzeroAlongAt univ M.ideal x) (hE : IsSNCDivisor n M.E) :
    IsInvDomain n M := by
  refine ⟨⟨?_, hI, hE, ?_⟩, ?_, hd, ?_⟩
  · rw [hN]
    exact isClosedSubmanifold_univ
  · rw [hN]
    exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE
  · rw [hN]
    exact fun x _ => ⟨n, le_rfl, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  · intro x _hx
    simpa only [hN] using hne x

/-- The real drop-members theorem restores every literal original old branch
away from the WHOLE cosupport, on the SAME tested tower. No adaptedness or
global SNC presentation of the old carrier is required for this generic fact. -/
theorem isOriginalBranchTestTower_of_disjoint_carrier (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    {H : Set X} (hDis : Disjoint M.cosupp H)
    {Y : CMfd.{u} n} (S : BlowupTower X Y) (hS : IsGeoTestTower M S) :
    IsOriginalBranchTestTower M H S := by
  intro W B hSNC hUnion
  let MW := MarkedIdeal.pullback (Subtype.val : W → X) M
  let N : MarkedIdeal n W := { MW with E := B ++ MW.E }
  have hNW : IsClosedSubmanifold n N.N := isClosedSubmanifold_preimage_val hN W
  have hIW : N.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hI
  have hSmall : IsGeoTestTower ({ N with E := MW.E } : MarkedIdeal n W) (restrict W S) :=
    isGeoTestTower_restrict W hN hI S hS
  have hSub : ∀ D ∈ MW.E, D ∈ N.E := fun _ hD => List.mem_append_right _ hD
  have hMiss : ∀ D ∈ N.E, D ∉ MW.E → IsClosed D ∧ Disjoint N.cosupp D := by
    intro D hD hNot
    have hDB : D ∈ B := (List.mem_append.mp hD).resolve_right hNot
    refine ⟨hSNC.1 D hD, Set.disjoint_left.mpr ?_⟩
    intro p hpM hpD
    have hpGlobal : p.val ∈ M.cosupp := by
      change p ∈ MW.cosupp at hpM
      rw [cosupp_pullback_val M
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)] at hpM
      exact hpM
    have hpH : p.val ∈ H := by
      change p ∈ (Subtype.val : W → X) ⁻¹' H
      rw [hUnion]
      exact mem_iUnion₂.mpr ⟨D, hDB, hpD⟩
    exact Set.disjoint_left.mp hDis hpGlobal hpH
  exact ((isGeoTestTower_withE_iff_of_disjoint
    (X := CMfd.of (n := n) W) N hNW hIW hSub hMiss (restrict W S)).1).mp hSmall

/-- The original natural nonzero hypothesis internally supplies the true
parent domain. Zero old count only on its WHOLE cosupport suffices for a SAME
ordinary parent canonical resolution with every original branch history. -/
theorem exists_canonical_parent_resolution_of_zero_cosupport_count (M : MarkedIdeal n X)
    (hN : M.N = univ) (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    (hne : ∀ x, IsNonzeroAlongAt univ M.ideal x) (hK : IsCompact M.cosupp)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hZero : ∀ x ∈ M.cosupp,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 0) :
    ∃ (Y : CMfd.{u} n) (S : BlowupTower X Y),
      IsCanonical M ((CanonicalCentres.canonicalInvariant n).inv M) S ∧
      IsGeoResolution M S ∧ IsOriginalBranchTestTower M H S := by
  have hDom := ambient_domain M hN hI hd hne (isSNCDivisor_of_boundaryAdapted h)
  have hDis : Disjoint M.cosupp H := by
    apply Set.disjoint_left.mpr
    intro x hx hxH
    have hp := (branchMultiplicity_pos_iff (isNormalCrossingsCarrier_of_boundaryAdapted h) x).mpr hxH
    have hz := hZero x hx
    omega
  obtain ⟨Y, S, hCan, hRes⟩ :=
    HironakaAdmissibleSequence.exists_isGeoResolution_isCanonical_of_isCompact
      (CanonicalCentres.canonicalInvariant n) hDom hK
  exact ⟨Y, S, hCan, hRes,
    isOriginalBranchTestTower_of_disjoint_carrier M hDom.isWellFormed.isClosedSubmanifold_N hI hDis S hRes.1⟩

/-- The original natural general-NC nonzero input internally supplies the
domain through the SAME completed history. The actual next-count-zero branch
then has an internally chosen parent-canonical whole-ambient resolving tail.
Only that current-parent tail is claimed canonical, not its nonempty prefix. -/
theorem exists_original_next_highest_phase_with_zero_completion
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hne : ∀ x, IsNonzeroAlongAt univ I x)
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
            IsCompact MV.cosupp ∧ HasCanonicalHighestRemainderPhase (X := CMfd.of (n := n) V) MV hV q ∧
            (q = 0 → ∃ (J : CMfd.{u} n) (S : BlowupTower Y J),
              IsCanonical (geoTransformAlong M T)
                ((CanonicalCentres.canonicalInvariant n).inv (geoTransformAlong M T)) S ∧
              IsGeoResolution (geoTransformAlong M T) S ∧
              IsOriginalBranchTestTower (geoTransformAlong M T) (strictAlong T H) S ∧
              IsGeoResolution M (T.append S) ∧ IsOriginalBranchTestTower M H (T.append S)) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  obtain ⟨Y, T, hResL, hMT, hHistory, hc, hNext⟩ :=
    exists_original_next_highest_phase I hI d hd hK h hr hBound
  refine ⟨Y, T, hResL, hMT, hHistory, hc, ?_⟩
  rcases hNext with hEmpty | ⟨q, V, hqr, hVSet, hCover, hVBound, hAttained, hKV, hPhase⟩
  · exact Or.inl hEmpty
  · refine Or.inr ⟨q, V, hqr, hVSet, hCover, hVBound, hAttained, hKV, hPhase, ?_⟩
    intro hq
    have hDom := ambient_domain M rfl hI hd hne (isSNCDivisor_of_boundaryAdapted h)
    have hDomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom T hMT
    have hTN : (geoTransformAlong M T).N = univ :=
      (DerivativeIdealTower.inclusions_tower M rfl hI (j := 0) (Nat.zero_le _) T hMT).2.1
    have hNeT : ∀ y, IsNonzeroAlongAt univ (geoTransformAlong M T).ideal y := by
      intro y
      have hyN : y ∈ (geoTransformAlong M T).N := by rw [hTN]; exact mem_univ y
      have hnz := hDomT.isNonzeroAlongAt y hyN
      simpa only [hTN] using hnz
    have hKT : IsCompact (geoTransformAlong M T).cosupp :=
      current_cosupport_compact M isClosedSubmanifold_univ hI hK T hMT
    have hZero : ∀ y ∈ (geoTransformAlong M T).cosupp,
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ 0 := by
      intro y hy
      let p : V := ⟨y, hCover hy⟩
      have hb := hVBound p
      rw [hq] at hb
      exact (branchMultiplicity_open V (isNormalCrossingsCarrier_of_boundaryAdapted hc)
        (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open V hc)) p).symm.trans_le hb
    obtain ⟨J, S, hCanS, hResS, hHistoryS⟩ :=
      exists_canonical_parent_resolution_of_zero_cosupport_count (geoTransformAlong M T)
        hTN hDomT.isWellFormed.isCoherent hDomT.one_le_d hNeT hKT hc hZero
    have hTestAppend : IsGeoTestTower M (T.append S) :=
      (isGeoTestTower_append_iff M T S).mpr ⟨hMT, hResS.1⟩
    have hResAppend : IsGeoResolution M (T.append S) := by
      refine ⟨hTestAppend, ?_⟩
      rw [geoTransformAlong_append]
      exact hResS.2
    exact ⟨J, S, hCanS, hResS, hHistoryS, hResAppend,
      isOriginalBranchTestTower_append M rfl hI T S hMT hHistory hHistoryS⟩

end
end Hironaka.HironakaOriginalNCZeroCountCompletion
