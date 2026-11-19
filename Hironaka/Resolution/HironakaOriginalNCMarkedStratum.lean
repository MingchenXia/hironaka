import Hironaka.Resolution.HironakaSharpActualFirstAmbientStrictTraceFactor
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Invariant.ResolutionInvariantSpec

/-!
# The actual marked-stratum parent on the unchanged native carrier

This module composes existing whole controlled-trace and arbitrary-tower
marked-sum APIs. The carrier is always the original smooth N, even when
N intersects the ambient stratum singularly. Every boundary slot and the
original positive mark are retained. The mark-one factor need not itself
be nonzero along N.

This is a parent-only adapter, with zero separate blueprint credit. The
NEW proper-carrier causal value and its unconditional canonical-history
interpreter are subsequent producers, not hypotheses or claims here.
Mathematics first: work/hironaka-g9-proper-carrier-marked-stratum-implementation-20261023/
mathematical-delta.tex. The published nine-node research proposal is unchanged.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalNCMarkedStratum

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  NormalCrossings IdealWeightPowers RestrictedIdealExtension RestrictedIdealWeight
  RestrictedIdealQuotient RestrictLeCalculus GermIdealPullbackCalculus
  RelativePrincipalizationSpan InvertibleIdealQuotient
  HomogenizedGlueingTower MemberInterTowerAlong
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  HironakaSharpActualFirstAmbientStrictTraceFactor
open CoefficientIdealRestriction (CentresIn)
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The actual ambient stratum equations, on the SAME native carrier and E. -/
def stratumFactor (M : MarkedIdeal n X) (Z : Set X) : MarkedIdeal n X :=
  ⟨M.N, M.E, vanishingIdeal (n := n) Z, 1⟩

/-- The genuine marked sum, before simplifying its coherent ideal power one. -/
def markedStratum (M : MarkedIdeal n X) (Z : Set X) : MarkedIdeal n X :=
  MarkedIdealOperationsTransform.MarkedIdeal.add M (stratumFactor M Z)

private theorem stratum_pair (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {Z : Set X} (hZ : IsClosedSubmanifold n Z) :
    IsSubmanifoldPair M (stratumFactor M Z) :=
  ⟨rfl, rfl, hM.isClosedSubmanifold_N, hM.isCoherent,
    VanishingIdealCoherent.isCoherent_vanishingIdeal hZ⟩

private theorem markedStratum_coherent (M : MarkedIdeal n X)
    (hI : M.ideal.IsCoherent) {Z : Set X} (hZ : IsClosedSubmanifold n Z) :
    (markedStratum M Z).ideal.IsCoherent :=
  isCoherent_sumIdeal (isCoherent_idealPow hI 1)
    (isCoherent_idealPow (VanishingIdealCoherent.isCoherent_vanishingIdeal hZ) M.d)

/-- This is the existing whole controlled-trace theorem with the SAME E retained. -/
theorem stratumFactor_geoTransform_ideal (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) {Z C : Set X}
    (hZ : IsClosedSubmanifold n Z) {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hCN : C ⊆ M.N) (hCZ : C ⊆ Z) :
    ((stratumFactor M Z).geoTransform C π).ideal =
      restrictOn n (geoStrictTransform π C M.N)
        (vanishingIdeal (n := n) (geoStrictTransform π C Z)) := by
  change ((⟨M.N, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X).geoTransform C π).ideal = _
  exact actual_first_controlled_ambient_strict_trace hN hZ hπ hCN hCZ

/-- Mark one gives the exact relative zero locus without requiring a smooth intersection. -/
theorem stratumFactor_cosupp (M : MarkedIdeal n X) {Z : Set X} (hZ : IsClosed Z) :
    (stratumFactor M Z).cosupp = M.N ∩ Z :=
  SmoothCentreLocus.cosupport_vanishingIdeal_one hZ

private theorem stratumFactor_geoTransform_restrictEquiv (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) {Z C : Set X}
    (hZ : IsClosedSubmanifold n Z) {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hCN : C ⊆ M.N) (hCZ : C ⊆ Z) :
    RestrictEquiv ((stratumFactor M Z).geoTransform C π)
      (stratumFactor (M.geoTransform C π) (geoStrictTransform π C Z)) := by
  have hZ' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold
    hπ hZ hCZ
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · change RestrictLe (geoStrictTransform π C M.N)
      ((stratumFactor M Z).geoTransform C π).ideal
      (vanishingIdeal (n := n) (geoStrictTransform π C Z))
    rw [stratumFactor_geoTransform_ideal M hN hZ hπ hCN hCZ]
    exact restrictLe_restrictOn
  · change RestrictLe (geoStrictTransform π C M.N)
      (vanishingIdeal (n := n) (geoStrictTransform π C Z))
      ((stratumFactor M Z).geoTransform C π).ideal
    rw [stratumFactor_geoTransform_ideal M hN hZ hπ hCN hCZ]
    exact restrictLe_self_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal hZ')

/-- All actual stratum-factor tests and whole raw-stratum representatives on the SAME tower. -/
theorem stratumFactor_tower_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {Z : Set X} (hZ : IsClosedSubmanifold n Z) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower M T → CentresIn Z T →
      IsGeoTestTower (stratumFactor M Z) T ∧
        IsClosedSubmanifold n (strictAlong T Z) ∧
        RestrictEquiv (geoTransformAlong (stratumFactor M Z) T)
          (stratumFactor (geoTransformAlong M T) (strictAlong T Z))
  | _, .refl, _hT, _hC =>
      ⟨trivial, hZ, RestrictEquiv.refl (VanishingIdealCoherent.isCoherent_vanishingIdeal hZ)⟩
  | _, .step T C π hπ, hT, hC => by
      obtain ⟨hP, hZT, hEq⟩ := stratumFactor_tower_dictionary M hM hZ T hT.1 hC.1
      have hMT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT.1
      have hCN : C ⊆ (geoTransformAlong M T).N := hT.2.subset_N
      have hCZ : C ⊆ strictAlong T Z := hC.2
      have hRaw : (stratumFactor (geoTransformAlong M T) (strictAlong T Z)).IsAdmissibleCentre C := by
        refine ⟨hT.2.1, ?_, hT.2.2.2⟩
        rw [stratumFactor_cosupp _ hZT.1]
        exact fun x hx => ⟨hCN hx, hCZ hx⟩
      have hActual : (geoTransformAlong (stratumFactor M Z) T).IsAdmissibleCentre C :=
        hEq.isAdmissibleCentre_iff.mpr hRaw
      have hPGeom := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
        (𝔪 := stratumFactor M Z) hM.isClosedSubmanifold_N (VanishingIdealCoherent.isCoherent_vanishingIdeal hZ) T hP
      have hTransform := hEq.geoTransform_eq (C := C) hPGeom.1.1 hPGeom.2
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hZT) hπ.contMDiff
      refine ⟨⟨hP, hActual⟩,
        BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold
          hπ hZT hCZ, ?_⟩
      change RestrictEquiv
        ((geoTransformAlong (stratumFactor M Z) T).geoTransform C π)
        (stratumFactor ((geoTransformAlong M T).geoTransform C π)
          (geoStrictTransform π C (strictAlong T Z)))
      rw [hTransform]
      exact stratumFactor_geoTransform_restrictEquiv _ hMT.isClosedSubmanifold_N
        hZT hπ hCN hCZ

private theorem stratumFactor_test_iff_centres (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) {Z : Set X} (hZ : IsClosedSubmanifold n Z) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
      (IsGeoTestTower (stratumFactor M Z) T ↔ CentresIn Z T)
  | _, .refl, _hT => ⟨fun _ => trivial, fun _ => trivial⟩
  | _, .step T C π hπ, hT => by
      constructor
      · intro hP
        have hPrev := (stratumFactor_test_iff_centres M hM hZ T hT.1).mp hP.1
        obtain ⟨_hPT, hZT, hEq⟩ := stratumFactor_tower_dictionary M hM hZ T hT.1 hPrev
        refine ⟨hPrev, ?_⟩
        intro x hx
        have hxp : x ∈ (stratumFactor (geoTransformAlong M T) (strictAlong T Z)).cosupp :=
          hEq.cosupp_eq ▸ hP.2.2.1 hx
        rw [stratumFactor_cosupp _ hZT.1] at hxp
        exact hxp.2
      · intro hC
        exact (stratumFactor_tower_dictionary M hM hZ (.step T C π hπ) hT hC).1

/-- Only genuine parent testness and actual strict-stratum centre containment are needed. -/
theorem markedStratum_test_tower_iff (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hd : 1 ≤ M.d) {Z : Set X} (hZ : IsClosedSubmanifold n Z)
    (T : BlowupTower X Y) :
    IsGeoTestTower (markedStratum M Z) T ↔ IsGeoTestTower M T ∧ CentresIn Z T := by
  have hAdd := (geoTransformAlong_add_along M (stratumFactor M Z)
    (stratum_pair M hM hZ) hd (le_refl 1) T).1
  change IsGeoTestTower (MarkedIdealOperationsTransform.MarkedIdeal.add M (stratumFactor M Z)) T ↔ _
  rw [hAdd]
  constructor
  · rintro ⟨hT, hP⟩
    exact ⟨hT, (stratumFactor_test_iff_centres M hM hZ T hT).mp hP⟩
  · rintro ⟨hT, hC⟩
    exact ⟨hT, (stratumFactor_test_iff_centres M hM hZ T hT).mpr hC⟩

/-- The exact original relative cosupport, intersected with the ambient stratum. -/
theorem markedStratum_cosupp (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hd : 1 ≤ M.d) {Z : Set X} (hZ : IsClosedSubmanifold n Z) :
    (markedStratum M Z).cosupp = M.cosupp ∩ Z := by
  change (MarkedIdealOperationsTransform.MarkedIdeal.add M (stratumFactor M Z)).cosupp = _
  rw [cosupp_add_along (stratum_pair M hM hZ) hd (le_refl 1), stratumFactor_cosupp M hZ.1]
  ext x
  constructor
  · rintro ⟨hx, _hxN, hxZ⟩
    exact ⟨hx, hxZ⟩
  · rintro ⟨hx, hxZ⟩
    exact ⟨hx, hx.1, hxZ⟩

/-- The stratum factor may vanish identically along N; the parent's nonzero ideal survives. -/
theorem markedStratum_isInvDomain {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {Z : Set X} (hZ : IsClosedSubmanifold n Z) :
    IsInvDomain k (markedStratum M Z) := by
  have hc := markedStratum_coherent M hM.isWellFormed.isCoherent hZ
  refine ⟨⟨hM.isWellFormed.isClosedSubmanifold_N, hc,
    hM.isWellFormed.isSNCDivisor, hM.isWellFormed.isTransverse⟩,
    hM.dimLE, ?_, ?_⟩
  · change 1 ≤ M.d * 1
    simpa using hM.one_le_d
  · intro x hx
    obtain ⟨g, hg, hfreq⟩ := hM.isNonzeroAlongAt x hx
    refine ⟨g, ?_, hfreq⟩
    exact le_sumIdeal_left (isCoherent_idealPow hM.isWellFormed.isCoherent 1) x g
      (BlowupDerivativeIdeal.mem_idealPow_one_of_mem
        (fun y f hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          hM.isWellFormed.isCoherent hf) hg)

private theorem restrictEquiv_trans {A B C : MarkedIdeal n X}
    (hAB : RestrictEquiv A B) (hBC : RestrictEquiv B C) : RestrictEquiv A C := by
  have hBCle : RestrictLe A.N B.ideal C.ideal := by
    simpa only [hAB.N_eq] using hBC.le
  have hBCge : RestrictLe A.N C.ideal B.ideal := by
    simpa only [hAB.N_eq] using hBC.ge
  exact ⟨hAB.N_eq.trans hBC.N_eq, hAB.E_eq.trans hBC.E_eq, hAB.d_eq.trans hBC.d_eq,
    RestrictLeCalculus.RestrictLe.trans hAB.le hBCle,
    RestrictLeCalculus.RestrictLe.trans hBCge hAB.ge⟩

private theorem add_replace_second_restrictEquiv (M P Q : MarkedIdeal n X)
    (hI : M.ideal.IsCoherent) (hP : P.ideal.IsCoherent) (hQ : Q.ideal.IsCoherent)
    (hEq : RestrictEquiv P Q) (hN : P.N = M.N) :
    RestrictEquiv (MarkedIdealOperationsTransform.MarkedIdeal.add M P)
      (MarkedIdealOperationsTransform.MarkedIdeal.add M Q) := by
  have hle : RestrictLe M.N P.ideal Q.ideal := by simpa only [hN] using hEq.le
  have hge : RestrictLe M.N Q.ideal P.ideal := by simpa only [hN] using hEq.ge
  refine ⟨rfl, rfl, congrArg (fun a => M.d * a) hEq.d_eq, ?_, ?_⟩
  · change RestrictLe M.N
      (sumIdeal (idealPow M.ideal P.d) (idealPow P.ideal M.d))
      (sumIdeal (idealPow M.ideal Q.d) (idealPow Q.ideal M.d))
    rw [hEq.d_eq]
    exact restrictLe_sumIdeal
      (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
      (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
      (restrictLe_refl (isCoherent_idealPow hI Q.d))
      (restrictLe_idealPow (fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hQ hg) hle M.d)
  · change RestrictLe M.N
      (sumIdeal (idealPow M.ideal Q.d) (idealPow Q.ideal M.d))
      (sumIdeal (idealPow M.ideal P.d) (idealPow P.ideal M.d))
    rw [← hEq.d_eq]
    exact restrictLe_sumIdeal
      (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
      (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
      (restrictLe_refl (isCoherent_idealPow hI P.d))
      (restrictLe_idealPow (fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hP hg) hge M.d)

/-- The actual WHOLE transformed marked sum has the same native fields and strict-stratum ideal. -/
theorem markedStratum_tower_restrictEquiv (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hd : 1 ≤ M.d) {Z : Set X} (hZ : IsClosedSubmanifold n Z)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (markedStratum M Z) T) :
    RestrictEquiv (geoTransformAlong (markedStratum M Z) T)
      (markedStratum (geoTransformAlong M T) (strictAlong T Z)) := by
  obtain ⟨hMT, hC⟩ := (markedStratum_test_tower_iff M hM hd hZ T).mp hT
  obtain ⟨hPT, hZT, hPEq⟩ := stratumFactor_tower_dictionary M hM hZ T hMT hC
  obtain ⟨hSumEq, hPair, _hSumCoh⟩ :=
    (geoTransformAlong_add_along M (stratumFactor M Z) (stratum_pair M hM hZ)
      hd (le_refl 1) T).2 hMT hPT
  have hReplace := add_replace_second_restrictEquiv (geoTransformAlong M T)
    (geoTransformAlong (stratumFactor M Z) T)
    (stratumFactor (geoTransformAlong M T) (strictAlong T Z))
    hPair.coh₁ hPair.coh₂ (VanishingIdealCoherent.isCoherent_vanishingIdeal hZT)
    hPEq hPEq.N_eq
  exact restrictEquiv_trans hSumEq hReplace

/-- The controlled cosupport is the WHOLE original current cosupport intersected with strict Z. -/
theorem markedStratum_tower_cosupp (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hd : 1 ≤ M.d) {Z : Set X} (hZ : IsClosedSubmanifold n Z)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (markedStratum M Z) T) :
    (geoTransformAlong (markedStratum M Z) T).cosupp =
      (geoTransformAlong M T).cosupp ∩ strictAlong T Z := by
  obtain ⟨hMT, hC⟩ := (markedStratum_test_tower_iff M hM hd hZ T).mp hT
  have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hMT
  have hZT := (stratumFactor_tower_dictionary M hM hZ T hMT hC).2.1
  have hdT : 1 ≤ (geoTransformAlong M T).d := by simpa only [d_geoTransformAlong] using hd
  exact (markedStratum_tower_restrictEquiv M hM hd hZ T hT).cosupp_eq.trans
    (markedStratum_cosupp _ hWF hdT hZT)

private theorem positive_power_vanishing_restricts_zero (N Z : Set X) (hNZ : N ⊆ Z)
    (I : GermIdeal n X) (d : ℕ) (hd : 1 ≤ d) :
    RestrictLe N (idealPow (vanishingIdeal (n := n) Z) d) I := by
  cases d with
  | zero => omega
  | succ k =>
      intro x _hx g hg
      change ((idealPow (vanishingIdeal (n := n) Z) k).mul
        (vanishingIdeal (n := n) Z)).mem x g at hg
      refine RelativePrincipalizationSpan.IsInSpanOnAt.trans ?_
        (IsInSpanAt.restrict (mem_mul_iff.mp hg))
      rintro _s ⟨a, b, _ha, hb, rfl⟩
      refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
      filter_upwards [hb.2] with y hy hyN
      simp [hy (hNZ hyN)]

/-- Includes q=0/full stratum and N contained in Z; the entire SAME record is compared. -/
theorem markedStratum_restrictEquiv_of_carrier_subset (M : MarkedIdeal n X)
    (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d) (Z : Set X) (hNZ : M.N ⊆ Z) :
    RestrictEquiv (markedStratum M Z) M := by
  have hOne : idealPow M.ideal 1 = M.ideal := by
    rw [idealPow_succ, idealPow_zero, BlowupControlledTransform.unitIdeal_mul hI]
  have hLe : M.ideal.Le (markedStratum M Z).ideal := by
    intro x g hg
    exact le_sumIdeal_left (isCoherent_idealPow hI 1) x g (hOne.symm ▸ hg)
  refine ⟨rfl, rfl, by change M.d * 1 = M.d; exact Nat.mul_one M.d, ?_, ?_⟩
  · intro x hx g hg
    refine RelativePrincipalizationSpan.IsInSpanOnAt.trans ?_
      (IsInSpanAt.restrict (IdealOrderArithmetic.mem_sumIdeal_iff.mp hg))
    rintro s (hs | hs)
    · change (idealPow M.ideal 1).mem x s at hs
      rw [hOne] at hs
      exact IsInSpanAt.restrict (isInSpanAt_self hs
        (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hs))
    · exact positive_power_vanishing_restricts_zero M.N Z hNZ M.ideal M.d hd x hx s hs
  · intro x _hx g hg
    exact IsInSpanAt.restrict (isInSpanAt_self (hLe x g hg)
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg))

end

end Hironaka.HironakaOriginalNCMarkedStratum
