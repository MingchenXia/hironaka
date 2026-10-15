/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaMonomialAnalyticSuperlevels
/-! Actual globally analytic historical starting-year thresholds for positive
companions. Complete source-first mathematics preceded code. Internally coherent
nonmonomial derivative ideals, actual inherited cosupport/order inequalities and
genuine blowup pullbacks construct every threshold; USC is not substituted for
analyticity. Full recursive companion and auxiliary Hilbert-Samuel presentations
remain further producers. No original statement or history is redefined. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalCompanionHistoryYearAnalytic
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderCanonical MonomialPartAlong
  StepOneRegime CanonicalCentres GermIdealOrder
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

/-- This is the actual original prefix-order locus pulled back along its actual tail. -/
def originalHistoryOrderSuperlevel (m : MarkedIdeal n X) (T : BlowupTower X Y) (j q : ℕ) : Set Y :=
  (tail T j).proj ⁻¹' ordGe (geoTransformAlong m (head T j)) q

/-- Original domain/test inputs internally give the coherent SAME nonmonomial
ideal at EVERY actual prefix, without supplying a presentation. -/
theorem isCoherent_originalHistoryNonmonomialIdeal (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y)
    (hT : IsGeoTestTower m T) (j : ℕ) :
    (nmPart (geoTransformAlong m (head T j))).IsCoherent := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T j)
    ((isGeoTestTower_iff_head_tail m T j).mp hT).1
  exact isCoherent_nonmonomialPartAlong hn hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isSNCDivisor hd.isWellFormed.isTransverse hd.isWellFormed.isCoherent hd.isNonzeroAlongAt

private theorem orderSuperlevel_analytic (hn : 0 < n) (m : MarkedIdeal n Y)
    (h : IsInvDomain k m) (q : ℕ) : IsComplexAnalyticSubset (n := n) (ordGe m q) := by
  have hc := isCoherent_nonmonomialPartAlong hn h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isSNCDivisor h.isWellFormed.isTransverse h.isWellFormed.isCoherent h.isNonzeroAlongAt
  cases q with
  | zero =>
    change IsComplexAnalyticSubset (n := n) (cosupport n m.N (nmPart m) 0)
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hc hg)]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold h.isWellFormed.isClosedSubmanifold_N
  | succ q =>
    exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hc
      h.isWellFormed.isClosedSubmanifold_N (Nat.succ_pos q)

/-- Actual derivative equations and true holomorphic tail projections construct
whole prefix-order analytic sets, with no dimension/compactness certificate. -/
theorem isComplexAnalyticSubset_originalHistoryOrderSuperlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y)
    (hT : IsGeoTestTower m T) (j q : ℕ) :
    IsComplexAnalyticSubset (n := n) (originalHistoryOrderSuperlevel m T j q) := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T j)
    ((isGeoTestTower_iff_head_tail m T j).mp hT).1
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail T j).contMDiff_proj
    (orderSuperlevel_analytic hn _ hd q)

/-- Literal original positive-companion year threshold, including its actual
higher-current-order baseline. No invariant or actual run is replaced. -/
def companionHistoryYearSuperlevel (m : MarkedIdeal n X) (T : BlowupTower X Y) (q r : ℕ) : Set Y :=
  {y | y ∈ (geoTransformAlong m T).cosupp ∧ q ≤ nmOrd (geoTransformAlong m T) y ∧
    regimeRun (OrdRegime m q) T y ≤ r}

private theorem currentBaseline_analytic (hn : 0 < n) (m : MarkedIdeal n X)
    (h : IsInvDomain k m) (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (q : ℕ) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong m T).cosupp ∧ q ≤ nmOrd (geoTransformAlong m T) y} := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have he : {y | y ∈ (geoTransformAlong m T).cosupp ∧ q ≤ nmOrd (geoTransformAlong m T) y} =
      (geoTransformAlong m T).cosupp ∩ ordGe (geoTransformAlong m T) q := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1,(mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt
        ((geoTransformAlong m T).cosupp_subset_N hy.1) q).mpr hy.2⟩
    · intro hy
      exact ⟨hy.1,(mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt
        ((geoTransformAlong m T).cosupp_subset_N hy.1) q).mp hy.2⟩
  rw [he]
  exact (CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hd.isWellFormed.isCoherent
    hd.isWellFormed.isClosedSubmanifold_N hd.one_le_d).inter (orderSuperlevel_analytic hn _ hd q)

section StepDictionaries
variable {Λ : Type v} [LinearOrder Λ] {m : MarkedIdeal n X}
  {f : ∀ {A : CMfd.{u} n}, BlowupTower X A → A → Λ}

/-- Exact ENTIRE actual zero-run threshold dictionary, from the real original
canonical geometry. Order dominance is a genuine generic comparison hypothesis. -/
theorem companionHistoryYearSuperlevel_step_zero (hn : 0 < n) (h : IsInvDomain k m)
    (hf : OrdMonotone m f) (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower m (.step T C π hπ)) (hc : IsCanonical m f (.step T C π hπ)) (q : ℕ) :
    companionHistoryYearSuperlevel m (.step T C π hπ) q 0 =
      {z | z ∈ (geoTransformAlong m (.step T C π hπ)).cosupp ∧
        q ≤ nmOrd (geoTransformAlong m (.step T C π hπ)) z} ∩
      π ⁻¹' ordGe (geoTransformAlong m T) (q+1) := by
  classical
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T (isGeoTestTower_step_iff m T C π hπ |>.mp hT).1
  ext z
  constructor
  · intro hz
    have hp := nmOrd_step_le_of_canonical hn h hf T C π hπ hT hc.2 hz.1
    have hnot : ¬ OrdRegime m q T (π z) := by
      intro hg
      have he := regimeRun_step_of (OrdRegime m q) T C π hπ hg
      have hle := hz.2.2
      rw [he] at hle
      omega
    have hne : nmOrd (geoTransformAlong m T) (π z) ≠ q := fun he => hnot ⟨hp.1,he⟩
    have hq : q+1 ≤ nmOrd (geoTransformAlong m T) (π z) := by
      have hle := hz.2.1.trans hp.2
      omega
    exact ⟨⟨hz.1,hz.2.1⟩,(mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt
      ((geoTransformAlong m T).cosupp_subset_N hp.1) (q+1)).mpr hq⟩
  · intro hz
    have hp := nmOrd_step_le_of_canonical hn h hf T C π hπ hT hc.2 hz.1.1
    have hq := (mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt
      ((geoTransformAlong m T).cosupp_subset_N hp.1) (q+1)).mp hz.2
    have hnot : ¬ OrdRegime m q T (π z) := by
      rintro ⟨_,he⟩
      omega
    refine ⟨hz.1.1,hz.1.2,?_⟩
    rw [regimeRun_step_of_not (OrdRegime m q) T C π hπ hnot]

/-- Exact ENTIRE recursive actual history-year threshold dictionary; no
contact or member-mask boundary is excluded. -/
theorem companionHistoryYearSuperlevel_step_succ (hn : 0 < n) (h : IsInvDomain k m)
    (hf : OrdMonotone m f) (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower m (.step T C π hπ)) (hc : IsCanonical m f (.step T C π hπ)) (q r : ℕ) :
    companionHistoryYearSuperlevel m (.step T C π hπ) q (r+1) =
      {z | z ∈ (geoTransformAlong m (.step T C π hπ)).cosupp ∧
        q ≤ nmOrd (geoTransformAlong m (.step T C π hπ)) z} ∩
      π ⁻¹' (ordGe (geoTransformAlong m T) (q+1) ∪ companionHistoryYearSuperlevel m T q r) := by
  classical
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T (isGeoTestTower_step_iff m T C π hπ |>.mp hT).1
  ext z
  constructor
  · intro hz
    have hp := nmOrd_step_le_of_canonical hn h hf T C π hπ hT hc.2 hz.1
    refine ⟨⟨hz.1,hz.2.1⟩,?_⟩
    by_cases hg : OrdRegime m q T (π z)
    · right
      have he := regimeRun_step_of (OrdRegime m q) T C π hπ hg
      have hle := hz.2.2
      rw [he] at hle
      exact ⟨hp.1,hz.2.1.trans hp.2,by omega⟩
    · left
      have hne : nmOrd (geoTransformAlong m T) (π z) ≠ q := fun he => hg ⟨hp.1,he⟩
      apply (mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt
        ((geoTransformAlong m T).cosupp_subset_N hp.1) (q+1)).mpr
      have hle := hz.2.1.trans hp.2
      omega
  · intro hz
    have hp := nmOrd_step_le_of_canonical hn h hf T C π hπ hT hc.2 hz.1.1
    refine ⟨hz.1.1,hz.1.2,?_⟩
    rcases hz.2 with ha | ha
    · have hq := (mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt
        ((geoTransformAlong m T).cosupp_subset_N hp.1) (q+1)).mp ha
      have hnot : ¬ OrdRegime m q T (π z) := by
        rintro ⟨_,he⟩
        omega
      rw [regimeRun_step_of_not (OrdRegime m q) T C π hπ hnot]
      exact Nat.zero_le _
    · by_cases hg : OrdRegime m q T (π z)
      · rw [regimeRun_step_of (OrdRegime m q) T C π hπ hg]
        exact Nat.succ_le_succ ha.2.2
      · rw [regimeRun_step_of_not (OrdRegime m q) T C π hπ hg]
        exact Nat.zero_le _

/-- Genuine actual order equations and blowup pullbacks make the literal
history-year locus globally analytic by its complete finite recursion. -/
theorem isComplexAnalyticSubset_companionHistoryYearSuperlevel (hn : 0 < n)
    (h : IsInvDomain k m) (hf : OrdMonotone m f) :
    ∀ {A : CMfd.{u} n} (T : BlowupTower X A), IsGeoTestTower m T → IsCanonical m f T →
      ∀ q r : ℕ, IsComplexAnalyticSubset (n := n) (companionHistoryYearSuperlevel m T q r)
  | _, .refl, hT, _, q, r => by
      have he : companionHistoryYearSuperlevel m (.refl : BlowupTower X X) q r =
          {z | z ∈ (geoTransformAlong m (.refl : BlowupTower X X)).cosupp ∧
            q ≤ nmOrd (geoTransformAlong m (.refl : BlowupTower X X)) z} := by
        ext z
        simp [companionHistoryYearSuperlevel,regimeRun_refl]
      rw [he]
      exact currentBaseline_analytic hn m h .refl hT q
  | _, .step T C π hπ, hT, hc, q, r => by
      have hTold := (isGeoTestTower_step_iff m T C π hπ).mp hT |>.1
      have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hTold
      have hA := orderSuperlevel_analytic hn _ hd (q+1)
      have hB := currentBaseline_analytic hn m h (.step T C π hπ) hT q
      cases r with
      | zero =>
        rw [companionHistoryYearSuperlevel_step_zero hn h hf T C π hπ hT hc q]
        exact hB.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hA)
      | succ r =>
        rw [companionHistoryYearSuperlevel_step_succ hn h hf T C π hπ hT hc q r]
        exact hB.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff
          (HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hA
            (isComplexAnalyticSubset_companionHistoryYearSuperlevel hn h hf T hTold hc.1 q r)))
end StepDictionaries

/-- ONLY original input/domain and the literal original canonical history:
actual global analytic companion history-year thresholds in every induction
dimension. No compactness, curve or analytic-presentation caller certificate. -/
theorem isComplexAnalyticSubset_originalCompanionHistoryYearSuperlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q r : ℕ) :
    IsComplexAnalyticSubset (n := n) (companionHistoryYearSuperlevel m T q r) := by
  let lower := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {B : CMfd.{u} n}
    (S : BlowupTower A B) (z : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J S z
  have hf : OrdMonotone m ((invFamily hn (k+1)).inv m) := GeneralValue.ordMonotone_genInv lower m
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  exact isComplexAnalyticSubset_companionHistoryYearSuperlevel hn h hf T hT hc q r

end
end Hironaka.HironakaOriginalCompanionHistoryYearAnalytic
