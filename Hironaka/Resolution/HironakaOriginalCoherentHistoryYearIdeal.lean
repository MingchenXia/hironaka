/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.SumIdealCoherentInclusionsExact
import Hironaka.Resolution.HironakaOriginalWholeContactLowerFirstAnalytic
import Hironaka.Resolution.HironakaEffectiveDivisorSum
/-! Actual coherent global enhanced history-year ideals, exact original zero
loci and BOTH real finite generator directions. Real original nonzero geometry
constructs SAME-current-SNC/univ/mark1 actual auxiliary marked-domain inputs.
Complete mathematics-first blueprint precedes code; full recursive thresholds
and auxiliary HS/global history scheduling remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalCoherentHistoryYearIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  NonmonomialOrderLocal NonmonomialOrderCanonical MonomialPartAlong
  GermIdealOrder RestrictedIdealExtension IdealWeightPowers
  DerivativeIdealAlong DerivativeIdealAlongCoherent GiraudAlong
  HironakaOriginalCompanionHistoryYearAnalytic StepOneRegime CanonicalCentres
  NormalCrossings SimultaneousNormalCrossings HironakaStepOneMemberLowerExtension
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

private theorem zeroLocus_sumIdeal {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    (sumIdeal I J).zeroLocus = I.zeroLocus ∩ J.zeroLocus := by
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

/-- Explicit real carrier vanishing and actual iterated relative derivative equations. -/
def carrierOrderIdeal (N : Set X) (I : GermIdeal n X) : ℕ → GermIdeal n X
  | 0 => vanishingIdeal (n := n) N
  | a+1 => sumIdeal (vanishingIdeal (n := n) N) (iterDerivIdealAlong N I a)

theorem isCoherent_carrierOrderIdeal {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent) (a : ℕ) :
    (carrierOrderIdeal N I a).IsCoherent := by
  cases a with
  | zero => exact VanishingIdealCoherent.isCoherent_vanishingIdeal hN
  | succ a =>
    exact isCoherent_sumIdeal (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
      (isCoherent_iterDerivIdealAlong hI hN a)

theorem zeroLocus_carrierOrderIdeal {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent) (a : ℕ) :
    (carrierOrderIdeal N I a).zeroLocus = cosupport n N I a := by
  cases a with
  | zero =>
    rw [carrierOrderIdeal,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hN.1,
      cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
  | succ a =>
    rw [carrierOrderIdeal,zeroLocus_sumIdeal (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
      (isCoherent_iterDerivIdealAlong hI hN a),BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hN.1,
      cosupport_succ_eq_inter_zeroLocus_iterDerivIdealAlong
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hN.2 a]

/-- The actual original Nm order ideal, retaining the genuine carrier. -/
def nonmonomialOrderIdeal (m : MarkedIdeal n X) (q : ℕ) : GermIdeal n X :=
  carrierOrderIdeal m.N (nmPart m) q

private theorem actual_nm_coherent (hn : 0 < n) {m : MarkedIdeal n X} (h : IsInvDomain k m) :
    (nmPart m).IsCoherent :=
  isCoherent_nonmonomialPartAlong hn h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isSNCDivisor h.isWellFormed.isTransverse h.isWellFormed.isCoherent h.isNonzeroAlongAt

private theorem isCoherent_nonmonomialOrderIdeal (hn : 0 < n) {m : MarkedIdeal n X}
    (h : IsInvDomain k m) (q : ℕ) : (nonmonomialOrderIdeal m q).IsCoherent :=
  isCoherent_carrierOrderIdeal h.isWellFormed.isClosedSubmanifold_N (actual_nm_coherent hn h) q

private theorem zeroLocus_nonmonomialOrderIdeal (hn : 0 < n) {m : MarkedIdeal n X}
    (h : IsInvDomain k m) (q : ℕ) : (nonmonomialOrderIdeal m q).zeroLocus = ordGe m q :=
  zeroLocus_carrierOrderIdeal h.isWellFormed.isClosedSubmanifold_N (actual_nm_coherent hn h) q

/-- The SAME actual current cosupport and Nm order baseline has this true whole defining ideal. -/
def companionYearBaselineIdeal (m : MarkedIdeal n X) (q : ℕ) : GermIdeal n X :=
  sumIdeal (carrierOrderIdeal m.N m.ideal m.d) (nonmonomialOrderIdeal m q)

theorem isCoherent_companionYearBaselineIdeal (hn : 0 < n) {m : MarkedIdeal n X}
    (h : IsInvDomain k m) (q : ℕ) : (companionYearBaselineIdeal m q).IsCoherent :=
  isCoherent_sumIdeal (isCoherent_carrierOrderIdeal h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent m.d)
    (isCoherent_nonmonomialOrderIdeal hn h q)

theorem zeroLocus_companionYearBaselineIdeal (hn : 0 < n) {m : MarkedIdeal n X}
    (h : IsInvDomain k m) (q : ℕ) :
    (companionYearBaselineIdeal m q).zeroLocus = {y | y ∈ m.cosupp ∧ q ≤ nmOrd m y} := by
  rw [companionYearBaselineIdeal,zeroLocus_sumIdeal
    (isCoherent_carrierOrderIdeal h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent m.d)
    (isCoherent_nonmonomialOrderIdeal hn h q),zeroLocus_carrierOrderIdeal h.isWellFormed.isClosedSubmanifold_N
      h.isWellFormed.isCoherent m.d,zeroLocus_nonmonomialOrderIdeal hn h q]
  ext y
  exact and_congr_right fun hy => mem_ordGe_iff h.isWellFormed h.isNonzeroAlongAt (m.cosupp_subset_N hy) q

/-- Actual whole finite-history equations: reset retains the true higher old order,
and increment uses the literal real product before the same actual blowup pullback. -/
def companionHistoryYearIdeal (m : MarkedIdeal n X) :
    {Y : CMfd.{u} n} → BlowupTower X Y → ℕ → ℕ → GermIdeal n Y
  | _, .refl, q, _ => companionYearBaselineIdeal m q
  | _, .step T C π hπ, q, 0 => sumIdeal
      (companionYearBaselineIdeal (geoTransformAlong m (.step T C π hπ)) q)
      (GermIdeal.pullback (m := n) π (nonmonomialOrderIdeal (geoTransformAlong m T) (q+1)))
  | _, .step T C π hπ, q, r+1 => sumIdeal
      (companionYearBaselineIdeal (geoTransformAlong m (.step T C π hπ)) q)
      (GermIdeal.pullback (m := n) π
        ((nonmonomialOrderIdeal (geoTransformAlong m T) (q+1)).mul (companionHistoryYearIdeal m T q r)))

theorem isCoherent_companionHistoryYearIdeal (hn : 0 < n) {m : MarkedIdeal n X}
    (h : IsInvDomain k m) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower m T →
      ∀ q r : ℕ,(companionHistoryYearIdeal m T q r).IsCoherent
  | _, .refl, _, q, _ => isCoherent_companionYearBaselineIdeal hn h q
  | _, .step T C π hπ, hT, q, r => by
    have hOld := (isGeoTestTower_step_iff m T C π hπ).mp hT |>.1
    have hdOld := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hOld
    have hdNew := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (.step T C π hπ) hT
    cases r with
    | zero =>
      exact isCoherent_sumIdeal (isCoherent_companionYearBaselineIdeal hn hdNew q)
        (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff (isCoherent_nonmonomialOrderIdeal hn hdOld (q+1)))
    | succ r =>
      exact isCoherent_sumIdeal (isCoherent_companionYearBaselineIdeal hn hdNew q)
        (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff
          (isCoherent_mul (isCoherent_nonmonomialOrderIdeal hn hdOld (q+1))
            (isCoherent_companionHistoryYearIdeal hn h T hOld q r)))

section CanonicalDictionary
variable {Λ : Type v} [LinearOrder Λ] {m : MarkedIdeal n X}
  {f : ∀ {A : CMfd.{u} n},BlowupTower X A → A → Λ}

theorem zeroLocus_companionHistoryYearIdeal (hn : 0 < n) (h : IsInvDomain k m) (hf : OrdMonotone m f) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower m T → IsCanonical m f T →
      ∀ q r : ℕ,(companionHistoryYearIdeal m T q r).zeroLocus = companionHistoryYearSuperlevel m T q r
  | _, .refl, _, _, q, _ => by
    rw [companionHistoryYearIdeal,zeroLocus_companionYearBaselineIdeal hn h q]
    ext z
    simp only [companionHistoryYearSuperlevel,mem_ofPred_eq,regimeRun_refl,Nat.zero_le,and_true]
    rfl
  | _, .step T C π hπ, hT, hc, q, r => by
    have hOld := (isGeoTestTower_step_iff m T C π hπ).mp hT |>.1
    have hdOld := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hOld
    have hdNew := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (.step T C π hπ) hT
    have hOrder := isCoherent_nonmonomialOrderIdeal hn hdOld (q+1)
    cases r with
    | zero =>
      rw [companionHistoryYearIdeal,zeroLocus_sumIdeal (isCoherent_companionYearBaselineIdeal hn hdNew q)
        (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hOrder),zeroLocus_companionYearBaselineIdeal hn hdNew q,
        BlowupExceptionalDivisor.zeroLocus_pullback hπ.contMDiff hOrder,zeroLocus_nonmonomialOrderIdeal hn hdOld (q+1),
        companionHistoryYearSuperlevel_step_zero hn h hf T C π hπ hT hc q]
    | succ r =>
      have hYear := isCoherent_companionHistoryYearIdeal hn h T hOld q r
      rw [companionHistoryYearIdeal,zeroLocus_sumIdeal (isCoherent_companionYearBaselineIdeal hn hdNew q)
        (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff (isCoherent_mul hOrder hYear)),
        zeroLocus_companionYearBaselineIdeal hn hdNew q,
        BlowupExceptionalDivisor.zeroLocus_pullback hπ.contMDiff (isCoherent_mul hOrder hYear),
        HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union hOrder hYear,
        zeroLocus_nonmonomialOrderIdeal hn hdOld (q+1),zeroLocus_companionHistoryYearIdeal hn h hf T hOld hc.1 q r,
        companionHistoryYearSuperlevel_step_succ hn h hf T C π hπ hT hc q r]
end CanonicalDictionary

/-- ONLY original input supplies the full coherent year ideal and exact original whole zero locus. -/
theorem original_companionHistoryYearIdeal_coherent_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q r : ℕ) :
    (companionHistoryYearIdeal m T q r).IsCoherent ∧
      (companionHistoryYearIdeal m T q r).zeroLocus = companionHistoryYearSuperlevel m T q r := by
  let lower := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {B : CMfd.{u} n}
    (S : BlowupTower A B) (z : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J S z
  have hf : OrdMonotone m ((invFamily hn (k+1)).inv m) := GeneralValue.ordMonotone_genInv lower m
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  exact ⟨isCoherent_companionHistoryYearIdeal hn h T hT q r,zeroLocus_companionHistoryYearIdeal hn h hf T hT hc q r⟩

/-- Actual finite holomorphic generators with BOTH nearby germ directions and SAME threshold equations. -/
theorem exists_original_companionHistoryYearIdeal_generators (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q r : ℕ) (x : Y) :
    ∃ U : Set Y,IsOpen U ∧ x ∈ U ∧ ∃ (N : ℕ) (a : Fin N → Y → ℂ),
      (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (a i) U) ∧
      (∀ y ∈ U,∀ g,(companionHistoryYearIdeal m T q r).mem y g ↔ IsInSpanAt (n := n) (· ∈ range a) y g) ∧
      ∀ y ∈ U,y ∈ companionHistoryYearSuperlevel m T q r ↔ ∀ i,a i y=0 := by
  obtain ⟨hI,hZ⟩ := original_companionHistoryYearIdeal_coherent_dictionary hn m h T hc q r
  obtain ⟨U,hU,hxU,N,a,ha,hgen⟩ := hI x
  refine ⟨U,hU,hxU,N,a,ha,hgen,?_⟩
  intro y hy
  rw [← hZ]
  constructor
  · intro hz i
    have hol : HolomorphicAt n (a i) y := eventually_of_mem (hU.mem_nhds hy)
      (fun z hz => (ha i z hz).mdifferentiableAt (hU.mem_nhds hz))
    apply hz (a i)
    apply (hgen y hy (a i)).mpr
    exact isInSpanAt_of_eq_mul ⟨i,rfl⟩ hol (holomorphicAt_const 1)
      (Eventually.of_forall fun z => (one_mul (a i z)).symm)
  · intro hz g hg
    obtain ⟨_,M,s,b,hs,_,he⟩ := (hgen y hy g).mp hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    obtain ⟨j,hj⟩ := hs i
    rw [← hj,hz j,mul_zero]

private theorem interior_cosupp_eq_empty {m : MarkedIdeal n Y} (h : IsInvDomain k m) :
    interior m.cosupp = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨g,hg,hfreq⟩ := h.isNonzeroAlongAt x (m.cosupp_subset_N (interior_subset hx))
  have hmem := HomogenizedGlueing.eventually_mem h.isWellFormed.isCoherent hg
  obtain ⟨z,⟨hzN,hzg⟩,hzgmem,hzO⟩ :=
    (hfreq.and_eventually (hmem.and (isOpen_interior.mem_nhds hx))).exists
  have hzcs := interior_subset hzO
  have hhol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h.isWellFormed.isCoherent hzgmem
  exact hzg ((vanishesToOrderOn_one_iff hzN hhol).mp ((hzcs.2 g hzgmem).mono h.one_le_d))

/-- The genuine auxiliary input retains WHOLE carrier, SAME current original boundary and actual history ideal. -/
def companionHistoryYearMarked (m : MarkedIdeal n X) (T : BlowupTower X Y) (q r : ℕ) : MarkedIdeal n Y :=
  ⟨univ,(geoTransformAlong m T).E,companionHistoryYearIdeal m T q r,1⟩

/-- ONLY original inputs produce the SAME-current-SNC genuine whole ambient marked-domain input. -/
theorem original_companionHistoryYearMarked_isInvDomain (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q r : ℕ) :
    IsInvDomain n (companionHistoryYearMarked m T q r) := by
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  obtain ⟨hI,hZ⟩ := original_companionHistoryYearIdeal_coherent_dictionary hn m h T hc q r
  have hi : interior (companionHistoryYearIdeal m T q r).zeroLocus = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hm := interior_mono (show (companionHistoryYearIdeal m T q r).zeroLocus ⊆ (geoTransformAlong m T).cosupp from
      fun z hz => (hZ ▸ hz).1) hy
    rw [interior_cosupp_eq_empty hd] at hm
    exact hm
  have hN : IsClosedSubmanifold n (univ : Set Y) :=
    ⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
  refine ⟨⟨hN,hI,hd.isWellFormed.isSNCDivisor,isTransverse_univ_of_isSNCDivisor hd.isWellFormed.isSNCDivisor⟩,
    (fun x _ => ⟨n,le_rfl,AnalyticIrreducibleComponents.regularAtDim_univ x⟩),le_rfl,?_⟩
  intro x hx
  apply isNonzeroAlongAt_of_thin_cosupport (d := 1) hI
  · intro O hO hOA
    change O ∩ univ ⊆ cosupport n univ (companionHistoryYearIdeal m T q r) 1 at hOA
    change O ∩ univ = ∅
    rw [inter_univ] at hOA ⊢
    rw [cosupport_one (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg),
      univ_inter] at hOA
    have hsub : O ⊆ interior (companionHistoryYearIdeal m T q r).zeroLocus := by
      rw [← hO.interior_eq]
      exact interior_mono hOA
    rw [hi] at hsub
    exact eq_empty_iff_forall_notMem.mpr (fun y hy => hsub hy)
  · exact hx

end
end Hironaka.HironakaOriginalCoherentHistoryYearIdeal
