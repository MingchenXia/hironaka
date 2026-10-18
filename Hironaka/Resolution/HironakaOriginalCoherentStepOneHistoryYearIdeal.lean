/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCoherentSpecialResetIdeal
/-! Literal real masked StepOne higher-or-equalSPECIAL reset ideals give actual
whole finite lower-year equations. Coherence precedes the exact original zero
locus; BOTH genuine generators and SAME-current-E ambient marked input.
Complete source-first math precedes Lean. Full arbitrary recursive/higher-special
semicoherent comparison and global scheduler remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCoherentStepOneHistoryYearIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaOriginalCoherentSpecialResetIdeal HironakaOriginalStepOneHistoryYearAnalytic
  RestrictedIdealExtension IdealWeightPowers StepOneValue HomogenizedIdealAlong
  HironakaStepOneMemberLowerExtension CanonicalCentres NormalCrossings SimultaneousNormalCrossings
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

private theorem hol_of_coherent {I : GermIdeal n X} (h : I.IsCoherent) :
    ∀ x g,I.mem x g → HolomorphicAt n g x :=
  fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h hg

private theorem zeroLocus_sumIdeal {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    (sumIdeal I J).zeroLocus = I.zeroLocus ∩ J.zeroLocus := by
  ext x
  constructor
  · intro hx
    exact ⟨fun g hg => hx g (le_sumIdeal_left hI x g hg),fun g hg => hx g (le_sumIdeal_right hJ x g hg)⟩
  · rintro ⟨hxI,hxJ⟩ g hg
    obtain ⟨_,N,s,a,hs,_,he⟩ := hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    rcases hs i with hi | hi
    · rw [hxI _ hi,mul_zero]
    · rw [hxJ _ hi,mul_zero]

/-- Actual finite original lower-history reset/increment ideal recursion, retaining every empty step. -/
def stepOneHistoryYearIdeal (m : MarkedIdeal n X) :
    {Y : CMfd.{u} n} → BlowupTower X Y → ℕ → ℕ → GermIdeal n Y
  | _,.refl,s,_ => stepOneLevelBaselineIdeal m .refl s
  | _,.step T C π hπ,s,0 => sumIdeal (stepOneLevelBaselineIdeal m (.step T C π hπ) s)
      (GermIdeal.pullback (m := n) π (stepOneSpecialResetIdeal m T s))
  | _,.step T C π hπ,s,r+1 => sumIdeal (stepOneLevelBaselineIdeal m (.step T C π hπ) s)
      (GermIdeal.pullback (m := n) π ((stepOneSpecialResetIdeal m T s).mul (stepOneHistoryYearIdeal m T s r)))

/-- TRUE actual baseline/reset coherence is constructed BEFORE the desired original whole threshold dictionary. -/
theorem isCoherent_stepOneHistoryYearIdeal (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T →
      ∀ s r : ℕ,(stepOneHistoryYearIdeal m T s r).IsCoherent
  | _,.refl,hc,s,_ => (original_stepOneLevelBaselineIdeal_dictionary hn m h hmax .refl hc s).1
  | _,.step T C π hπ,hc,s,r => by
    have hB := (original_stepOneLevelBaselineIdeal_dictionary hn m h hmax (.step T C π hπ) hc s).1
    have hReset := (original_stepOneSpecialResetIdeal_dictionary hn m h hmax T hc.1 s).1
    cases r with
    | zero => exact isCoherent_sumIdeal hB (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hReset)
    | succ r =>
      exact isCoherent_sumIdeal hB (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff
        (isCoherent_mul hReset (isCoherent_stepOneHistoryYearIdeal hn m h hmax T hc.1 s r)))

/-- BOTH actual run equations give the SAME entire enhanced original masked lower-history year threshold. -/
theorem zeroLocus_stepOneHistoryYearIdeal (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T →
      ∀ s r : ℕ,(stepOneHistoryYearIdeal m T s r).zeroLocus = stepOneHistoryYearSuperlevel m T s r
  | _,.refl,hc,s,_ => by
    rw [stepOneHistoryYearIdeal,(original_stepOneLevelBaselineIdeal_dictionary hn m h hmax .refl hc s).2]
    ext z
    simp only [stepOneHistoryYearSuperlevel,mem_ofPred_eq,StepOneRegime.regimeRun_refl,Nat.zero_le,and_true]
  | _,.step T C π hπ,hc,s,r => by
    obtain ⟨hB,hBZ⟩ := original_stepOneLevelBaselineIdeal_dictionary hn m h hmax (.step T C π hπ) hc s
    obtain ⟨hReset,hResetZ⟩ := original_stepOneSpecialResetIdeal_dictionary hn m h hmax T hc.1 s
    cases r with
    | zero =>
      rw [stepOneHistoryYearIdeal,zeroLocus_sumIdeal hB (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hReset),
        hBZ,BlowupExceptionalDivisor.zeroLocus_pullback hπ.contMDiff hReset,hResetZ,
        stepOneHistoryYearSuperlevel_step_zero hn m h hmax T C π hπ hc s]
    | succ r =>
      have hYear := isCoherent_stepOneHistoryYearIdeal hn m h hmax T hc.1 s r
      rw [stepOneHistoryYearIdeal,zeroLocus_sumIdeal hB
        (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff (isCoherent_mul hReset hYear)),hBZ,
        BlowupExceptionalDivisor.zeroLocus_pullback hπ.contMDiff (isCoherent_mul hReset hYear),
        HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union hReset hYear,hResetZ,
        zeroLocus_stepOneHistoryYearIdeal hn m h hmax T hc.1 s r,
        stepOneHistoryYearSuperlevel_step_succ hn m h hmax T C π hπ hc s r]

/-- Original input independently supplies actual whole coherence AND the exact literal original zero dictionary. -/
theorem original_stepOneHistoryYearIdeal_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T)
    (s r : ℕ) :
    (stepOneHistoryYearIdeal m T s r).IsCoherent ∧
      (stepOneHistoryYearIdeal m T s r).zeroLocus = stepOneHistoryYearSuperlevel m T s r :=
  ⟨isCoherent_stepOneHistoryYearIdeal hn m h hmax T hc s r,zeroLocus_stepOneHistoryYearIdeal hn m h hmax T hc s r⟩

/-- TRUE finite holomorphic generators present BOTH nearby germ membership and the literal whole lower-year locus. -/
theorem exists_original_stepOneHistoryYearIdeal_generators (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T)
    (s r : ℕ) (x : Y) :
    ∃ U : Set Y,IsOpen U ∧ x ∈ U ∧ ∃ (N : ℕ) (a : Fin N → Y → ℂ),
      (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (a i) U) ∧
      (∀ y ∈ U,∀ g,(stepOneHistoryYearIdeal m T s r).mem y g ↔ IsInSpanAt (n := n) (· ∈ range a) y g) ∧
      ∀ y ∈ U,y ∈ stepOneHistoryYearSuperlevel m T s r ↔ ∀ i,a i y=0 := by
  obtain ⟨hI,hZ⟩ := original_stepOneHistoryYearIdeal_dictionary hn m h hmax T hc s r
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
    obtain ⟨_,M,t,b,ht,_,he⟩ := (hgen y hy g).mp hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    obtain ⟨j,hj⟩ := ht i
    rw [← hj,hz j,mul_zero]

private theorem interior_original_cosupp_eq_empty {m : MarkedIdeal n Y} (h : IsInvDomain k m) :
    interior m.cosupp = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨g,hg,hfreq⟩ := h.isNonzeroAlongAt x (m.cosupp_subset_N (interior_subset hx))
  have hmem := HomogenizedGlueing.eventually_mem h.isWellFormed.isCoherent hg
  obtain ⟨z,⟨hzN,hzg⟩,hzgmem,hzO⟩ := (hfreq.and_eventually (hmem.and (isOpen_interior.mem_nhds hx))).exists
  have hzcs := interior_subset hzO
  have hhol := hol_of_coherent h.isWellFormed.isCoherent z g hzgmem
  exact hzg ((GermIdealOrder.vanishesToOrderOn_one_iff hzN hhol).mp ((hzcs.2 g hzgmem).mono h.one_le_d))

/-- Real whole carrier, SAME actual ordered current original SNC boundary, literal lower-year ideal and mark one. -/
def stepOneHistoryYearMarked (m : MarkedIdeal n X) (T : BlowupTower X Y) (s r : ℕ) : MarkedIdeal n Y :=
  ⟨univ,(geoTransformAlong m T).E,stepOneHistoryYearIdeal m T s r,1⟩

/-- Actual original nonzero geometry and exact whole year dictionary internally construct the genuine marked domain. -/
theorem original_stepOneHistoryYearMarked_isInvDomain (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T)
    (s r : ℕ) : IsInvDomain n (stepOneHistoryYearMarked m T s r) := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k) m h hmax hn T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hb.2.1
  obtain ⟨hI,hZ⟩ := original_stepOneHistoryYearIdeal_dictionary hn m h hmax T hc s r
  have hi : interior (stepOneHistoryYearIdeal m T s r).zeroLocus = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hm := interior_mono (show (stepOneHistoryYearIdeal m T s r).zeroLocus ⊆ (geoTransformAlong m T).cosupp from
      fun z hz => (hZ ▸ hz).1) hy
    rw [interior_original_cosupp_eq_empty hd] at hm
    exact hm
  have hN : IsClosedSubmanifold n (univ : Set Y) :=
    ⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
  refine ⟨⟨hN,hI,hd.isWellFormed.isSNCDivisor,isTransverse_univ_of_isSNCDivisor hd.isWellFormed.isSNCDivisor⟩,
    (fun x _ => ⟨n,le_rfl,AnalyticIrreducibleComponents.regularAtDim_univ x⟩),le_rfl,?_⟩
  intro x hx
  apply isNonzeroAlongAt_of_thin_cosupport (d := 1) hI
  · intro O hO hOA
    change O ∩ univ ⊆ GermIdealOrder.cosupport n univ (stepOneHistoryYearIdeal m T s r) 1 at hOA
    change O ∩ univ = ∅
    rw [inter_univ] at hOA ⊢
    rw [GermIdealOrder.cosupport_one (hol_of_coherent hI),univ_inter] at hOA
    have hsub : O ⊆ interior (stepOneHistoryYearIdeal m T s r).zeroLocus := by
      rw [← hO.interior_eq]
      exact interior_mono hOA
    rw [hi] at hsub
    exact eq_empty_iff_forall_notMem.mpr (fun y hy => hsub hy)
  · exact hx

/-- ONLY original full positive input constructs the actual entire coherent companion lower-year and SAME-boundary marked domain. -/
theorem original_full_positive_companion_lower_year_coherent_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp)
    (hq : 1 ≤ HironakaOriginalFrozenCompanionPresentation.orderAt m T x) (s r : ℕ) :
    let K := HironakaOriginalFrozenCompanionPresentation.companionAt m T x
    let S := HironakaOriginalFrozenCompanionPresentation.companionTailAt m T x
    (stepOneHistoryYearIdeal K S s r).IsCoherent ∧
      (stepOneHistoryYearIdeal K S s r).zeroLocus = stepOneHistoryYearSuperlevel K S s r ∧
      IsInvDomain n (stepOneHistoryYearMarked K S s r) := by
  dsimp only
  obtain ⟨_hpatch,hK,hmax,hcan,_hdict⟩ :=
    HironakaOriginalFrozenCompanionPresentation.actual_frozen_companion_domain_and_cosupport hn m h T hc x hx hq
  obtain ⟨hI,hZ⟩ := original_stepOneHistoryYearIdeal_dictionary hn _ hK hmax _ hcan s r
  exact ⟨hI,hZ,original_stepOneHistoryYearMarked_isInvDomain hn _ hK hmax _ hcan s r⟩

end
end Hironaka.HironakaOriginalCoherentStepOneHistoryYearIdeal
