/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedCurrentLower
/-! Literal admissible level-cut histories contain no lower data or canonicity
field. Actual lower TESTs follow by real history induction. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteLevelCutLowerTests
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  StepOneLowerDomain StepOneValue StepOneValueMasked StepOneRegime StepOneCanonicalTail
  StepOneCompare MemberRestrictAdmissible HironakaOriginalFrozenRecursiveLower InvDomainTowerAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

/-- Only literal original admissibility and ordinary positive level cuts. -/
def IsLevelCutTower (M : MarkedIdeal n X) : ∀ {Y : CMfd.{u} n},BlowupTower X Y → Prop
  | _,.refl => True
  | _,.step T C _ _ => IsLevelCutTower M T ∧
      (geoTransformAlong M T).IsAdmissibleCentre C ∧
      ∀ y∈(geoTransformAlong M T).cosupp,¬IsSpecial M T y → 0<level M T y →
        ∀ c∈C,level M T y≤level M T c

/-- A real whole Step One cut supplies the recipe by its literal first coordinate. -/
theorem levelCutTower_step_of_stepone_cut (hn : 0<n) (M : MarkedIdeal n X)
    (T : BlowupTower X Y) (hT : IsLevelCutTower M T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCut : ∀ y∈(geoTransformAlong M T).cosupp,∀ c∈C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c) :
    IsLevelCutTower M (.step T C π hπ) := by
  refine ⟨hT,hC,?_⟩
  intro y hy _hns _hp c hc
  have hh := Prod.Lex.le_iff.mp (hCut y hy c hc)
  rw [Seq.StepOneValueMasked.stepOneInvL_fst,
    Seq.StepOneValueMasked.stepOneInvL_fst] at hh
  exact hh.elim (fun h => h.le) (fun h => h.1.le)

theorem levelCutTower_geoTest (M : MarkedIdeal n X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsLevelCutTower M T) : IsGeoTestTower M T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih => exact ⟨ih hT.1,hT.2.1⟩

private theorem actual_positive_trace_test (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (s : ℕ) (hs : level M T y=s+1)
    (hLower : let r := regimeRun (stepRegime M (s+1)) T y
      let H := head T r
      let S := tail T r
      let W := lowerMask M (s+1) H (S.proj y)
      IsGeoTestTower (lowerMarked M (s+1) H (S.proj y)) (restrict W S))
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hLevel : ∀ c∈C,s+1≤level M T c) :
    let r := regimeRun (stepRegime M (s+1)) T y
    let H := head T r
    let S := tail T r
    let W := lowerMask M (s+1) H (S.proj y)
    IsGeoTestTower (lowerMarked M (s+1) H (S.proj y)) (restrict W (.step S C π hπ)) := by
  let r := regimeRun (stepRegime M (s+1)) T y
  let H := head T r
  let S := tail T r
  let W := lowerMask M (s+1) H (S.proj y)
  let J := lowerMarked M (s+1) H (S.proj y)
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hyBar : y∈(geoTransformAlong (barMarked M) T).cosupp := by
    rw [(he.2 T).2 hBar];exact hy
  obtain ⟨hReg,hHead⟩ := stepRegime_and_mem_cosupp_head M hM.isWellFormed T hBar hyBar hns
  rw [hs] at hReg hHead
  have hH := ((isGeoTestTower_iff_head_tail (barMarked M) T r).mp hBar).1
  obtain ⟨hp,_hDom⟩ := mem_lowerMask_and_isInvDomain_M M hM.isWellFormed hM.one_le_d
    hn hmax hM.dimLE H hH hHead hReg
  have hJT : IsGeoTestTower J (restrict W S) := hLower
  have hApp : H.append S=T := head_append_tail T r
  have hBarNext : IsGeoTestTower (barMarked M) (.step T C π hπ) :=
    (he.2 (.step T C π hπ)).1.mpr ⟨hT,hC⟩
  have hHS : IsGeoTestTower (barMarked M) (H.append (.step S C π hπ)) := by
    simpa only [BlowupTower.append_step,hApp] using hBarNext
  have hTailStep := (isGeoTestTower_append_iff (barMarked M) H (.step S C π hπ)).mp hHS
  have hHeadWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked M hM.isWellFormed) H hH
  have hRestricted := isGeoTestTower_restrict W hHeadWF.isClosedSubmanifold_N
    hHeadWF.isCoherent (.step S C π hπ) hTailStep.2
  have hOldTail := ((isGeoTestTower_iff_head_tail (barMarked M) T r).mp hBar).2
  have hAdm := hRestricted.2
  rw [geoTransformAlong_restrict W hHeadWF.isClosedSubmanifold_N hHeadWF.isCoherent S hOldTail,
    ←geoTransformAlong_append,hApp] at hAdm
  have hTrace : (geoTransformAlong J (restrict W S)).IsAdmissibleCentre
      ((Subtype.val : openPreimage S W → Y) ⁻¹' C) := by
    apply (isAdmissibleCentre_lowerMarked_succ_iff M hM.isWellFormed hn H S
      (by rw [hApp];exact hBar) hp hJT _).mpr
    refine ⟨by rwa [hApp],?_⟩
    intro q hq
    have hGe := hLevel q hq
    have hLe : level M T q≤s+1 := by
      have hh := level_le_of_mem_lowerMask M (fun A hA => hM.isWellFormed.isSNCDivisor.1 A hA)
        H S hReg.1 q.property
      rwa [hApp] at hh
    have hDict := mem_cosupp_lowerMarkedM_iff M hM.isWellFormed hM.one_le_d hn hmax H S
      (by rw [hApp];exact hBar) hHead hReg.1 hp hJT q
    rw [hApp,(he.2 T).2 hBar] at hDict
    have hqCos := hDict.mpr ⟨hC.2.1 hq,le_antisymm hLe hGe⟩
    exact ((mem_cosupp_lowerMarked_succ_iff M hM.isWellFormed hn H S
      (by rw [hApp];exact hBar) hp hJT q).mp hqCos).2
  exact ⟨hJT,hTrace⟩

/-- The private assertion is established by true finite-history induction,
not supplied as a caller lower TEST or canonicality certificate. -/
private theorem positive_lower_tests_of_levelCutTower (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsLevelCutTower M T) :
    ∀ z∈(geoTransformAlong M T).cosupp,∀ s : ℕ,
      let r := regimeRun (stepRegime M (s+1)) T z
      let H := head T r
      let S := tail T r
      let W := lowerMask M (s+1) H (S.proj z)
      IsGeoTestTower (lowerMarked M (s+1) H (S.proj z)) (restrict W S) := by
  induction T with
  | refl => intro z hz s;trivial
  | step T C π hπ ih =>
    intro z hz s
    have hOldTest := levelCutTower_geoTest M T hT.1
    have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      hM.isWellFormed T hOldTest
    have hOldPoint : π z∈(geoTransformAlong M T).cosupp :=
      proj_mem_cosupp_of_mem_cosupp hWF.isClosedSubmanifold_N hWF.isCoherent
        (.step .refl C π hπ) ⟨trivial,hT.2.1⟩ hz
    by_cases hOld : stepRegime M (s+1) T (π z)
    · have hPositive : 0<level M T (π z) := by rw [hOld.1];omega
      have hLower := ih hT.1 (π z) hOldPoint s
      have hLevel : ∀ c∈C,s+1≤level M T c := by
        intro c hc
        rw [←hOld.1]
        exact hT.2.2 (π z) hOldPoint hOld.2 hPositive c hc
      have hNext := actual_positive_trace_test hn M hM hmax T hOldTest
        (π z) hOldPoint hOld.2 s hOld.1 hLower C hT.2.1 π hπ hLevel
      rw [regimeRun_step_of (stepRegime M (s+1)) T C π hπ hOld]
      exact hNext
    · rw [regimeRun_step_of_not (stepRegime M (s+1)) T C π hπ hOld]
      trivial

/-- Actual original lower TEST after ANY finite literal admissible level-cut
history. No old or next CAN, lower TEST or point certificate is an input. -/
theorem levelCutTower_current_lower_test (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsLevelCutTower M T)
    (z : Y) (hz : z∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T z) :
    IsGeoTestTower (lowerAt M T z) (lowerTailAt M T z) := by
  let F : ℕ → Prop := fun ℓ =>
    let r := regimeRun (stepRegime M ℓ) T z
    let H := head T r
    let S := tail T r
    let W := lowerMask M ℓ H (S.proj z)
    IsGeoTestTower (lowerMarkedM M ℓ H (S.proj z)) (restrict W S)
  change F (level M T z)
  by_cases hZero : level M T z=0
  · have hUpper := levelCutTower_geoTest M T hT
    have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d
    have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hUpper
    have hzBar : z∈(geoTransformAlong (barMarked M) T).cosupp := by
      rw [(he.2 T).2 hBar];exact hz
    have hHead := (stepRegime_and_mem_cosupp_head M hM.isWellFormed T hBar hzBar hns).2
    rw [hZero] at hHead
    let r := regimeRun (stepRegime M 0) T z
    have hAppend : IsGeoTestTower (barMarked M) ((head T r).append (tail T r)) := by
      rw [head_append_tail];exact hBar
    have hLower := StepOneCompare.isGeoTestTower_cosupp_lowerMarkedB M hM.isWellFormed
      hM.one_le_d hmax (head T r) (tail T r) hAppend hHead
    have hF : F 0 := hLower.1
    exact (congrArg F hZero).mpr hF
  · obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero hZero
    have hF : F (s+1) := positive_lower_tests_of_levelCutTower hn M hM hmax T hT z hz s
    exact (congrArg F hs).mpr hF

/-- Genuine current DOMAIN, actual lower endpoint and WHOLE cosupport after
finite level-cut histories are internally constructed from original inputs. -/
theorem levelCutTower_current_lower_data (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsLevelCutTower M T)
    (z : Y) (hz : z∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T z) :
    let J := lowerAt M T z
    let R := lowerTailAt M T z
    IsInvDomain k J ∧ IsGeoTestTower J R ∧ IsInvDomain k (geoTransformAlong J R) ∧
      ∃ hp : z∈patchAt M T z,
        (⟨z,hp⟩ : patchAt M T z)∈(geoTransformAlong J R).cosupp ∧
        ∀ p : patchAt M T z,p∈(geoTransformAlong J R).cosupp ↔
          p.val∈(geoTransformAlong M T).cosupp ∧ level M T p.val=level M T z := by
  have hUpper := levelCutTower_geoTest M T hT
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hUpper
  have hzBar : z∈(geoTransformAlong (barMarked M) T).cosupp := by
    rw [(he.2 T).2 hBar];exact hz
  obtain ⟨hReg,hHead⟩ := stepRegime_and_mem_cosupp_head M hM.isWellFormed T hBar hzBar hns
  let r := runAt M T z
  have hH := ((isGeoTestTower_iff_head_tail (barMarked M) T r).mp hBar).1
  obtain ⟨hp,hDom⟩ := mem_lowerMask_and_isInvDomain_M M hM.isWellFormed hM.one_le_d
    hn hmax hM.dimLE (head T r) hH hHead hReg
  have hJ : IsInvDomain k (lowerAt M T z) := hDom
  have hTest := levelCutTower_current_lower_test hn M hM hmax T hT z hz hns
  have hApp := head_append_tail T r
  have hDict : ∀ p : patchAt M T z,
      p∈(geoTransformAlong (lowerAt M T z) (lowerTailAt M T z)).cosupp ↔
        p.val∈(geoTransformAlong M T).cosupp ∧ level M T p.val=level M T z := by
    intro p
    have hd := mem_cosupp_lowerMarkedM_iff M hM.isWellFormed hM.one_le_d hn hmax
      (head T r) (tail T r) (by rw [hApp];exact hBar) hHead hReg.1 hp hTest p
    rw [hApp,(he.2 T).2 hBar] at hd
    exact hd
  exact ⟨hJ,hTest,isInvDomain_geoTransformAlong hJ _ hTest,hp,(hDict ⟨z,hp⟩).mpr ⟨hz,rfl⟩,hDict⟩

end
end Hironaka.HironakaOriginalFiniteLevelCutLowerTests
