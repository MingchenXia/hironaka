import Hironaka.Resolution.HironakaActualCoreHistoricalMaskAvoidance
import Hironaka.Resolution.HironakaOriginalFiniteLevelCutLowerTests

/-! Genuine own-run smaller domains/TESTs and actual empty middles on
WHOLE original projected-core maximal histories. No lower CAN or
HasLowerData input. Native clocks and all original boundary slots remain. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCoreHistoricalLowerGeometry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  StepOneValue StepOneValueMasked StepOneRegime StepOneMaskTower StepOneLowerDomain
  StepOneCanonicalTail StepOneNearby RestrictEmptyTower HomogenizedIdealAlong
  HomogenizedIdealAlongTower HironakaActualInitialCountCoreComparison
  HironakaActualRecursiveCoreValues HironakaStageCenters CanonicalCentres
  HironakaOriginalFrozenRecursiveLower HironakaOriginalFiniteLevelCutLowerTests
  HironakaActualCoreHistoricalMaskAvoidance NonmonomialOrderLocal
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

private theorem core_max_level_cut (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X)
    (hJ : J.IsWellFormed) (hd : 1≤J.d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (barMarked J) T →
      StageCentres (fun S C=>∀y∈(geoTransformAlong (barMarked J) S).cosupp,∀c∈C,
        stepOneCoreInv hn k J S y≤stepOneCoreInv hn k J S c) T → IsLevelCutTower J T
  | _, .refl, _, _ => trivial
  | _, .step S C π hπ, hT, hCuts => by
      have hEquiv := coeff_homAlong_wEquiv J hJ.isClosedSubmanifold_N hJ.isCoherent hd
      have hOriginal := (hEquiv.2 (.step S C π hπ)).1.mp hT
      refine ⟨core_max_level_cut hn k J hJ hd S hT.1 hCuts.1,hOriginal.2,?_⟩
      intro y hy _hNS _hPos c hc
      have hyBar : y∈(geoTransformAlong (barMarked J) S).cosupp := by
        rw [(hEquiv.2 S).2 hT.1]
        exact hy
      have hCompare := Prod.Lex.le_iff.mp (hCuts.2 y hyBar c hc)
      have hFirst (p) : (ofLex (stepOneCoreInv hn k J S p)).1=level J S p :=
        Seq.StepOneValueMasked.stepOneInvL_fst _ J _ S p
      rw [hFirst,hFirst] at hCompare
      exact hCompare.elim (fun h=>h.le) (fun h=>h.1.le)

/-- Original whole core-maximum cuts DERIVE genuine source/current lower
domains and lower tests at EVERY actual own-run reference. -/
theorem actual_core_max_current_lower_geometry
    (hn : 0<n) (k d : ℕ) (J : MarkedIdeal n X) (hJ : IsInvDomain (d+1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    (hCuts : StageCentres (fun S C=>∀y∈(geoTransformAlong (barMarked J) S).cosupp,∀c∈C,
      stepOneCoreInv hn k J S y≤stepOneCoreInv hn k J S c) T)
    (z : Y) (hz : z∈(geoTransformAlong (barMarked J) T).cosupp) (hNS : ¬IsSpecial J T z) :
    IsInvDomain d (lowerAt J T z) ∧ IsGeoTestTower (lowerAt J T z) (lowerTailAt J T z) ∧
      IsInvDomain d (geoTransformAlong (lowerAt J T z) (lowerTailAt J T z)) ∧
      ∃ hp : z∈patchAt J T z,
        (⟨z,hp⟩ : patchAt J T z)∈(geoTransformAlong (lowerAt J T z) (lowerTailAt J T z)).cosupp ∧
        ∀p : patchAt J T z,p∈(geoTransformAlong (lowerAt J T z) (lowerTailAt J T z)).cosupp ↔
          (p : Y)∈(geoTransformAlong (barMarked J) T).cosupp ∧ level J T p=level J T z := by
  have hLevel := core_max_level_cut hn k J hJ.isWellFormed hJ.one_le_d T hT hCuts
  have hEquiv := coeff_homAlong_wEquiv J hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hJ.one_le_d
  have hzOriginal : z∈(geoTransformAlong J T).cosupp := by
    rwa [(hEquiv.2 T).2 hT] at hz
  obtain ⟨hLower,hTest,hCurrent,hp,hPoint,hDict⟩ :=
    levelCutTower_current_lower_data hn J hJ hMax T hLevel z hzOriginal hNS
  refine ⟨hLower,hTest,hCurrent,hp,hPoint,?_⟩
  intro p
  rw [(hEquiv.2 T).2 hT]
  exact hDict p

theorem stage_centres_prefix
    (P : ∀{Y : CMfd.{u} n},BlowupTower X Y → Set Y → Prop)
    {A : CMfd.{u} n} (H : BlowupTower X A) :
    ∀{Y : CMfd.{u} n}(S : BlowupTower A Y),StageCentres P (H.append S) → StageCentres P H
  | _, .refl, h => h
  | _, .step S _ _ _, h => stage_centres_prefix P H S h.1

private theorem stage_centres_head
    (P : ∀{Y : CMfd.{u} n},BlowupTower X Y → Set Y → Prop)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) (h : StageCentres P T) :
    StageCentres P (head T j) := by
  rw [←head_append_tail T j] at h
  exact stage_centres_prefix P (head T j) (tail T j) h

private theorem core_middle_of_runs
    (hn : 0<n) (k : ℕ) {b : ℕ} (J : MarkedIdeal n X) (hJ : IsInvDomain b J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    (hCuts : StageCentres (fun S C=>∀y∈(geoTransformAlong (barMarked J) S).cosupp,∀c∈C,
      stepOneCoreInv hn k J S y≤stepOneCoreInv hn k J S c) T)
    {z p : Y} (hz : z∈(geoTransformAlong (barMarked J) T).cosupp) {s : ℕ}
    (hLevel : level J T z=s) {rz rp : ℕ}
    (hrz : regimeRun (stepRegime J s) T z=rz) (hrp : regimeRun (stepRegime J s) T p=rp)
    (hLe : rz≤rp) (hpStart : level J (head T rp) ((tail T rp).proj p)=s) :
    ∃ B : BlowupTower (split T rp).1 (split T rz).1,
      (head T rp).append B=head T rz ∧ B.append (tail T rz)=tail T rp ∧
        CentresAvoid (lowerMask J s (head T rp) ((tail T rp).proj p)) B := by
  have hClosed : ∀H∈J.E,IsClosed H := fun H hH=>hJ.isWellFormed.isSNCDivisor.1 H hH
  rcases hLe.lt_or_eq with hLt | hEq
  · have hrpLe : rp≤T.length := hrp ▸ regimeRun_le_length _ T p
    have hrzLt : rz<T.length := hLt.trans_le hrpLe
    obtain ⟨τ,hτ₁,hτ₂⟩ := exists_split_le T (a:=rz) (b:=rz+1) (Nat.le_succ rz)
    have hτLen : τ.length=1 := by
      have h := congrArg BlowupTower.length hτ₁
      rw [BlowupTower.length_append,length_head,length_head] at h
      omega
    obtain ⟨C,π,hπ,rfl⟩ := exists_eq_step_refl τ hτLen
    obtain ⟨B,hB₁,hB₂⟩ := exists_split_le T (a:=rz+1) (b:=rp) (by omega)
    refine ⟨B.append (.step .refl C π hπ),?_,?_,?_⟩
    · rw [←BlowupTower.append_assoc,hB₁,hτ₁]
    · rw [BlowupTower.append_assoc,hτ₂,hB₂]
    · show CentresAvoid _ (.step B C π hπ)
      have hNotRegime := not_regime_head_regimeRun (stepRegime J s) T z (by rw [hrz];exact hrzLt)
      rw [hrz] at hNotRegime
      have hPoint := mem_cosupp_head J hJ.isWellFormed T hT hz (rz+1)
      have hCount := level_le_head J hClosed T z (rz+1)
      rw [hLevel] at hCount
      rw [←hB₁] at hNotRegime hPoint hCount
      have hHead : (head T rp).append (.step B C π hπ)=head T rz := by
        rw [←hτ₁,←hB₁]
        rfl
      have hHeadTest : IsGeoTestTower (barMarked J) ((head T rp).append (.step B C π hπ)) := by
        rw [hHead]
        exact ((isGeoTestTower_iff_head_tail (barMarked J) T rz).mp hT).1
      have hHeadCuts := stage_centres_head _ T rz hCuts
      rw [←hHead] at hHeadCuts
      exact actual_step_core_centres_avoid_earlier_mask hn k J hJ hMax (head T rp) s
        ((tail T rp).proj p) hpStart B C π hπ hHeadTest hHeadCuts _ hPoint hCount hNotRegime
  · subst hEq
    obtain ⟨B,hB₁,hB₂⟩ := exists_split_le T (le_refl rz)
    refine ⟨B,hB₁,hB₂,centresAvoid_of_length_eq_zero _ B ?_⟩
    have h := congrArg BlowupTower.length hB₁
    rw [BlowupTower.length_append] at h
    omega

/-- Query cosupport/regime/run ordering and the exact empty middle between
ACTUAL run starts are DERIVED from the ENTIRE actual fixed lower cosupp. -/
theorem actual_core_max_fixed_lower_empty_middle
    (hn : 0<n) (k d : ℕ) (J : MarkedIdeal n X) (hJ : IsInvDomain (d+1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    (hCuts : StageCentres (fun S C=>∀y∈(geoTransformAlong (barMarked J) S).cosupp,∀c∈C,
      stepOneCoreInv hn k J S y≤stepOneCoreInv hn k J S c) T)
    (z : Y) (hz : z∈(geoTransformAlong (barMarked J) T).cosupp) (hNS : ¬IsSpecial J T z)
    (p : patchAt J T z) (hp : p∈(geoTransformAlong (lowerAt J T z) (lowerTailAt J T z)).cosupp) :
    ∃ B : BlowupTower (split T (runAt J T p)).1 (split T (runAt J T z)).1,
      (head T (runAt J T p)).append B=head T (runAt J T z) ∧
      B.append (tail T (runAt J T z))=tail T (runAt J T p) ∧
      CentresAvoid (lowerMask J (level J T z) (head T (runAt J T p))
        ((tail T (runAt J T p)).proj p)) B := by
  obtain ⟨_hL,_hTest,_hCurrent,_hzPatch,_hzPoint,hDict⟩ :=
    actual_core_max_current_lower_geometry hn k d J hJ hMax T hT hCuts z hz hNS
  have hpParent := (hDict p).mp hp
  obtain ⟨hReg,hHead⟩ := stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hT hz hNS
  let r := runAt J T z
  have hSplitTest : IsGeoTestTower (barMarked J) ((head T r).append (tail T r)) := by
    rw [head_append_tail]
    exact hT
  have hpCount : level J ((head T r).append (tail T r)) p=level J T z := by
    rw [head_append_tail]
    exact hpParent.2
  have hpReg := stepRegime_and_le_regimeRun_of_mem_lowerMask J hJ.isWellFormed hJ.one_le_d
    hMax (head T r) (tail T r) hSplitTest hReg.1 p.2 hpCount
  rw [head_append_tail] at hpReg
  have hTailLen : (tail T r).length=r := by
    rw [length_tail,min_eq_left (regimeRun_le_length _ T z)]
  have hRunQuery : regimeRun (stepRegime J (level J T z)) T (p : Y)=runAt J T p := by
    simp only [runAt,hpParent.2]
  have hRunLe : runAt J T z≤runAt J T p := by
    rw [hTailLen,hRunQuery] at hpReg
    exact hpReg.2
  have hQueryStart := (stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hT hpParent.1 hpReg.1.2).1.1
  have hpStart : level J (head T (runAt J T p)) ((tail T (runAt J T p)).proj p)=level J T z :=
    hQueryStart.trans hpParent.2
  exact core_middle_of_runs hn k J hJ hMax T hT hCuts hz rfl rfl hRunQuery hRunLe hpStart

private theorem step_core_own_value
    (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (z : Y) (hNS : ¬IsSpecial J T z) (hp : z∈patchAt J T z) :
    stepOneCoreInv hn k J T z=toLex (level J T z,
      ((coreInv hn (k+1) (lowerAt J T z) (lowerTailAt J T z) ⟨z,hp⟩ : ValTy (k+1)) :
        WithTop (ValTy (k+1)))) := by
  have hMask : (tail T (runAt J T z)).proj z∈maskAt J T z := hp
  unfold stepOneCoreInv
  change toLex ((ofLex (Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) J
    (lowerMarkedM J) T z)).1,WithTop.map (eraseGamma (k+1))
      (ofLex (Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) J (lowerMarkedM J) T z)).2)=_
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial _ J _ T hNS,
    Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ J _ hMask]
  rfl

/-- Genuine historical lower geometry precedes the actual DIM2 native
own-curve value computation, without CAN or a numerical certificate. -/
theorem actual_core_max_own_curve_value
    (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    (hCuts : StageCentres (fun S C=>∀y∈(geoTransformAlong (barMarked J) S).cosupp,∀c∈C,
      stepOneCoreInv hn k J S y≤stepOneCoreInv hn k J S c) T)
    (z : Y) (hz : z∈(geoTransformAlong (barMarked J) T).cosupp) (hNS : ¬IsSpecial J T z) :
    ∃ hp : z∈patchAt J T z, IsInvDomain 1 (lowerAt J T z) ∧
      IsGeoTestTower (lowerAt J T z) (lowerTailAt J T z) ∧
      (⟨z,hp⟩ : patchAt J T z)∈(geoTransformAlong (lowerAt J T z) (lowerTailAt J T z)).cosupp ∧
      stepOneCoreInv hn k J T z=toLex (level J T z,
        ((curveCoreValue k (nmOrd (geoTransformAlong (lowerAt J T z) (lowerTailAt J T z))
          ⟨z,hp⟩) : ValTy (k+1)) : WithTop (ValTy (k+1)))) := by
  obtain ⟨hL,hLowerTest,_hCurrent,hp,hPoint,_hDict⟩ :=
    actual_core_max_current_lower_geometry hn k 1 J hJ hMax T hT hCuts z hz hNS
  refine ⟨hp,hL,hLowerTest,hPoint,?_⟩
  have hOwn := step_core_own_value hn k J T z hNS hp
  have hCurve := actual_curve_core_value hn k (lowerAt J T z) hL (lowerTailAt J T z) hLowerTest ⟨z,hp⟩ hPoint
  exact hOwn.trans (congrArg (fun value : ValTy (k+1)=>toLex (level J T z,(value : WithTop (ValTy (k+1)))))
    hCurve)

end
end Hironaka.HironakaActualCoreHistoricalLowerGeometry
