import Hironaka.Resolution.HironakaG8OccupiedRetainedRestart
import Hironaka.Invariant.GeneralCompanionPhase
import Hironaka.Resolution.HironakaG8NativePhaseCertificate
import Hironaka.Resolution.HironakaOriginalNCCanonicalOpenReflection
import Hironaka.Resolution.HironakaOriginalOldBranchTestLocality

/-! The actual lower-order mask misses every higher centre. This keeps the
inherited and restarted order runs comparable on the same active stratum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8OccupiedMixedRestart
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaEmbeddedAnalytic ResolutionInvariantSpec GermIdealOrder
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime NonmonomialOrderCanonical
  GeneralValue GeneralCanonicalTail GeneralCompanionPhase CanonicalCentres ResolutionDriver StepOneRegime
  StepOneEmptyPrefix HomogenizedIdealAlong
  HironakaG8OccupiedPrincipalResidual HironakaG8OccupiedRetainedRestart
  HironakaG8PrincipalRetainedEpochFinite HironakaSharpActualChronologicalResidualDictionary
  HironakaG8NativePhaseCertificate HironakaG8NativeRelativeClearing HironakaG8NativeSimultaneousCentre
  HironakaG1OriginalUnequalMarkCanonical MarkedIdealBiholomorphism

variable {n : ℕ} {X D Y : CMfd.{0} (n+1)}

private abbrev whole (W : Set X) (E : List (Set X)) (d : ℕ) : MarkedIdeal (n+1) X :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,d⟩

private abbrev evaluator : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
    ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
  fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z

private theorem full_run_companion_data
    (B : MarkedIdeal (n+1) D) (hB : IsInvDomain (n+1) B)
    (S : BlowupTower D Y) (hCan : IsCanonical B ((canonicalInvariant (n+1)).inv B) S)
    (y : Y) (hy : y ∈ (geoTransformAlong B S).cosupp) (q : ℕ) (hq : 1 ≤ q)
    (hOrder : nmOrd (geoTransformAlong B S) y = q)
    (hRun : regimeRun (OrdRegime B q) S y = S.length) :
    GenLowerData evaluator (n+1) B q .refl S y := by
  have hTest := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hB S hCan
  have hLow := hasGenLowerData_of_isCanonical evaluator
    (StepOneSeq.isMaxOrderValue_stepOneInvM (k := n+1) (invFamily (Nat.succ_pos n) n) (Nat.succ_pos n))
    (Nat.succ_pos n) hB S hTest hCan y hy q hOrder hq
  rw [hRun] at hLow
  let Data (s : Σ A : CMfd.{0} (n+1), BlowupTower D A × BlowupTower A Y) :=
    GenLowerData evaluator (n+1) B q s.2.1 s.2.2 y
  change Data (split S S.length) at hLow
  rw [split_of_length_le S S.length le_rfl] at hLow
  exact hLow

private theorem value_eq_companion_of_full_run
    (B : MarkedIdeal (n+1) D) (S : BlowupTower D Y) (y : Y) (q : ℕ) (hq : 1 ≤ q)
    (hOrder : nmOrd (geoTransformAlong B S) y = q)
    (hRun : regimeRun (OrdRegime B q) S y = S.length) :
    (canonicalInvariant (n+1)).inv B S y =
      toLex (q,toLex (Sum.inr (genLowerValue evaluator B q .refl S y))) := by
  change genInv evaluator B S y = _
  have hn : q ≠ 0 := by omega
  rw [genInv_of_nmOrd_ne_zero evaluator B S hOrder hn,hRun]
  let f (s : Σ A : CMfd.{0} (n+1), BlowupTower D A × BlowupTower A Y) :=
    genLowerValue evaluator B q s.2.1 s.2.2 y
  change toLex (q,toLex (Sum.inr (f (split S S.length)))) = _
  rw [split_of_length_le S S.length le_rfl]

/-- Both kinds of lower-order point, including those whose run reaches
back into the occupied prefix, have the same full rebased value. Only
the actual higher centres and actual canonical histories enter the proof. -/
theorem original_value_rebase_across_higher_centres
    (M : MarkedIdeal (n+1) X) (hM : IsInvDomain (n+1) M)
    (P : BlowupTower X D) (S : BlowupTower D Y) (q : ℕ) (hq : 1 ≤ q)
    (hHigher : CentresOrdGt M q P) :
    let B := geoTransformAlong M P
    (∀ x ∈ B.cosupp, nmOrd B x ≤ q) →
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (P.append S) →
    IsCanonical B ((canonicalInvariant (n+1)).inv B) S →
    ∀ y ∈ (geoTransformAlong B S).cosupp,
      nmOrd (geoTransformAlong B S) y = q →
      regimeRun (OrdRegime B q) S y = S.length →
      (canonicalInvariant (n+1)).inv M (P.append S) y =
        (canonicalInvariant (n+1)).inv B S y := by
  dsimp only
  intro hCap hCan hCanB y hy hOrder hRun
  let B := geoTransformAlong M P
  let R := canonicalInvariant.{0} (n+1)
  have hBefore := isCanonical_of_append M (R.inv M) P S hCan
  have hP := R.isInvValue.isGeoTestTower_of_isCanonical hM P hBefore
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hM (P.append S) hCan
  have hB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hP
  obtain ⟨hm,_hDom,_hMax,hLowerCan,hSupport⟩ :=
    full_run_companion_data B hB S hCanB y hy q hq hOrder hRun
  have hPhase := genInv_eq_of_mem_cosupp_phase
    (StepOneSeq.isMaxOrderValue_stepOneInvM (k := n+1) (invFamily (Nat.succ_pos n) n) (Nat.succ_pos n))
    (Nat.succ_pos n) hM hq P hP hCap hHigher S hTest hCan hLowerCan
    (⟨y,hm⟩ : openPreimage S (ordMask B q)) hSupport
  have hFresh := value_eq_companion_of_full_run B S y q hq hOrder hRun
  rw [genLowerValue_eq_of_mem evaluator B (T₀ := (.refl : BlowupTower D D)) (T₁ := S) (y := y) hm] at hFresh
  exact hPhase.trans hFresh.symm

private theorem lower_value_on_same_mask
    (A : MarkedIdeal (n+1) D) (U : Opens D) (S : BlowupTower D Y)
    (y : Y) (q : ℕ) (hU : ordMask A q = U) (hm : S.proj y ∈ U) :
    genLowerValue evaluator A q .refl S y =
      ((evaluator (companionOn A U q) (restrict U S) (⟨y,hm⟩ : openPreimage S U)) :
        WithTop (ℕ ×ₗ WithTop (ValTy n))) := by
  subst U
  exact genLowerValue_eq_of_mem evaluator A (T₀ := (.refl : BlowupTower D D)) (T₁ := S) (y := y) hm

private theorem same_companion_value
    (A F : MarkedIdeal (n+1) D) (S : BlowupTower D Y) (y : Y) (q : ℕ) (hq : 1 ≤ q)
    (hMask : ordMask F q = ordMask A q)
    (hComp : companionOn A (ordMask A q) q = companionOn F (ordMask A q) q)
    (hm : S.proj y ∈ ordMask A q)
    (hOrderA : nmOrd (geoTransformAlong A S) y = q)
    (hOrderF : nmOrd (geoTransformAlong F S) y = q)
    (hRunA : regimeRun (OrdRegime A q) S y = S.length)
    (hRunF : regimeRun (OrdRegime F q) S y = S.length) :
    (canonicalInvariant (n+1)).inv A S y = (canonicalInvariant (n+1)).inv F S y := by
  have hValA := value_eq_companion_of_full_run A S y q hq hOrderA hRunA
  have hValF := value_eq_companion_of_full_run F S y q hq hOrderF hRunF
  rw [lower_value_on_same_mask A (ordMask A q) S y q rfl hm] at hValA
  rw [lower_value_on_same_mask F (ordMask A q) S y q hMask hm] at hValF
  let f (J : MarkedIdeal (n+1) (ordMask A q)) : ValTy (n+1) :=
    toLex (q,toLex (Sum.inr ((evaluator J (restrict (ordMask A q) S)
      (⟨y,hm⟩ : openPreimage S (ordMask A q))) : WithTop (ℕ ×ₗ WithTop (ValTy n)))))
  exact hValA.trans ((congrArg f hComp).trans hValF.symm)


private theorem maximum_eq_on_active_stratum {Λ : Type*} [LinearOrder Λ] {Z : Type*}
    (o : Z → ℕ) (v w : Z → Λ) (A B : Set Z) (q : ℕ)
    (hCap : ∀ z ∈ A, o z ≤ q) (hLevel : ∀ z, z ∈ B ↔ z ∈ A ∧ o z = q)
    (hValue : ∀ z ∈ B, v z = w z) (hHigher : ∀ {x y}, o x < o y → v x < v y)
    (hActive : B.Nonempty) : maxLocus v A = maxLocus w B := by
  obtain ⟨a,ha⟩ := hActive
  obtain ⟨haA,haq⟩ := (hLevel a).mp ha
  ext y
  constructor
  · intro hy
    have hyq : o y = q := le_antisymm (hCap y hy.1) (by
      by_contra hn
      exact (not_lt_of_ge (hy.2 a haA)) (hHigher (by rw [haq]; exact Nat.lt_of_not_ge hn)))
    have hyB := (hLevel y).mpr ⟨hy.1,hyq⟩
    refine ⟨hyB,fun z hz => ?_⟩
    rw [← hValue z hz,← hValue y hyB]
    exact hy.2 z ((hLevel z).mp hz).1
  · intro hy
    obtain ⟨hyA,hyq⟩ := (hLevel y).mp hy.1
    refine ⟨hyA,fun z hz => ?_⟩
    by_cases hzB : z ∈ B
    · rw [hValue z hzB,hValue y hy.1]
      exact hy.2 z hzB
    · have hzq : o z ≠ q := fun he => hzB ((hLevel z).mpr ⟨hz,he⟩)
      exact le_of_lt (hHigher (by rw [hyq]; exact lt_of_le_of_ne (hCap z hz) hzq))

/-- The native, rebased whole and chronological whole maxima agree on
a common actual lower prefix. The original companion reads uniformly
across the higher step, including off-centre top competitors. -/
theorem occupied_principal_mixed_maxima_at_common_prefix
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hPure : W ⊆ closure (regularLocus (n := n+1) W n))
    (E : List (Set X)) (μ : ℕ) (hμ : 2 ≤ μ)
    (hDom : IsInvDomain (n+1) (whole W E 1))
    (hOld : HasNoBoundaryFactor (whole W E 1))
    (hBound : ∀ x ∈ W, order (n+1) univ (vanishingIdeal (n := n+1) W) x ≤ (μ : ℕ∞))
    (C : Set X) (π : D → X) (hπ : IsBlowupAlong (n+1) C π)
    (hHigh : (whole W E μ).IsAdmissibleCentre C) (q : ℕ) (hq : 1 ≤ q) (hqμ : q < μ)
    (S : BlowupTower D Y) :
    let M := whole W E 1
    let H : BlowupTower X D := .step .refl C π hπ
    let A := geoTransformAlong M H
    let F := whole (strictTransform (n+1) π W) A.E q
    let R := canonicalInvariant.{0} (n+1)
    IsMaximalOrderAlong F.N F.ideal q →
    IsCanonical M (R.inv M) (H.append S) →
    IsCanonical A (R.inv A) S →
    IsCanonical F (R.inv F) S →
    (geoTransformAlong F S).cosupp.Nonempty →
    maxLocus (R.inv M (H.append S)) (geoTransformAlong M (H.append S)).cosupp =
      maxLocus (R.inv F S) (geoTransformAlong F S).cosupp ∧
    maxLocus (R.inv A S) (geoTransformAlong A S).cosupp =
      maxLocus (R.inv F S) (geoTransformAlong F S).cosupp := by
  dsimp only
  intro hCap hCanOld hCanA hCanF hActive
  let M := whole W E 1
  let H : BlowupTower X D := .step .refl C π hπ
  let A := geoTransformAlong M H
  let F := whole (strictTransform (n+1) π W) A.E q
  let B := geoTransformAlong A S
  let G := geoTransformAlong F S
  let R := canonicalInvariant.{0} (n+1)
  have hLow : M.IsAdmissibleCentre C := ⟨hHigh.1,
    hHigh.2.1.trans (cosupport_anti (show 1 ≤ μ by omega)),hHigh.2.2⟩
  have hA : IsInvDomain (n+1) A :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom H ⟨trivial,hLow⟩
  obtain ⟨hF,hNo,hMask,hComp⟩ := occupied_hypersurface_companion_eq_fresh_companion
    W hW hI hPure E μ hμ hDom hOld hBound C π hπ hHigh q hq
  obtain ⟨_hI,_hNo,hN,_hE,hRes⟩ := occupied_hypersurface_residual_eq_fresh_ideal
    W hW hI hPure E μ hμ hDom hOld hBound C π hπ hHigh
  change A.N = univ at hN
  have hPartF := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hF.isWellFormed.1
    hF.isWellFormed.3 hF.isWellFormed.4 hF.isWellFormed.2 hNo
  change nmPart F = RestrictedIdealExtension.restrictOn (n+1) univ F.ideal at hPartF
  rw [BlowupTowerTransforms.restrictOn_univ hF.isWellFormed.isCoherent] at hPartF
  have hPart : nmPart A = nmPart F := hRes.trans hPartF.symm
  have hActiveData := occupied_lower_active_support_and_runs A F hA hF hq hN rfl hPart hNo hCap S hCanA hCanF
  dsimp only at hActiveData
  obtain ⟨hOrdBound,hLevel,hRuns⟩ := hActiveData
  have hTrans : geoTransformAlong M (H.append S) = B := geoTransformAlong_append M H S
  have hHigher : CentresOrdGt M q H := by
    refine ⟨trivial,fun x hx => ?_⟩
    change x ∈ ordGe M (q+1)
    apply ordGe_anti M (show q+1 ≤ μ by omega)
    rw [ordGe_eq_cosupport_of_hasNoBoundaryFactor M hDom.isWellFormed hOld]
    exact hHigh.2.1 hx
  have hCapA (x : D) (_hx : x ∈ A.cosupp) : nmOrd A x ≤ q := by
    apply nmOrd_le_of_notMem
    have he : ordGe A (q+1) = ordGe F (q+1) := by
      change cosupport (n+1) A.N (nmPart A) (q+1) = cosupport (n+1) F.N (nmPart F) (q+1)
      rw [hN,hPart]
    rw [he,ordGe_eq_cosupport_of_hasNoBoundaryFactor F hF.isWellFormed hNo]
    exact hCap x
  have hRead (y : Y) (hy : y ∈ G.cosupp) :
      R.inv M (H.append S) y = R.inv F S y ∧ R.inv A S y = R.inv F S y := by
    obtain ⟨hyB,hyq⟩ := (hLevel y).mp hy
    obtain ⟨hyG,hRA,hRF⟩ := hRuns y hy
    have hm := (full_run_companion_data A hA S hCanA y hyB q hq hyq hRA)
    obtain ⟨hm,_⟩ := hm
    have hVal := same_companion_value A F S y q hq hMask.symm
      (hComp (ordMask A q)) hm hyq hyG hRA hRF
    have hRebase := original_value_rebase_across_higher_centres M hDom H S q hq
      hHigher hCapA hCanOld hCanA y hyB hyq hRA
    exact ⟨hRebase.trans hVal,hVal⟩
  have hChronL {x y : Y} (h : nmOrd B x < nmOrd B y) :
      R.inv M (H.append S) x < R.inv M (H.append S) y := by
    change genInv evaluator M (H.append S) x < genInv evaluator M (H.append S) y
    apply genInv_lt_of_nmOrd_lt evaluator M
    rw [hTrans]
    exact h
  have hRebaseL {x y : Y} (h : nmOrd B x < nmOrd B y) : R.inv A S x < R.inv A S y :=
    genInv_lt_of_nmOrd_lt evaluator A h
  change maxLocus (R.inv M (H.append S)) (geoTransformAlong M (H.append S)).cosupp =
      maxLocus (R.inv F S) G.cosupp ∧
    maxLocus (R.inv A S) B.cosupp = maxLocus (R.inv F S) G.cosupp
  rw [hTrans]
  exact ⟨maximum_eq_on_active_stratum (nmOrd B) _ _ B.cosupp G.cosupp q hOrdBound hLevel
    (fun y hy => (hRead y hy).1) hChronL hActive,
    maximum_eq_on_active_stratum (nmOrd B) _ _ B.cosupp G.cosupp q hOrdBound hLevel
    (fun y hy => (hRead y hy).2) hRebaseL hActive⟩

/-- Every literal lower canonical tower in the retained principal
epoch is whole mark-one canonical after the occupied higher cut,
including when its active locus meets the off-centre part. -/
theorem occupied_principal_mixed_restart_finite_canonical
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hPure : W ⊆ closure (regularLocus (n := n+1) W n))
    (E : List (Set X)) (μ : ℕ) (hμ : 2 ≤ μ)
    (hDom : IsInvDomain (n+1) (whole W E 1))
    (hOld : HasNoBoundaryFactor (whole W E 1))
    (hBound : ∀ x ∈ W, order (n+1) univ (vanishingIdeal (n := n+1) W) x ≤ (μ : ℕ∞))
    (C : Set X) (π : D → X) (hπ : IsBlowupAlong (n+1) C π)
    (hHigh : (whole W E μ).IsAdmissibleCentre C) (q : ℕ) (hq : 1 ≤ q) (hqμ : q < μ)
    (S : BlowupTower D Y) :
    let M := whole W E 1
    let H : BlowupTower X D := .step .refl C π hπ
    let A := geoTransformAlong M H
    let F := whole (strictTransform (n+1) π W) A.E q
    let R := canonicalInvariant.{0} (n+1)
    IsMaximalOrderAlong F.N F.ideal q →
    IsCanonical M (R.inv M) H →
    IsCanonical F (R.inv F) S →
    IsCanonical M (R.inv M) (H.append S) ∧ IsCanonical A (R.inv A) S := by
  dsimp only
  intro hCap hCanH hCanF
  let M := whole W E 1
  let H : BlowupTower X D := .step .refl C π hπ
  let A := geoTransformAlong M H
  let F := whole (strictTransform (n+1) π W) A.E q
  let R := canonicalInvariant.{0} (n+1)
  change IsCanonical F (R.inv F) S at hCanF
  change IsCanonical M (R.inv M) (H.append S) ∧ IsCanonical A (R.inv A) S
  induction S with
  | refl => exact ⟨hCanH,trivial⟩
  | step S K σ hσ ih =>
    obtain ⟨hChron,hLocal⟩ := ih hCanF.1
    rcases hCanF.2 with he | hc
    · exact ⟨⟨hChron,Or.inl he⟩,⟨hLocal,Or.inl he⟩⟩
    · by_cases hne : K.Nonempty
      · obtain ⟨a,ha⟩ := hne
        have hAct : (geoTransformAlong F S).cosupp.Nonempty := by
          rw [hc] at ha
          exact ⟨a,ha.1⟩
        have hMax := occupied_principal_mixed_maxima_at_common_prefix W hW hI hPure E μ hμ hDom hOld hBound
          C π hπ hHigh q hq hqμ S hCap hChron hLocal hCanF.1 hAct
        exact ⟨⟨hChron,Or.inr (hc.trans hMax.1.symm)⟩,⟨hLocal,Or.inr (hc.trans hMax.2.symm)⟩⟩
      · have he := Set.not_nonempty_iff_eq_empty.mp hne
        exact ⟨⟨hChron,Or.inl he⟩,⟨hLocal,Or.inl he⟩⟩

/-- An actual native phase whose adopted raw chart covers the whole
active locus and is the literal restriction of the whole native record. -/
def HasAdoptedWholeNativeChart
    (W : Set D) (E : List (Set D)) (H : ℕ → ℕ)
    (S : BlowupTower D Y) (F : MarkedIdeal (n+1) D) : Prop :=
  ∃ (I : Type) (A : NativeWindows D I W E H (phaseLevel W H)) (i : I),
    (∀ j, IsCanonical (A.powered j) ((canonicalInvariant (n+1)).inv (A.powered j))
      (restrict (A.openSet j) S) ∧ IsGeoResolution (A.powered j) (restrict (A.openSet j) S)) ∧
    NativeSimultaneousStages (canonicalInvariant (n+1)) A.openSet A.powered S ∧
    F.cosupp ⊆ A.openSet i ∧
    A.record i = MarkedIdeal.pullback (Subtype.val : A.openSet i → D) F

/-- The retained native certificate gives whole CAN when its actual
adopted raw chart contains the entire active locus. Outside the locus
the restricted native phase has only empty centres. -/
theorem actual_native_phase_canonical_of_adopted_whole_chart
    (W : Set D) (E : List (Set D)) (H : ℕ → ℕ) (S : BlowupTower D Y)
    (hPhase : ActualNativePhase W E H S)
    (F : MarkedIdeal (n+1) D) (hF : IsInvDomain (n+1) F) (hN : F.N = univ)
    (hLevel : phaseLevel W H ⊆ F.cosupp)
    (hChart : HasAdoptedWholeNativeChart W E H S F) :
    IsCanonical F ((canonicalInvariant (n+1)).inv F) S := by
  obtain ⟨I,A,i,hTerminal,_hSync,hCover,hRaw⟩ := hChart
  have hCan := (canonicalInvariant_isCanonical_power_iff (A.record i) (A.domain i)
    (A.exponent i) (A.positive i) (restrict (A.openSet i) S)).mpr (hTerminal i).1
  rw [hRaw] at hCan
  have hDomChart := InvDomainTowerAlong.isInvDomain_pullback_val (A.openSet i) hF
  have hTestChart := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hDomChart _ hCan
  have hClosed : IsClosed F.cosupp := by
    unfold MarkedIdeal.cosupp
    rw [hN]
    exact OrderTaylor.isClosed_cosupport hF.isWellFormed.isCoherent F.d
  have hTest := HironakaOriginalOldBranchOpenHistory.isGeoTestTower_of_open_cover F
    hF.isWellFormed.isClosedSubmanifold_N hF.isWellFormed.isCoherent S (by
      intro x
      by_cases hx : x ∈ A.openSet i
      · exact ⟨A.openSet i,hx,hTestChart⟩
      · let U : Opens D := ⟨F.cosuppᶜ,hClosed.isOpen_compl⟩
        have hxU : x ∈ U := fun hxS => hx (hCover hxS)
        have hDis : Disjoint (U : Set D) (phaseLevel W H) :=
          Set.disjoint_left.mpr fun _ hxU hxH => hxU (hLevel hxH)
        have he := RestrictEmptyTower.isEmptyTower_restrict_of_centresOver U hDis S hPhase.supports
        exact ⟨U,hxU,ResolutionInvariantExt.isGeoTestTower_of_isEmptyTower
          (MarkedIdeal.pullback (Subtype.val : U → D) F) _ he⟩)
  exact HironakaOriginalNCCanonicalOpenReflection.isCanonical_of_restrict_cosupport_cover
    (canonicalInvariant (n+1)) F hF (A.openSet i) hCover S hTest hCan

/-- Consume the actual labelled lower phase certificate at an occupied
principal hypersurface cut, without a separately supplied native CAN
proof. The adopted chart identifies the native record and covers all its
initial cosupport. -/
theorem occupied_principal_labelled_restart_canonical
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hPure : W ⊆ closure (regularLocus (n := n+1) W n))
    (E : List (Set X)) (μ : ℕ) (hμ : 2 ≤ μ)
    (hDom : IsInvDomain (n+1) (whole W E 1))
    (hOld : HasNoBoundaryFactor (whole W E 1))
    (hBound : ∀ x ∈ W, order (n+1) univ (vanishingIdeal (n := n+1) W) x ≤ (μ : ℕ∞))
    (C : Set X) (π : D → X) (hπ : IsBlowupAlong (n+1) C π)
    (hHigh : (whole W E μ).IsAdmissibleCentre C) (q : ℕ) (hq : 1 ≤ q) (hqμ : q < μ)
    (Hlower : ℕ → ℕ) (S : BlowupTower D Y) :
    let M := whole W E 1
    let H : BlowupTower X D := .step .refl C π hπ
    let A := geoTransformAlong M H
    let W' := strictTransform (n+1) π W
    let F := whole W' A.E q
    let R := canonicalInvariant.{0} (n+1)
    IsMaximalOrderAlong F.N F.ideal q →
    IsCanonical M (R.inv M) H →
    ActualNativePhase W' A.E Hlower S →
    phaseLevel W' Hlower ⊆ F.cosupp →
    HasAdoptedWholeNativeChart W' A.E Hlower S F →
    IsCanonical M (R.inv M) (H.append S) ∧ IsCanonical A (R.inv A) S := by
  dsimp only
  intro hCap hCan hPhase hLevel hChart
  obtain ⟨hF,_hNo,_hMask,_hComp⟩ := occupied_hypersurface_companion_eq_fresh_companion
    W hW hI hPure E μ hμ hDom hOld hBound C π hπ hHigh q hq
  have hNative := actual_native_phase_canonical_of_adopted_whole_chart _ _ Hlower S hPhase _ hF rfl hLevel hChart
  exact occupied_principal_mixed_restart_finite_canonical W hW hI hPure E μ hμ hDom hOld hBound
    C π hπ hHigh q hq hqμ S hCap hCan hNative

end
end Hironaka.HironakaG8OccupiedMixedRestart
