import Hironaka.Resolution.HironakaActualRecursiveCoreValues
import Hironaka.Resolution.HironakaActualPositiveCoreCountPresentation

/-! An actual first higher-dimensional native core reference comparison.
The reference starts at the original source clock, and the SAME whole
test history is retained. Arbitrary earlier prefixes are not reset. -/
set_option autoImplicit false
open Set Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualInitialCountCoreComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerSplit
  StepOneValue StepOneValueMasked StepOneMaskTower StepOneNearby StepOneRegime
  HomogenizedIdealAlong HironakaActualPositiveCoreCountPresentation
  HironakaActualRecursiveCoreValues HironakaStageCenters CanonicalCentres
  NonmonomialOrderLocal
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X : CMfd.{u} n}

private theorem split_at_length : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    split T T.length = ⟨X, .refl, T⟩
  | _, .refl => rfl
  | _, .step T C π hπ => by
      change (⟨(split T T.length).1, (split T T.length).2.1,
        .step (split T T.length).2.2 C π hπ⟩ :
          Σ A : CMfd.{u} n, BlowupTower X A × BlowupTower A _) = _
      rw [split_at_length T]

private theorem same_positive_mask
    (J : MarkedIdeal n X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    {a w : Y₀} (hw : w ∈ maskA J T₀ a)
    (hl : level J T₀ w = level J T₀ a) : maskA J T₀ w = maskA J T₀ a := by
  have hm := mem_origMembers_iff_of_mem_maskA J T₀ hw hl
  apply Opens.ext
  change interior {z | (∀ H ∈ origMembers J T₀, z ∈ H → w ∈ H) ∧
      ¬ (level J T₀ z = level J T₀ w ∧ IsSpecial J T₀ z)} =
    interior {z | (∀ H ∈ origMembers J T₀, z ∈ H → a ∈ H) ∧
      ¬ (level J T₀ z = level J T₀ a ∧ IsSpecial J T₀ z)}
  apply congrArg interior
  ext z
  constructor
  · rintro ⟨hz, hns⟩
    exact ⟨fun H hH hzH => (hm H hH).mp (hz H hH hzH), by simpa only [hl] using hns⟩
  · rintro ⟨hz, hns⟩
    exact ⟨fun H hH hzH => (hm H hH).mpr (hz H hH hzH), by simpa only [hl] using hns⟩

private theorem inv_same_open
    {k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (K : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (z : Y)
    {U V : Opens X} (hUV : U=V) (hzU : T.proj z ∈ U) (hzV : T.proj z ∈ V) :
    R.inv (MarkedIdeal.pullback (Subtype.val : U → X) K) (restrict U T) ⟨z,hzU⟩ =
      R.inv (MarkedIdeal.pullback (Subtype.val : V → X) K) (restrict V T) ⟨z,hzV⟩ := by
  subst V
  rfl

/-- Actual masks and the native run identify the SAME fixed initial lower
reference on EVERY original TEST, without native or lower CAN. -/
theorem actual_initial_positive_count_native_reference
    {k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1 ≤ J.d)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (s : ℕ) (a : X)
    (hLevel : level J (.refl : BlowupTower X X) a = s+1)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    (p : openPreimage T (lowerMask J (s+1) (.refl : BlowupTower X X) a))
    (hpLevel : level J T p = s+1) :
    Seq.StepOneValueMasked.stepOneInvM R J T p =
      toLex (s+1, ((R.inv (lowerMarked J (s+1) (.refl : BlowupTower X X) a)
        (restrict (lowerMask J (s+1) (.refl : BlowupTower X X) a) T) p : Λ) : WithTop Λ)) := by
  have hT' : IsGeoTestTower (barMarked J) ((.refl : BlowupTower X X).append T) := by
    simpa only [BlowupTower.refl_append] using hT
  have hpLevel' : level J ((.refl : BlowupTower X X).append T) p = s+1 := by
    simpa only [BlowupTower.refl_append] using hpLevel
  have hReg := stepRegime_and_le_regimeRun_of_mem_lowerMask J hJ hd hMax
    (.refl : BlowupTower X X) T hT' hLevel p.2 hpLevel'
  simp only [BlowupTower.refl_append] at hReg
  have hRun : regimeRun (stepRegime J (s+1)) T p = T.length :=
    (regimeRun_le_length _ T p).antisymm hReg.2
  have hClosed : ∀ H ∈ J.E, IsClosed H := fun H hH => hJ.isSNCDivisor.1 H hH
  have hInitial : level J (.refl : BlowupTower X X) (T.proj p) = s+1 := by
    have hUpper := level_le_of_forall_mem_imp J (.refl : BlowupTower X X) (interior_subset p.2).1
    have hLower := level_append_le J hClosed (.refl : BlowupTower X X) T p
    simp only [BlowupTower.refl_append, hpLevel, hLevel] at hUpper hLower
    omega
  have hSameLevel : level J (.refl : BlowupTower X X) (T.proj p) =
      level J (.refl : BlowupTower X X) a := hInitial.trans hLevel.symm
  have hMask := same_positive_mask J (.refl : BlowupTower X X) p.2 hSameLevel
  have hMembers := membersThrough_eq_of_mem_maskA J (.refl : BlowupTower X X) p.2 hSameLevel
  change Seq.StepOneValueMasked.stepOneInvL R J (lowerMarkedM J) T p = _
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R J _ T hReg.1.2,
    hpLevel, hRun]
  unfold head tail
  rw [split_at_length T]
  have hpMask : T.proj p ∈ lowerMask J (s+1) (.refl : BlowupTower X X) (T.proj p) := by
    change T.proj p ∈ maskA J (.refl : BlowupTower X X) (T.proj p)
    rw [hMask]
    exact p.2
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem R J _ hpMask]
  simp only [lowerMarkedM, lowerMarked, lowerMask, hMembers]
  exact congrArg (fun value : Λ => toLex (s+1, (value : WithTop Λ)))
    (inv_same_open R _ T (p : Y) hMask hpMask p.2)

/-- A genuine dimension-two source internally produces its fixed curve
lower model and tests, then computes the ACTUAL next recursive core entry
and its ENTIRE numerical cuts. No lower CAN or value certificate. -/
theorem actual_initial_count_curve_core_comparison
    (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (s : ℕ) (a : X)
    (ha : a ∈ (barMarked J).cosupp)
    (hLevel : level J (.refl : BlowupTower X X) a = s+1)
    (hNotSpecial : ¬ IsSpecial J (.refl : BlowupTower X X) a) :
    let W := lowerMask J (s+1) (.refl : BlowupTower X X) a
    let L := lowerMarked J (s+1) (.refl : BlowupTower X X) a
    a ∈ W ∧ IsInvDomain 1 L ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (barMarked J) T →
        StageCentres (fun S C => ∀ c∈C, s+1 ≤ level J S c) T →
          IsGeoTestTower L (restrict W T) ∧
          (geoTransformAlong L (restrict W T)).cosupp =
            (Subtype.val : openPreimage T W → Y) ⁻¹'
              {y | y ∈ (geoTransformAlong (barMarked J) T).cosupp ∧ level J T y=s+1} ∧
          ∀ p ∈ (geoTransformAlong L (restrict W T)).cosupp,
            let v := Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T p
            let c := toLex ((ofLex v).1, WithTop.map (eraseGamma (k+1)) (ofLex v).2)
            c = toLex (s+1, ((curveCoreValue k
              (nmOrd (geoTransformAlong L (restrict W T)) p) : ValTy (k+1)) : WithTop (ValTy (k+1)))) ∧
              ∀ q : ℕ, toLex (s+1, ((curveCoreValue k q : ValTy (k+1)) : WithTop (ValTy (k+1)))) ≤ c ↔
                q ≤ nmOrd (geoTransformAlong L (restrict W T)) p := by
  dsimp only
  obtain ⟨hW, hL, hFuture⟩ := actual_positive_count_whole_presentation
    hn J hJ hMax (.refl : BlowupTower X X) trivial s a ha hLevel hNotSpecial
  refine ⟨hW, hL, ?_⟩
  intro Y T hT hCuts
  have hT' : IsGeoTestTower (barMarked J) ((.refl : BlowupTower X X).append T) := by
    simpa only [BlowupTower.refl_append] using hT
  have hCuts' : StageCentres
      (fun S C => ∀ c∈C, s+1 ≤ level J ((.refl : BlowupTower X X).append S) c) T := by
    simpa only [BlowupTower.refl_append] using hCuts
  obtain ⟨hTL, _hCurrent, hCos, _hBorn⟩ := hFuture T hT' hCuts'
  simp only [BlowupTower.refl_append] at hCos
  refine ⟨hTL, hCos, ?_⟩
  intro p hp
  have hpParent : (p : Y) ∈ (geoTransformAlong (barMarked J) T).cosupp ∧ level J T p=s+1 := by
    rw [hCos] at hp
    exact hp
  have hNative := actual_initial_positive_count_native_reference (invFamily hn (k+1))
    J hJ.isWellFormed hJ.one_le_d hMax s a hLevel T hT p hpParent.2
  have hCurve := actual_curve_core_value hn k
    (lowerMarked J (s+1) (.refl : BlowupTower X X) a) hL
    (restrict (lowerMask J (s+1) (.refl : BlowupTower X X) a) T) hTL p hp
  have hCore : toLex ((ofLex (Seq.StepOneValueMasked.stepOneInvM
      (invFamily hn (k+1)) J T p)).1,
      WithTop.map (eraseGamma (k+1)) (ofLex (Seq.StepOneValueMasked.stepOneInvM
        (invFamily hn (k+1)) J T p)).2) =
      toLex (s+1, ((curveCoreValue k (nmOrd (geoTransformAlong
        (lowerMarked J (s+1) (.refl : BlowupTower X X) a)
        (restrict (lowerMask J (s+1) (.refl : BlowupTower X X) a) T)) p) :
          ValTy (k+1)) : WithTop (ValTy (k+1)))) := by
    rw [hNative]
    change toLex (s+1, ((coreInv hn (k+1)
      (lowerMarked J (s+1) (.refl : BlowupTower X X) a)
      (restrict (lowerMask J (s+1) (.refl : BlowupTower X X) a) T) p :
        ValTy (k+1)) : WithTop (ValTy (k+1)))) = _
    rw [hCurve]
  refine ⟨hCore, ?_⟩
  intro q
  rw [hCore, Prod.Lex.toLex_le_toLex]
  simp only [lt_self_iff_false, true_and, false_or, WithTop.coe_le_coe]
  exact (curveCoreValue_strictMono k).le_iff_le

/-- The explicit projection of the UNCHANGED actual native Step One value;
the preceding theorem supplies its genuine fixed-reference semantics. -/
def stepOneCoreInv (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) : ℕ ×ₗ WithTop (ValTy (k+1)) :=
  let v := Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T y
  toLex ((ofLex v).1, WithTop.map (eraseGamma (k+1)) (ofLex v).2)

private theorem core_cuts_count (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) (s q : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      StageCentres (fun S C => ∀ c∈C,
        toLex (s+1, ((curveCoreValue k q : ValTy (k+1)) : WithTop (ValTy (k+1)))) ≤
          stepOneCoreInv hn k J S c) T →
        StageCentres (fun S C => ∀ c∈C, s+1 ≤ level J S c) T
  | _, .refl, _ => trivial
  | _, .step S C π hπ, hCuts => by
      refine ⟨core_cuts_count hn k J s q S hCuts.1, ?_⟩
      intro c hc
      have h := hCuts.2 c hc
      change toLex (s+1, _) ≤ toLex (_, _) at h
      have hFirst : (ofLex (Seq.StepOneValueMasked.stepOneInvM
          (invFamily hn (k+1)) J S c)).1 = level J S c :=
        Seq.StepOneValueMasked.stepOneInvL_fst _ J _ S c
      rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h, _⟩
      · simpa only [hFirst] using h.le
      · simpa only [hFirst] using h.le

/-- Whole geometric cuts of the ACTUAL projected native value DERIVE the
next fixed lower companion tests by genuine prefix induction. -/
theorem actual_initial_count_native_core_cut_presentation
    (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (s : ℕ) (a : X)
    (ha : a ∈ (barMarked J).cosupp)
    (hLevel : level J (.refl : BlowupTower X X) a = s+1)
    (hNotSpecial : ¬ IsSpecial J (.refl : BlowupTower X X) a)
    (q : ℕ) (hq : 1≤q) :
    let W := lowerMask J (s+1) (.refl : BlowupTower X X) a
    let L := lowerMarked J (s+1) (.refl : BlowupTower X X) a
    let V := NonmonomialOrderTail.ordMask L q
    let A := MarkedIdeal.pullback (Subtype.val : V → W) L
    let O := CompanionRebase.companionOf n (M := CMfd.of (n := n) V) A q
    IsInvDomain 1 L ∧ IsInvDomain 1 O ∧ IsMaximalOrderAlong O.N O.ideal O.d ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (barMarked J) T →
        StageCentres (fun S C => ∀ c∈C,
          toLex (s+1, ((curveCoreValue k q : ValTy (k+1)) : WithTop (ValTy (k+1)))) ≤
            stepOneCoreInv hn k J S c) T →
          IsGeoTestTower O (restrict V (restrict W T)) ∧
          (geoTransformAlong O (restrict V (restrict W T))).cosupp =
            (Subtype.val : openPreimage (restrict W T) V → openPreimage T W) ⁻¹'
              {p | p ∈ (geoTransformAlong L (restrict W T)).cosupp ∧
                toLex (s+1, ((curveCoreValue k q : ValTy (k+1)) : WithTop (ValTy (k+1)))) ≤
                  stepOneCoreInv hn k J T p} := by
  dsimp only
  let W := lowerMask J (s+1) (.refl : BlowupTower X X) a
  let L := lowerMarked J (s+1) (.refl : BlowupTower X X) a
  obtain ⟨_hW, hL, hFuture⟩ := actual_initial_count_curve_core_comparison
    hn k J hJ hMax s a ha hLevel hNotSpecial
  obtain ⟨hO, hMaxO, _hReflTest, _hReflCos⟩ :=
    actual_curve_core_masked_whole_presentation (X := CMfd.of (n := n) W)
      hn k L hL q hq (.refl : BlowupTower (CMfd.of (n := n) W) _) trivial trivial
  refine ⟨hL, hO, hMaxO, ?_⟩
  have hLowerCuts : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (barMarked J) T →
      StageCentres (fun S C => ∀ c∈C,
        toLex (s+1, ((curveCoreValue k q : ValTy (k+1)) : WithTop (ValTy (k+1)))) ≤
          stepOneCoreInv hn k J S c) T →
      StageCentres (fun S C => C ⊆ ordGe (geoTransformAlong L S) q) (restrict W T) := by
    intro Y T
    induction T with
    | refl => intro _ _; trivial
    | @step Y Z S C π hπ ih =>
      intro hT hCuts
      have hCount := core_cuts_count hn k J s q (.step S C π hπ) hCuts
      obtain ⟨hTL, _hCos, _hValue⟩ := hFuture (.step S C π hπ) hT hCount
      obtain ⟨hSL, _hCosS, hValueS⟩ := hFuture S hT.1 hCount.1
      have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hL (restrict W S) hSL
      refine ⟨ih hT.1 hCuts.1, ?_⟩
      intro p hp
      have hpCos : p ∈ (geoTransformAlong L (restrict W S)).cosupp := hTL.2.2.1 hp
      have hOrder : q ≤ nmOrd (geoTransformAlong L (restrict W S)) p :=
        ((hValueS p hpCos).2 q).mp (hCuts.2 p hp)
      exact (mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
        ((geoTransformAlong L (restrict W S)).cosupp_subset_N hpCos) q).mpr hOrder
  intro Y T hT hCuts
  have hCount := core_cuts_count hn k J s q T hCuts
  obtain ⟨hTL, _hCosL, hValues⟩ := hFuture T hT hCount
  obtain ⟨_hO, _hMaxO, hTO, hCosO⟩ := actual_curve_core_masked_whole_presentation (X := CMfd.of (n := n) W)
    hn k L hL q hq (restrict W T) hTL (hLowerCuts T hT hCuts)
  refine ⟨hTO, ?_⟩
  rw [hCosO]
  apply congrArg (fun S : Set (openPreimage T W) =>
    (Subtype.val : openPreimage (restrict W T) (NonmonomialOrderTail.ordMask L q) → openPreimage T W) ⁻¹' S)
  ext p
  constructor
  · rintro ⟨hp, hCore⟩
    rw [actual_curve_core_value hn k L hL (restrict W T) hTL p hp] at hCore
    exact ⟨hp, ((hValues p hp).2 q).mpr ((curveCoreValue_strictMono k).le_iff_le.mp hCore)⟩
  · rintro ⟨hp, hNative⟩
    refine ⟨hp, ?_⟩
    rw [actual_curve_core_value hn k L hL (restrict W T) hTL p hp]
    exact (curveCoreValue_strictMono k).monotone (((hValues p hp).2 q).mp hNative)

end
end Hironaka.HironakaActualInitialCountCoreComparison
