import Hironaka.Resolution.HironakaActualPositiveCountCoreDimensionReduction

/-! Actual projected-core finite/special comparison and WHOLE historical
middle-mask avoidance. No lower CAN, lower-data or lower TEST certificate;
all original prefix, boundary and empty-step clocks are retained. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCoreHistoricalMaskAvoidance
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  StepOneValue StepOneValueMasked StepOneRegime StepOneMaskTower StepOneLowerDomain
  StepOneCanonicalTail StepOneNearby RestrictEmptyTower HomogenizedIdealAlong
  HironakaActualInitialCountCoreComparison HironakaActualRecursiveCoreValues
  HironakaStageCenters CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

private theorem step_core_fst (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (ofLex (stepOneCoreInv hn k J T y)).1=level J T y :=
  Seq.StepOneValueMasked.stepOneInvL_fst _ J _ T y

/-- Genuine own-run mask membership makes the ACTUAL native lower entry
finite on ANY parent TEST. No lower-history geometric interpretation is
used here, only the literal native formula defined on all towers. -/
theorem actual_step_core_finite (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X)
    (hJ : J.IsWellFormed) (hd : 1≤J.d) (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    (y : Y) (hy : y∈(geoTransformAlong (barMarked J) T).cosupp) (hNS : ¬IsSpecial J T y) :
    stepOneCoreInv hn k J T y<toLex (level J T y,(⊤ : WithTop (ValTy (k+1)))) := by
  obtain ⟨hReg,hCos⟩ := stepRegime_and_mem_cosupp_head J hJ T hT hy hNS
  have hHead := ((isGeoTestTower_iff_head_tail (barMarked J) T
    (regimeRun (stepRegime J (level J T y)) T y)).mp hT).1
  have hMask := mem_lowerMask_of_stepRegime J hJ hd hn hMax _ hHead hCos hReg
  unfold stepOneCoreInv
  change toLex ((ofLex (Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) J
      (lowerMarkedM J) T y)).1,WithTop.map (eraseGamma (k+1))
      (ofLex (Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) J (lowerMarkedM J) T y)).2)<_
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial _ J _ T hNS,
    Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ J _ hMask]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,WithTop.coe_lt_top _⟩)

private theorem top_le_step_core_outside_regime
    (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (s : ℕ) (w : Y)
    (hw : s≤level J T w) (hNotRegime : ¬stepRegime J s T w) :
    toLex (s,(⊤ : WithTop (ValTy (k+1))))≤stepOneCoreInv hn k J T w := by
  by_cases hSpecial : IsSpecial J T w
  · unfold stepOneCoreInv
    change _≤toLex ((ofLex (Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1))
      J (lowerMarkedM J) T w)).1,WithTop.map (eraseGamma (k+1))
      (ofLex (Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k+1)) J (lowerMarkedM J) T w)).2)
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial _ J _ T hSpecial]
    apply Prod.Lex.toLex_le_toLex.mpr
    rcases hw.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,le_rfl⟩
  · have hStrict : s<level J T w := hw.lt_of_ne (fun h=>hNotRegime ⟨h.symm,hSpecial⟩)
    apply Prod.Lex.le_iff.mpr
    exact Or.inl (by simpa only [ofLex_toLex,step_core_fst] using hStrict)

/-- ANY actual parent TEST gives strict ACTUAL core comparison over an
earlier mask with a point out of its regime, without lower-data inputs. -/
theorem actual_step_core_lt_of_earlier_mask
    (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1≤J.d)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (S : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (barMarked J) (T₀.append S)) (s : ℕ) (a : Y₀)
    (ha : level J T₀ a=s) (p : Y)
    (hp : p∈(geoTransformAlong (barMarked J) (T₀.append S)).cosupp)
    (hpW : S.proj p∈lowerMask J s T₀ a) (w : Y)
    (hw : s≤level J (T₀.append S) w) (hNotRegime : ¬stepRegime J s (T₀.append S) w) :
    stepOneCoreInv hn k J (T₀.append S) p<stepOneCoreInv hn k J (T₀.append S) w := by
  have hUpper := level_le_of_mem_lowerMask J (fun H hH=>hJ.isSNCDivisor.1 H hH) T₀ S ha hpW
  rcases hUpper.lt_or_eq with h | h
  · apply Prod.Lex.lt_iff.mpr
    exact Or.inl (by simpa only [step_core_fst] using h.trans_le hw)
  · have hReg := (stepRegime_and_le_regimeRun_of_mem_lowerMask J hJ hd hMax T₀ S hT ha hpW h).1
    have hFinite := actual_step_core_finite hn k J hJ hd hMax (T₀.append S) hT p hp hReg.2
    rw [h] at hFinite
    exact hFinite.trans_le (top_le_step_core_outside_regime hn k J (T₀.append S) s w hw hNotRegime)

private theorem last_core_centre_avoids_mask
    (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1≤J.d)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) {Y₀ Y Z : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (S : BlowupTower Y₀ Y) (C : Set Y) (π : Z→Y)
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked J) (T₀.append (.step S C π hπ)))
    (hDominates : ∀y∈(geoTransformAlong (barMarked J) (T₀.append S)).cosupp,∀c∈C,
      stepOneCoreInv hn k J (T₀.append S) y≤stepOneCoreInv hn k J (T₀.append S) c)
    (s : ℕ) (a : Y₀) (ha : level J T₀ a=s) (w : Y)
    (hw : w∈(geoTransformAlong (barMarked J) (T₀.append S)).cosupp)
    (hCount : s≤level J (T₀.append S) w) (hNotRegime : ¬stepRegime J s (T₀.append S) w) :
    Disjoint C (S.proj ⁻¹' (lowerMask J s T₀ a : Set Y₀)) := by
  apply Set.disjoint_left.mpr
  intro p hpC hpW
  have hpCos : p∈(geoTransformAlong (barMarked J) (T₀.append S)).cosupp := hT.2.2.1 hpC
  have hStrict := actual_step_core_lt_of_earlier_mask hn k J hJ hd hMax T₀ S hT.1 s a ha
    p hpCos hpW w hCount hNotRegime
  exact (not_le.mpr hStrict) (hDominates w hw p hpC)

/-- Geometric ACTUAL core maxima at EVERY inherited original prefix force
EVERY original middle centre to miss the WHOLE earlier native mask. -/
theorem actual_step_core_centres_avoid_earlier_mask
    (hn : 0<n) (k : ℕ) {b : ℕ} (J : MarkedIdeal n X) (hJ : IsInvDomain b J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (s : ℕ) (a : Y₀) (ha : level J T₀ a=s) :
    ∀ {Y Z : CMfd.{u} n} (S : BlowupTower Y₀ Y) (C : Set Y) (π : Z→Y)
      (hπ : IsBlowupAlong n C π), IsGeoTestTower (barMarked J) (T₀.append (.step S C π hπ)) →
      StageCentres (fun H D=>∀y∈(geoTransformAlong (barMarked J) H).cosupp,∀c∈D,
        stepOneCoreInv hn k J H y≤stepOneCoreInv hn k J H c) (T₀.append (.step S C π hπ)) →
      ∀w∈(geoTransformAlong (barMarked J) (T₀.append S)).cosupp,s≤level J (T₀.append S) w →
        ¬stepRegime J s (T₀.append S) w → CentresAvoid (lowerMask J s T₀ a) (.step S C π hπ)
  | _, _, .refl, C, π, hπ, hT, hCuts, w, hw, hCount, hNotRegime => by
      exact ⟨trivial,last_core_centre_avoids_mask hn k J hJ.isWellFormed hJ.one_le_d hMax
        T₀ .refl C π hπ hT hCuts.2 s a ha w hw hCount hNotRegime⟩
  | _, _, .step S₂ C₂ π₂ hπ₂, C, π, hπ, hT, hCuts, w, hw, hCount, hNotRegime => by
      have hPre : IsGeoTestTower (barMarked J) (T₀.append (.step S₂ C₂ π₂ hπ₂)) := hT.1
      obtain ⟨hw₂,hCount₂,hNotRegime₂⟩ := not_stepRegime_proj J hJ.isWellFormed hJ.one_le_d
        hn hMax hJ.dimLE (T₀.append S₂) C₂ π₂ hπ₂ hPre hw hCount hNotRegime
      refine ⟨actual_step_core_centres_avoid_earlier_mask hn k J hJ hMax T₀ s a ha
        S₂ C₂ π₂ hπ₂ hPre hCuts.1 (π₂ w) hw₂ hCount₂ hNotRegime₂,?_⟩
      exact last_core_centre_avoids_mask hn k J hJ.isWellFormed hJ.one_le_d hMax T₀
        (.step S₂ C₂ π₂ hπ₂) C π hπ hT hCuts.2 s a ha w hw hCount hNotRegime

end
end Hironaka.HironakaActualCoreHistoricalMaskAvoidance
