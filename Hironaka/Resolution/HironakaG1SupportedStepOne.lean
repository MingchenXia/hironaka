import Hironaka.Resolution.HironakaG1NormalCentreTransport

/-! # Original Step One values on an actual supported native history -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1SupportedStepOne

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver
  CanonicalCentres NormalCrossings HomogenizedIdealAlong
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeRecursiveValues
  HironakaActualSectionBoundaryDimension HironakaOriginalFamilyDepthStability
  HironakaG1NormalCentreTransport HironakaSmoothSubmersionCanonicalValueDimensionShift

variable {n k q : ℕ} {X : CMfd.{0} n} {hk : k ≤ n}
  {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀ y ∈ V, RegularAtDim (n := n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

set_option maxHeartbeats 800000 in
/-- At a common recursive bound, a supported maximal-order history and its
actual native lift have the same original Step One values up to the
dimension shift. The native history is canonical on the same steps. -/
theorem Lift.original_same_bound_step_one_values
    (hn : 0 < n) (hkpos : 0 < k) (M : MarkedIdeal n X) (hM : IsInvDomain (q + 1) M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M) T) :
    let B := nativePullback hk W hW M
    IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B) Q ∧
      ∀ z : nativeManifold hk V hV, z.val ∈ (geoTransformAlong M T).cosupp →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M T z.val =
          stepDimensionMap (sameIndexMap (n - k) q)
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B Q z) := by
  let B := nativePullback hk W hW M
  let d := n - k
  have hDepth := original_step_one_depth_stability hn d q M hM hmax T
  obtain ⟨hNative, hOffset⟩ := Lift.original_step_one_offset_values
    hn hkpos M hM hMN hTrans hmax h (hDepth.1.mpr hCan)
  refine ⟨hNative, fun z hz => ?_⟩
  have hMap : familyDimensionMap d q = depthPadMap d q ∘ sameIndexMap d q :=
    funext fun v => (depthPadMap_sameIndexMap d q v).symm
  apply (strictMono_stepDimensionMap (strictMono_depthPadMap d q)).injective
  calc
    _ = Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d + q)) M T z.val :=
      (hDepth.2 hCan z.val hz).symm
    _ = stepDimensionMap (familyDimensionMap d q)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B Q z) := hOffset z hz
    _ = _ := by
      simp only [hMap, stepDimensionMap, ofLex_toLex, WithTop.map_map]
      rfl

set_option maxHeartbeats 700000 in
/-- The original Step One maxima of a supported record and its actual
native section are exact images and preimages at the common bound. -/
theorem Lift.original_same_bound_step_one_max_loci
    (hn : 0 < n) (hkpos : 0 < k) (M : MarkedIdeal n X) (hM : IsInvDomain (q + 1) M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M) T) :
    let B := nativePullback hk W hW M
    let i : nativeManifold hk V hV → Y := Subtype.val
    let C := maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M T)
      (geoTransformAlong M T).cosupp
    let D := maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B Q)
      (geoTransformAlong B Q).cosupp
    D = i ⁻¹' C ∧ i '' D = C :=
  Lift.max_loci_of_value_comparison hn M hM.isWellFormed hMN hTrans h _ _
    (stepDimensionMap (sameIndexMap (n - k) q))
    (strictMono_stepDimensionMap (strictMono_sameIndexMap (n - k) q))
    (Lift.original_same_bound_step_one_values hn hkpos M hM hMN hTrans hmax h hCan).2

set_option maxHeartbeats 900000 in
/-- The supported and native original Step One histories are canonical
simultaneously at the common recursive bound. -/
theorem Lift.original_same_bound_step_one_canonical_iff
    (hn : 0 < n) (hkpos : 0 < k) (M : MarkedIdeal n X) (hM : IsInvDomain (q + 1) M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (h : Lift hk W hWc hW M.E T V hVc hV Q) :
    IsCanonical (nativePullback hk W hW M)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) (nativePullback hk W hW M)) Q ↔
      IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M) T := by
  refine ⟨?_, fun hCan => (Lift.original_same_bound_step_one_values
    hn hkpos M hM hMN hTrans hmax h hCan).1⟩
  induction h with
  | refl => intro _; trivial
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    rintro ⟨hPrefix, hCentre | hCentre⟩
    · exact ⟨ih hPrefix, Or.inl (by rw [hCentre, image_empty])⟩
    · have hCan := ih hPrefix
      have hImage := (Lift.original_same_bound_step_one_max_loci
        hn hkpos M hM hMN hTrans hmax h hCan).2
      exact ⟨hCan, Or.inr (hCentre ▸ hImage)⟩

set_option maxHeartbeats 900000 in
/-- One tight supported Step One record permits arbitrary additional
ambient recursion depth. Both sides use their own original histories and
all three Step One branches. -/
theorem Lift.original_step_one_with_depth
    (hn : 0 < n) (hkpos : 0 < k) (a : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (q + 1) M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (h : Lift hk W hWc hW M.E T V hVc hV Q) :
    let B := nativePullback hk W hW M
    let f : ∀ {Z : CMfd.{0} n}, BlowupTower X Z → Z → ℕ ×ₗ WithTop (ValTy (a + q)) :=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (a + q)) M
    let g : ∀ {Z : CMfd.{0} k}, BlowupTower (nativeManifold hk W hW) Z → Z → ℕ ×ₗ WithTop (ValTy q) :=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B
    (IsCanonical B g Q ↔ IsCanonical M f T) ∧
      (IsCanonical M f T → ∀ z : nativeManifold hk V hV, z.val ∈ (geoTransformAlong M T).cosupp →
        f T z.val = stepDimensionMap (depthPadMap a q ∘ sameIndexMap (n - k) q) (g Q z)) := by
  have hDepth := original_step_one_depth_stability hn a q M hM hmax T
  refine ⟨(Lift.original_same_bound_step_one_canonical_iff
    hn hkpos M hM hMN hTrans hmax h).trans hDepth.1.symm, fun hCan z hz => ?_⟩
  have hTight := hDepth.1.mp hCan
  let B := nativePullback hk W hW M
  calc
    _ = stepDimensionMap (depthPadMap a q)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M T z.val) := hDepth.2 hTight z.val hz
    _ = stepDimensionMap (depthPadMap a q) (stepDimensionMap (sameIndexMap (n - k) q)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B Q z)) :=
      congrArg (stepDimensionMap (depthPadMap a q))
        ((Lift.original_same_bound_step_one_values hn hkpos M hM hMN hTrans hmax h hTight).2 z hz)
    _ = _ := by
      simp only [stepDimensionMap, ofLex_toLex, WithTop.map_map]
      rfl

end
end Hironaka.HironakaG1SupportedStepOne
