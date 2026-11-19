import Hironaka.Resolution.HironakaG1LiteralRatioPointProfiles
import Hironaka.Resolution.HironakaG1NativeOrderDispatcher
import Hironaka.Resolution.HironakaG1NormalValueMaps

/-! # Exact recursive comparison between two supported lifts of one marked history -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace

namespace Hironaka.HironakaG1PairedLiftCompanionValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong NormalCrossings SubmanifoldChartedSpace GeneralValue StepOneRegime HironakaHolomorphicJetChartInvariance
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime CompanionRebase
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualSectionBoundaryDimension HironakaOriginalFamilyDepthStability
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaG1NormalValueMaps
  HironakaG1LiteralRatioPointProfiles HironakaG1NativeOrderDispatcher
  HironakaG1InitialPositiveGeneralRead HironakaG1LaterPositiveSuccessorRead
  HironakaG8LocalHistory

private theorem positive_read_injective {q : ℕ} (o : ℕ) :
    Function.Injective (positiveSuccessorRead (k := q) o) := by
  intro a b h
  exact WithTop.coe_inj.mp (Sum.inr.inj (congrArg (fun v : ValTy (q+1) => ofLex ((ofLex v).2)) h))

variable {d k₁ k₂ q : ℕ} {X Y : CMfd.{0} d}
  {hk₁ : k₁ ≤ d} {hk₂ : k₂ ≤ d}
  {W₁ W₂ : Set X} {hwc₁ : IsClosed W₁} {hwc₂ : IsClosed W₂}
  {hw₁ : ∀ x ∈ W₁, RegularAtDim (n := d) W₁ x k₁}
  {hw₂ : ∀ x ∈ W₂, RegularAtDim (n := d) W₂ x k₂}
  {V₁ V₂ : Set Y} {hvc₁ : IsClosed V₁} {hvc₂ : IsClosed V₂}
  {hv₁ : ∀ y ∈ V₁, RegularAtDim (n := d) V₁ y k₁}
  {hv₂ : ∀ y ∈ V₂, RegularAtDim (n := d) V₂ y k₂}
  {T : BlowupTower X Y}
  {B₁ : BlowupTower (nativeManifold hk₁ W₁ hw₁) (nativeManifold hk₁ V₁ hv₁)}
  {B₂ : BlowupTower (nativeManifold hk₂ W₂ hw₂) (nativeManifold hk₂ V₂ hv₂)}
  {P Q : MarkedIdeal d X}

set_option maxHeartbeats 1700000 in
/-- Exact supported recoding is cancellable between two actual lifts.
The ambient comparison can come from literal identity or a separate
marked-class theorem. The compared native values are the original ones. -/
theorem paired_lift_value_of_ambient_value
    (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hk : k₁ ≤ k₂)
    (hPD : IsInvDomain q P) (hQD : IsInvDomain q Q)
    (hP : P.N ⊆ W₁) (hQ : Q.N ⊆ W₂)
    (hTr₁ : IsTransverse d W₁ P.E) (hTr₂ : IsTransverse d W₂ Q.E)
    (L₁ : Lift hk₁ W₁ hwc₁ hw₁ P.E T V₁ hvc₁ hv₁ B₁)
    (L₂ : Lift hk₂ W₂ hwc₂ hw₂ Q.E T V₂ hvc₂ hv₂ B₂)
    (hCan₁ : IsCanonical P ((invFamily (h₁.trans_le hk₁) q).inv P) T)
    (hCan₂ : IsCanonical Q ((invFamily (h₁.trans_le hk₁) q).inv Q) T)
    (x : nativeManifold hk₁ V₁ hv₁) (y : nativeManifold hk₂ V₂ hv₂)
    (hx : x.val ∈ (geoTransformAlong P T).cosupp)
    (hy : y.val ∈ (geoTransformAlong Q T).cosupp)
    (hValue : (invFamily (h₁.trans_le hk₁) q).inv P T x.val =
      (invFamily (h₁.trans_le hk₁) q).inv Q T y.val) :
    (invFamily h₂ q).inv (nativePullback hk₂ W₂ hw₂ Q) B₂ y =
      sameIndexMap (k₂-k₁) q ((invFamily h₁ q).inv (nativePullback hk₁ W₁ hw₁ P) B₁ x) := by
  let hd := h₁.trans_le hk₁
  have hV₁ := (Lift.original_same_bound_values hd h₁ P hPD hP hTr₁ L₁ hCan₁).2 x hx
  have hV₂ := (Lift.original_same_bound_values hd h₂ Q hQD hQ hTr₂ L₂ hCan₂).2 y hy
  apply (strictMono_sameIndexMap (d-k₂) q).injective
  rw [sameIndexMap_add, show (k₂-k₁)+(d-k₂) = d-k₁ by omega]
  exact hV₂.symm.trans (hValue.symm.trans hV₁)

set_option maxHeartbeats 2300000 in
/-- A single marked canonical history on two supported native carriers
has the same reduced endpoint profile and the exact relative dimension
recoding of both actual positive companions. Both companions have the
same original order clock and true mark. -/
theorem paired_same_record_positive_companions
    (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hk : k₁ ≤ k₂)
    (hPD : IsInvDomain (q+1) P)
    (hP : P.N ⊆ W₁) (hQ : P.N ⊆ W₂)
    (hTr₁ : IsTransverse d W₁ P.E) (hTr₂ : IsTransverse d W₂ P.E)
    (L₁ : Lift hk₁ W₁ hwc₁ hw₁ P.E T V₁ hvc₁ hv₁ B₁)
    (L₂ : Lift hk₂ W₂ hwc₂ hw₂ P.E T V₂ hvc₂ hv₂ B₂)
    (hCan : IsCanonical P ((invFamily (h₁.trans_le hk₁) (q+1)).inv P) T)
    (x : nativeManifold hk₁ V₁ hv₁) (y : nativeManifold hk₂ V₂ hv₂)
    (hx : x.val ∈ (geoTransformAlong P T).cosupp) (hxy : x.val = y.val)
    (ho : 0 < nmOrd (geoTransformAlong P T) x.val) :
    let M := nativePullback hk₁ W₁ hw₁ P
    let N := nativePullback hk₂ W₂ hw₂ P
    let C := (geoTransformAlong M B₁).cosupp
    let D := (geoTransformAlong N B₂).cosupp
    let o := nmOrd (geoTransformAlong P T) x.val
    let r := regimeRun (OrdRegime M o) B₁ x
    let s := regimeRun (OrdRegime N o) B₂ y
    y ∈ D ∧
    (fun l => hilbertSamuelAt (vanishingIdeal (n := k₁) C) x l) =
      (fun l => hilbertSamuelAt (vanishingIdeal (n := k₂) D) y l) ∧
    r = s ∧ (compAt M o (head B₁ r)).d = (compAt N o (head B₂ s)).d ∧
    ∃ a b : ℕ ×ₗ WithTop (ValTy q),
      PositiveOrderCompanionWitness (k := q) h₁ M B₁ x o (fun v => v = positiveSuccessorRead o a) ∧
      PositiveOrderCompanionWitness (k := q) h₂ N B₂ y o (fun v => v = positiveSuccessorRead o b) ∧
      b = stepDimensionMap (sameIndexMap (k₂-k₁) q) a := by
  intro M N C D o r s
  let hd := h₁.trans_le hk₁
  have hy : y.val ∈ (geoTransformAlong P T).cosupp := hxy ▸ hx
  have hA := actual_native_order_dispatch hd h₁ L₁ hPD hP hTr₁ hCan x hx
  have hB := actual_native_order_dispatch hd h₂ L₂ hPD hQ hTr₂ hCan y hy
  obtain ⟨_,_,_,hx₁,_,_,hBranch₁⟩ := hA
  obtain ⟨_,_,_,_,_,_,hBranch₂⟩ := hB
  have hOrdY : nmOrd (geoTransformAlong P T) y.val = o :=
    congrArg (nmOrd (geoTransformAlong P T)) hxy.symm
  rw [if_neg (Nat.ne_of_gt ho)] at hBranch₁
  rw [if_neg (Nat.ne_of_gt (hOrdY.symm ▸ ho)), hOrdY] at hBranch₂
  obtain ⟨hRun₁,_,a,_,ha,_,hA,_,_,_⟩ := hBranch₁
  obtain ⟨hRun₂,_,b,_,hb,_,hB,_,_,_⟩ := hBranch₂
  have hT := (invFamily hd (q+1)).isInvValue.isGeoTestTower_of_isCanonical hPD T hCan
  have hProfiles := paired_lift_endpoint_profiles hd hk₁ hk₂ P P hPD hPD hP hQ hTr₁ hTr₂
    L₁ L₂ (LocEquiv.refl Kinds.wp P) hT x y hx₁ hxy
  have hMarks : (compAt M o (head B₁ r)).d = (compAt N o (head B₂ s)).d := by
    simp only [compAt, companionOf, companionAlong_d, MarkedIdealBiholomorphism.MarkedIdeal.pullback, d_geoTransformAlong]
    rfl
  have hClock := hRun₁.symm.trans
    ((congrArg (regimeRun (OrdRegime P o) T) hxy).trans hRun₂)
  have hNative := paired_lift_value_of_ambient_value h₁ h₂ hk hPD hPD hP hQ hTr₁ hTr₂
    L₁ L₂ hCan hCan x y hx hy
      (congrArg ((invFamily hd (q+1)).inv P T) hxy)
  have hLeaf : b = stepDimensionMap (sameIndexMap (k₂-k₁) q) a := by
    apply positive_read_injective o
    exact hb.symm.trans (hNative.trans (congrArg (sameIndexMap (k₂-k₁) (q+1)) ha))
  exact ⟨hProfiles.1,hProfiles.2,hClock,hMarks,a,b,hA,hB,hLeaf⟩

end
end Hironaka.HironakaG1PairedLiftCompanionValues
