import Hironaka.Resolution.HironakaG1ChronologicalCompanionSuffix
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaG1LaterPositiveSuccessorRead
import Hironaka.Resolution.HironakaG1LaterPositiveBranchOrder
import Hironaka.Resolution.HironakaG1LaterMixedCentreBoundaryTrace
import Hironaka.Resolution.HironakaG8PowerLowerMarks

/-! # Live companion leaves on a common chronological chart -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1ChronologicalLeafTies

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal ResolutionInvariantSpec
  BlowupTowerIsomorphism ResolutionInvariantSegments HironakaG8LocalHistory HironakaG11InvBMClass
  InvDomainTowerAlong CanonicalCentres ResolutionDriver DivisorExponentAlong HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneRegime HironakaG8MemberLoci
  HironakaG1ChronologicalCompanionSuffix HironakaG1OriginalUnequalMarkCanonical
  HironakaG1RecursiveMemberValueTransport HironakaG1LaterPositiveSuccessorRead
  HironakaG1InitialPositiveGeneralRead HironakaG1LaterPositiveBranchOrder
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualOpenZeroSectionDifferentials
  GeneralValue NonmonomialOrderRegime NonmonomialOrderTail CompanionRebase
  HironakaG1LaterMixedCentreBoundaryTrace HironakaG8PowerLowerMarks InvDomainMemberRestriction

/-- A genuine open refinement of a selected canonical record, presented
on a specified common tower. The chosen point is identified by its literal
image in the original endpoint. -/
structure ChronologicalChart {n : ℕ} {X Y A B : CMfd.{0} n}
    {K : MarkedIdeal n X} (T : BlowupTower X Y) (y : Y)
    (S : BlowupTower A B) (z : B) where
  window : Opens X
  base : A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) window
  endpoint : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T window)
  iso : IsTowerIso base S (restrict window T) endpoint
  point : (endpoint z).val = y

def ChronologicalChart.record {n : ℕ} {X Y A B : CMfd.{0} n}
    {K : MarkedIdeal n X} {T : BlowupTower X Y} {y : Y} {S : BlowupTower A B} {z : B}
    (C : ChronologicalChart (K := K) T y S z) : MarkedIdeal n A :=
  pullback C.base (pullback (Subtype.val : C.window → X) K)

set_option maxHeartbeats 850000 in
theorem ChronologicalChart.read {n k : ℕ} (hn : 0 < n) {X Y A B : CMfd.{0} n}
    {K : MarkedIdeal n X} {T : BlowupTower X Y} {y : Y} {S : BlowupTower A B} {z : B}
    (C : ChronologicalChart (K := K) T y S z) (hK : IsInvDomain k K)
    (hCan : IsCanonical K ((invFamily hn k).inv K) T)
    (hy : y ∈ (geoTransformAlong K T).cosupp) :
    IsInvDomain k C.record ∧ IsCanonical C.record ((invFamily hn k).inv C.record) S ∧
      z ∈ (geoTransformAlong C.record S).cosupp ∧
      (invFamily hn k).inv C.record S z = (invFamily hn k).inv K T y := by
  let I := invFamily hn k
  let L := pullback (Subtype.val : C.window → X) K
  have hTest := I.isInvValue.isGeoTestTower_of_isCanonical hK T hCan
  have hEnd : (C.endpoint z).val ∈ (geoTransformAlong K T).cosupp := C.point.symm ▸ hy
  have hEnd' : C.endpoint z ∈ (geoTransformAlong L (restrict C.window T)).cosupp := by
    rw [cosupp_geoTransformAlong_restrict hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent C.window T hTest]
    exact hEnd
  have hDL := isInvDomain_pullback_val C.window hK
  have hCL := Seq.ResolutionInvariantExt.isCanonical_restrict I hK C.window T hCan
  have hDom := isInvDomain_pullback C.base hDL
  have hCan' := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso I hDL C.base C.iso hCL
  have hz : z ∈ (geoTransformAlong C.record S).cosupp := by
    change z ∈ (geoTransformAlong (pullback C.base L) S).cosupp
    rw [IsTowerIso.cosupp_geoTransformAlong C.base hDL.isWellFormed.isClosedSubmanifold_N
      hDL.isWellFormed.isCoherent C.iso (I.isInvValue.isGeoTestTower_of_isCanonical hDL _ hCL)]
    exact hEnd'
  have hValue := I.isInvValue.towerIso C.base L hDL S (restrict C.window T) C.endpoint C.iso hCL z hEnd'
  have hRest := I.isInvValue.restrictOpen K hK C.window T hCan (C.endpoint z) hEnd
  exact ⟨hDom, hCan', hz, hValue.trans (hRest.trans (congrArg (I.inv K T) C.point))⟩

set_option maxHeartbeats 900000 in
/-- Exact recursive leaf equality on a shared tested chronological
chart. The native marks agree for this literal value comparison. -/
theorem chronological_chart_recursive_tie {n k : ℕ} (hn : 0 < n)
    {X₁ Y₁ X₂ Y₂ A B : CMfd.{0} n} {K₁ : MarkedIdeal n X₁} {K₂ : MarkedIdeal n X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂} {y₁ : Y₁} {y₂ : Y₂}
    {S : BlowupTower A B} {z : B}
    (C₁ : ChronologicalChart (K := K₁) T₁ y₁ S z)
    (C₂ : ChronologicalChart (K := K₂) T₂ y₂ S z)
    (h₁ : IsInvDomain k K₁) (h₂ : IsInvDomain k K₂)
    (hCan₁ : IsCanonical K₁ ((invFamily hn k).inv K₁) T₁)
    (hCan₂ : IsCanonical K₂ ((invFamily hn k).inv K₂) T₂)
    (hy₁ : y₁ ∈ (geoTransformAlong K₁ T₁).cosupp)
    (hy₂ : y₂ ∈ (geoTransformAlong K₂ T₂).cosupp)
    (hMark : C₁.record.d = C₂.record.d)
    (hClass : LocWPEquiv C₁.record C₂.record)
    (hDim : SameCarrierDim C₁.record C₂.record)
    (hExp : ∀ D ∈ C₁.record.E, ∀ x ∈ C₁.record.cosupp, x ∈ D →
      C₂.record.d * divExpAlong n C₁.record.N C₁.record.ideal D x =
        C₁.record.d * divExpAlong n C₂.record.N C₂.record.ideal D x) :
    (invFamily hn k).inv K₁ T₁ y₁ = (invFamily hn k).inv K₂ T₂ y₂ := by
  obtain ⟨hD₁, hC₁, hz₁, hV₁⟩ := C₁.read hn h₁ hCan₁ hy₁
  obtain ⟨hD₂, hC₂, _, hV₂⟩ := C₂.read hn h₂ hCan₂ hy₂
  have hTie : (invFamily hn k).inv C₁.record S z = (invFamily hn k).inv C₂.record S z := by
    -- Compare to the same geometric reference record on the second side.
    have hRefl : LocWPEquiv C₁.record C₁.record := LocEquiv.refl Kinds.wp _
    have hDimRefl : SameCarrierDim C₁.record C₁.record := fun _ _ _ => Iff.rfl
    have hExpRefl : ∀ D ∈ C₁.record.E, ∀ x ∈ C₁.record.cosupp, x ∈ D →
        C₁.record.d * divExpAlong n C₁.record.N C₁.record.ideal D x =
        C₁.record.d * divExpAlong n C₁.record.N C₁.record.ideal D x := by intros; rfl
    have hLeft := canonicalTwoPairCuts_invFamily hn k C₁.record C₂.record C₁.record C₁.record
      hD₁ hD₂ hD₁ hD₁ hClass hDim hExp hRefl hDimRefl hExpRefl rfl hMark.symm trivial trivial trivial trivial
      S S hC₁ hC₂ hC₁ hC₁ z hz₁ z hz₁
    have hRight := canonicalTwoPairCuts_invFamily hn k C₁.record C₁.record C₁.record C₂.record
      hD₁ hD₁ hD₁ hD₂ hRefl hDimRefl hExpRefl hClass hDim hExp rfl hMark trivial trivial trivial trivial
      S S hC₁ hC₁ hC₁ hC₂ z hz₁ z hz₁
    exact le_antisymm (le_of_not_gt (fun h => (lt_irrefl _) (hLeft.mpr h)))
      (le_of_not_gt (fun h => (lt_irrefl _) (hRight.mpr h)))
  exact hV₁.symm.trans (hTie.trans hV₂)

section Positive

variable {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
  (J : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) (b : ℕ)

local notation "r" => regimeRun (stepRegime J (b+1)) T y
local notation "H" => head T r
local notation "R" => tail T r
local notation "O" => maskA J H (BlowupTower.proj R y)
local notation "K" => positiveMemberOn J H (BlowupTower.proj R y) O
local notation "G" => restrict O R
local notation "v" => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y

/-- The live finite leaf is read on the literal masked suffix selected
by the positive companion run. Its boundary is the chronological one. -/
theorem positive_companion_leaf_at_actual_selected_suffix
    (hJ : IsInvDomain (k+1) J) (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y) :
    ∃ hp : BlowupTower.proj R y ∈ O,
      let z : openPreimage R O := ⟨y, hp⟩
      IsInvDomain k K ∧ IsCanonical K ((invFamily hn k).inv K) G ∧
        z ∈ (geoTransformAlong K G).cosupp ∧
        (ofLex v).2 = ((invFamily hn k).inv K G z : WithTop (ValTy k)) := by
  obtain ⟨_, _, _, _, _, _, hp, hDom, hCanK, _, hz, hV⟩ :=
    positive_companion_chronological_suffix hn J hJ hMax T hCan y hy hLevel hNS
  exact ⟨hp, hDom, hCanK, hz, congrArg (fun a => (ofLex a).2) hV⟩

end Positive

/-- The literal companion letter and its canonical order-mask history. -/
abbrev ActualOrderMaskCompanion {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (L : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) (o : ℕ)
    (c : ℕ ×ₗ WithTop (ValTy k)) : Prop :=
    let r := regimeRun (OrdRegime L o) T y
    let H := head T r
    let S := tail T r
    let O := ordMask (geoTransformAlong L H) o
    let J := compAt L o H
    ∃ hp : S.proj y ∈ O,
      let R := restrict O S
      let z : openPreimage S O := ⟨y, hp⟩
      IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) R ∧
      z ∈ (geoTransformAlong J R).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J R z = c

set_option maxHeartbeats 850000 in
/-- A realized upper positive-order companion supplies the data needed
to read its next positive finite leaf. The comparison stays at the
companion and selected cuts of this exact witness. -/
theorem realized_companion_of_positive_order_witness {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (L : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) (o : ℕ)
    (c : ℕ ×ₗ WithTop (ValTy k))
    (h : PositiveOrderCompanionWitness (k := k) hn L T y o
      (fun v => v = positiveSuccessorRead o c)) :
    ActualOrderMaskCompanion hn L T y o c := by
  unfold ActualOrderMaskCompanion
  intro r H S O J
  obtain ⟨hp, hDom, hMax, hCan, hz, hValue⟩ := h
  have hv := congrArg (fun a : ValTy (k+1) => ofLex ((ofLex a).2)) hValue
  exact ⟨hp, hDom, hMax, hCan, hz, WithTop.coe_inj.mp (Sum.inr.inj hv)⟩

set_option maxHeartbeats 1700000 in
/-- Two live finite companion leaves tie when their actual selected
suffixes admit a common chronological open chart whose source records
have equal native marks and the same normalized local class. -/
theorem finite_companion_leaves_tie_on_chronological_chart {n k b : ℕ} (hn : 0 < n)
    {X₁ Y₁ X₂ Y₂ A B : CMfd.{0} n}
    (J₁ : MarkedIdeal n X₁) (J₂ : MarkedIdeal n X₂)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂) (y₁ : Y₁) (y₂ : Y₂)
    (hJ₁ : IsInvDomain (k+1) J₁) (hJ₂ : IsInvDomain (k+1) J₂)
    (hMax₁ : IsMaximalOrderAlong J₁.N J₁.ideal J₁.d)
    (hMax₂ : IsMaximalOrderAlong J₂.N J₂.ideal J₂.d)
    (hCan₁ : IsCanonical J₁ (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J₁) T₁)
    (hCan₂ : IsCanonical J₂ (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J₂) T₂)
    (hy₁ : y₁ ∈ (geoTransformAlong J₁ T₁).cosupp)
    (hy₂ : y₂ ∈ (geoTransformAlong J₂ T₂).cosupp)
    (hLevel₁ : level J₁ T₁ y₁ = b+1) (hLevel₂ : level J₂ T₂ y₂ = b+1)
    (hNativeMark : J₁.d = J₂.d)
    (hNS₁ : ¬ IsSpecial J₁ T₁ y₁) (hNS₂ : ¬ IsSpecial J₂ T₂ y₂)
    (S : BlowupTower A B) (z : B)
    (hChart :
      let r₁ := regimeRun (stepRegime J₁ (b+1)) T₁ y₁
      let r₂ := regimeRun (stepRegime J₂ (b+1)) T₂ y₂
      let R₁ := tail T₁ r₁
      let R₂ := tail T₂ r₂
      let O₁ := maskA J₁ (head T₁ r₁) (R₁.proj y₁)
      let O₂ := maskA J₂ (head T₂ r₂) (R₂.proj y₂)
      let K₁ := positiveMemberOn J₁ (head T₁ r₁) (R₁.proj y₁) O₁
      let K₂ := positiveMemberOn J₂ (head T₂ r₂) (R₂.proj y₂) O₂
      ∀ (hp₁ : R₁.proj y₁ ∈ O₁) (hp₂ : R₂.proj y₂ ∈ O₂),
        ∃ (C₁ : ChronologicalChart (K := K₁) (restrict O₁ R₁) ⟨y₁,hp₁⟩ S z)
          (C₂ : ChronologicalChart (K := K₂) (restrict O₂ R₂) ⟨y₂,hp₂⟩ S z),
          LocWPEquiv C₁.record C₂.record ∧
          SameCarrierDim C₁.record C₂.record ∧
          ∀ D ∈ C₁.record.E, ∀ x ∈ C₁.record.cosupp, x ∈ D →
            C₂.record.d * divExpAlong n C₁.record.N C₁.record.ideal D x =
              C₁.record.d * divExpAlong n C₂.record.N C₂.record.ideal D x) :
    (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J₁ T₁ y₁)).2 =
      (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J₂ T₂ y₂)).2 := by
  obtain ⟨hp₁, hD₁, hC₁, hz₁, hV₁⟩ := positive_companion_leaf_at_actual_selected_suffix
    hn J₁ T₁ y₁ b hJ₁ hMax₁ hCan₁ hy₁ hLevel₁ hNS₁
  obtain ⟨hp₂, hD₂, hC₂, hz₂, hV₂⟩ := positive_companion_leaf_at_actual_selected_suffix
    hn J₂ T₂ y₂ b hJ₂ hMax₂ hCan₂ hy₂ hLevel₂ hNS₂
  obtain ⟨C₁,C₂,hLoc,hDim,hExp⟩ := hChart hp₁ hp₂
  have hd : C₁.record.d = C₂.record.d := by
    change (lowerMarkedM J₁ (b+1) (head T₁ (regimeRun (stepRegime J₁ (b+1)) T₁ y₁))
      ((tail T₁ (regimeRun (stepRegime J₁ (b+1)) T₁ y₁)).proj y₁)).d =
      (lowerMarkedM J₂ (b+1) (head T₂ (regimeRun (stepRegime J₂ (b+1)) T₂ y₂))
      ((tail T₂ (regimeRun (stepRegime J₂ (b+1)) T₂ y₂)).proj y₂)).d
    rw [lowerMarkedM_succ_mark, lowerMarkedM_succ_mark, hNativeMark]
  have hTie := chronological_chart_recursive_tie hn C₁ C₂ hD₁ hD₂ hC₁ hC₂ hz₁ hz₂ hd hLoc hDim hExp
  exact hV₁.trans ((congrArg (fun a : ValTy k => (a : WithTop (ValTy k))) hTie).trans hV₂.symm)

/-- At the literal true-mark order the actual companion mark is that
same mark. In particular it is independent of the selected order head. -/
theorem compAt_d_eq_of_true_mark {n : ℕ} {A B : CMfd.{0} n}
    (L : MarkedIdeal n A) (H : BlowupTower A B) (o : ℕ) (ho : o = L.d) :
    (compAt L o H).d = o := by
  rw [compAt, companionOf, companionAlong_d]
  change (if o < (geoTransformAlong L H).d then
    o * ((geoTransformAlong L H).d - o) else o) = o
  rw [d_geoTransformAlong, ← ho, if_neg (lt_irrefl o)]

set_option maxHeartbeats 900000 in
/-- The companion of a later positive read is the literal Step One
letter on the actual order mask of its selected lower suffix. -/
theorem laterPositiveRead_companion_on_actual_order_mask {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
    {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (y : Y) (F : LaterPositiveRead Q T y k s) :
    let r := regimeRun (stepRegime (properNormalMarked Q) (s+1)) T y
    let H := head T r
    let R := tail T r
    let p := R.proj y
    let O := maskA (properNormalMarked Q) H p
    let A := CMfd.of (n := n+1) O
    let B := CMfd.of (n := n+1) (openPreimage R O)
    let L : MarkedIdeal (n+1) A := lowerMarkedM
      (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q) (s+1) H p
    let V : BlowupTower A B := restrict O R
    ∃ hp : p ∈ O, ActualOrderMaskCompanion (Nat.succ_pos n) L V
      (⟨y,hp⟩ : openPreimage R O) F.order F.companion := by
  intro r H R p O A B L V
  obtain ⟨hp, _, _, hRealized⟩ := F.realized
  exact ⟨hp, realized_companion_of_positive_order_witness (Nat.succ_pos n) L V
    ⟨y,hp⟩ F.order F.companion hRealized⟩

set_option maxHeartbeats 1400000 in
/-- Every actual later positive companion of one canonical proper-normal
prefix has the same literal mark determined by the original record. -/
theorem laterPositiveRead_actual_companion_mark {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
    {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hQ : IsInvDomain (k+1) Q)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k+1))
        (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s+1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y)
    (F : LaterPositiveRead Q T y k s) :
    let X₀ := CMfd.of (n := n+1) (productOpen U)
    let P : MarkedIdeal (n+1) X₀ := properNormalMarked Q
    let r := regimeRun (stepRegime P (s+1)) T y
    let H := head T r
    let R := tail T r
    let p := R.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n+1) O
    let B := CMfd.of (n := n+1) (openPreimage R O)
    let L : MarkedIdeal (n+1) A := lowerMarkedM (X := X₀) P (s+1) H p
    let V : BlowupTower A B := restrict O R
    ∀ hp : p ∈ O,
      let z : openPreimage R O := ⟨y, hp⟩
      let j := regimeRun (OrdRegime L F.order) V z
      (compAt L F.order (head V j)).d = (coeffMarkedAlong (barMarked P)).d := by
  intro X₀ P r H R p O A B L V hp z j
  have hFixed := laterPositiveRead_order_eq_fixed_mark Q T hQ hCan y hy hLevel hNS F
  have hMark : F.order = L.d := by
    change F.order = (lowerMarkedM (X := X₀) P (s+1) H p).d
    rw [lowerMarkedM_succ_mark, hFixed, coeffMarkedAlong_mark]
    rfl
  exact (compAt_d_eq_of_true_mark L (head V j) F.order hMark).trans hFixed

end
end Hironaka.HironakaG1ChronologicalLeafTies
