import Hironaka.Resolution.HironakaG1InitialPositiveFiniteCentres
import Hironaka.Resolution.HironakaG1InitialPositiveNestedRead
import Hironaka.Resolution.HironakaG1InitialCompanionSpecial

/-!
# Maxima on a mixed initial positive stratum

The literal companion has level zero at an initial positive cut. It
distinguishes the two native branches under the same padded outer level.
-/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialPositiveMixedStratum

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue StepOneRegime
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualOpenZeroSectionDifferentials
  HironakaG1InitialPositiveFiniteCentres HironakaG1InitialPositiveGeneralRead
  HironakaG1InitialPositiveNestedRead HironakaG1InitialCompanionSpecial
  HironakaG1NormalNestedOrderMap HironakaG1ProperCarrierNormalLocalClass
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionInitialBar
  HironakaG8HomStable HomogenizedIdealAlong StepOneValueMasked

section InitialMixed

variable {n q s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  (hQ : IsInvDomain (q + 1) Q)

local notation "X₀" => CMfd.of (n := n + 1) (productOpen U)
local notation "T₀" => BlowupTower.refl (X := X₀)
local notation "P" => properNormalMarked Q
local notation "R" => invFamily (Nat.succ_pos n) q

private theorem stepOne_le_zero_top_and_lt_iff {d q : ℕ} {A B : CMfd.{0} d}
    (hd : 0 < d) (J : MarkedIdeal d A) (hJ : IsInvDomain (q + 1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (K : BlowupTower A B)
    (hK : IsGeoTestTower J K) (x : B) (hx : x ∈ (geoTransformAlong J K).cosupp)
    (hZero : level J K x = 0) :
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily hd q) J K
    let top : ℕ ×ₗ WithTop (ValTy q) := toLex (0, (⊤ : WithTop (ValTy q)))
    f x ≤ top ∧ (f x < top ↔ ¬ IsSpecial J K x) := by
  intro f top
  have hFirst : (ofLex (f x)).1 = 0 :=
    (Seq.StepOneValueMasked.stepOneInvL_fst (invFamily hd q) J (lowerMarkedM J) K x).trans hZero
  have hLe : f x ≤ top := Prod.Lex.le_iff.mpr (Or.inr ⟨hFirst, le_top⟩)
  refine ⟨hLe, ?_⟩
  by_cases hS : IsSpecial J K x
  · have hTop : f x = top :=
      (Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (invFamily hd q) J (lowerMarkedM J) K hS).trans
        (congrArg (fun j => toLex (j, (⊤ : WithTop (ValTy q)))) hZero)
    exact iff_of_false (fun h => (lt_irrefl top) (hTop ▸ h)) (fun h => h hS)
  · have hEq := bar_local_any_boundary (X := A) J hJ
    have hKBar := ((hEq.wEquiv.2 K).1).mp hK
    have hxBar : x ∈ (geoTransformAlong (barMarked J) K).cosupp := ((hEq.wEquiv.2 K).2 hK).symm ▸ hx
    have hFinite := Seq.StepOneValueMasked.lowerValueL_ne_top J (invFamily hd q)
      hJ.isWellFormed hJ.one_le_d hd hMax (lowerMarkedM J) K hKBar hxBar hS
    refine iff_of_true ?_ hS
    change Seq.StepOneValueMasked.stepOneInvL (invFamily hd q) J (lowerMarkedM J) K x < _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial _ J _ K hS]
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hZero, lt_top_iff_ne_top.mpr hFinite⟩)

include hQ in
set_option maxHeartbeats 600000 in
private theorem initial_companion_le_zero_top_and_lt_iff {y : productOpen U}
    (F : InitialFiniteRead Q T₀ y q s) (hy : y ∈ (properNormalMarked Q).cosupp) :
    F.value ≤ toLex (0, (⊤ : WithTop (ValTy q))) ∧
      (F.value < toLex (0, (⊤ : WithTop (ValTy q))) ↔ ¬ IsSpecial (sectionMarked Q) T₀ y) := by
  let O := initialMask Q T₀ y
  let W := initialCompanionMask Q T₀ y s
  let A := CMfd.of (n := n + 1) W
  let J := initialCompanion Q T₀ y s
  let K := BlowupTower.refl (X := A)
  let x : W := F.point
  have hx : (x.val : O).val = y := rfl
  have hLevel : level P T₀ y = s + 1 := F.initial_level
  obtain ⟨hZero, hSp⟩ := initial_positive_companion_special_iff Q hQ y hy hLevel x hx
  have hx0 : level J K x = 0 := hZero
  have hComp := stepOne_le_zero_top_and_lt_iff (Nat.succ_pos n) J F.domain F.maximal K trivial x F.cosupp hx0
  exact ⟨hComp.1, hComp.2.trans (not_congr hSp)⟩

include hQ in
set_option maxHeartbeats 900000 in
/-- At the initial stage, within one positive level, a realized finite
padded anchor lies strictly below a section-special padded-nonspecial
anchor exactly when its own section is nonspecial. The comparison uses
the original zero-level companion, with no comparison of unequal marks. -/
theorem initial_finite_le_section_special_and_lt_iff
    (hn : 0 < n) {V : Set (productOpen U)} {hVc : IsClosed V}
    {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
    {N : BlowupTower (nativeManifold (Y := X₀) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Y := X₀) (Nat.le_succ n) V hV)}
    {hWc : IsClosed (zeroPlane U)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
      (sectionMarked Q).E T₀ V hVc hV N)
    (z : nativeManifold (Y := X₀) (Nat.le_succ n) V hV)
    (hz : z.val ∈ (properNormalMarked Q).cosupp) (hzLevel : level P T₀ z.val = s + 1)
    (hzNS : ¬ IsSpecial P T₀ z.val) (hzSpecial : IsSpecial (sectionMarked Q) T₀ z.val)
    {y : productOpen U} (F : InitialFiniteRead Q T₀ y q s) (hy : y ∈ (properNormalMarked Q).cosupp) :
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (q + 1)) P T₀
    f y ≤ f z.val ∧ (f y < f z.val ↔ ¬ IsSpecial (sectionMarked Q) T₀ y) := by
  intro f
  let o := (coeffMarkedAlong (barMarked (X := X₀) P)).d
  let top : ℕ ×ₗ WithTop (ValTy q) := toLex (0, (⊤ : WithTop (ValTy q)))
  let j (v : ℕ ×ₗ WithTop (ValTy q)) : ℕ ×ₗ WithTop (ValTy (q + 1)) :=
    toLex (s + 1, (positiveSuccessorRead o v : WithTop (ValTy (q + 1))))
  obtain ⟨hNative, hRaw⟩ := original_initial_positive_special_nested_read hn Q hQ hLift z
    hz hzLevel hzNS hzSpecial id
  rw [hNative] at hRaw
  have hzRead : f z.val = j top := hRaw
  have hyRead : f y = j F.value := F.upper_eq
  have hStrict : StrictMono j := by
    intro u v h
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, WithTop.coe_lt_coe.mpr
      (Prod.Lex.toLex_lt_toLex.mpr (Or.inr
        ⟨rfl, Sum.Lex.inr_lt_inr_iff.mpr (WithTop.coe_lt_coe.mpr h)⟩))⟩)
  rw [hyRead, hzRead, hStrict.le_iff_le, hStrict.lt_iff_lt]
  exact initial_companion_le_zero_top_and_lt_iff Q hQ F hy

include hQ in
set_option maxHeartbeats 800000 in
/-- On a same-level initial stratum of padded-nonspecial cosupport points
containing a section-special point, the original padded maxima are exactly
the section-special points of that stratum. The selected point is supplied on
the literal native lift. -/
theorem initial_mixed_stratum_max_locus
    (hn : 0 < n) {V : Set (productOpen U)} {hVc : IsClosed V}
    {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
    {N : BlowupTower (nativeManifold (Y := X₀) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Y := X₀) (Nat.le_succ n) V hV)}
    {hWc : IsClosed (zeroPlane U)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
      (sectionMarked Q).E T₀ V hVc hV N)
    (z : nativeManifold (Y := X₀) (Nat.le_succ n) V hV)
    (S : Set (productOpen U)) (hz : z.val ∈ S)
    (hAnchor : ∀ y ∈ S, y ∈ (properNormalMarked Q).cosupp ∧ level P T₀ y = s + 1 ∧
      ¬ IsSpecial P T₀ y)
    (hzSpecial : IsSpecial (sectionMarked Q) T₀ z.val) :
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (q + 1)) P T₀
    maxLocus f S = S ∩ {y | IsSpecial (sectionMarked Q) T₀ y} := by
  intro f
  have hCompare (y : productOpen U) (hy : y ∈ S) :
      f y ≤ f z.val ∧ (f y < f z.val ↔ ¬ IsSpecial (sectionMarked Q) T₀ y) := by
    obtain ⟨hyCos, hyLevel, hyNS⟩ := hAnchor y hy
    obtain ⟨hzCos, hzLevel, hzNS⟩ := hAnchor z.val hz
    obtain ⟨F⟩ := exists_initialFiniteRead Q T₀ y hQ trivial hyCos hyLevel hyNS rfl
    exact initial_finite_le_section_special_and_lt_iff Q hQ hn hLift z
      hzCos hzLevel hzNS hzSpecial F hyCos
  ext y
  constructor
  · rintro ⟨hy, hMax⟩
    refine ⟨hy, ?_⟩
    by_contra hyNS
    exact (not_lt_of_ge (hMax z.val hz)) ((hCompare y hy).2.mpr hyNS)
  · rintro ⟨hy, hySpecial⟩
    have hBack : f z.val ≤ f y := le_of_not_gt fun h =>
      (hCompare y hy).2.mp h hySpecial
    exact ⟨hy, fun x hx => ((hCompare x hx).1).trans hBack⟩

end InitialMixed


end

end Hironaka.HironakaG1InitialPositiveMixedStratum
