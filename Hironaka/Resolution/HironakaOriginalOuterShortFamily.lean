/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalShortUniformIndex
/-! Whole actual original family short-order histories.
Complete four-node Mathematics.tex preceded proofs. Crossing recursive
values and full mixed spectra/global scheduling remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalOuterShortFamily
noncomputable section
open Classical
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  MonomialInvariantEmptyMember MarkedIdealBiholomorphism NonmonomialOrderLocal
  NonmonomialOrderRegime NonmonomialOrderTail StepOneRegime GeneralValue
  CompanionRebase CompanionReductionAlong HomogenizedIdealAlong
  HironakaOriginalInteriorEmptyHistory HironakaOriginalGeneralCrossingHistory
  HironakaOriginalInvariantEmptyInsertion HironakaOriginalPositiveCompanionEmptyInsertion
  HironakaOriginalStepOneEmptyInsertion HironakaOriginalCrossingValueTransport
  StepOneValue StepOneValueMasked HironakaOriginalPositiveMemberEmptyInsertion
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- BOTH true whole original outer-short split records, with actual same tail. -/
theorem actual_general_short_splits (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y)
    (o : ℕ) (y : Y) (hs : regimeRun (OrdRegime M o) (H.append S) y<S.length) :
    let r := regimeRun (OrdRegime M o) (H.append S) y
    let r' := regimeRun (OrdRegime M o) (interiorEmptyHistory H S) y
    r'=r ∧ split (H.append S) r=⟨(split S r).1,H.append (head S r),tail S r⟩ ∧
      split (interiorEmptyHistory H S) r'=⟨(split S r).1,interiorEmptyHistory H (head S r),tail S r⟩ := by
  dsimp only
  have hr : regimeRun (OrdRegime M o) (interiorEmptyHistory H S) y=
      regimeRun (OrdRegime M o) (H.append S) y := by
    rw [ordRegime_run_dictionary M hM H hH o S y,if_pos hs]
  refine ⟨hr,StepOneEmptyPrefix.split_append_of_le H S _ hs.le,?_⟩
  rw [hr]
  exact StepOneEmptyPrefix.split_append_of_le
    (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S _ hs.le

private theorem companion_pullback_boundary_heq {D : CMfd.{u} n}
    (J J' : MarkedIdeal n D) (j : ℕ) (hj : j≤J.E.length)
    (hJ' : J'=insertEmpty j J) (o : ℕ)
    (U V : Opens D) (hUV : U=V) :
    HEq (companionOf n (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → D) J') o)
      (insertEmpty j (companionOf n (MarkedIdeal.pullback (M' := CMfd.of (n := n) V) (Subtype.val : V → D) J) o)) := by
  subst V
  subst J'
  apply heq_of_eq
  have hp : MarkedIdeal.pullback (M' := CMfd.of (n := n) U)
      (Subtype.val : U → D) (insertEmpty j J)=
      insertEmpty j (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → D) J) := by
    change MarkedIdeal.mk _ ((J.E.insertIdx j ∅).map ((Subtype.val : U → D) ⁻¹' ·)) _ _ =
      MarkedIdeal.mk _ ((J.E.map ((Subtype.val : U → D) ⁻¹' ·)).insertIdx j ∅) _ _
    rw [List.map_insertIdx,Set.preimage_empty]
    rfl
  rw [hp]
  exact companionOf_insertEmpty _ (by
    change j≤(J.E.map ((Subtype.val : U → D) ⁻¹' ·)).length
    rwa [List.length_map]) o

private theorem companion_boundary_length {D : CMfd.{u} n}
    (M : MarkedIdeal n X) (o : ℕ) (K : BlowupTower X D) :
    (compAt M o K).E.length=(geoTransformAlong M K).E.length := by
  unfold compAt companionOf companionAlong
  split_ifs <;> simp only [MarkedIdealOperationsTransform.MarkedIdeal.add,
    MarkedIdeal.pullback,List.length_map]

private theorem entire_tail_heq {D : CMfd.{u} n} (U V : Opens D) (hUV : U=V)
    (Q : BlowupTower D Y) : HEq (restrict U Q) (restrict V Q) := by
  cases hUV
  rfl

/-- Original actual input supplies whole selected mask/companion/tail and valid j internally. -/
theorem actual_general_short_companion_diagram (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y)
    (o : ℕ) (y : Y) (hs : regimeRun (OrdRegime M o) (H.append S) y<S.length) :
    let r := regimeRun (OrdRegime M o) (H.append S) y
    let P := head S r
    let Q := tail S r
    let j := M.E.length+H.length
    let U := ordMask (geoTransformAlong M (H.append P)) o
    let V := ordMask (geoTransformAlong M (interiorEmptyHistory H P)) o
    U=V ∧ j≤(compAt M o (H.append P)).E.length ∧
      HEq (compAt M o (interiorEmptyHistory H P)) (insertEmpty j (compAt M o (H.append P))) ∧
      HEq (restrict V Q) (restrict U Q) := by
  dsimp only
  let r := regimeRun (OrdRegime M o) (H.append S) y
  let P := head S r
  have hp : 0<P.length := by rw [length_head];omega
  have he := whole_record_of_nonempty_tail M hM H hH P hp
  have hj : M.E.length+H.length≤(geoTransformAlong M (H.append P)).E.length := by
    rw [length_E_geoTransformAlong,BlowupTower.length_append]
    omega
  have hm : ordMask (geoTransformAlong M (H.append P)) o=
      ordMask (geoTransformAlong M (interiorEmptyHistory H P)) o := by
    rw [he]
    apply Opens.ext
    change (closure (ordGe _ (o+1)))ᶜ=(closure (ordGe _ (o+1)))ᶜ
    rw [ordGe_insertEmpty _ hj]
  refine ⟨hm,?_,?_,?_⟩
  · rw [companion_boundary_length]
    exact hj
  · unfold compAt
    exact companion_pullback_boundary_heq _ _ _ hj he o _ _ hm.symm
  · exact entire_tail_heq _ _ hm.symm _

private def maskFamilyValue (hn : 0<n) (k : ℕ) {D : CMfd.{u} n}
    (U : Opens D) (J : MarkedIdeal n U) (Q : BlowupTower D Y) (y : Y) : WithTop (ValTy k) :=
  if h : Q.proj y∈U then
    ((invFamily hn k).inv J (restrict U Q) (⟨y,h⟩ : openPreimage Q U) : WithTop (ValTy k))
  else ⊤

/-- Consumes ONLY the proved actual specific-family insertion producer. -/
private theorem maskFamilyValue_boundary (hn : 0<n) (k : ℕ) {D : CMfd.{u} n}
    (U V : Opens D) (J : MarkedIdeal n U) (K : MarkedIdeal n V)
    (hUV : U=V) (j : ℕ) (hj : j≤K.E.length) (he : K.E.take j=List.replicate j ∅)
    (hJK : HEq J (insertEmpty j K)) (Q : BlowupTower D Y) (y : Y) :
    maskFamilyValue hn k U J Q y=
      WithTop.map (shiftFamily k 0) (maskFamilyValue hn k V K Q y) := by
  subst V
  have hJ : J=insertEmpty j K := eq_of_heq hJK
  subst J
  unfold maskFamilyValue
  split_ifs with h
  · apply congrArg (fun v : ValTy k => (v : WithTop (ValTy k)))
    exact (invFamily_insertEmpty hn k (A := CMfd.of (n := n) U) K j hj
      (restrict U Q) (⟨y,h⟩ : openPreimage Q U)).trans
      (shiftFamily_inv_eq_shiftFamily_zero hn k (X := CMfd.of (n := n) U) K hj he
        (restrict U Q) (⟨y,h⟩ : openPreimage Q U))
  · rfl

/-- Private original-boundary consumer, not a newly claimed old Step One node. -/
private theorem actual_initial_lower_value (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (j : ℕ) (hj : j≤M.E.length) (s : ℕ)
    {D : CMfd.{u} n} (H : BlowupTower X D) (Q : BlowupTower D Y) (y : Y) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn k) (insertEmpty j M)
        (lowerMarkedM (insertEmpty j M)) s H Q y =
      WithTop.map (shiftFamily k 0)
        (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) s H Q y) := by
  have hm : lowerMask (insertEmpty j M) s H (Q.proj y)=lowerMask M s H (Q.proj y) := by
    cases s with
    | zero => exact maskB_insertEmpty M hj H (Q.proj y)
    | succ s => exact maskA_insertEmpty M hj H (Q.proj y)
  have hp := lowerMarkedM_insertion_empty_prefix M hj H (Q.proj y) s
  change maskFamilyValue hn k _ _ Q y=
    WithTop.map (shiftFamily k 0) (maskFamilyValue hn k _ _ Q y)
  exact maskFamilyValue_boundary hn k _ _ _ _ hm _ hp.1 hp.2
    (lowerMarkedM_insertEmpty_heq M hj H (Q.proj y) s) Q y

/-- Complete actual initial-boundary Step One identity, including true
contact choices/positive lower recursion. This private consumer follows the
existing actual invariant-insertion proof route and is not a new BP node. -/
private theorem actual_initial_step_value (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (j : ℕ) (hj : j≤M.E.length) (T : BlowupTower X Y) (y : Y) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (insertEmpty j M) T y=
      pairShift (shiftFamily k 0) (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y) := by
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [level_insertEmpty M hj T y]
  by_cases hs : IsSpecial M T y
  · rw [if_pos ((isSpecial_insertEmpty_iff M hj T y).mpr hs),if_pos hs]
    rfl
  · rw [if_neg (fun h => hs ((isSpecial_insertEmpty_iff M hj T y).mp h)),if_neg hs]
    rw [regimeRun_stepRegime_insertEmpty M hj]
    rw [actual_initial_lower_value hn k M j hj]
    rfl

private def actualInner (hn : 0<n) (k : ℕ) :
    ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z →
      ℕ ×ₗ WithTop (ValTy k) :=
  fun {D} J {Z} Q z => Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := Z) Q z

private def maskStepValue (hn : 0<n) (k : ℕ) {D : CMfd.{u} n}
    (U : Opens D) (J : MarkedIdeal n U) (Q : BlowupTower D Y) (y : Y) :
      WithTop (ℕ ×ₗ WithTop (ValTy k)) :=
  if h : Q.proj y∈U then
    (actualInner hn k J (restrict U Q) (⟨y,h⟩ : openPreimage Q U) : WithTop (ℕ ×ₗ WithTop (ValTy k)))
  else ⊤

private theorem maskStepValue_boundary (hn : 0<n) (k : ℕ) {D : CMfd.{u} n}
    (U V : Opens D) (J : MarkedIdeal n U) (K : MarkedIdeal n V)
    (hUV : U=V) (j : ℕ) (hj : j≤K.E.length) (hJK : HEq J (insertEmpty j K))
    (Q : BlowupTower D Y) (y : Y) :
    maskStepValue hn k U J Q y=
      WithTop.map (pairShift (shiftFamily k 0)) (maskStepValue hn k V K Q y) := by
  subst V
  have hJ : J=insertEmpty j K := eq_of_heq hJK
  subst J
  unfold maskStepValue actualInner
  split_ifs with h
  · exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy k) => (v : WithTop (ℕ ×ₗ WithTop (ValTy k))))
      (actual_initial_step_value hn k K j hj (restrict U Q) (⟨y,h⟩ : openPreimage Q U))
  · rfl

private def splitGeneralValue (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X) (o : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) :
      WithTop (ℕ ×ₗ WithTop (ValTy k)) :=
  genLowerValue (actualInner hn k) M o v.2.1 v.2.2 y

/-- ALL-k ENTIRE actual original family value on the TRUE own-order short
branch, including positive inner recursion and independently chosen contact.
No old/new canonical or lower-value comparison certificate is supplied. -/
theorem actual_entire_outer_short_family_value (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y) (y : Y)
    (hs : regimeRun (OrdRegime M (nmOrd (geoTransformAlong M (H.append S)) y))
      (H.append S) y<S.length) :
    (invFamily hn (k+1)).inv M (interiorEmptyHistory H S) y=
      shiftFamily (k+1) (M.E.length+H.length) ((invFamily hn (k+1)).inv M (H.append S) y) := by
  by_cases h0 : nmOrd (geoTransformAlong M (H.append S)) y=0
  · exact invFamily_interior_monomial_leaf hn (k+1) M hM H hH S (by omega) y h0
  let o := nmOrd (geoTransformAlong M (H.append S)) y
  have hνnew : nmOrd (geoTransformAlong M (interiorEmptyHistory H S)) y=o :=
    nmOrd_interior_empty_all_tails M hM H hH S y
  have hc := actual_general_short_splits M hM H hH S o y hs
  have hd := actual_general_short_companion_diagram M hM H hH S o y hs
  let r := regimeRun (OrdRegime M o) (H.append S) y
  let P := head S r
  let Q := tail S r
  have hv : genLowerValue (actualInner hn k) M o (interiorEmptyHistory H P) Q y=
      WithTop.map (pairShift (shiftFamily k 0))
        (genLowerValue (actualInner hn k) M o (H.append P) Q y) := by
    change maskStepValue hn k _ _ Q y=
      WithTop.map (pairShift (shiftFamily k 0)) (maskStepValue hn k _ _ Q y)
    exact maskStepValue_boundary hn k _ _ _ _ hd.1.symm _ hd.2.1 hd.2.2.1 Q y
  change genInv (actualInner hn k) M (interiorEmptyHistory H S) y=
    generalShift (M.E.length+H.length) (pairShift (shiftFamily k 0))
      (genInv (actualInner hn k) M (H.append S) y)
  rw [genInv_of_nmOrd_ne_zero (actualInner hn k) M _ hνnew h0,
    genInv_of_nmOrd_ne_zero (actualInner hn k) M _ (show nmOrd (geoTransformAlong M (H.append S)) y=o from rfl) h0]
  change toLex (o,toLex (Sum.inr (splitGeneralValue hn k M o
      (split (interiorEmptyHistory H S) (regimeRun (OrdRegime M o) (interiorEmptyHistory H S) y)) y))) =
    generalShift (M.E.length+H.length) (pairShift (shiftFamily k 0))
      (toLex (o,toLex (Sum.inr (splitGeneralValue hn k M o (split (H.append S) r) y))))
  rw [hc.2.2,hc.2.1]
  simp only [generalShift,ofLex_toLex,Sum.map_inr]
  exact congrArg (fun v : WithTop (ℕ ×ₗ WithTop (ValTy k)) =>
    (toLex (o,toLex (Sum.inr v)) : ValTy (k+1))) hv

/-- Complete actual successor-family short spectra reflect ALL comparisons,
without same-order, monomial-inner or companion-special restrictions. -/
theorem actual_entire_outer_short_family_comparisons (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y) (y z : Y)
    (hy : regimeRun (OrdRegime M (nmOrd (geoTransformAlong M (H.append S)) y)) (H.append S) y<S.length)
    (hz : regimeRun (OrdRegime M (nmOrd (geoTransformAlong M (H.append S)) z)) (H.append S) z<S.length) :
    let v := (invFamily hn (k+1)).inv M (H.append S) y
    let w := (invFamily hn (k+1)).inv M (H.append S) z
    let v' := (invFamily hn (k+1)).inv M (interiorEmptyHistory H S) y
    let w' := (invFamily hn (k+1)).inv M (interiorEmptyHistory H S) z
    (v'<w' ↔ v<w) ∧ (v'≤w' ↔ v≤w) ∧ (v'=w' ↔ v=w) := by
  dsimp only
  rw [actual_entire_outer_short_family_value hn k M hM H hH S y hy,
    actual_entire_outer_short_family_value hn k M hM H hH S z hz]
  have hm := strictMono_shiftFamily (k+1) (M.E.length+H.length)
  exact ⟨hm.lt_iff_lt,hm.le_iff_le,hm.injective.eq_iff⟩

end
end Hironaka.HironakaOriginalOuterShortFamily
