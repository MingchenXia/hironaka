/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.MarkedIdealAddEquationExact
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Resolution.HironakaOriginalPositiveMemberEmptyInsertion
import Hironaka.Resolution.HironakaOriginalPositiveCompanionEmptyInsertion

/-! Empty original entries in the entire actual recursively constructed invariant. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalInvariantEmptyInsertion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres MonomialInvariantEmptyMember HironakaOriginalMemberFutureShift
  HironakaOriginalStepOneEmptyInsertion HironakaOriginalPositiveMemberEmptyInsertion
  HironakaOriginalPositiveCompanionEmptyInsertion StepOneValue StepOneRegime
  StepOneValueMasked BlowupTowerSplit NonmonomialOrderLocal NonmonomialOrderTail
  GeneralValue MarkedIdealRestrictOpen MarkedIdealBiholomorphism
variable {n : ℕ} {X Y : CMfd.{u} n}

def pairShift {α : Type*} (f : α → α) (v : ℕ ×ₗ WithTop α) : ℕ ×ₗ WithTop α :=
  toLex ((ofLex v).1, WithTop.map f (ofLex v).2)

def generalShift {α : Type*} (j : ℕ) (f : α → α)
    (v : ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop α)) :
    ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop α) :=
  toLex ((ofLex v).1, toLex (Sum.map (shiftVal j) (WithTop.map f) (ofLex (ofLex v).2)))

def shiftFamily : (k : ℕ) → ℕ → ValTy k → ValTy k
  | 0, _ => id
  | k+1, j => generalShift j (pairShift (shiftFamily k 0))

theorem strictMono_pairShift {α : Type*} [LinearOrder α] {f : α → α}
    (hf : StrictMono f) : StrictMono (pairShift f) := by
  intro a b hab
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases Prod.Lex.toLex_lt_toLex.mp hab with h | ⟨h,h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,hf.withTop_map h'⟩

theorem strictMono_generalShift {α : Type*} [LinearOrder α] (j : ℕ) {f : α → α}
    (hf : StrictMono f) : StrictMono (generalShift j f) := by
  have hs : ∀ a b : WithBot MonomialInvariant.Val ⊕ WithTop α,
      toLex a < toLex b →
      toLex (Sum.map (shiftVal j) (WithTop.map f) a) <
        toLex (Sum.map (shiftVal j) (WithTop.map f) b) := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        exact Sum.Lex.inl_lt_inl_iff.mpr
          ((strictMono_shiftVal j) (Sum.Lex.inl_lt_inl_iff.mp hab))
      | inr b => exact Sum.Lex.inl_lt_inr _ _
    | inr a =>
      cases b with
      | inl b => exact False.elim (Sum.Lex.not_inr_lt_inl hab)
      | inr b =>
        exact Sum.Lex.inr_lt_inr_iff.mpr
          (hf.withTop_map (Sum.Lex.inr_lt_inr_iff.mp hab))
  intro a b hab
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases Prod.Lex.toLex_lt_toLex.mp hab with h | ⟨h,h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,hs _ _ h'⟩

theorem strictMono_shiftFamily : ∀ (k j : ℕ), StrictMono (shiftFamily k j)
  | 0, _ => strictMono_id
  | k+1, j => strictMono_generalShift j (strictMono_pairShift (strictMono_shiftFamily k 0))

def shiftFamilyEmbedding (k j : ℕ) : ValTy k ↪o ValTy k :=
  OrderEmbedding.ofStrictMono (shiftFamily k j) (strictMono_shiftFamily k j)

theorem lowerMarkedB_boundary_empty_prefix (m : MarkedIdeal n X)
    (H : BlowupTower X Y) (p : Y) :
    (lowerMarkedB m H p).E.take m.E.length = List.replicate m.E.length ∅ := by
  have ht : (geoTransformAlong (barMarked m) H).E.take m.E.length = origMembers m H := rfl
  change ((geoTransformAlong (barMarked m) H).E.map
    ((Subtype.val : maskB m H p → Y) ⁻¹' ·)).take m.E.length = _
  rw [← List.map_take,ht]
  apply List.eq_replicate_iff.mpr
  refine ⟨?_,?_⟩
  · rw [List.length_map,origMembers_eq,List.length_map]
  · intro W hW
    obtain ⟨V,hV,rfl⟩ := List.mem_map.mp hW
    ext z
    constructor
    · intro hz
      exact False.elim ((interior_subset z.property).2.1 V hV hz)
    · intro hz
      exact False.elim hz

private theorem take_empty_prefix {α : Type*} (E : List α) (a : α) {c r : ℕ}
    (h : E.take r = List.replicate r a) (hc : c ≤ r) :
    E.take c = List.replicate c a := by
  have hh := congrArg (List.take c) h
  simpa only [List.take_take,List.take_replicate,Nat.min_eq_left hc] using hh

theorem shiftFamily_inv_eq_shiftFamily_zero (hn : 0 < n) (k : ℕ)
    (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length)
    (he : m.E.take j = List.replicate j ∅) (T : BlowupTower X Y) (y : Y) :
    shiftFamily k j ((invFamily hn k).inv m T y) =
      shiftFamily k 0 ((invFamily hn k).inv m T y) := by
  cases k with
  | zero => rfl
  | succ k =>
    change generalShift j (pairShift (shiftFamily k 0))
        (genInv (fun {A} J {B} R z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z) m T y) =
      generalShift 0 (pairShift (shiftFamily k 0))
        (genInv (fun {A} J {B} R z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z) m T y)
    unfold generalShift genInv genSecond
    by_cases ho : nmOrd (geoTransformAlong m T) y = 0
    · rw [if_pos ho]
      simp only [ofLex_toLex,Sum.map_inl]
      congr 3
      apply congrArg Sum.inl
      exact shiftVal_inv_eq_shiftVal_zero_of_ge _ _
        (memberIdx_ge_of_empty_prefix (empty_prefix_geoTransformAlong m j hj he T) y)
    · rw [if_neg ho]
      rfl

open Classical in
private def maskValue {α : Type*}
    (F : ∀ {A : CMfd.{u} n}, MarkedIdeal n A → ∀ {B : CMfd.{u} n}, BlowupTower A B → B → α)
    (U : Opens X) (J : MarkedIdeal n U) (T : BlowupTower X Y) (y : Y) : WithTop α :=
  if h : T.proj y ∈ U then
    (F J (restrict U T) (⟨y,h⟩ : openPreimage T U) : WithTop α)
  else ⊤

private theorem maskValue_congr_map {α : Type*}
    (F : ∀ {A : CMfd.{u} n}, MarkedIdeal n A → ∀ {B : CMfd.{u} n}, BlowupTower A B → B → α)
    (f : α → α) (U V : Opens X) (J : MarkedIdeal n U) (K : MarkedIdeal n V)
    (hUV : U = V) (j : ℕ) (hJK : HEq J (insertEmpty j K))
    (hF : ∀ {B : CMfd.{u} n} (R : BlowupTower (CMfd.of (n := n) V) B) (z : B),
      F (insertEmpty j K) R z = f (F K R z))
    (T : BlowupTower X Y) (y : Y) :
    maskValue F U J T y = WithTop.map f (maskValue F V K T y) := by
  classical
  subst V
  have heq : J = insertEmpty j K := eq_of_heq hJK
  subst J
  unfold maskValue
  split_ifs with h
  · exact congrArg (fun a : α => (a : WithTop α))
      (hF (restrict U T) (⟨y,h⟩ : openPreimage T U))
  · rfl

theorem lowerMarkedM_insertEmpty_heq (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (H : BlowupTower X Y) (p : Y) (s : ℕ) :
    HEq (lowerMarkedM (insertEmpty j m) s H p)
      (insertEmpty (if s = 0 then j else actualLowerInsertionIndex m H p j)
        (lowerMarkedM m s H p)) := by
  cases s with
  | zero =>
    change HEq (lowerMarkedB (insertEmpty j m) H p) (insertEmpty j (lowerMarkedB m H p))
    exact lowerMarkedB_insertEmpty_heq m hj H p
  | succ s =>
    change HEq (lowerMarked (insertEmpty j m) (s+1) H p)
      (insertEmpty (actualLowerInsertionIndex m H p j) (lowerMarked m (s+1) H p))
    exact lowerMarked_succ_insertEmpty_heq m hj H p s

theorem lowerMarkedM_insertion_empty_prefix (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (H : BlowupTower X Y) (p : Y) (s : ℕ) :
    let c := if s = 0 then j else actualLowerInsertionIndex m H p j
    c ≤ (lowerMarkedM m s H p).E.length ∧
      (lowerMarkedM m s H p).E.take c = List.replicate c ∅ := by
  cases s with
  | zero =>
    change j ≤ (lowerMarkedB m H p).E.length ∧
      (lowerMarkedB m H p).E.take j = List.replicate j ∅
    refine ⟨?_,take_empty_prefix _ ∅ (lowerMarkedB_boundary_empty_prefix m H p) hj⟩
    change j ≤ ((geoTransformAlong (barMarked m) H).E.map _).length
    rw [List.length_map,length_E_geoTransformAlong]
    change j ≤ m.E.length + H.length
    omega
  | succ s =>
    change actualLowerInsertionIndex m H p j ≤ (lowerMarked m (s+1) H p).E.length ∧
      (lowerMarked m (s+1) H p).E.take (actualLowerInsertionIndex m H p j) = _
    have hpre := original_lower_tail_empty_prefix m H p s (BlowupTower.refl)
    exact ⟨actualLowerInsertionIndex_le_lowerBoundary m H p s hj,
      take_empty_prefix _ ∅ hpre.2
        (actualLowerInsertionIndex_le_retainedOriginalCount m H p hj)⟩

private theorem lowerValue_insertEmpty (hn : 0 < n) (k : ℕ)
    (hrec : ∀ {A B : CMfd.{u} n} (J : MarkedIdeal n A) (j : ℕ), j ≤ J.E.length →
      ∀ (R : BlowupTower A B) (z : B),
      (invFamily hn k).inv (insertEmpty j J) R z = shiftFamily k j ((invFamily hn k).inv J R z))
    (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length) (s : ℕ)
    {A : CMfd.{u} n} (H : BlowupTower X A) (T : BlowupTower A Y) (y : Y) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn k) (insertEmpty j m)
        (lowerMarkedM (insertEmpty j m)) s H T y =
      WithTop.map (shiftFamily k 0)
        (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) m (lowerMarkedM m) s H T y) := by
  have hmask : lowerMask (insertEmpty j m) s H (T.proj y) = lowerMask m s H (T.proj y) := by
    cases s with
    | zero => exact maskB_insertEmpty m hj H (T.proj y)
    | succ s => exact maskA_insertEmpty m hj H (T.proj y)
  have hp := lowerMarkedM_insertion_empty_prefix m hj H (T.proj y) s
  change maskValue ((invFamily hn k).inv) _ _ T y =
    WithTop.map (shiftFamily k 0) (maskValue ((invFamily hn k).inv) _ _ T y)
  apply maskValue_congr_map _ _ _ _ _ _ hmask
    (if s = 0 then j else actualLowerInsertionIndex m H (T.proj y) j)
    (lowerMarkedM_insertEmpty_heq m hj H (T.proj y) s)
  intro B R z
  rw [hrec _ _ hp.1]
  exact shiftFamily_inv_eq_shiftFamily_zero hn k _ hp.1 hp.2 R z

private theorem stepOneInvM_insertEmpty (hn : 0 < n) (k : ℕ)
    (hrec : ∀ {A B : CMfd.{u} n} (J : MarkedIdeal n A) (j : ℕ), j ≤ J.E.length →
      ∀ (R : BlowupTower A B) (z : B),
      (invFamily hn k).inv (insertEmpty j J) R z = shiftFamily k j ((invFamily hn k).inv J R z))
    (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length) (T : BlowupTower X Y) (y : Y) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (insertEmpty j m) T y =
      pairShift (shiftFamily k 0) (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m T y) := by
  classical
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [level_insertEmpty m hj T y]
  by_cases hs : IsSpecial m T y
  · rw [if_pos ((isSpecial_insertEmpty_iff m hj T y).mpr hs),if_pos hs]
    rfl
  · rw [if_neg (fun h => hs ((isSpecial_insertEmpty_iff m hj T y).mp h)),if_neg hs]
    rw [regimeRun_stepRegime_insertEmpty m hj]
    rw [lowerValue_insertEmpty hn k hrec m hj]
    rfl

private theorem companion_pullback_insertEmpty_heq (J J' : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ J.E.length) (hJ : J' = insertEmpty j J) (o : ℕ)
    (U V : Opens X) (hUV : U = V) :
    HEq (CompanionRebase.companionOf n (M := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) J') o)
      (insertEmpty j (CompanionRebase.companionOf n (M := CMfd.of (n := n) V)
        (MarkedIdeal.pullback (Subtype.val : V → X) J) o)) := by
  subst V
  subst J'
  apply heq_of_eq
  have hp : MarkedIdeal.pullback (M' := CMfd.of (n := n) U)
      (Subtype.val : U → X) (insertEmpty j J) =
      insertEmpty j (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) J) := by
    change MarkedIdeal.mk _ ((J.E.insertIdx j ∅).map ((Subtype.val : U → X) ⁻¹' ·)) _ _ =
      MarkedIdeal.mk _ ((J.E.map ((Subtype.val : U → X) ⁻¹' ·)).insertIdx j ∅) _ _
    rw [List.map_insertIdx,Set.preimage_empty]
    rfl
  rw [hp]
  exact companionOf_insertEmpty _ (by
    change j ≤ (J.E.map ((Subtype.val : U → X) ⁻¹' ·)).length
    rwa [List.length_map]) o

theorem compAt_insertEmpty_heq (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (o : ℕ) (H : BlowupTower X Y) :
    HEq (compAt (insertEmpty j m) o H) (insertEmpty j (compAt m o H)) := by
  unfold compAt
  exact companion_pullback_insertEmpty_heq (geoTransformAlong m H)
    (geoTransformAlong (insertEmpty j m) H) (le_length_E_geoTransformAlong m hj H)
    (geoTransformAlong_insertEmpty m hj H) o _ _
    (ordMask_geoTransformAlong_insertEmpty m hj H o)

private theorem genLowerValue_insertEmpty (hn : 0 < n) (k : ℕ)
    (hrec : ∀ {A B : CMfd.{u} n} (J : MarkedIdeal n A) (j : ℕ), j ≤ J.E.length →
      ∀ (R : BlowupTower A B) (z : B),
      (invFamily hn k).inv (insertEmpty j J) R z = shiftFamily k j ((invFamily hn k).inv J R z))
    (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length) (o : ℕ)
    {A : CMfd.{u} n} (H : BlowupTower X A) (T : BlowupTower A Y) (y : Y) :
    genLowerValue (fun {A} J {B} R z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z)
        (insertEmpty j m) o H T y =
      WithTop.map (pairShift (shiftFamily k 0))
        (genLowerValue (fun {A} J {B} R z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z)
          m o H T y) := by
  change maskValue (fun {A} J {B} R z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z)
      _ _ T y = WithTop.map (pairShift (shiftFamily k 0))
      (maskValue (fun {A} J {B} R z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z) _ _ T y)
  apply maskValue_congr_map _ _ _ _ _ _ (ordMask_geoTransformAlong_insertEmpty m hj H o)
    j (compAt_insertEmpty_heq m hj o H)
  intro B R z
  apply stepOneInvM_insertEmpty hn k hrec
  have hc : (compAt m o H).E.length = (geoTransformAlong m H).E.length := by
    unfold compAt CompanionRebase.companionOf
    unfold CompanionReductionAlong.companionAlong
    split_ifs <;> simp only [MarkedIdealOperationsTransform.MarkedIdeal.add,
      MarkedIdeal.pullback,List.length_map]
  rw [hc]
  exact le_length_E_geoTransformAlong m hj H

theorem invFamily_insertEmpty (hn : 0 < n) :
    ∀ (k : ℕ) {A B : CMfd.{u} n} (m : MarkedIdeal n A) (j : ℕ), j ≤ m.E.length →
      ∀ (T : BlowupTower A B) (y : B),
      (invFamily hn k).inv (insertEmpty j m) T y = shiftFamily k j ((invFamily hn k).inv m T y)
  | 0, _, _, _, _, _, _, _ => rfl
  | k+1, A, B, m, j, hj, T, y => by
    change genInv
        (fun {A} J {B} R z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z)
        (insertEmpty j m) T y =
      generalShift j (pairShift (shiftFamily k 0))
        (genInv (fun {A} J {B} R z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z) m T y)
    unfold genInv genSecond generalShift
    rw [nmOrd_geoTransformAlong_insertEmpty m hj T y]
    by_cases ho : nmOrd (geoTransformAlong m T) y = 0
    · simp only [if_pos ho,ofLex_toLex,Sum.map_inl]
      congr 3
      apply congrArg Sum.inl
      exact towerInvAlong_insertEmpty m hj T y
    · simp only [if_neg ho,ofLex_toLex,Sum.map_inr]
      rw [regimeRun_insertEmpty m hj]
      rw [genLowerValue_insertEmpty hn k (invFamily_insertEmpty hn k) m hj]

theorem invFamily_insertEmpty_comparisons (hn : 0 < n) (k : ℕ)
    (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length) (T : BlowupTower X Y) (y : Y)
    {A B : CMfd.{u} n} (m' : MarkedIdeal n A) (hj' : j ≤ m'.E.length)
    (T' : BlowupTower A B) (y' : B) :
    let v := (invFamily hn k).inv m T y
    let w := (invFamily hn k).inv m' T' y'
    let v' := (invFamily hn k).inv (insertEmpty j m) T y
    let w' := (invFamily hn k).inv (insertEmpty j m') T' y'
    (v' < w' ↔ v < w) ∧ (v' ≤ w' ↔ v ≤ w) ∧ (v' = w' ↔ v = w) := by
  dsimp only
  rw [invFamily_insertEmpty hn k m j hj T y,invFamily_insertEmpty hn k m' j hj' T' y']
  exact ⟨(strictMono_shiftFamily k j).lt_iff_lt,(strictMono_shiftFamily k j).le_iff_le,
    (strictMono_shiftFamily k j).injective.eq_iff⟩

theorem maxLocus_invFamily_insertEmpty (hn : 0 < n) (k : ℕ)
    (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length) (T : BlowupTower X Y) (S : Set Y) :
    ResolutionDriver.maxLocus ((invFamily hn k).inv (insertEmpty j m) T) S =
      ResolutionDriver.maxLocus ((invFamily hn k).inv m T) S := by
  have he : (invFamily hn k).inv (insertEmpty j m) T =
      shiftFamily k j ∘ ((invFamily hn k).inv m T) :=
    funext (fun y => invFamily_insertEmpty hn k m j hj T y)
  rw [he]
  exact MaxLocusLocal.maxLocus_comp_strictMono (strictMono_shiftFamily k j) _ S

theorem isCanonical_invFamily_insertEmpty_iff (hn : 0 < n) (k : ℕ)
    (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length) :
    ∀ {A : CMfd.{u} n} (T : BlowupTower X A),
      ResolutionInvariantSpec.IsCanonical (insertEmpty j m)
        ((invFamily hn k).inv (insertEmpty j m)) T ↔
      ResolutionInvariantSpec.IsCanonical m ((invFamily hn k).inv m) T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
    change (_ ∧ (C = ∅ ∨ C = ResolutionDriver.maxLocus
      ((invFamily hn k).inv (insertEmpty j m) T) (geoTransformAlong (insertEmpty j m) T).cosupp)) ↔
      (_ ∧ (C = ∅ ∨ C = ResolutionDriver.maxLocus
        ((invFamily hn k).inv m T) (geoTransformAlong m T).cosupp))
    rw [isCanonical_invFamily_insertEmpty_iff hn k m hj T,
      cosupp_geoTransformAlong_insertEmpty m hj T,maxLocus_invFamily_insertEmpty hn k m hj T]

theorem isCanonicalSegment_invFamily_insertEmpty_iff (hn : 0 < n) (k : ℕ)
    (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length) :
    ∀ {A : CMfd.{u} n} (T : BlowupTower X A),
      ResolutionDriver.IsCanonicalSegment (insertEmpty j m)
        ((invFamily hn k).inv (insertEmpty j m)) T ↔
      ResolutionDriver.IsCanonicalSegment m ((invFamily hn k).inv m) T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
    change (_ ∧ C.Nonempty ∧ C = ResolutionDriver.maxLocus
      ((invFamily hn k).inv (insertEmpty j m) T) (geoTransformAlong (insertEmpty j m) T).cosupp) ↔
      (_ ∧ C.Nonempty ∧ C = ResolutionDriver.maxLocus
        ((invFamily hn k).inv m T) (geoTransformAlong m T).cosupp)
    rw [isCanonicalSegment_invFamily_insertEmpty_iff hn k m hj T,
      cosupp_geoTransformAlong_insertEmpty m hj T,maxLocus_invFamily_insertEmpty hn k m hj T]

end
end Hironaka.HironakaOriginalInvariantEmptyInsertion
