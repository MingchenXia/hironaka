/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalBoundaryHistoryMap
import Hironaka.Resolution.HironakaOriginalGeneralCrossingHistory
/-! Actual canonical initial-boundary compatibility at every family depth.
Complete three-node mathematics preceded code. Full higher interior transport remains open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalRecursiveBoundaryHistoryMap
noncomputable section
open Classical
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail GeneralValue
  CompanionRebase CompanionReductionAlong
  HironakaOriginalCrossingLowerHistory HironakaOriginalBoundaryHistoryMap
  HironakaOriginalInvariantEmptyInsertion HironakaOriginalGeneralCrossingHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Chronological recursive map; every actual lower index uses its original level. -/
def recursiveHistoryShift : (k : ℕ) → ℕ → ValTy k → ValTy k
  | 0, _ => id
  | k+1, j => generalShift j (fun v =>
      toLex ((ofLex v).1,WithTop.map (recursiveHistoryShift k (j-(ofLex v).1)) (ofLex v).2))

def recursiveStepShift (k j : ℕ) (v : ℕ ×ₗ WithTop (ValTy k)) : ℕ ×ₗ WithTop (ValTy k) :=
  toLex ((ofLex v).1,WithTop.map (recursiveHistoryShift k (j-(ofLex v).1)) (ofLex v).2)

theorem recursiveHistoryShift_succ (k j : ℕ) :
    recursiveHistoryShift (k+1) j=generalShift j (recursiveStepShift k j) := rfl

theorem strictMono_recursiveHistoryShift : ∀ k j : ℕ, StrictMono (recursiveHistoryShift k j)
  | 0, _ => strictMono_id
  | k+1, j => by
    rw [recursiveHistoryShift_succ]
    apply strictMono_generalShift
    intro a b hab
    apply Prod.Lex.toLex_lt_toLex.mpr
    rcases Prod.Lex.toLex_lt_toLex.mp hab with h | ⟨hℓ,hv⟩
    · exact Or.inl h
    · change (ofLex a).1=(ofLex b).1 at hℓ
      refine Or.inr ⟨hℓ,?_⟩
      change WithTop.map (recursiveHistoryShift k (j-(ofLex a).1)) (ofLex a).2<
        WithTop.map (recursiveHistoryShift k (j-(ofLex b).1)) (ofLex b).2
      rw [hℓ]
      exact (strictMono_recursiveHistoryShift k (j-(ofLex b).1)).withTop_map hv

theorem strictMono_recursiveStepShift (k j : ℕ) : StrictMono (recursiveStepShift k j) := by
  intro a b hab
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases Prod.Lex.toLex_lt_toLex.mp hab with h | ⟨hℓ,hv⟩
  · exact Or.inl h
  · change (ofLex a).1=(ofLex b).1 at hℓ
    refine Or.inr ⟨hℓ,?_⟩
    change WithTop.map (recursiveHistoryShift k (j-(ofLex a).1)) (ofLex a).2<
      WithTop.map (recursiveHistoryShift k (j-(ofLex b).1)) (ofLex b).2
    rw [hℓ]
    exact (strictMono_recursiveHistoryShift k (j-(ofLex b).1)).withTop_map hv

def recursiveHistoryShiftEmbedding (k j : ℕ) : ValTy k ↪o ValTy k :=
  OrderEmbedding.ofStrictMono (recursiveHistoryShift k j) (strictMono_recursiveHistoryShift k j)

def recursiveStepShiftEmbedding (k j : ℕ) :
    (ℕ ×ₗ WithTop (ValTy k)) ↪o (ℕ ×ₗ WithTop (ValTy k)) :=
  OrderEmbedding.ofStrictMono (recursiveStepShift k j) (strictMono_recursiveStepShift k j)

theorem recursiveHistoryShift_zero : ∀ k : ℕ, recursiveHistoryShift k 0=shiftFamily k 0
  | 0 => rfl
  | k+1 => by
    rw [recursiveHistoryShift_succ]
    change generalShift 0 (recursiveStepShift k 0)=generalShift 0 (pairShift (shiftFamily k 0))
    apply congrArg (generalShift 0)
    funext v
    simp only [recursiveStepShift,Nat.zero_sub,recursiveHistoryShift_zero k,pairShift]

theorem recursiveHistoryShift_one (j : ℕ) : recursiveHistoryShift 1 j=shiftFamily 1 j := rfl


private def FamilyBoundaryCompatible (hn : 0<n) (k : ℕ) : Prop :=
  ∀ {X Y : CMfd.{u} n} (M : MarkedIdeal n X), IsInvDomain k M →
    ∀ (T : BlowupTower X Y), IsCanonical M ((invFamily hn k).inv M) T →
    ∀ (j : ℕ), j≤M.E.length → ∀ (y : Y), y∈(geoTransformAlong M T).cosupp →
      recursiveHistoryShift k j ((invFamily hn k).inv M T y)=
        shiftFamily k j ((invFamily hn k).inv M T y)

/-- Actual lower canonical data consume ONLY the genuine preceding specific depth IH. -/
private theorem canonical_step_initial_of_lower (hn : 0<n) (k : ℕ)
    (hFamily : FamilyBoundaryCompatible.{u} hn k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (j : ℕ) (hj : j≤M.E.length) (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) :
    recursiveStepShift k j (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y)=
      pairShift (shiftFamily k 0) (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y) := by
  by_cases hsp : IsSpecial M T y
  · unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hsp]
    rfl
  have hfacts := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) M hM hmax hn T hcan
  have hbarcos : y∈(geoTransformAlong (barMarked M) T).cosupp := hfacts.2.2.symm ▸ hy
  have hsc := (Seq.StepOneBridge.isCanonical_iff (k := k+1)
    (invFamily hn k) M hM hmax hn T).mp hcan
  let ℓ := level M T y
  let r := regimeRun (stepRegime M ℓ) T y
  let K := head T r
  let Q := tail T r
  let p := Q.proj y
  let U := lowerMask M ℓ K p
  let J := lowerMarkedM M ℓ K p
  have hd := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical M (k := k+1)
    (invFamily hn k) hM.isWellFormed hM.one_le_d hn hmax hM.dimLE T hfacts.1 hsc y hbarcos hsp
  change ∃ hp : p∈U, IsInvDomain k J ∧
    IsCanonical J ((invFamily hn k).inv J) (restrict U Q) ∧
      (⟨y,hp⟩ : openPreimage Q U)∈(geoTransformAlong J (restrict U Q)).cosupp at hd
  obtain ⟨hp,hdom,hcanJ,hcosJ⟩ := hd
  have hK := (isGeoTestTower_iff_head_tail (barMarked M) T r).mp hfacts.1 |>.1
  have hwhole : K.append Q=T := head_append_tail T r
  have hcurrent : stepRegime M ℓ (K.append Q) y := by rw [hwhole];exact ⟨rfl,hsp⟩
  have hreach : Q.length≤regimeRun (stepRegime M ℓ) (K.append Q) y := by
    rw [hwhole]
    change (tail T r).length≤r
    rw [length_tail]
    exact Nat.min_le_left _ _
  have hbase := regime_at_base_of_reaching_run (stepRegime M ℓ) K Q y hcurrent hreach
  have hprefix := original_initial_lower_history_empty_prefix M hM.isWellFormed K hK p j hj
  rw [hbase.1] at hprefix
  change j-ℓ≤J.E.length ∧ J.E.take (j-ℓ)=List.replicate (j-ℓ) ∅ at hprefix
  have hv := hFamily (X := CMfd.of (n := n) U) J hdom (restrict U Q) hcanJ
    (j-ℓ) hprefix.1 (⟨y,hp⟩ : openPreimage Q U) hcosJ
  have hz := shiftFamily_inv_eq_shiftFamily_zero (X := CMfd.of (n := n) U)
    hn k J hprefix.1 hprefix.2 (restrict U Q) (⟨y,hp⟩ : openPreimage Q U)
  have hval := hv.trans hz
  have hmasked : WithTop.map (recursiveHistoryShift k (j-ℓ))
      (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) ℓ K Q y)=
    WithTop.map (shiftFamily k 0)
      (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) ℓ K Q y) := by
    rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
    simp only [WithTop.map_coe]
    exact congrArg (fun v : ValTy k => (v : WithTop (ValTy k))) hval
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_neg hsp]
  simp only [recursiveStepShift,pairShift,ofLex_toLex]
  exact congrArg (fun v : WithTop (ValTy k) => toLex (ℓ,v)) hmasked

private def familyInner (hn : 0<n) (k : ℕ) :
    ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z →
      ℕ ×ₗ WithTop (ValTy k) :=
  fun {D} J {Z} Q z => Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := Z) Q z

private theorem companion_boundary_length (M : MarkedIdeal n X) (o : ℕ)
    {D : CMfd.{u} n} (K : BlowupTower X D) :
    (compAt M o K).E.length=M.E.length+K.length := by
  unfold compAt companionOf companionAlong
  split_ifs <;> simp only [MarkedIdealOperationsTransform.MarkedIdeal.add,
    MarkedIdealBiholomorphism.MarkedIdeal.pullback,List.length_map,length_E_geoTransformAlong]

private def generic_split_lower {Λ : Type*} [LinearOrder Λ]
    (F : ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z → Λ)
    (M : MarkedIdeal n X) (o : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) : WithTop Λ :=
  genLowerValue F M o v.2.1 v.2.2 y

private theorem generic_monomial_maps {Λ : Type*} [LinearOrder Λ]
    (F : ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z → Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y)
    (h0 : nmOrd (geoTransformAlong M T) y=0) (j : ℕ) (f g : Λ → Λ) :
    generalShift j f (genInv F M T y)=generalShift j g (genInv F M T y) := by
  unfold generalShift genInv genSecond
  rw [h0]
  rfl

private theorem generic_positive_maps {Λ : Type*} [LinearOrder Λ]
    (F : ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z → Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) (o : ℕ)
    (hν : nmOrd (geoTransformAlong M T) y=o) (ho : o≠0) (j : ℕ) (f g : Λ → Λ)
    (hL : WithTop.map f (generic_split_lower F M o (split T (regimeRun (OrdRegime M o) T y)) y)=
      WithTop.map g (generic_split_lower F M o (split T (regimeRun (OrdRegime M o) T y)) y)) :
    generalShift j f (genInv F M T y)=generalShift j g (genInv F M T y) := by
  rw [genInv_of_nmOrd_ne_zero F M _ hν ho]
  change generalShift j f (toLex (o,toLex (Sum.inr (generic_split_lower F M o
      (split T (regimeRun (OrdRegime M o) T y)) y))))=
    generalShift j g (toLex (o,toLex (Sum.inr (generic_split_lower F M o
      (split T (regimeRun (OrdRegime M o) T y)) y))))
  simp only [generalShift,ofLex_toLex,Sum.map_inr]
  exact congrArg (fun v : WithTop Λ => toLex (o,toLex (Sum.inr v))) hL

/-- The preceding IH is used only on genuine original canonical companion data. -/
private theorem family_boundary_succ (hn : 0<n) (k : ℕ)
    (hFamily : FamilyBoundaryCompatible.{u} hn k) : FamilyBoundaryCompatible.{u} hn (k+1) := by
  intro D Z M hM T hcan j hj y hy
  change generalShift j (recursiveStepShift k j) (genInv (familyInner hn k) M T y)=
    generalShift j (pairShift (shiftFamily k 0)) (genInv (familyInner hn k) M T y)
  by_cases h0 : nmOrd (geoTransformAlong M T) y=0
  · exact generic_monomial_maps (familyInner hn k) M T y h0 j _ _
  let o := nmOrd (geoTransformAlong M T) y
  let r := regimeRun (OrdRegime M o) T y
  let K := head T r
  let Q := tail T r
  let U := ordMask (geoTransformAlong M K) o
  let J := compAt M o K
  have hd := original_canonical_general_crossing_data hn k M hM T BlowupTower.refl
    hcan o y hy rfl (by omega) (Nat.zero_le _)
  simp only [BlowupTower.append_refl,BlowupTower.length_refl,Nat.sub_zero] at hd
  change ∃ hp : Q.proj y∈U,
    IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (familyInner hn k J) (restrict U Q) ∧
      (⟨y,hp⟩ : openPreimage Q U)∈(geoTransformAlong J (restrict U Q)).cosupp at hd
  obtain ⟨hp,hdom,hmax,hcanJ,hcosJ⟩ := hd
  have hjJ : j≤J.E.length := by
    change j≤(compAt M o K).E.length
    rw [companion_boundary_length]
    omega
  have hv := canonical_step_initial_of_lower (X := CMfd.of (n := n) U)
    hn k hFamily J hdom hmax (restrict U Q) hcanJ j hjJ
    (⟨y,hp⟩ : openPreimage Q U) hcosJ
  have hL : WithTop.map (recursiveStepShift k j) (genLowerValue (familyInner hn k) M o K Q y)=
      WithTop.map (pairShift (shiftFamily k 0)) (genLowerValue (familyInner hn k) M o K Q y) := by
    rw [genLowerValue_eq_of_mem (familyInner hn k) M hp]
    simp only [WithTop.map_coe]
    exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy k) => (v : WithTop (ℕ ×ₗ WithTop (ValTy k)))) hv
  exact generic_positive_maps (familyInner hn k) M T y o rfl h0 j _ _ hL

private theorem family_boundary_all (hn : 0<n) : ∀ k : ℕ, FamilyBoundaryCompatible.{u} hn k
  | 0 => by intro M hM T hcan j hj y hy; rfl
  | k+1 => family_boundary_succ hn k (family_boundary_all hn k)

/-- Original inputs internally discharge the true lower-depth induction at EVERY depth. -/
theorem original_canonical_step_initial_boundary_compatibility (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (j : ℕ) (hj : j≤M.E.length) (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) :
    recursiveStepShift k j (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y)=
      pairShift (shiftFamily k 0) (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y) :=
  canonical_step_initial_of_lower hn k (family_boundary_all hn k) M hM hmax T hcan j hj y hy

/-- ALL original canonical family values, with no supplied lower/value/branch certificate. -/
theorem original_canonical_family_initial_boundary_compatibility (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X Y) (hcan : IsCanonical M ((invFamily hn k).inv M) T)
    (j : ℕ) (hj : j≤M.E.length) (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) :
    recursiveHistoryShift k j ((invFamily hn k).inv M T y)=
      shiftFamily k j ((invFamily hn k).inv M T y) :=
  family_boundary_all hn k M hM T hcan j hj y hy

/-- A TRUE empty initial prefix is supplied explicitly only for this stronger corollary. -/
theorem original_canonical_family_empty_initial_boundary_compatibility (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X Y) (hcan : IsCanonical M ((invFamily hn k).inv M) T)
    (j : ℕ) (hj : j≤M.E.length) (hprefix : M.E.take j=List.replicate j ∅)
    (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) :
    recursiveHistoryShift k j ((invFamily hn k).inv M T y)=
      recursiveHistoryShift k 0 ((invFamily hn k).inv M T y) := by
  rw [recursiveHistoryShift_zero]
  exact (original_canonical_family_initial_boundary_compatibility hn k M hM T hcan j hj y hy).trans
    (shiftFamily_inv_eq_shiftFamily_zero hn k M hj hprefix T y)

end
end Hironaka.HironakaOriginalRecursiveBoundaryHistoryMap
