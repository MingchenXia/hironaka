/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCompanionChronologicalBoundaryAnalytic
import Hironaka.Resolution.HironakaStepOneSpecialAnalyticLoci
/-! Original-input coherent fixed companion presentations and ENTIRE arbitrary
lower-threshold dictionary on the true reference open, with actual special-top
analytic consumers. Full global arbitrary-lower analytics remain subsequent work.
Complete source-first blueprint: hironaka-original-frozen-companion-presentation-extension.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFrozenCompanionPresentation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail StepOneRegime
  CanonicalCentres GeneralValue GeneralCanonicalTail StepOneValue HomogenizedIdealAlong StepOneLowerDomain
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y : CMfd.{u} n}

def orderAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) : ℕ :=
  nmOrd (geoTransformAlong m T) x

def runAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) : ℕ :=
  regimeRun (OrdRegime m (orderAt m T x)) T x

def maskAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) : Opens (split T (runAt m T x)).1 :=
  ordMask (geoTransformAlong m (head T (runAt m T x))) (orderAt m T x)

def patchAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) : Opens Y :=
  openPreimage (tail T (runAt m T x)) (maskAt m T x)

def companionAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :
    MarkedIdeal n (maskAt m T x) :=
  compAt m (orderAt m T x) (head T (runAt m T x))

def companionTailAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :
    BlowupTower (CMfd.of (n := n) (maskAt m T x)) (CMfd.of (n := n) (patchAt m T x)) :=
  restrict (maskAt m T x) (tail T (runAt m T x))

/-- Original canonical inputs internally construct the fixed whole companion geometry. -/
theorem actual_frozen_companion_domain_and_cosupport (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) :
    x ∈ patchAt m T x ∧ IsInvDomain (k+1) (companionAt m T x) ∧
      IsMaximalOrderAlong (companionAt m T x).N (companionAt m T x).ideal (companionAt m T x).d ∧
      IsCanonical (companionAt m T x)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (companionAt m T x)) (companionTailAt m T x) ∧
      ∀ p : patchAt m T x,
        p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp ↔
          (p : Y) ∈ (geoTransformAlong m T).cosupp ∧ nmOrd (geoTransformAlong m T) (p : Y)=orderAt m T x := by
  let R := invFamily hn k
  let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM R J S z
  have hM := StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+1) R hn
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hD := hasGenLowerData_of_isCanonical lower hM hn h T hT
    (show IsCanonical m (genInv lower m) T from hc)
  obtain ⟨hmask,hK,hmax,hcanK,_⟩ := hD x hx (orderAt m T x) rfl hq
  refine ⟨hmask,hK,hmax,hcanK,?_⟩
  have hTW := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) R (companionAt m T x)
    hK hmax hn (companionTailAt m T x) hcanK).2.1
  obtain ⟨hhead,htail⟩ := (isGeoTestTower_iff_head_tail m T (runAt m T x)).mp hT
  intro p
  have hd := mem_cosupp_compAt_iff hn h hq (head T (runAt m T x)) (tail T (runAt m T x))
    hhead htail hTW p
  rw [← geoTransformAlong_head_tail m T (runAt m T x)] at hd
  exact hd

/-- The actual order mask and true companion test history bound the whole current cosupport. -/
theorem order_le_on_actual_frozen_companion_patch (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x) (hp : (p : Y) ∈ (geoTransformAlong m T).cosupp) :
    nmOrd (geoTransformAlong m T) (p : Y) ≤ orderAt m T x := by
  obtain ⟨_,hK,hmax,hcanK,_⟩ := actual_frozen_companion_domain_and_cosupport hn m h T hc x hx hq
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hTW := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k)
    (companionAt m T x) hK hmax hn (companionTailAt m T x) hcanK).2.1
  obtain ⟨hhead,htail⟩ := (isGeoTestTower_iff_head_tail m T (runAt m T x)).mp hT
  have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T (runAt m T x)) hhead
  have hp' : (p : Y) ∈
      (geoTransformAlong (geoTransformAlong m (head T (runAt m T x))) (tail T (runAt m T x))).cosupp := by
    rw [← geoTransformAlong_head_tail]
    exact hp
  have hb := nmOrd_le_of_notMem (notMem_ordGe_of_mask hn hdom hq (maskAt m T x)
    (fun y _ hy => (mem_ordMask_iff hn hdom.isWellFormed hdom.isNonzeroAlongAt (orderAt m T x) y).mp hy)
    (tail T (runAt m T x)) htail hTW (p : Y) hp' p.2)
  rwa [← geoTransformAlong_head_tail] at hb

/-- Real original rebase comparison identifies independently selected histories
with the one reference companion on its ENTIRE true cosupport. -/
theorem original_value_eq_actual_frozen_companion (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp) :
    (invFamily hn (k+1)).inv m T (p : Y) =
      toLex (orderAt m T x,toLex (Sum.inr
        ((Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (companionAt m T x) (companionTailAt m T x) p :
          ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k))))) := by
  let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J S z
  have hM := StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+1) (invFamily hn k) hn
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hcanG : IsCanonical m (genInv lower m) T := hc
  have hD := hasGenLowerData_of_isCanonical lower hM hn h T hT hcanG
  obtain ⟨_,_,_,hcanK,_⟩ := actual_frozen_companion_domain_and_cosupport hn m h T hc x hx hq
  exact genInv_eq_of_mem_cosupp_compAt hM hn h T hT hcanG hD hx rfl hq rfl hcanK p hp

/-- The whole original arbitrary-lower threshold family uses the SAME true fixed companion. -/
theorem original_superlevel_pullback_eq_actual_frozen_companion (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (β : WithTop (ℕ ×ₗ WithTop (ValTy k))) :
    (Subtype.val : patchAt m T x → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
      toLex (orderAt m T x,toLex (Sum.inr β)) ≤ (invFamily hn (k+1)).inv m T y} =
    {p | p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp ∧
      β ≤ (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (companionAt m T x) (companionTailAt m T x) p :
        WithTop (ℕ ×ₗ WithTop (ValTy k)))} := by
  obtain ⟨_,_,_,_,hdict⟩ := actual_frozen_companion_domain_and_cosupport hn m h T hc x hx hq
  ext p
  constructor
  · intro hp
    have hle := order_le_on_actual_frozen_companion_patch hn m h T hc x hx hq p hp.1
    have hge : orderAt m T x ≤ nmOrd (geoTransformAlong m T) (p : Y) := by
      have hh := Prod.Lex.le_iff.mp hp.2
      change orderAt m T x < nmOrd (geoTransformAlong m T) (p : Y) ∨
        orderAt m T x = nmOrd (geoTransformAlong m T) (p : Y) ∧ _ at hh
      exact hh.elim (fun hl => hl.le) (fun hl => hl.1.le)
    have hpK := (hdict p).mpr ⟨hp.1,hle.antisymm hge⟩
    have hv := original_value_eq_actual_frozen_companion hn m h T hc x hx hq p hpK
    have hcomp := hp.2
    rw [hv,Prod.Lex.toLex_le_toLex] at hcomp
    exact ⟨hpK,Sum.Lex.inr_le_inr_iff.mp (hcomp.resolve_left (lt_irrefl _)).2⟩
  · intro hp
    refine ⟨((hdict p).mp hp.1).1,?_⟩
    rw [original_value_eq_actual_frozen_companion hn m h T hc x hx hq p hp.1,
      Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl,Sum.Lex.inr_le_inr_iff.mpr hp.2⟩

/-- The literal original transformed coefficient marked ideal of the fixed companion. -/
def coefficientStageAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :
    MarkedIdeal n (patchAt m T x) :=
  geoTransformAlong (barMarked (companionAt m T x)) (companionTailAt m T x)

/-- Actual well-formed coefficient geometry and the ENTIRE original companion cosupport. -/
theorem actual_frozen_coefficient_isWellFormed_and_cosupport (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) :
    (coefficientStageAt m T x).IsWellFormed ∧
      (coefficientStageAt m T x).cosupp = (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp := by
  obtain ⟨_,hK,hmax,hcanK,_⟩ := actual_frozen_companion_domain_and_cosupport hn m h T hc x hx hq
  have hdata := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k)
    (companionAt m T x) hK hmax hn (companionTailAt m T x) hcanK
  exact ⟨MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked _ hK.isWellFormed) _ hdata.1,hdata.2.2⟩

/-- Only original inputs construct actual finite holomorphic functions generating
EVERY nearby germ of the literal original coefficient ideal, in both directions. -/
theorem exists_actual_frozen_coefficient_generators (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x) :
    ∃ U : Set (patchAt m T x), IsOpen U ∧ p ∈ U ∧ ∃ (N : ℕ) (a : Fin N → patchAt m T x → ℂ),
      (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (a i) U) ∧
        ∀ z ∈ U,∀ g,(coefficientStageAt m T x).ideal.mem z g ↔
          IsInSpanAt (n := n) (· ∈ range a) z g :=
  (actual_frozen_coefficient_isWellFormed_and_cosupport hn m h T hc x hx hq).1.isCoherent p

/-- Real special/member/coefficient equations construct the literal original
special-top thresholds on the ENTIRE actual reference open, in all induction levels. -/
theorem isComplexAnalyticSubset_original_special_tail_superlevel_on_frozen_patch (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) (s : ℕ) :
    IsComplexAnalyticSubset (n := n)
      ((Subtype.val : patchAt m T x → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        toLex (orderAt m T x,toLex (Sum.inr
          ((toLex (s,(⊤ : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) :
            WithTop (ℕ ×ₗ WithTop (ValTy k))))) ≤ (invFamily hn (k+1)).inv m T y}) := by
  obtain ⟨_,hK,hmax,hcanK,_⟩ := actual_frozen_companion_domain_and_cosupport hn m h T hc x hx hq
  have hdata := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k)
    (companionAt m T x) hK hmax hn (companionTailAt m T x) hcanK
  rw [original_superlevel_pullback_eq_actual_frozen_companion hn m h T hc x hx hq]
  simp_rw [WithTop.coe_le_coe]
  have hA := HironakaStepOneSpecialAnalyticLoci.isComplexAnalyticSubset_stepOneInvM_top_superlevel
    (invFamily hn k) hn (companionAt m T x) hK.isWellFormed hK.one_le_d hmax
      (companionTailAt m T x) hdata.1 s
  rw [hdata.2.2] at hA
  exact hA

end
end Hironaka.HironakaOriginalFrozenCompanionPresentation
