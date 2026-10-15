/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFrozenCompanionPresentation
/-! Actual all-dimensional recursive member/contact lower presentations and next
literal analytic threshold consumers, built only from original canonical inputs.
Complete source-first mathematics: hironaka-original-frozen-recursive-lower-extension.tex.
Whole arbitrary-lower global closure remains open. -/
set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u
namespace Hironaka.HironakaOriginalFrozenRecursiveLower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime
  StepOneCanonicalTail ResolutionInvariantSpec CanonicalCentres

noncomputable section

variable {n k : ℕ} {X Y : CMfd.{u} n}

abbrev runAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) : ℕ :=
  regimeRun (stepRegime m (level m T x)) T x

abbrev maskAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :=
  lowerMask m (level m T x) (head T (runAt m T x)) ((tail T (runAt m T x)).proj x)

abbrev patchAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) : Opens Y :=
  openPreimage (tail T (runAt m T x)) (maskAt m T x)

abbrev lowerAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :
    MarkedIdeal n (maskAt m T x) :=
  lowerMarkedM m (level m T x) (head T (runAt m T x)) ((tail T (runAt m T x)).proj x)

abbrev lowerTailAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :=
  restrict (maskAt m T x) (tail T (runAt m T x))

theorem actual_lower_domain_and_cosupport_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x) :
    x ∈ patchAt m T x ∧ IsInvDomain k (lowerAt m T x) ∧
      IsCanonical (lowerAt m T x) ((invFamily hn k).inv (lowerAt m T x)) (lowerTailAt m T x) ∧
      ∀ p : patchAt m T x,
        p ∈ (geoTransformAlong (lowerAt m T x) (lowerTailAt m T x)).cosupp ↔
          (p : Y) ∈ (geoTransformAlong m T).cosupp ∧ level m T (p : Y) = level m T x := by
  let R := invFamily hn k
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) R m h hmax hn T hcan
  have hbarcan := (Seq.StepOneBridge.isCanonical_iff (k := k+1) R m h hmax hn T).mp hcan
  have hxbar : x ∈ (geoTransformAlong (barMarked m) T).cosupp := by rw [hb.2.2]; exact hx
  have hD := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := k+1) m R
    h.isWellFormed h.one_le_d hn hmax h.dimLE T hb.1 hbarcan
  obtain ⟨hmask, hdom, hcanL, _⟩ := hD x hxbar hsp
  have hdom : IsInvDomain k (lowerAt m T x) := by simpa using hdom
  refine ⟨hmask, hdom, hcanL, ?_⟩
  obtain ⟨hreg, hhead⟩ := stepRegime_and_mem_cosupp_head m h.isWellFormed T hb.1 hxbar hsp
  have hsplit : (head T (runAt m T x)).append (tail T (runAt m T x)) = T := head_append_tail T _
  have hsplitT : IsGeoTestTower (barMarked m)
      ((head T (runAt m T x)).append (tail T (runAt m T x))) := by rw [hsplit]; exact hb.1
  have hTW := R.isInvValue.isGeoTestTower_of_isCanonical hdom _ hcanL
  intro p
  have hd := mem_cosupp_lowerMarkedM_iff m h.isWellFormed h.one_le_d hn hmax
    (head T (runAt m T x)) (tail T (runAt m T x)) hsplitT hhead hreg.1 hmask hTW p
  rw [hsplit, hb.2.2] at hd
  exact hd

theorem stepOneInvM_eq_actual_fixed_lower (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (lowerAt m T x) (lowerTailAt m T x)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m T (p : Y) =
      toLex (level m T x, (((invFamily hn k).inv (lowerAt m T x) (lowerTailAt m T x) p : ValTy k) :
        WithTop (ValTy k))) := by
  let R := invFamily hn k
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) R m h hmax hn T hcan
  have hbarcan := (Seq.StepOneBridge.isCanonical_iff (k := k+1) R m h hmax hn T).mp hcan
  have hxbar : x ∈ (geoTransformAlong (barMarked m) T).cosupp := by rw [hb.2.2]; exact hx
  have hD : ∀ {V : CMfd.{u} n} (S : BlowupTower X V), S.length ≤ T.length →
      IsGeoTestTower (barMarked m) S →
      IsCanonical (barMarked m) (Seq.StepOneValueMasked.stepOneInvM R m) S →
      Seq.StepOneValueMasked.HasLowerDataL R m (lowerMarkedM m) S :=
    fun S _ hS hc => Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := k+1) m R
      h.isWellFormed h.one_le_d hn hmax h.dimLE S hS hc
  exact Seq.StepOneCanonicalTail.stepOneInvM_eq_lower (k := k+1) m R
    h.isWellFormed h.one_le_d hn hmax h.dimLE T hb.1 hbarcan hD hxbar ⟨rfl, hsp⟩ rfl p hp

private theorem level_le_on_actual_patch (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (p : patchAt m T x) : level m T (p : Y) ≤ level m T x := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k) m h hmax hn T hcan
  have hxbar : x ∈ (geoTransformAlong (barMarked m) T).cosupp := by rw [hb.2.2]; exact hx
  obtain ⟨hreg, _⟩ := stepRegime_and_mem_cosupp_head m h.isWellFormed T hb.1 hxbar hsp
  have hl := level_le_of_mem_lowerMask m (fun W hW => h.isWellFormed.isSNCDivisor.1 W hW)
    (head T (runAt m T x)) (tail T (runAt m T x)) hreg.1 p.2
  rwa [head_append_tail] at hl

theorem stepOne_superlevel_pullback_eq_actual_lower_threshold (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (α : WithTop (ValTy k)) :
    (Subtype.val : patchAt m T x → Y) ⁻¹'
      {y | y ∈ (geoTransformAlong m T).cosupp ∧
        toLex (level m T x, α) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m T y} =
      {p | p ∈ (geoTransformAlong (lowerAt m T x) (lowerTailAt m T x)).cosupp ∧
        α ≤ ((invFamily hn k).inv (lowerAt m T x) (lowerTailAt m T x) p : WithTop (ValTy k))} := by
  obtain ⟨_, _, _, hdict⟩ := actual_lower_domain_and_cosupport_dictionary hn m h hmax T hcan x hx hsp
  ext p
  constructor
  · intro hp
    have hle := level_le_on_actual_patch hn m h hmax T hcan x hx hsp p
    have hge : level m T x ≤ level m T (p : Y) := by
      have hc := Prod.Lex.le_iff.mp hp.2
      rw [Seq.StepOneValueMasked.stepOneInvL_fst] at hc
      exact hc.elim (fun hl => hl.le) (fun hl => hl.1.le)
    have hpL := (hdict p).mpr ⟨hp.1, hle.antisymm hge⟩
    have hv := stepOneInvM_eq_actual_fixed_lower hn m h hmax T hcan x hx hsp p hpL
    refine ⟨hpL, ?_⟩
    have hcomp := hp.2
    rw [hv, Prod.Lex.toLex_le_toLex] at hcomp
    exact (hcomp.resolve_left (lt_irrefl _)).2
  · intro hp
    have hv := stepOneInvM_eq_actual_fixed_lower hn m h hmax T hcan x hx hsp p hp.1
    refine ⟨((hdict p).mp hp.1).1, ?_⟩
    rw [hv, Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl, hp.2⟩

/-- The actual final member/contact lower ideal has true local generators. -/
theorem exists_actual_recursive_lower_generators (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (p : patchAt m T x) :
    ∃ U : Set (patchAt m T x),IsOpen U ∧ p ∈ U ∧ ∃ (N : ℕ) (a : Fin N → patchAt m T x → ℂ),
      (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (a i) U) ∧
        ∀ z ∈ U,∀ g,(geoTransformAlong (lowerAt m T x) (lowerTailAt m T x)).ideal.mem z g ↔
          IsInSpanAt (n := n) (· ∈ range a) z g := by
  obtain ⟨_,hL,hcanL,_⟩ := actual_lower_domain_and_cosupport_dictionary hn m h hmax T hc x hx hsp
  have hTL := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hL _ hcanL
  exact (InvDomainTowerAlong.isInvDomain_geoTransformAlong hL _ hTL).isWellFormed.isCoherent p

/-- The ACTUAL next lower input internally supplies the positive analytic threshold,
without assuming lower-analyticity or a selected lower-domain certificate. -/
theorem isComplexAnalyticSubset_stepOne_next_positive_count_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (a b : ℕ) (ha : 1 ≤ a) :
    IsComplexAnalyticSubset (n := n)
      ((Subtype.val : patchAt m T x → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong m T).cosupp ∧
          toLex (level m T x,(HironakaOriginalCompanionChronologicalBoundaryAnalytic.positiveCanonicalCompanionCountThreshold k a b :
            WithTop (ValTy (k+1)))) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) m T y}) := by
  obtain ⟨_,hL,hcanL,_⟩ := actual_lower_domain_and_cosupport_dictionary hn m h hmax T hc x hx hsp
  rw [stepOne_superlevel_pullback_eq_actual_lower_threshold hn m h hmax T hc x hx hsp]
  simp_rw [WithTop.coe_le_coe]
  exact HironakaOriginalCompanionChronologicalBoundaryAnalytic.isComplexAnalyticSubset_canonical_positive_companion_count_superlevel
    hn (lowerAt m T x) hL (lowerTailAt m T x) hcanL a b ha

open HironakaOriginalFrozenCompanionPresentation (companionAt companionTailAt orderAt)

/-- The original positive cosupport point has an internally constructed actual
lift to the true frozen companion open. -/
def companionReferencePoint (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) :
    HironakaOriginalFrozenCompanionPresentation.patchAt m T x :=
  ⟨x,(HironakaOriginalFrozenCompanionPresentation.actual_frozen_companion_domain_and_cosupport (k := k) hn m h T hc x hx hq).1⟩

set_option maxHeartbeats 1200000 in
/-- Only original data construct the next recursive literal full-value analytic
threshold on the ENTIRE real member/contact reference open. -/
theorem isComplexAnalyticSubset_original_next_positive_count_superlevel_on_recursive_patch (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+2) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+2)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (hsp : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x)
      (companionReferencePoint (k := k+1) hn m h T hc x hx hq)) (a b : ℕ) (ha : 1 ≤ a) :
    let p := companionReferencePoint (k := k+1) hn m h T hc x hx hq
    p ∈ patchAt (companionAt m T x) (companionTailAt m T x) p ∧
    IsComplexAnalyticSubset (n := n)
      ((fun z : patchAt (companionAt m T x) (companionTailAt m T x) p =>
        ((z : HironakaOriginalFrozenCompanionPresentation.patchAt m T x) : Y)) ⁻¹'
        {y | y ∈ (geoTransformAlong m T).cosupp ∧
          toLex (orderAt m T x,toLex (Sum.inr
            ((toLex (level (companionAt m T x) (companionTailAt m T x) p,
              (HironakaOriginalCompanionChronologicalBoundaryAnalytic.positiveCanonicalCompanionCountThreshold k a b :
                WithTop (ValTy (k+1)))) : ℕ ×ₗ WithTop (ValTy (k+1))) :
                  WithTop (ℕ ×ₗ WithTop (ValTy (k+1)))))) ≤ (invFamily hn (k+2)).inv m T y}) := by
  let p := companionReferencePoint (k := k+1) hn m h T hc x hx hq
  obtain ⟨_,hK,hmax,hcanK,hdict⟩ :=
    HironakaOriginalFrozenCompanionPresentation.actual_frozen_companion_domain_and_cosupport (k := k+1) hn m h T hc x hx hq
  have hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp :=
    (hdict p).mpr ⟨hx,rfl⟩
  refine ⟨(actual_lower_domain_and_cosupport_dictionary hn _ hK hmax _ hcanK p hp hsp).1,?_⟩
  have hA := isComplexAnalyticSubset_stepOne_next_positive_count_superlevel
    hn (companionAt m T x) hK hmax (companionTailAt m T x) hcanK p hp hsp a b ha
  convert hA using 1
  ext z
  have hd := Set.ext_iff.mp
    (HironakaOriginalFrozenCompanionPresentation.original_superlevel_pullback_eq_actual_frozen_companion
      hn m h T hc x hx hq
        ((toLex (level (companionAt m T x) (companionTailAt m T x) p,
          (HironakaOriginalCompanionChronologicalBoundaryAnalytic.positiveCanonicalCompanionCountThreshold k a b :
            WithTop (ValTy (k+1)))) : ℕ ×ₗ WithTop (ValTy (k+1))) :
              WithTop (ℕ ×ₗ WithTop (ValTy (k+1)))))
    (z : HironakaOriginalFrozenCompanionPresentation.patchAt m T x)
  simpa only [mem_preimage,mem_ofPred_eq,WithTop.coe_le_coe] using hd

end
end Hironaka.HironakaOriginalFrozenRecursiveLower
