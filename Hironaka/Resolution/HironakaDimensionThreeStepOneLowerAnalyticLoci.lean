/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaGeneralTwoAnalyticSuperlevels

/-!
# Actual dimension-three nonspecial Step 1 lower analytic patches

The real original domain and literal canonical Seq tower internally produce the
actual dimension-two lower datum, actual canonical restricted tail and complete
same-level cosupport dictionary. The whole actual Step 1 threshold on the entire
literal patch is exactly its fixed actual lower threshold and hence analytic.
The first threshold entry is the point's actual current level. Special and higher
level boundary descent, whole General3 and global G3 termination remain open.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u
namespace Hironaka.HironakaDimensionThreeStepOneLowerAnalyticLoci

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime
  StepOneCanonicalTail ResolutionInvariantSpec CanonicalCentres
  HironakaGeneralTwoAnalyticSuperlevels

open Hironaka

noncomputable section

variable {n : ℕ} {X Y : CMfd.{u} n}

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
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x) :
    x ∈ patchAt m T x ∧ IsInvDomain 2 (lowerAt m T x) ∧
      IsCanonical (lowerAt m T x) ((invFamily hn 2).inv (lowerAt m T x)) (lowerTailAt m T x) ∧
      ∀ p : patchAt m T x,
        p ∈ (geoTransformAlong (lowerAt m T x) (lowerTailAt m T x)).cosupp ↔
          (p : Y) ∈ (geoTransformAlong m T).cosupp ∧ level m T (p : Y) = level m T x := by
  let R := invFamily hn 2
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) R m h hmax hn T hcan
  have hbarcan := (Seq.StepOneBridge.isCanonical_iff (k := 3) R m h hmax hn T).mp hcan
  have hxbar : x ∈ (geoTransformAlong (barMarked m) T).cosupp := by rw [hb.2.2]; exact hx
  have hD := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := 3) m R
    h.isWellFormed h.one_le_d hn hmax h.dimLE T hb.1 hbarcan
  obtain ⟨hmask, hdom, hcanL, _⟩ := hD x hxbar hsp
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
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (lowerAt m T x) (lowerTailAt m T x)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m T (p : Y) =
      toLex (level m T x, (((invFamily hn 2).inv (lowerAt m T x) (lowerTailAt m T x) p : ValTy 2) :
        WithTop (ValTy 2))) := by
  let R := invFamily hn 2
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) R m h hmax hn T hcan
  have hbarcan := (Seq.StepOneBridge.isCanonical_iff (k := 3) R m h hmax hn T).mp hcan
  have hxbar : x ∈ (geoTransformAlong (barMarked m) T).cosupp := by rw [hb.2.2]; exact hx
  have hD : ∀ {V : CMfd.{u} n} (S : BlowupTower X V), S.length ≤ T.length →
      IsGeoTestTower (barMarked m) S →
      IsCanonical (barMarked m) (Seq.StepOneValueMasked.stepOneInvM R m) S →
      Seq.StepOneValueMasked.HasLowerDataL R m (lowerMarkedM m) S :=
    fun S _ hS hc => Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := 3) m R
      h.isWellFormed h.one_le_d hn hmax h.dimLE S hS hc
  exact Seq.StepOneCanonicalTail.stepOneInvM_eq_lower (k := 3) m R
    h.isWellFormed h.one_le_d hn hmax h.dimLE T hb.1 hbarcan hD hxbar ⟨rfl, hsp⟩ rfl p hp

private theorem level_le_on_actual_patch (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (p : patchAt m T x) : level m T (p : Y) ≤ level m T x := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) m h hmax hn T hcan
  have hxbar : x ∈ (geoTransformAlong (barMarked m) T).cosupp := by rw [hb.2.2]; exact hx
  obtain ⟨hreg, _⟩ := stepRegime_and_mem_cosupp_head m h.isWellFormed T hb.1 hxbar hsp
  have hl := level_le_of_mem_lowerMask m (fun W hW => h.isWellFormed.isSNCDivisor.1 W hW)
    (head T (runAt m T x)) (tail T (runAt m T x)) hreg.1 p.2
  rwa [head_append_tail] at hl

theorem stepOne_superlevel_pullback_eq_actual_lower_threshold (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (α : WithTop (ValTy 2)) :
    (Subtype.val : patchAt m T x → Y) ⁻¹'
      {y | y ∈ (geoTransformAlong m T).cosupp ∧
        toLex (level m T x, α) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m T y} =
      {p | p ∈ (geoTransformAlong (lowerAt m T x) (lowerTailAt m T x)).cosupp ∧
        α ≤ ((invFamily hn 2).inv (lowerAt m T x) (lowerTailAt m T x) p : WithTop (ValTy 2))} := by
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

theorem isComplexAnalyticSubset_stepOne_superlevel_on_actual_patch (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (α : WithTop (ValTy 2)) : IsComplexAnalyticSubset (n := n)
      ((Subtype.val : patchAt m T x → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong m T).cosupp ∧
          toLex (level m T x, α) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m T y}) := by
  obtain ⟨_, hdom, hcanL, _⟩ := actual_lower_domain_and_cosupport_dictionary hn m h hmax T hcan x hx hsp
  rw [stepOne_superlevel_pullback_eq_actual_lower_threshold hn m h hmax T hcan x hx hsp]
  cases α with
  | top =>
    have heq : {p | p ∈ (geoTransformAlong (lowerAt m T x) (lowerTailAt m T x)).cosupp ∧
        (⊤ : WithTop (ValTy 2)) ≤ ((invFamily hn 2).inv (lowerAt m T x) (lowerTailAt m T x) p : WithTop (ValTy 2))} = ∅ := by
      ext p
      simp
    rw [heq]
    exact isComplexAnalyticSubset_empty
  | coe α =>
    simpa only [WithTop.coe_le_coe] using
      isComplexAnalyticSubset_canonical_general_two_superlevel hn (lowerAt m T x) hdom
        (lowerTailAt m T x) hcanL α

theorem exists_analytic_neighbourhood_stepOne_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T x)
    (α : WithTop (ValTy 2)) :
    ∃ P : Opens Y, x ∈ P ∧ IsComplexAnalyticSubset (n := n)
      ((Subtype.val : P → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        toLex (level m T x, α) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m T y}) := by
  exact ⟨patchAt m T x, (actual_lower_domain_and_cosupport_dictionary hn m h hmax T hcan x hx hsp).1,
    isComplexAnalyticSubset_stepOne_superlevel_on_actual_patch hn m h hmax T hcan x hx hsp α⟩

end
end Hironaka.HironakaDimensionThreeStepOneLowerAnalyticLoci
