/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaDimensionThreeStepOneLowerAnalyticLoci

/-!
# Actual General3 nonspecial companion neighbourhoods

The literal constructed invFamily3 and actual canonical Seq tower internally
produce the real companion domain, maximal order and canonical restricted tail.
The whole actual companion patch has the exact original General3/companion
cosupport superlevel dictionary. At a genuinely nonspecial actual companion
point, one actual ambient open works for every lower threshold whose first
Step 1 entry is the point's current level. Special and higher-level boundary
descent, whole General3 analyticity and global G3 termination remain open.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u
namespace Hironaka.HironakaGeneralThreeNonspecialAnalyticLoci

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedIdealAlong StepOneValue StepOneRegime ResolutionInvariantSpec
  CanonicalCentres NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  GeneralValue CompanionRebase GeneralCanonicalTail

open Hironaka

noncomputable section

variable {n : ℕ} {X Y : CMfd.{u} n}

def orderAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) : ℕ :=
  nmOrd (geoTransformAlong m T) x

def runAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) : ℕ :=
  regimeRun (OrdRegime m (orderAt m T x)) T x

def maskAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :=
  ordMask (geoTransformAlong m (head T (runAt m T x))) (orderAt m T x)

def patchAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) : Opens Y :=
  openPreimage (tail T (runAt m T x)) (maskAt m T x)

def companionAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :
    MarkedIdeal n (maskAt m T x) :=
  compAt m (orderAt m T x) (head T (runAt m T x))

def companionTailAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y) :
    BlowupTower (CMfd.of (n := n) (maskAt m T x)) (CMfd.of (n := n) (patchAt m T x)) :=
  restrict (maskAt m T x) (tail T (runAt m T x))

def lowerPatchAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y)
    (p : patchAt m T x) : Opens (patchAt m T x) :=
  HironakaDimensionThreeStepOneLowerAnalyticLoci.patchAt
    (X := CMfd.of (n := n) (maskAt m T x)) (Y := CMfd.of (n := n) (patchAt m T x))
    (companionAt m T x) (companionTailAt m T x) p

def thresholdAt (m : MarkedIdeal n X) (T : BlowupTower X Y) (x : Y)
    (p : patchAt m T x) (α : WithTop (ValTy 2)) : ValTy 3 :=
  toLex (orderAt m T x, toLex (Sum.inr
    ((toLex (level (companionAt m T x) (companionTailAt m T x) p, α) : ℕ ×ₗ WithTop (ValTy 2)) :
      WithTop (ℕ ×ₗ WithTop (ValTy 2)))))

theorem actual_companion_domain_and_cosupport_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) :
    x ∈ patchAt m T x ∧ IsInvDomain 3 (companionAt m T x) ∧
      IsMaximalOrderAlong (companionAt m T x).N (companionAt m T x).ideal (companionAt m T x).d ∧
      IsCanonical (companionAt m T x)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) (companionAt m T x)) (companionTailAt m T x) ∧
      ∀ p : patchAt m T x,
        p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp ↔
          (p : Y) ∈ (geoTransformAlong m T).cosupp ∧ nmOrd (geoTransformAlong m T) (p : Y) = orderAt m T x := by
  let R := invFamily hn 2
  let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM R J S z
  have hM := StepOneSeq.isMaxOrderValue_stepOneInvM (k := 3) R hn
  have hT := (invFamily hn 3).isInvValue.isGeoTestTower_of_isCanonical h T hcan
  have hcanG : IsCanonical m (genInv lower m) T := hcan
  have hD := hasGenLowerData_of_isCanonical lower hM hn h T hT hcanG
  obtain ⟨hmask, hK, hmax, hcanK, _⟩ := hD x hx (orderAt m T x) rfl hq
  refine ⟨hmask, hK, hmax, hcanK, ?_⟩
  have hTW := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) R (companionAt m T x)
    hK hmax hn (companionTailAt m T x) hcanK).2.1
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail m T (runAt m T x)).mp hT
  intro p
  have hd := mem_cosupp_compAt_iff hn h hq (head T (runAt m T x)) (tail T (runAt m T x))
    hhead htail hTW p
  rw [← geoTransformAlong_head_tail m T (runAt m T x)] at hd
  exact hd

private theorem order_le_on_actual_companion_patch (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x) (hp : (p : Y) ∈ (geoTransformAlong m T).cosupp) :
    nmOrd (geoTransformAlong m T) (p : Y) ≤ orderAt m T x := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hT := (invFamily hn 3).isInvValue.isGeoTestTower_of_isCanonical h T hcan
  have hTW := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2)
    (companionAt m T x) hK hmax hn (companionTailAt m T x) hcanK).2.1
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail m T (runAt m T x)).mp hT
  have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T (runAt m T x)) hhead
  have hp' : (p : Y) ∈
      (geoTransformAlong (geoTransformAlong m (head T (runAt m T x))) (tail T (runAt m T x))).cosupp := by
    rw [← geoTransformAlong_head_tail]
    exact hp
  have hb := nmOrd_le_of_notMem (notMem_ordGe_of_mask hn hdom hq (maskAt m T x)
    (fun y _ hy => (mem_ordMask_iff hn hdom.isWellFormed hdom.isNonzeroAlongAt (orderAt m T x) y).mp hy)
    (tail T (runAt m T x)) htail hTW (p : Y) hp' p.2)
  rwa [← geoTransformAlong_head_tail] at hb

theorem general_value_eq_actual_fixed_companion (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp) :
    (invFamily hn 3).inv m T (p : Y) =
      toLex (orderAt m T x, toLex (Sum.inr
        ((Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) (companionAt m T x) (companionTailAt m T x) p :
          ℕ ×ₗ WithTop (ValTy 2)) : WithTop (ℕ ×ₗ WithTop (ValTy 2))))) := by
  let R := invFamily hn 2
  let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM R J S z
  have hM := StepOneSeq.isMaxOrderValue_stepOneInvM (k := 3) R hn
  have hT := (invFamily hn 3).isInvValue.isGeoTestTower_of_isCanonical h T hcan
  have hcanG : IsCanonical m (genInv lower m) T := hcan
  have hD := hasGenLowerData_of_isCanonical lower hM hn h T hT hcanG
  obtain ⟨_, _, _, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  exact genInv_eq_of_mem_cosupp_compAt hM hn h T hT hcanG hD hx rfl hq rfl hcanK p hp

theorem general_superlevel_pullback_eq_actual_companion_threshold (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (β : WithTop (ℕ ×ₗ WithTop (ValTy 2))) :
    (Subtype.val : patchAt m T x → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
      toLex (orderAt m T x, toLex (Sum.inr β)) ≤ (invFamily hn 3).inv m T y} =
      {p | p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp ∧
        β ≤ (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) (companionAt m T x) (companionTailAt m T x) p :
          WithTop (ℕ ×ₗ WithTop (ValTy 2)))} := by
  obtain ⟨_, _, _, _, hdict⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) J S z
  ext p
  constructor
  · intro hp
    have hle := order_le_on_actual_companion_patch hn m h T hcan x hx hq p hp.1
    have hge : orderAt m T x ≤ nmOrd (geoTransformAlong m T) (p : Y) := by
      have hc := Prod.Lex.le_iff.mp hp.2
      change orderAt m T x < nmOrd (geoTransformAlong m T) (p : Y) ∨
        orderAt m T x = nmOrd (geoTransformAlong m T) (p : Y) ∧ _ at hc
      exact hc.elim (fun hl => hl.le) (fun hl => hl.1.le)
    have hpK := (hdict p).mpr ⟨hp.1, hle.antisymm hge⟩
    have hv := general_value_eq_actual_fixed_companion hn m h T hcan x hx hq p hpK
    have hcomp := hp.2
    rw [hv, Prod.Lex.toLex_le_toLex] at hcomp
    refine ⟨hpK, ?_⟩
    exact Sum.Lex.inr_le_inr_iff.mp (hcomp.resolve_left (lt_irrefl _)).2
  · intro hp
    refine ⟨((hdict p).mp hp.1).1, ?_⟩
    rw [general_value_eq_actual_fixed_companion hn m h T hcan x hx hq p hp.1,
      Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl, Sum.Lex.inr_le_inr_iff.mpr hp.2⟩

section NestedOpen

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem exists_ambient_open_analytic_transfer (U : Opens M) (V : Opens U) :
    ∃ W : Opens M, (W : Set M) = (Subtype.val : U → M) '' (V : Set U) ∧
      ∀ A : Set M, IsComplexAnalyticSubset (n := n)
        ((fun z : V => ((z : U) : M)) ⁻¹' A) →
        IsComplexAnalyticSubset (n := n) ((Subtype.val : W → M) ⁻¹' A) := by
  let W : Opens M := ⟨(Subtype.val : U → M) '' (V : Set U),
    U.isOpen.isOpenMap_subtype_val _ V.isOpen⟩
  have hU : ∀ y : W, (y : M) ∈ U := by
    intro y
    obtain ⟨z, _, hz⟩ := y.2
    rw [← hz]
    exact z.2
  let f₀ : W → U := fun y => ⟨y, hU y⟩
  have hV : ∀ y : W, f₀ y ∈ V := by
    intro y
    obtain ⟨z, hzV, hz⟩ := y.2
    have he : f₀ y = z := Subtype.ext hz.symm
    rw [he]
    exact hzV
  let f : W → V := fun y => ⟨f₀ y, hV y⟩
  have hf₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f₀ :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val hU
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f :=
    BlowupRestrictOpen.contMDiff_opens_mk hf₀ hV
  refine ⟨W, rfl, ?_⟩
  intro A hA
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hA

end NestedOpen

private theorem actual_companion_lower_patch_contains_point (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hnot : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p) :
    p ∈ lowerPatchAt m T x p := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  exact (HironakaDimensionThreeStepOneLowerAnalyticLoci.actual_lower_domain_and_cosupport_dictionary
    (X := CMfd.of (n := n) (maskAt m T x)) (Y := CMfd.of (n := n) (patchAt m T x)) hn (companionAt m T x) hK hmax (companionTailAt m T x) hcanK p hp hnot).1

private theorem actual_nested_general_superlevel_analytic (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hnot : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (α : WithTop (ValTy 2)) : IsComplexAnalyticSubset (n := n)
      ((fun z : lowerPatchAt m T x p => ((z : patchAt m T x) : Y)) ⁻¹'
        {y | y ∈ (geoTransformAlong m T).cosupp ∧ thresholdAt m T x p α ≤ (invFamily hn 3).inv m T y}) := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  change IsComplexAnalyticSubset (n := n)
    ((Subtype.val : lowerPatchAt m T x p → patchAt m T x) ⁻¹'
      ((Subtype.val : patchAt m T x → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        toLex (orderAt m T x, toLex (Sum.inr
          ((toLex (level (companionAt m T x) (companionTailAt m T x) p, α) : ℕ ×ₗ WithTop (ValTy 2)) :
            WithTop (ℕ ×ₗ WithTop (ValTy 2))))) ≤ (invFamily hn 3).inv m T y}))
  rw [general_superlevel_pullback_eq_actual_companion_threshold hn m h T hcan x hx hq]
  simpa only [lowerPatchAt, WithTop.coe_le_coe] using
    HironakaDimensionThreeStepOneLowerAnalyticLoci.isComplexAnalyticSubset_stepOne_superlevel_on_actual_patch
      (X := CMfd.of (n := n) (maskAt m T x)) (Y := CMfd.of (n := n) (patchAt m T x)) hn (companionAt m T x) hK hmax (companionTailAt m T x) hcanK p hp hnot α

private theorem exists_ambient_neighbourhood_analytic_family
    {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {ι : Type*} (U : Opens M) (V : Opens U) (p : U) (hp : p ∈ V) (A : ι → Set M)
    (hA : ∀ i, IsComplexAnalyticSubset (n := n) ((fun z : V => ((z : U) : M)) ⁻¹' A i)) :
    ∃ W : Opens M, (p : M) ∈ W ∧ ∀ i,
      IsComplexAnalyticSubset (n := n) ((Subtype.val : W → M) ⁻¹' A i) := by
  obtain ⟨W, hW, ht⟩ := exists_ambient_open_analytic_transfer (n := n) U V
  refine ⟨W, ?_, fun i => ht (A i) (hA i)⟩
  change (p : M) ∈ (W : Set M)
  rw [hW]
  exact ⟨p, hp, rfl⟩

theorem exists_analytic_neighbourhood_general_three_superlevels (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (hsp : ∀ p : patchAt m T x, (p : Y) = x → ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p) :
    ∃ p : patchAt m T x, (p : Y) = x ∧ ∃ U : Opens Y, x ∈ U ∧
      ∀ α : WithTop (ValTy 2), IsComplexAnalyticSubset (n := n)
        ((Subtype.val : U → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
          thresholdAt m T x p α ≤ (invFamily hn 3).inv m T y}) := by
  obtain ⟨hxP, _, _, _, hdict⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  let p : patchAt m T x := ⟨x, hxP⟩
  have hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp :=
    (hdict p).mpr ⟨hx, rfl⟩
  have hnot := hsp p rfl
  let V := lowerPatchAt m T x p
  have hpV := actual_companion_lower_patch_contains_point hn m h T hcan x hx hq p hp hnot
  let L : WithTop (ValTy 2) → Set Y := fun α =>
    {y | y ∈ (geoTransformAlong m T).cosupp ∧ thresholdAt m T x p α ≤ (invFamily hn 3).inv m T y}
  have hinner : ∀ α, IsComplexAnalyticSubset (n := n)
      ((fun z : V => ((z : patchAt m T x) : Y)) ⁻¹' L α) :=
    fun α => actual_nested_general_superlevel_analytic hn m h T hcan x hx hq p hp hnot α
  obtain ⟨U, hU, htransfer⟩ := exists_ambient_neighbourhood_analytic_family (patchAt m T x) V p hpV L hinner
  exact ⟨p, rfl, U, hU, htransfer⟩

end
end Hironaka.HironakaGeneralThreeNonspecialAnalyticLoci
