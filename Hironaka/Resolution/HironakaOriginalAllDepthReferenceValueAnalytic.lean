/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCoherentStepOneHistoryYearIdeal
/-! Actual all-depth attained-original-full-reference-value analytic neighborhoods
from ONLY original domain and canonical history. The SAME already constructed
original invariant supplies actual local admissible-level geometry internally. Complete source-first blueprint
precedes Lean; arbitrary global thresholds/transformed semicoherence/scheduler OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalAllDepthReferenceValueAnalytic
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaOriginalFrozenCompanionPresentation HironakaOriginalCoherentSpecialResetIdeal
  HironakaMonomialAnalyticSuperlevels NonmonomialOrderLocal GeneralValue
  StepOneValue HomogenizedIdealAlong CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y : CMfd.{u} n}

/-- The genuine original open inclusion gives a true open image of every actual inner open. -/
def imageOpen (U : Opens X) (V : Opens U) : Opens X :=
  ⟨(Subtype.val : U → X) '' (V : Set U),U.isOpen.isOpenMap_subtype_val _ V.isOpen⟩

private theorem imageOpen_mem (U : Opens X) (V : Opens U) (q : U) :
    q ∈ V ↔ (q : X) ∈ imageOpen U V := by
  constructor
  · intro hq
    exact ⟨q,hq,rfl⟩
  · rintro ⟨p,hp,hpq⟩
    have he : p=q := Subtype.ext hpq
    exact he ▸ hp

private theorem imageOpen_le (U : Opens X) (V : Opens U) : imageOpen U V ≤ U :=
  fun _ ⟨q,_hq,hqx⟩ => hqx ▸ q.property

private def actual_imageOpen_diffeo (U : Opens X) (V : Opens U) :
    CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (imageOpen U V) :=
  MaxLocusLocal.nestedDiffeo U V (imageOpen U V) (imageOpen_mem U V) (imageOpen_le U V)

/-- Entire actual threshold equations pass to the SAME real original image open. -/
theorem isComplexAnalyticSubset_pullback_imageOpen (U : Opens X) (V : Opens U) (A : Set X)
    (hA : IsComplexAnalyticSubset (n := n) ((fun p : V => ((p : U) : X)) ⁻¹' A)) :
    IsComplexAnalyticSubset (n := n) ((Subtype.val : imageOpen U V → X) ⁻¹' A) := by
  have h := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (actual_imageOpen_diffeo U V).symm.contMDiff hA
  convert h using 1
  ext p
  rfl

/-- SAME actual zero-order original value and genuine whole monomial equations, including higher-first-entry points. -/
theorem isComplexAnalyticSubset_actual_zero_order_reference_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (x : Y)
    (ho : nmOrd (geoTransformAlong m T) x=0) :
    IsComplexAnalyticSubset (n := n) {y | y ∈ (geoTransformAlong m T).cosupp ∧
      (invFamily hn (k+1)).inv m T x ≤ (invFamily hn (k+1)).inv m T y} := by
  let lower := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {B : CMfd.{u} n}
    (S : BlowupTower A B) (z : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J S z
  have hv := genInv_of_nmOrd_eq_zero lower m T ho
  have ht := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  have hC := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hd.isWellFormed.isCoherent
    hd.isWellFormed.isClosedSubmanifold_N hd.one_le_d
  have hM := isComplexAnalyticSubset_canonical_monomial_superlevel hn m h T ht
    (MonomialCaseAlong.gammaAlong n (geoTransformAlong m T).N (geoTransformAlong m T).ideal
      (geoTransformAlong m T).E (geoTransformAlong m T).d x)
  have heq : {y | y ∈ (geoTransformAlong m T).cosupp ∧
      (invFamily hn (k+1)).inv m T x ≤ (invFamily hn (k+1)).inv m T y} =
    (geoTransformAlong m T).cosupp ∩ {y | y ∈ (geoTransformAlong m T).N ∧
      (invFamily hn (k+1)).inv m T x ≤ (invFamily hn (k+1)).inv m T y} := by
    ext y
    exact ⟨fun hy => ⟨hy.1,(geoTransformAlong m T).cosupp_subset_N hy.1,hy.2⟩,
      fun hy => ⟨hy.1,hy.2.2⟩⟩
  rw [heq]
  apply hC.inter
  change IsComplexAnalyticSubset (n := n) {y | y ∈ (geoTransformAlong m T).N ∧
    genInv lower m T x ≤ genInv lower m T y}
  rw [hv]
  exact hM

/-- The actual positive SPECIAL companion reference internally supplies the original ENTIRE true open analytic threshold. -/
theorem exists_analytic_actual_special_reference_open (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (hsp : IsSpecial (companionAt m T x) (companionTailAt m T x)
      (HironakaOriginalFrozenRecursiveLower.companionReferencePoint hn m h T hc x hx hq)) :
    ∃ U : Opens Y,x ∈ U ∧ IsComplexAnalyticSubset (n := n)
      ((Subtype.val : U → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        (invFamily hn (k+1)).inv m T x ≤ (invFamily hn (k+1)).inv m T y}) := by
  let p := HironakaOriginalFrozenRecursiveLower.companionReferencePoint hn m h T hc x hx hq
  obtain ⟨hpatch,hK,hmax,hcan,hdict⟩ := actual_frozen_companion_domain_and_cosupport hn m h T hc x hx hq
  have hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp :=
    (hdict p).mpr ⟨hx,rfl⟩
  have hv := original_value_eq_actual_frozen_companion hn m h T hc x hx hq p hp
  have hTop := original_stepOneSpecialResetIdeal_top_dictionary hn (companionAt m T x) hK hmax
    (companionTailAt m T x) hcan (level (companionAt m T x) (companionTailAt m T x) p)
  have hA := CodimOneSupport.isComplexAnalyticSubset_zeroLocus hTop.1
  rw [hTop.2] at hA
  have hval : Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (companionAt m T x)
      (companionTailAt m T x) p = toLex (level (companionAt m T x) (companionTailAt m T x) p,(⊤ : WithTop (ValTy k))) := by
    have hsp' : IsSpecial (companionAt m T x) (companionTailAt m T x) p := hsp
    simp [Seq.StepOneValueMasked.stepOneInvM,Seq.StepOneValueMasked.stepOneInvL,hsp']
  refine ⟨patchAt m T x,hpatch,?_⟩
  have hset := original_superlevel_pullback_eq_actual_frozen_companion hn m h T hc x hx hq
    ((toLex (level (companionAt m T x) (companionTailAt m T x) p,(⊤ : WithTop (ValTy k))) :
      ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k)))
  have hv' : (invFamily hn (k+1)).inv m T x =
      toLex (orderAt m T x,toLex (Sum.inr
        ((toLex (level (companionAt m T x) (companionTailAt m T x) p,(⊤ : WithTop (ValTy k))) :
          ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k))))) := by
    exact hv.trans (congrArg (fun v : ℕ ×ₗ WithTop (ValTy k) =>
      toLex (orderAt m T x,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy k)))))) hval)
  have hLift : IsComplexAnalyticSubset (n := n)
      ((Subtype.val : patchAt m T x → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong m T).cosupp ∧
          (toLex (orderAt m T x,toLex (Sum.inr
            ((toLex (level (companionAt m T x) (companionTailAt m T x) p,(⊤ : WithTop (ValTy k))) :
              ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k))))) : ValTy (k+1)) ≤
            (invFamily hn (k+1)).inv m T y}) := by
    exact hset.symm ▸ (by simpa only [WithTop.coe_le_coe] using hA)
  exact hv'.symm ▸ hLift


/-- ONLY the SAME original constructed invariant internally supplies a true smooth attained-reference superlevel open at EVERY dimension. -/
theorem exists_closedSubmanifold_original_reference_superlevel (hn : 0 < n)
    (d : ℕ) (m : MarkedIdeal n X) (h : IsInvDomain d m)
    (T : BlowupTower X Y) (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ U : Opens Y,x ∈ U ∧ IsClosedSubmanifold n
      ((Subtype.val : U → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        (invFamily hn d).inv m T x ≤ (invFamily hn d).inv m T y}) := by
  let R := invFamily.{u} hn d
  let f := R.inv m T
  have hbound := R.isInvValue.usc m h T hc x hx
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hbound
  let U : Opens Y := ⟨V,hVo⟩
  have hAdm := R.isInvValue.admissible m h T hc U (f x) (fun y hy hyU => hV hyU hy)
  have heq : ((Subtype.val : U → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧ f x ≤ f y}) =
      (Subtype.val : U → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧ f y=f x} := by
    ext q
    constructor
    · intro hq
      exact ⟨hq.1,(hV q.property hq.1).antisymm hq.2⟩
    · intro hq
      exact ⟨hq.1,by rw [hq.2]⟩
  exact ⟨U,hxV,heq.symm ▸ hAdm.1⟩

/-- Genuine original closed smooth reference geometry supplies entire analytic equations at EVERY original recursive depth. -/
theorem exists_analytic_original_reference_superlevel (hn : 0 < n)
    (d : ℕ) (m : MarkedIdeal n X) (h : IsInvDomain d m)
    (T : BlowupTower X Y) (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ U : Opens Y,x ∈ U ∧ IsComplexAnalyticSubset (n := n)
      ((Subtype.val : U → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        (invFamily hn d).inv m T x ≤ (invFamily hn d).inv m T y}) := by
  obtain ⟨U,hxU,hU⟩ := exists_closedSubmanifold_original_reference_superlevel hn d m h T hc x hx
  exact ⟨U,hxU,AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hU⟩

/-- ONLY original inputs internally construct the ACTUAL coherent vanishing ideal and its ENTIRE full-reference zero dictionary. -/
theorem exists_coherent_original_reference_superlevel (hn : 0 < n)
    (d : ℕ) (m : MarkedIdeal n X) (h : IsInvDomain d m)
    (T : BlowupTower X Y) (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ U : Opens Y,x ∈ U ∧
      let A := (Subtype.val : U → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        (invFamily hn d).inv m T x ≤ (invFamily hn d).inv m T y}
      (vanishingIdeal (n := n) A).IsCoherent ∧ (vanishingIdeal (n := n) A).zeroLocus = A := by
  obtain ⟨U,hxU,hU⟩ := exists_closedSubmanifold_original_reference_superlevel hn d m h T hc x hx
  exact ⟨U,hxU,VanishingIdealCoherent.isCoherent_vanishingIdeal hU,
    BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hU.1⟩

/-- The SAME actual whole full-reference ideal supplies finite genuine original holomorphic equations with BOTH nearby germ directions. -/
theorem exists_original_reference_superlevel_generators (hn : 0 < n)
    (d : ℕ) (m : MarkedIdeal n X) (h : IsInvDomain d m)
    (T : BlowupTower X Y) (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ U : Opens Y,x ∈ U ∧
      let A := (Subtype.val : U → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        (invFamily hn d).inv m T x ≤ (invFamily hn d).inv m T y}
      ∀ p : U,∃ V : Set U,IsOpen V ∧ p ∈ V ∧ ∃ (N : ℕ) (a : Fin N → U → ℂ),
        (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (a i) V) ∧
        (∀ z ∈ V,∀ g,(vanishingIdeal (n := n) A).mem z g ↔ IsInSpanAt (n := n) (· ∈ range a) z g) ∧
        ∀ z ∈ V,z ∈ A ↔ ∀ i,a i z=0 := by
  obtain ⟨U,hxU,hI,hZ⟩ := exists_coherent_original_reference_superlevel hn d m h T hc x hx
  refine ⟨U,hxU,?_⟩
  dsimp only
  intro p
  obtain ⟨V,hV,hpV,N,a,ha,hgen⟩ := hI p
  refine ⟨V,hV,hpV,N,a,ha,hgen,?_⟩
  intro z hz
  rw [← hZ]
  constructor
  · intro hzero i
    have hol : HolomorphicAt n (a i) z := eventually_of_mem (hV.mem_nhds hz)
      (fun q hq => (ha i q hq).mdifferentiableAt (hV.mem_nhds hq))
    apply hzero (a i)
    apply (hgen z hz (a i)).mpr
    exact isInSpanAt_of_eq_mul ⟨i,rfl⟩ hol (holomorphicAt_const 1)
      (Eventually.of_forall fun q => (one_mul (a i q)).symm)
  · intro hzero g hg
    obtain ⟨_,K,s,b,hs,_,he⟩ := (hgen z hz g).mp hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    obtain ⟨j,hj⟩ := hs i
    rw [← hj,hzero j,mul_zero]

end
end Hironaka.HironakaOriginalAllDepthReferenceValueAnalytic
