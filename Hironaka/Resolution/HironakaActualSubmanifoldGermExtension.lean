/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.SubmanifoldIdealRestriction
import Hironaka.Support.SubmanifoldRestrictLeOriginalExact
import Hironaka.MarkedIdeal.SubmanifoldRestrictLe

/-!
# Genuine ambient extensions of actual intrinsic holomorphic germs

The native flattening atlas constructs literal local holomorphic retractions,
not an extension certificate. Whole vanishing ideals of arbitrary singular
intrinsic subsets and reflection of ambient restricted comparisons follow.
No controlled coefficient or canonical history equality is inferred.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSubmanifoldGermExtension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.RegularLocusDense IsManifold
  SubmanifoldChartedSpace SubmanifoldIdealRestriction RelativePrincipalizationSpan
  RestrictedIdealWeight
variable {n k : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

/-- The ACTUAL flattening atlas produces a true local ambient extension of EVERY intrinsic holomorphic germ. -/
theorem exists_ambient_holomorphic_germ (hk : k≤n)
    (hW : ∀ x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀ (p : W) (b : W → ℂ),HolomorphicAt k b p →
      ∃ B : X → ℂ,HolomorphicAt n B p.val ∧ B∘(Subtype.val : W → X)=ᶠ[nhds p] b := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro p b hb
  let F := FlatData.ofRegularAtDim (hW p.val p.property)
  let e := F.chart hk
  let G : X → ComplexModel k := fun y => coordinateProjection n k (F.flat (F.amb.val y))
  let R : X → W := fun y => e.symm (G y)
  have hpAmb : p.val∈F.ambSource := FlatData.mem_ambSource_ofRegularAtDim (hW p.val p.property)
  have hpSource : p∈e.source := hpAmb
  have hpCoord : G p.val∈e.target := e.map_source hpSource
  have hG (y : X) (hy : y∈F.ambSource) :
      ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G y := by
    have h1 : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ F.amb.val y :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas F.amb.property) hy.1
    have h2 : ContDiffAt ℂ ∞ (fun z => coordinateProjection n k (F.flat z)) (F.amb.val y) :=
      (coordinateProjection n k).contDiff.contDiffAt.comp _
        ((contDiffOn_of_differentiableOn_complex F.differentiableOn_flat
          F.flat.open_source).contDiffAt (F.flat.open_source.mem_nhds hy.2))
    exact h2.contMDiffAt.comp y h1
  have hemax : e∈maximalAtlas 𝓘(ℂ,ComplexModel k) ∞ W :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas hk hW F)
  have hR : ∀ᶠ y in nhds p.val,
      ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ R y := by
    filter_upwards [F.isOpen_ambSource.mem_nhds hpAmb,
      (hG p.val hpAmb).continuousAt.eventually (e.open_target.mem_nhds hpCoord)] with y hy hyCoord
    exact (contMDiffAt_symm_of_mem_maximalAtlas hemax hyCoord).comp y (hG y hy)
  have hRp : R p.val=p := e.left_inv hpSource
  have hbR : HolomorphicAt k b (R p.val) := by rwa [hRp]
  refine ⟨b∘R,hbR.comp_contMDiff hR,?_⟩
  filter_upwards [e.open_source.mem_nhds hpSource] with q hq
  change b (e.symm (e q))=b q
  rw [e.left_inv hq]

private theorem mem_vanishing_of_span {ℓ : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel ℓ) M] (V : Set M) {p : M} {b : M → ℂ}
    (hb : IsInSpanAt (n := ℓ) ((vanishingIdeal (n := ℓ) V).mem p) p b) :
    (vanishingIdeal (n := ℓ) V).mem p b := by
  obtain ⟨hhol,N,s,a,hs,_ha,he⟩ := hb
  refine ⟨hhol,?_⟩
  have hall : ∀ᶠ q in nhds p,∀ i : Fin N,q∈V→s i q=0 := eventually_all.mpr fun i => (hs i).2
  filter_upwards [he,hall] with q hq hqs hqV
  rw [hq]
  exact Finset.sum_eq_zero fun i _ => by rw [hqs i hqV,mul_zero]

/-- The ENTIRE independent original vanishing ideal of ANY singular intrinsic subset is its genuine ambient restriction. -/
theorem pullback_vanishing_image (hk : k≤n)
    (hW : ∀ x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀ V : Set W,GermIdeal.pullback (m := k) (Subtype.val : W → X)
      (vanishingIdeal (n := n) ((Subtype.val : W → X) '' V))=vanishingIdeal (n := k) V := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hval := contMDiff_val hk hW
  intro V
  apply GermIdeal.ext
  funext p b
  apply propext
  constructor
  · intro hb
    change IsInSpanAt (n := k) (fun c => ∃ a,
      (vanishingIdeal (n := n) ((Subtype.val : W → X) '' V)).mem p.val a ∧ c=a∘Subtype.val) p b at hb
    apply mem_vanishing_of_span V
    apply IsInSpanAt.mono ?_ hb
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨ha.1.comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt),?_⟩
    filter_upwards [continuous_subtype_val.continuousAt.eventually ha.2] with q hq hqV
    exact hq ⟨q,hqV,rfl⟩
  · intro hb
    obtain ⟨B,hB,hEq⟩ := exists_ambient_holomorphic_germ hk hW p b hb.1
    have hnear : {q : W | B q.val=b q ∧ (q∈V→b q=0)}∈nhds p := hEq.and hb.2
    obtain ⟨U,hU,hsub⟩ := (mem_nhds_subtype W p _).mp hnear
    have hBV : (vanishingIdeal (n := n) ((Subtype.val : W → X) '' V)).mem p.val B := by
      refine ⟨hB,?_⟩
      filter_upwards [hU] with y hy hyV
      obtain ⟨q,hqV,rfl⟩ := hyV
      obtain ⟨he,hv⟩ := hsub hy
      exact he.trans (hv hqV)
    have hBB : HolomorphicAt k (B∘(Subtype.val : W → X)) p :=
      hB.comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt)
    have hspan : IsInSpanAt (n := k) (fun c => ∃ a,
        (vanishingIdeal (n := n) ((Subtype.val : W → X) '' V)).mem p.val a ∧ c=a∘Subtype.val)
        p (B∘Subtype.val) := InvertibleIdealQuotient.isInSpanAt_self ⟨B,hBV,rfl⟩ hBB
    obtain ⟨_hhol,N,s,a,hs,ha,he⟩ := hspan
    exact ⟨hb.1,N,s,a,hs,ha,hEq.symm.trans he⟩

/-- Genuine coefficient extensions prove the formerly missing CONVERSE of ambient restricted ideal comparison. -/
theorem restrictLe_iff_restrictIdeal_le (hk : k≤n)
    (hW : ∀ x∈W,RegularAtDim (n := n) W x k) (𝔞 𝔟 : GermIdeal n X) (h𝔞 : 𝔞.IsCoherent) :
    letI := chartedSpace hk hW
    RestrictLe W 𝔞 𝔟 ↔ (restrictIdeal (k := k) (W := W) 𝔞).Le (restrictIdeal (k := k) (W := W) 𝔟) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hval := contMDiff_val hk hW
  constructor
  · exact SubmanifoldRestrictLe.restrictIdeal_le_of_restrictLe hval h𝔞
  · intro hle x hx g hg
    let p : W := ⟨x,hx⟩
    have hghol : HolomorphicAt n g x := SubmanifoldRestrictLe.holomorphicAt_of_mem_of_isCoherent h𝔞 hg
    have hgW : (restrictIdeal (k := k) (W := W) 𝔞).mem p (g∘Subtype.val) := by
      change IsInSpanAt (n := k) (fun s => ∃ a,𝔞.mem p.val a ∧ s=a∘Subtype.val)
        p (g∘Subtype.val)
      apply InvertibleIdealQuotient.isInSpanAt_self ⟨g,hg,rfl⟩
      exact hghol.comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt)
    obtain ⟨_hhol,N,s,a,hs,ha,he⟩ := hle p (g∘Subtype.val) hgW
    choose t ht hst using hs
    have hcoeff (i : Fin N) : ∃ A : X → ℂ,HolomorphicAt n A p.val ∧ A∘Subtype.val=ᶠ[nhds p] a i :=
      exists_ambient_holomorphic_germ hk hW p (a i) (ha i)
    choose A hA hAe using hcoeff
    refine ⟨N,t,A,ht,hA,?_⟩
    have heq : {q : W | g q.val=∑ i : Fin N,A i q.val*t i q.val}∈nhds p := by
      filter_upwards [he,eventually_all.mpr hAe] with q hq hqA
      simp only [Function.comp_apply] at hq hqA
      rw [hq]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← hqA i,hst i]
      rfl
    obtain ⟨U,hU,hsub⟩ := (mem_nhds_subtype W p _).mp heq
    filter_upwards [hU] with y hy hyW
    exact hsub (show (⟨y,hyW⟩ : W)∈(Subtype.val : W → X) ⁻¹' U from hy)

end
end Hironaka.HironakaActualSubmanifoldGermExtension
