/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAnalyticHSGenericDenominator
import Hironaka.Resolution.HironakaSmoothCentreRealDomainOriginalCentreOpen
import Hironaka.Analytic.ThinDimensionDrop
/-! Actual centre-space analytic exceptions for all intrinsic HS orders.
The true denominator is pulled back before thinness or any HS claim. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaOriginalCentreAnalyticHSException
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaOriginalAnalyticHSGenericDenominator HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreRelativeIdeal HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainOriginalCentreOpen BlowupFlatCoordinates
  AnalyticSubsetOpens AnalyticDimensionBasics RegularPointDimension
  HironakaRelativeNormalIdeal HironakaSmoothCentreCoherentDomain
  HironakaHolomorphicJetChartInvariance

variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- The literal denominator zero subset of the genuine original centre trace. -/
def centreDenominatorException (C : Set M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (g : ComplexModel d → ℂ) (D : Opens M) : Set D :=
  {p | (p : M) ∈ C ∧ g (tangentProjection d t
    (Φ.toFun (chartAt (ComplexModel (d+t)) x (p : M))))=0}

/-- A genuine nonzero origin germ gives a true analytic thin exception on an
actual original-centre window, with strict local dimension drop. -/
theorem exists_actual_centre_denominator_thin_window
    (C : Set M) (hC : IsComplexAnalyticSubset (n := d+t) C) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0)
    (hflat : ∀ {y : M},y ∈ (chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d))
    (W : Opens (ComplexModel d)) (h0W : (0 : ComplexModel d) ∈ W)
    (g : ComplexModel d → ℂ) (hg : ∀ a ∈ W,HolomorphicAt d g a)
    (hgnz : (g : Germ (𝓝 (0 : ComplexModel d)) ℂ) ≠ 0) :
    ∃ D : Opens M,x ∈ D ∧
      IsComplexAnalyticSubset (n := d+t) (centreDenominatorException C x Φ g D) ∧
      (∀ O : Set D,IsOpen O → O ∩ ((↑) ⁻¹' C : Set D) ⊆ centreDenominatorException C x Φ g D →
        O ∩ ((↑) ⁻¹' C : Set D)=∅) ∧
      (∀ p k,RegularAtDim (n := d+t) (centreDenominatorException C x Φ g D) p k → k<d) ∧
      ∀ p : D,(p : M) ∈ C → ∃ a ∈ W,
        actualFlatteningInverseMap x Φ (tangentInclusion d t a)=(p : M) ∧
        tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x (p : M)))=a := by
  have hV : IsOpen ((W : Set (ComplexModel d)) ∩ (tangentInclusion d t) ⁻¹' Φ.target) :=
    W.isOpen.inter (Φ.isOpen_target.preimage (tangentInclusion d t).continuous)
  have h0V : (0 : ComplexModel d) ∈ (W : Set (ComplexModel d)) ∩ (tangentInclusion d t) ⁻¹' Φ.target :=
    ⟨h0W,by simpa only [mem_preimage,map_zero] using actualFlattening_target_zero_mem x Φ h0⟩
  obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let B : Set (ComplexModel d) := Metric.ball 0 ε
  have hBW : B ⊆ W := fun a ha => (hεV ha).1
  have hpoint : ∀ a ∈ B,tangentInclusion d t a ∈ Φ.target := fun a ha => (hεV ha).2
  let D : Opens M := ⟨originalCentreBaseOpen x Φ B,isOpen_originalCentreBaseOpen x Φ B Metric.isOpen_ball⟩
  have hxD : x ∈ D := by
    refine ⟨⟨mem_chart_source _ _,Φ.center_mem_source⟩,?_⟩
    change tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x x)) ∈ B
    rw [h0,map_zero]
    exact Metric.mem_ball_self hε
  let f : ComplexModel d → M := fun a => actualFlatteningInverseMap x Φ (tangentInclusion d t a)
  let b : M → ComplexModel d := fun p => tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x p))
  have himage : C ∩ (D : Set M)=f '' B :=
    originalCentreBaseOpen_centre_eq_image C x Φ hsrc hflat B hpoint
  have hfb : ∀ a ∈ B,b (f a)=a := by
    intro a ha
    obtain ⟨_,hF⟩ := flatInverse_mem Φ (hpoint a ha) hsrc
    change tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x
      (actualFlatteningInverseMap x Φ (tangentInclusion d t a))))=a
    simp only [actualFlatteningInverseMap]
    rw [hF,tangentProjection_tangentInclusion]
  have hmem : ∀ a ∈ B,f a ∈ C ∩ (D : Set M) := fun a ha =>
    himage.symm ▸ (show f a ∈ f '' B from ⟨a,ha,rfl⟩)
  have hparam : ∀ p : D,(p : M) ∈ C → ∃ a ∈ B,f a=(p : M) := by
    intro p hp
    have hpim : (p : M) ∈ f '' B := by rw [← himage]; exact ⟨hp,p.property⟩
    exact hpim
  have hcont : ContinuousOn f B := by
    intro a ha
    exact (((actualFlatteningInverseMap_mdifferentiable x Φ hsrc _ (hpoint a ha)).continuousAt).comp
      (tangentInclusion d t).continuous.continuousAt).continuousWithinAt
  have hhol : ∀ p : D,HolomorphicAt (d+t) (fun p : D => g (b p)) p := by
    intro p
    change HolomorphicAt (d+t) ((fun y : M => g (b y)) ∘ Subtype.val) p
    apply (holomorphicAt_comp_val_iff D).mpr
    apply holomorphicAt_comp_flat Φ (G := fun u => g (tangentProjection d t u)) p.property.1
    have hbase := (hg (b p) (hBW p.property.2)).mono fun _ hz => hz.differentiableAt
    have hev := ((tangentProjection d t).continuous.tendsto
      (Φ.toFun (chartAt (ComplexModel (d+t)) x (p : M)))).eventually hbase
    exact hev.mono fun u hu => hu.comp u (tangentProjection d t).differentiableAt
  have hCD : IsComplexAnalyticSubset (n := d+t) ((↑) ⁻¹' C : Set D) :=
    isComplexAnalyticSubset_preimage_val hC D
  have hE : IsComplexAnalyticSubset (n := d+t) (centreDenominatorException C x Φ g D) :=
    hCD.inter (actual_holomorphic_zero_analytic (fun p : D => g (b p)) hhol)
  have hthin : ∀ O : Set D,IsOpen O → O ∩ ((↑) ⁻¹' C : Set D) ⊆ centreDenominatorException C x Φ g D →
      O ∩ ((↑) ⁻¹' C : Set D)=∅ := by
    intro O hO hOE
    apply eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hpO,hpC⟩
    let OM : Set M := (Subtype.val : D → M) '' O
    have hOM : IsOpen OM := D.isOpen.isOpenMap_subtype_val _ hO
    let V : Set (ComplexModel d) := B ∩ f ⁻¹' OM
    have hVo : IsOpen V := hcont.isOpen_inter_preimage Metric.isOpen_ball hOM
    obtain ⟨a,ha,hap⟩ := hparam p hpC
    have hVne : V.Nonempty := ⟨a,ha,by change f a ∈ OM; rw [hap]; exact ⟨p,hpO,rfl⟩⟩
    have hzero : ∀ a ∈ V,g a=0 := by
      intro a ha
      obtain ⟨q,hqO,hq⟩ := ha.2
      have hqC : (q : M) ∈ C := hq ▸ (hmem a ha.1).1
      have hz := (hOE ⟨hqO,hqC⟩).2
      change g (b q)=0 at hz
      rw [hq,hfb a ha.1] at hz
      exact hz
    have hdiff : DifferentiableOn ℂ g B := fun a ha => (hg a (hBW ha)).mdifferentiableAt.differentiableAt.differentiableWithinAt
    have hzeroB : ∀ a ∈ B,g a=0 :=
      eqOn_zero_of_isOpen_convex Metric.isOpen_ball (convex_ball 0 ε) hdiff hVo
        inter_subset_left hVne hzero
    apply hgnz
    apply Germ.coe_eq.mpr
    exact Filter.eventually_of_mem (Metric.ball_mem_nhds _ hε) hzeroB
  have hdim : DimLE (n := d+t) ((↑) ⁻¹' C : Set D) d := by
    intro p k hpk
    have hreg : RegularAtDim (n := d+t) ((↑) ⁻¹' C : Set D) p d :=
      regularAtDim_preimage_val_iff.mpr
        (Hironaka.RegularPatchNeighborhood.regularAtDim_of_flattening (Nat.le_add_right d t)
          Φ hflat hpk.2.1 p.property.1.1 p.property.1.2)
    exact Nat.le_of_eq (eq_of_regularAtDim hpk hreg)
  refine ⟨D,hxD,hE,hthin,?_,?_⟩
  · intro p k hp
    exact ThinDimensionDrop.lt_of_regularAtDim_of_thin hCD (fun _ hp => hp.1) hthin hdim hp
  · intro p hp
    obtain ⟨a,ha,hap⟩ := hparam p hp
    exact ⟨a,hBW ha,hap,by rw [← hap]; exact hfb a ha⟩

/-- ONLY original analytic regular-centre geometry and coherence produce an
actual strictly smaller analytic exception with ALL existing intrinsic HS orders
constant on its ENTIRE genuine centre complement. -/
theorem exists_original_centre_analytic_exception_intrinsic_hs
    (C : Set M) (hC : IsComplexAnalyticSubset (n := d+t) C) (x : M)
    (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ (D : Opens M) (hxD : x ∈ D) (E : Set D),
      IsComplexAnalyticSubset (n := d+t) E ∧ E ⊆ ((↑) ⁻¹' C : Set D) ∧
      (∀ p k,RegularAtDim (n := d+t) E p k → k<d) ∧
      (⟨x,hxD⟩ : D) ∈ closure (((↑) ⁻¹' C : Set D) \ E) ∧
      ∃ h : ℕ → ℕ,∀ p : D,(p : M) ∈ C → p ∉ E →
        ∀ ℓ,hilbertSamuelAt A (p : M) ℓ=h ℓ := by
  obtain ⟨Φ,hsrc,h0,hflat,W,h0W,g,hg,hgnz,_hzero,r,hhs⟩ :=
    exists_original_analytic_denominator_intrinsic_hs C x hreg A hA
  obtain ⟨D,hxD,hE,hthin,hdim,hparam⟩ :=
    exists_actual_centre_denominator_thin_window C hC x Φ hsrc h0 hflat W h0W g hg hgnz
  let E := centreDenominatorException C x Φ g D
  refine ⟨D,hxD,E,hE,(fun _ hp => hp.1),hdim,?_,?_,?_⟩
  · apply mem_closure_iff_nhds.mpr
    intro V hV
    obtain ⟨O,hOV,hOo,hxO⟩ := mem_nhds_iff.mp hV
    by_contra hn
    have hOE : O ∩ ((↑) ⁻¹' C : Set D) ⊆ E := by
      intro p hp
      by_contra hpE
      exact hn ⟨p,hOV hp.1,hp.2,hpE⟩
    have he := hthin O hOo hOE
    have hx : (⟨x,hxD⟩ : D) ∈ O ∩ ((↑) ⁻¹' C : Set D) := ⟨hxO,hreg.2.1⟩
    rw [he] at hx
    exact hx
  · exact fun ℓ => ∑ q : Fin (ℓ+1),r q.val*(d+ℓ-q.val).choose d
  · intro p hpC hpE ℓ
    obtain ⟨a,ha,hap,hpa⟩ := hparam p hpC
    have hga : g a ≠ 0 := by
      intro hz
      exact hpE ⟨hpC,by rw [hpa]; exact hz⟩
    simpa only [hap] using (hhs a ha hga).2 ℓ

end
end Hironaka.HironakaOriginalCentreAnalyticHSException
