/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCentreAnalyticHSException
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.ConstantRankImage
/-! One actual smaller-dimensional exception for finite simultaneous original
intrinsic HS profiles. Fixed-input geometry; transformed-chain drivers stay open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaOriginalFiniteSimultaneousHSException
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaOriginalCentreAnalyticHSException HironakaOriginalAnalyticHSGenericDenominator
  HironakaHolomorphicJetChartInvariance HironakaSmoothCentreCoherentDomain
  HironakaRelativeNormalIdeal AnalyticSubsetOpens AnalyticSubsetPreimage
  AnalyticDimensionBasics RegularPointDimension

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual open inclusions preserve analytic exceptions and genuine centre thinness. -/
theorem actual_open_inclusion_analytic_thin (C : Set M) {D U : Opens M} (hDU : D ≤ U)
    (E : Set U) (hE : IsComplexAnalyticSubset (n := n) E)
    (hthin : ∀ O : Set U,IsOpen O → O ∩ ((↑) ⁻¹' C : Set U) ⊆ E → O ∩ ((↑) ⁻¹' C : Set U)=∅) :
    IsComplexAnalyticSubset (n := n) ((Opens.inclusion hDU) ⁻¹' E) ∧
    ∀ O : Set D,IsOpen O → O ∩ ((↑) ⁻¹' C : Set D) ⊆ (Opens.inclusion hDU) ⁻¹' E →
      O ∩ ((↑) ⁻¹' C : Set D)=∅ := by
  refine ⟨isComplexAnalyticSubset_preimage (contMDiff_inclusion hDU) hE,?_⟩
  intro O hO hOE
  let OM : Set M := (Subtype.val : D → M) '' O
  have hOM : IsOpen OM := D.isOpen.isOpenMap_subtype_val _ hO
  let OU : Set U := (Subtype.val : U → M) ⁻¹' OM
  have hOU : IsOpen OU := hOM.preimage continuous_subtype_val
  have hOUE : OU ∩ ((↑) ⁻¹' C : Set U) ⊆ E := by
    rintro p ⟨hpO,hpC⟩
    obtain ⟨q,hqO,hqp⟩ := hpO
    have hqC : (q : M) ∈ C := hqp.symm ▸ hpC
    have he := hOE ⟨hqO,hqC⟩
    have hqp' : Opens.inclusion hDU q=p := Subtype.ext hqp
    exact hqp' ▸ he
  have he := hthin OU hOU hOUE
  apply eq_empty_iff_forall_notMem.mpr
  rintro p ⟨hpO,hpC⟩
  have hh : Opens.inclusion hDU p ∈ OU ∩ ((↑) ⁻¹' C : Set U) := ⟨⟨p,hpO,rfl⟩,hpC⟩
  rw [he] at hh
  exact hh

private theorem single_actual_thin_hs_window {d t : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    (C : Set X) (hC : IsComplexAnalyticSubset (n := d+t) C) (x : X)
    (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) X) (hA : A.IsCoherent) :
    ∃ (D : Opens X),x ∈ D ∧ ∃ E : Set D,
      IsComplexAnalyticSubset (n := d+t) E ∧ E ⊆ ((↑) ⁻¹' C : Set D) ∧
      (∀ O : Set D,IsOpen O → O ∩ ((↑) ⁻¹' C : Set D) ⊆ E → O ∩ ((↑) ⁻¹' C : Set D)=∅) ∧
      ∃ h : ℕ → ℕ,∀ p : D,(p : X) ∈ C → p ∉ E → ∀ ℓ,hilbertSamuelAt A (p : X) ℓ=h ℓ := by
  obtain ⟨Φ,hsrc,h0,hflat,W,h0W,g,hg,hgnz,_hzero,r,hhs⟩ :=
    exists_original_analytic_denominator_intrinsic_hs C x hreg A hA
  obtain ⟨D,hxD,hE,hthin,_hdim,hparam⟩ :=
    exists_actual_centre_denominator_thin_window C hC x Φ hsrc h0 hflat W h0W g hg hgnz
  refine ⟨D,hxD,centreDenominatorException C x Φ g D,hE,(fun _ hp => hp.1),hthin,
    (fun ℓ => ∑ q : Fin (ℓ+1),r q.val*(d+ℓ-q.val).choose d),?_⟩
  intro p hpC hpE ℓ
  obtain ⟨a,ha,hap,hpa⟩ := hparam p hpC
  have hga : g a ≠ 0 := by
    intro hz
    exact hpE ⟨hpC,by rw [hpa]; exact hz⟩
  simpa only [hap] using (hhs a ha hga).2 ℓ

/-- ONLY original analytic regular-centre geometry and genuine finite original
coherence give ONE actual thin exception for ALL positions and ALL HS orders. -/
theorem exists_original_finite_simultaneous_intrinsic_hs_exception
    {d t : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    {ι : Type*} [Fintype ι]
    (C : Set X) (hC : IsComplexAnalyticSubset (n := d+t) C) (x : X)
    (hreg : RegularAtDim (n := d+t) C x d)
    (A : ι → GermIdeal (d+t) X) (hA : ∀ i,(A i).IsCoherent) :
    ∃ (D : Opens X) (hxD : x ∈ D) (E : Set D),
      IsComplexAnalyticSubset (n := d+t) E ∧ E ⊆ ((↑) ⁻¹' C : Set D) ∧
      (∀ O : Set D,IsOpen O → O ∩ ((↑) ⁻¹' C : Set D) ⊆ E → O ∩ ((↑) ⁻¹' C : Set D)=∅) ∧
      (∀ p k,RegularAtDim (n := d+t) E p k → k<d) ∧
      (⟨x,hxD⟩ : D) ∈ closure (((↑) ⁻¹' C : Set D) \ E) ∧
      ∃ h : ι → ℕ → ℕ,∀ i,∀ p : D,(p : X) ∈ C → p ∉ E →
        ∀ ℓ,hilbertSamuelAt (A i) (p : X) ℓ=h i ℓ := by
  choose U hxU E hE hEC hthin profile hprofile using
    fun i => single_actual_thin_hs_window C hC x hreg (A i) (hA i)
  obtain ⟨V,hVreg,hVo,hxV⟩ := mem_nhds_iff.mp
    (Hironaka.RegularPatchNeighborhood.eventually_regularAtDim hreg)
  let D : Opens X := ⟨V ∩ ⋂ i,(U i : Set X),hVo.inter (isOpen_iInter_of_finite fun i => (U i).isOpen)⟩
  have hxD : x ∈ D := ⟨hxV,mem_iInter.mpr hxU⟩
  have hDU : ∀ i,D ≤ U i := fun i p hp => mem_iInter.mp hp.2 i
  let F : ι → Set D := fun i => (Opens.inclusion (hDU i)) ⁻¹' E i
  have hF : ∀ i,IsComplexAnalyticSubset (n := d+t) (F i) :=
    fun i => (actual_open_inclusion_analytic_thin C (hDU i) (E i) (hE i) (hthin i)).1
  have hFT : ∀ i,∀ O : Set D,IsOpen O → O ∩ ((↑) ⁻¹' C : Set D) ⊆ F i →
      O ∩ ((↑) ⁻¹' C : Set D)=∅ :=
    fun i => (actual_open_inclusion_analytic_thin C (hDU i) (E i) (hE i) (hthin i)).2
  let B : Set D := ⋃ i,F i
  have hB : IsComplexAnalyticSubset (n := d+t) B := by
    simpa only [Finset.mem_univ,iUnion_true] using
      ConstantRankImage.isComplexAnalyticSubset_biUnion (Finset.univ : Finset ι) (fun i _ => hF i)
  have hBC : B ⊆ ((↑) ⁻¹' C : Set D) := by
    intro p hp
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    exact hEC i hi
  have hBT : ∀ O : Set D,IsOpen O → O ∩ ((↑) ⁻¹' C : Set D) ⊆ B →
      O ∩ ((↑) ⁻¹' C : Set D)=∅ := by
    intro O hO hOB
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have havoid : ∀ i ∈ (Finset.univ : Finset ι),∀ W : Set D,IsOpen W → W ⊆ univ →
        (W ∩ ((↑) ⁻¹' C : Set D)).Nonempty → ∃ y ∈ W ∩ ((↑) ⁻¹' C : Set D),y ∉ F i := by
      intro i _ W hW _ hWne
      by_contra hn
      have hWF : W ∩ ((↑) ⁻¹' C : Set D) ⊆ F i := by
        intro y hy
        by_contra hyF
        exact hn ⟨y,hy,hyF⟩
      exact hWne.ne_empty (hFT i W hW hWF)
    obtain ⟨O',_hO',hO'O,hne,hmiss⟩ := ThinDimensionDrop.exists_isOpen_avoid
      (Finset.univ : Finset ι) havoid (fun i _ => by simpa only [sdiff_eq,univ_inter] using (hF i).isClosed.isOpen_compl)
      hO (subset_univ O) ⟨p,hp⟩
    obtain ⟨y,hyO',hyC⟩ := hne
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hOB ⟨hO'O hyO',hyC⟩)
    have hh : y ∈ O' ∩ F i := ⟨hyO',hi⟩
    rw [hmiss i (Finset.mem_univ i)] at hh
    exact hh
  have hCD := isComplexAnalyticSubset_preimage_val hC D
  have hdim : DimLE (n := d+t) ((↑) ⁻¹' C : Set D) d := by
    intro p k hpk
    have hpd : RegularAtDim (n := d+t) ((↑) ⁻¹' C : Set D) p d :=
      regularAtDim_preimage_val_iff.mpr (hVreg p.property.1 hpk.2.1)
    exact Nat.le_of_eq (eq_of_regularAtDim hpk hpd)
  refine ⟨D,hxD,B,hB,hBC,hBT,?_,?_,profile,?_⟩
  · intro p k hp
    exact ThinDimensionDrop.lt_of_regularAtDim_of_thin hCD hBC hBT hdim hp
  · apply mem_closure_iff_nhds.mpr
    intro W hW
    obtain ⟨O,hOW,hOo,hxO⟩ := mem_nhds_iff.mp hW
    by_contra hn
    have hOB : O ∩ ((↑) ⁻¹' C : Set D) ⊆ B := by
      intro p hp
      by_contra hpB
      exact hn ⟨p,hOW hp.1,hp.2,hpB⟩
    have he := hBT O hOo hOB
    have hh : (⟨x,hxD⟩ : D) ∈ O ∩ ((↑) ⁻¹' C : Set D) := ⟨hxO,hreg.2.1⟩
    rw [he] at hh
    exact hh
  · intro i p hpC hpB ℓ
    have hpE : Opens.inclusion (hDU i) p ∉ E i := fun hp => hpB (mem_iUnion.mpr ⟨i,hp⟩)
    exact hprofile i (Opens.inclusion (hDU i) p) hpC hpE ℓ

/-- Actual reduced ideals of a finite original analytic chain supply ALL genuine
coherence inputs internally; no prescribed profiles or chain models are needed. -/
theorem exists_original_finite_analytic_family_simultaneous_hs_exception
    {d t : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    {ι : Type*} [Fintype ι]
    (C : Set X) (hC : IsComplexAnalyticSubset (n := d+t) C) (x : X)
    (hreg : RegularAtDim (n := d+t) C x d)
    (V : ι → Set X) (hV : ∀ i,IsComplexAnalyticSubset (n := d+t) (V i)) :
    ∃ (D : Opens X) (hxD : x ∈ D) (E : Set D),
      IsComplexAnalyticSubset (n := d+t) E ∧ E ⊆ ((↑) ⁻¹' C : Set D) ∧
      (∀ O : Set D,IsOpen O → O ∩ ((↑) ⁻¹' C : Set D) ⊆ E → O ∩ ((↑) ⁻¹' C : Set D)=∅) ∧
      (∀ p k,RegularAtDim (n := d+t) E p k → k<d) ∧
      (⟨x,hxD⟩ : D) ∈ closure (((↑) ⁻¹' C : Set D) \ E) ∧
      ∃ h : ι → ℕ → ℕ,∀ i,∀ p : D,(p : X) ∈ C → p ∉ E →
        ∀ ℓ,hilbertSamuelAt (vanishingIdeal (n := d+t) (V i)) (p : X) ℓ=h i ℓ :=
  exists_original_finite_simultaneous_intrinsic_hs_exception C hC x hreg
    (fun i => vanishingIdeal (n := d+t) (V i))
    (fun i => CartanIrreducible.cartanCoherence (V i) (hV i))

end
end Hironaka.HironakaOriginalFiniteSimultaneousHSException
