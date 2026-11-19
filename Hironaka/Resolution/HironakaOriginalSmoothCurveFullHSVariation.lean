/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteSimultaneousHSException
import Hironaka.Resolution.HironakaOriginalFullValueVariationLocus
import Hironaka.Resolution.HironakaDimensionTwoStepOneAnalyticSuperlevels
/-! EXACT ALL-order simultaneous HS variation on actual smooth curves. Genuine
local denominator envelopes are constructed BEFORE zero-dimensional subset
geometry proves the actual bad set analytic. Higher dimensions stay open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSmoothCurveFullHSVariation
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaOriginalFiniteSimultaneousHSException HironakaOriginalFullValueVariationLocus
  HironakaHolomorphicJetChartInvariance HironakaOneDimensionalCanonicalSuperlevels
  AnalyticDimensionBasics DimensionMonotone AnalyticSubsetOpens AnalyticSubsetPreimage RegularPointDimension

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The independently defined LITERAL bad set tests the entire original family
profile, with EVERY order, in an actual original open neighbourhood. -/
def actualSimultaneousHSVariationLocus {ι : Type*} (A : ι → GermIdeal n M) (S : Set M) (q : ℕ) : Set M :=
  actualValueVariationLocus (n := n) (fun x i ℓ => hilbertSamuelAt (A i) x ℓ) S q

/-- Only genuine original centre geometry and coherence supply the analytic
local dimension-drop envelope containing the LITERAL whole-profile bad set. -/
theorem exists_actual_full_hs_variation_local_envelope
    {d t : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal (d+t) X) (hA : ∀ i,(A i).IsCoherent)
    {S : Set X} (hS : IsComplexAnalyticSubset (n := d+t) S)
    (hreg : ∀ x ∈ S,RegularAtDim (n := d+t) S x d) {x : X} (hx : x ∈ S) :
    ∃ D : Opens X,x ∈ D ∧ ∃ E : Set D,
      IsComplexAnalyticSubset (n := d+t) E ∧
      (∀ p k,RegularAtDim (n := d+t) E p k → k<d) ∧
      (Subtype.val : D → X) ⁻¹' actualSimultaneousHSVariationLocus A S d ⊆ E := by
  obtain ⟨D,hxD,E,hE,_hEC,_hthin,hdim,_hclosure,profile,hprofile⟩ :=
    exists_original_finite_simultaneous_intrinsic_hs_exception S hS x (hreg x hx) A hA
  refine ⟨D,hxD,E,hE,hdim,?_⟩
  intro p hp
  by_contra hpE
  apply hp.2
  let U : Set X := (Subtype.val : D → X) '' Eᶜ
  have hU : IsOpen U := D.isOpen.isOpenMap_subtype_val _ hE.isClosed.isOpen_compl
  refine ⟨hreg p hp.1,U,hU,⟨p,hpE,rfl⟩,?_⟩
  rintro y ⟨hyS,hyU⟩
  obtain ⟨z,hzE,hzy⟩ := hyU
  have hzS : (z : X) ∈ S := hzy.symm ▸ hyS
  funext i ℓ
  change hilbertSamuelAt (A i) y ℓ=hilbertSamuelAt (A i) p ℓ
  rw [← hzy]
  exact (hprofile i z hzS hzE ℓ).trans (hprofile i p hp.1 hpE ℓ).symm

/-- GENUINE analytic zero-dimensional envelopes make the EXACT GLOBAL all-order
bad set on an actual smooth curve analytic, closed and zero-dimensional. -/
theorem actual_smooth_curve_full_hs_variation_analytic
    {t : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (1+t)) X] [IsComplexManifold (1+t) X]
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal (1+t) X) (hA : ∀ i,(A i).IsCoherent)
    {S : Set X} (hS : IsComplexAnalyticSubset (n := 1+t) S)
    (hreg : ∀ x ∈ S,RegularAtDim (n := 1+t) S x 1) :
    IsComplexAnalyticSubset (n := 1+t) (actualSimultaneousHSVariationLocus A S 1) ∧
      DimLE (n := 1+t) (actualSimultaneousHSVariationLocus A S 1) 0 ∧
      IsClosed (actualSimultaneousHSVariationLocus A S 1) ∧
      IsDiscrete (actualSimultaneousHSVariationLocus A S 1) := by
  have hloc : ∀ x ∈ S,∃ D : Opens X,x ∈ D ∧
      IsComplexAnalyticSubset (n := 1+t) ((Subtype.val : D → X) ⁻¹' actualSimultaneousHSVariationLocus A S 1) ∧
      DimLE (n := 1+t) ((Subtype.val : D → X) ⁻¹' actualSimultaneousHSVariationLocus A S 1) 0 := by
    intro x hx
    obtain ⟨D,hxD,E,hE,hdim,hsub⟩ := exists_actual_full_hs_variation_local_envelope A hA hS hreg hx
    have hdE : DimLE (n := 1+t) E 0 := fun p k hp => Nat.le_of_lt_succ (hdim p k hp)
    have hSM := isClosedSubmanifold_subset_of_analytic_dimLE_zero hE hdE hsub
    exact ⟨D,hxD,isComplexAnalyticSubset_of_isClosedSubmanifold hSM,DimLE.anti hE hsub hdE⟩
  have hBa : IsComplexAnalyticSubset (n := 1+t) (actualSimultaneousHSVariationLocus A S 1) := by
    apply isComplexAnalyticSubset_of_forall_opens
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨D,hxD,hDa,_hDd⟩ := hloc x hx
      exact ⟨D,hxD,hDa⟩
    · let U : Opens X := ⟨Sᶜ,hS.isClosed.isOpen_compl⟩
      have he : (Subtype.val : U → X) ⁻¹' actualSimultaneousHSVariationLocus A S 1=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact p.property hp.1
      exact ⟨U,hx,he.symm ▸ isComplexAnalyticSubset_empty⟩
  have hBd : DimLE (n := 1+t) (actualSimultaneousHSVariationLocus A S 1) 0 := by
    intro x k hx
    obtain ⟨D,hxD,_hDa,hDd⟩ := hloc x hx.2.1.1
    exact hDd ⟨x,hxD⟩ k (regularAtDim_preimage_val_iff.mpr hx)
  exact ⟨hBa,hBd,hBa.isClosed,isDiscrete_of_analytic_dimLE_zero hBa hBd⟩

/-- The EXACT whole-profile bad set meets ANY actual compact set in finitely
many points, without a compact ambient or a finite-order surrogate. -/
theorem actual_smooth_curve_full_hs_variation_compact_finite
    {t : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (1+t)) X] [IsComplexManifold (1+t) X]
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal (1+t) X) (hA : ∀ i,(A i).IsCoherent)
    {S : Set X} (hS : IsComplexAnalyticSubset (n := 1+t) S)
    (hreg : ∀ x ∈ S,RegularAtDim (n := 1+t) S x 1) {K : Set X} (hK : IsCompact K) :
    (actualSimultaneousHSVariationLocus A S 1 ∩ K).Finite := by
  obtain ⟨_ha,_hd,hc,hdisc⟩ := actual_smooth_curve_full_hs_variation_analytic A hA hS hreg
  exact (hK.of_isClosed_subset (hc.inter hK.isClosed) inter_subset_right).finite
    (hdisc.mono inter_subset_left)

/-- ANY genuine zero-dimensional analytic pure set has EMPTY actual ALL-order
profile bad set, without coherence or a finite-family assumption. -/
theorem actual_zero_dimensional_full_hs_variation_empty {ι : Type*}
    (A : ι → GermIdeal n M) {S : Set M} (hS : IsComplexAnalyticSubset (n := n) S)
    (hpure : IsPureDim (n := n) S 0) : actualSimultaneousHSVariationLocus A S 0=∅ :=
  actualValueVariationLocus_zero_empty _ hS hpure

omit [IsComplexManifold n M] in
private theorem actual_product_variation_eq_union {α β : Type*} (f : M → α) (g : M → β)
    (S : Set M) (q : ℕ) :
    actualValueVariationLocus (n := n) (fun x => (f x,g x)) S q=
      actualValueVariationLocus (n := n) f S q ∪ actualValueVariationLocus (n := n) g S q := by
  ext x
  constructor
  · intro hx
    by_cases hf : x ∈ actualValueVariationLocus (n := n) f S q
    · exact Or.inl hf
    · right
      refine ⟨hx.1,?_⟩
      rintro ⟨hreg,V,hVo,hxV,hV⟩
      have hfG : RegularAtDim (n := n) S x q ∧ ∃ U : Set M,IsOpen U ∧ x ∈ U ∧
          ∀ y ∈ S ∩ U,f y=f x := by
        by_contra hn
        exact hf ⟨hx.1,hn⟩
      obtain ⟨_hr,U,hUo,hxU,hU⟩ := hfG
      apply hx.2
      exact ⟨hreg,U ∩ V,hUo.inter hVo,⟨hxU,hxV⟩,fun y hy =>
        Prod.ext (hU y ⟨hy.1,hy.2.1⟩) (hV y ⟨hy.1,hy.2.2⟩)⟩
  · rintro (hx | hx)
    · refine ⟨hx.1,?_⟩
      rintro ⟨hreg,U,hUo,hxU,hU⟩
      exact hx.2 ⟨hreg,U,hUo,hxU,fun y hy => congrArg Prod.fst (hU y hy)⟩
    · refine ⟨hx.1,?_⟩
      rintro ⟨hreg,U,hUo,hxU,hU⟩
      exact hx.2 ⟨hreg,U,hUo,hxU,fun y hy => congrArg Prod.snd (hU y hy)⟩

open MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- The TRUE original FULL invariant and EVERY original HS order give the EXACT
GLOBAL simultaneous tuple bad set on a genuine smooth current curve. -/
theorem original_smooth_curve_full_invariant_all_hs_variation_analytic
    {t : ℕ} {X Y : CMfd.{u} (1+t)} (d : ℕ)
    (m : MarkedIdeal (1+t) X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily (by omega : 0<1+t) d).inv m) T)
    {S : Set Y} (hS : IsComplexAnalyticSubset (n := 1+t) S)
    (hreg : ∀ x ∈ S,RegularAtDim (n := 1+t) S x 1) (hSP : S ⊆ (geoTransformAlong m T).cosupp)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal (1+t) Y) (hA : ∀ i,(A i).IsCoherent) :
    IsComplexAnalyticSubset (n := 1+t) (actualValueVariationLocus (n := 1+t)
      (fun x => ((invFamily (by omega : 0<1+t) d).inv m T x,fun i ℓ => hilbertSamuelAt (A i) x ℓ)) S 1) ∧
      DimLE (n := 1+t) (actualValueVariationLocus (n := 1+t)
      (fun x => ((invFamily (by omega : 0<1+t) d).inv m T x,fun i ℓ => hilbertSamuelAt (A i) x ℓ)) S 1) 0 := by
  have hpure : IsPureDim (n := 1+t) S 1 := fun x k hx =>
    eq_of_regularAtDim hx (hreg x hx.2.1)
  obtain ⟨hRa,hdR⟩ := original_full_value_variation_locus_analytic (by omega : 0<1+t) d m h T hc hS hpure hSP
  obtain ⟨hHa,hdH,_hclosed,_hdisc⟩ := actual_smooth_curve_full_hs_variation_analytic A hA hS hreg
  rw [actual_product_variation_eq_union]
  exact HironakaDimensionTwoStepOneAnalyticSuperlevels.analytic_dimzero_union hRa hdR hHa hdH

end
end Hironaka.HironakaOriginalSmoothCurveFullHSVariation
