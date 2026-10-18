/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullReferenceGlobalExtension
import Hironaka.Resolution.HironakaCurveAnalyticPredicates
import Hironaka.Resolution.HironakaDimensionThreeStepOneCurveEnvelope
import Hironaka.Analytic.PureSingularLocus
/-! Actual ORIGINAL FULL-value variation locus: true component minima and first
higher cuts construct its exact global analytic dimension-drop geometry.
Only the ORIGINAL-value part of BM97 Lemma13.7; simultaneous HS/transform driver OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalFullValueVariationLocus
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  GlobalComponents RegularLocusComponent AnalyticDimensionBasics
  HironakaDimensionThreeStepOneCurveEnvelope HironakaCurveAnalyticPredicates
  HironakaOriginalFullReferenceGlobalExtension HironakaOriginalFullHistorySuperlevelsAnalytic
  HironakaOriginalReferenceValueOpenNaturality CanonicalCentres
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Λ : Type v} [LinearOrder Λ] [WellFoundedLT Λ]

/-- The LITERAL actual nonsmooth/nonconstant subset, independently of equations. -/
def actualValueVariationLocus (f : M → Λ) (S : Set M) (q : ℕ) : Set M :=
  {x | x ∈ S ∧ ¬(RegularAtDim (n := n) S x q ∧
    ∃ U : Set M,IsOpen U ∧ x ∈ U ∧ ∀ y ∈ S ∩ U,f y=f x)}

/-- True well-founded attained minima and actual first higher cuts construct a
proper analytic component jump and its true geometric dimension drop. -/
theorem exists_actual_component_minimum_analytic_jump (f : M → Λ) (C : Set M)
    (hcut : ∀ b,IsComplexAnalyticSubset (n := n) {x | x ∈ C ∧ b ≤ f x})
    {S : Set M} (hS : IsComplexAnalyticSubset (n := n) S) {q : ℕ}
    (hpure : IsPureDim (n := n) S q) (hSC : S ⊆ C)
    (B : globalComponents (n := n) S) :
    ∃ (a : Λ) (E : Set M),(∃ x ∈ (B : Set M),f x=a) ∧
      (∀ x ∈ (B : Set M),a ≤ f x) ∧ E={x | x ∈ (B : Set M) ∧ a < f x} ∧
      IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E (q-1) := by
  have hBa := (isComplexAnalyticallyIrreducible_of_mem_globalComponents hS B.property).1
  have hBne := (isComplexAnalyticallyIrreducible_of_mem_globalComponents hS B.property).2.1
  have hBS := subset_of_mem_globalComponents hS B.property
  obtain ⟨a,ha,hmin⟩ := wellFounded_lt.has_min (f '' (B : Set M)) (hBne.image f)
  have hbound : ∀ x ∈ (B : Set M),a ≤ f x := fun x hx => le_of_not_gt (hmin _ ⟨x,hx,rfl⟩)
  by_cases hhigh : ({b | ∃ x ∈ (B : Set M),f x=b ∧ a < b} : Set Λ).Nonempty
  · obtain ⟨b,hb,hbmin⟩ := wellFounded_lt.has_min {b | ∃ x ∈ (B : Set M),f x=b ∧ a < b} hhigh
    obtain ⟨z,hz,hzb,hab⟩ := hb
    let P := {x | x ∈ C ∧ b ≤ f x}
    have hEa : IsComplexAnalyticSubset (n := n) ((B : Set M) ∩ P) := hBa.inter (hcut b)
    have he : (B : Set M) ∩ P={x | x ∈ (B : Set M) ∧ a < f x} := by
      ext x
      constructor
      · rintro ⟨hxB,_hxC,hbx⟩
        exact ⟨hxB,hab.trans_le hbx⟩
      · rintro ⟨hxB,hax⟩
        exact ⟨hxB,hSC (hBS hxB),le_of_not_gt (hbmin _ ⟨x,hxB,rfl,hax⟩)⟩
    have hnot : ¬(B : Set M) ⊆ P := by
      intro hs
      obtain ⟨x,hx,hfx⟩ := ha
      have hh := (hs hx).2
      rw [hfx] at hh
      exact (not_le_of_gt hab) hh
    have hthin : ∀ O : Set M,IsOpen O → O ∩ (B : Set M) ⊆ (B : Set M) ∩ P → O ∩ (B : Set M)=∅ := by
      obtain ⟨c,_hc,hBC⟩ := B.property
      intro O hO hs
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxO,hxB⟩
      have hxCl : x ∈ closure (component (n := n) S c) := hBC ▸ hxB
      obtain ⟨y,hyO,hyC⟩ := mem_closure_iff.mp hxCl O hO hxO
      have hcP : component (n := n) S c ⊆ P := component_subset_of_isOpen (hcut b) hO
        ⟨y,hyO,hyC⟩ (fun t ht => (hs ⟨ht.1,hBC.symm ▸ subset_closure ht.2⟩).2)
      apply hnot
      rw [hBC]
      exact closure_minimal hcP (hcut b).isClosed
    exact ⟨a,(B : Set M) ∩ P,ha,hbound,he,hEa,
      ThinDimensionDrop.dimLE_pred_of_thin hBa inter_subset_left hthin
        (DimensionMonotone.DimLE.anti hS hBS hpure.dimLE)⟩
  · refine ⟨a,∅,ha,hbound,?_,isComplexAnalyticSubset_empty,?_⟩
    · symm
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx,hax⟩
      exact hhigh ⟨f x,x,hx,rfl,hax⟩
    · exact fun _ _ hx => False.elim hx.2.1

/-- Genuine local finiteness preserves any true analytic regular-dimension bound. -/
theorem analytic_dimLE_iUnion_of_actual_locallyFinite {ι : Type*} (A : ι → Set M)
    (hlf : LocallyFinite A) (hA : ∀ i,IsComplexAnalyticSubset (n := n) (A i)) {r : ℕ}
    (hd : ∀ i,DimLE (n := n) (A i) r) :
    IsComplexAnalyticSubset (n := n) (⋃ i,A i) ∧ DimLE (n := n) (⋃ i,A i) r := by
  refine ⟨isComplexAnalyticSubset_iUnion_of_locallyFinite A hlf hA,?_⟩
  intro x k hx
  obtain ⟨V,hxV,hfin⟩ := hlf x
  obtain ⟨U,hUV,hU,hxU⟩ := mem_nhds_iff.mp hxV
  let t := hfin.toFinset
  have he : (⋃ i ∈ t,A i) ∩ U=(⋃ i,A i) ∩ U := by
    ext y
    constructor
    · rintro ⟨hy,hyU⟩
      obtain ⟨i,_hi,hyi⟩ := mem_iUnion₂.mp hy
      exact ⟨mem_iUnion.mpr ⟨i,hyi⟩,hyU⟩
    · rintro ⟨hy,hyU⟩
      obtain ⟨i,hyi⟩ := mem_iUnion.mp hy
      exact ⟨mem_iUnion₂.mpr ⟨i,hfin.mem_toFinset.mpr ⟨y,hyi,hUV hyU⟩,hyi⟩,hyU⟩
  exact (analytic_dimLE_finset_union t A (fun i _ => hA i) (fun i _ => hd i)).2 x k
    (RegularPointDimension.regularAtDim_of_inter_eq hU hxU he.symm hx)

/-- Exact literal bad-locus geometry, constructed from real component jumps. -/
theorem actualValueVariationLocus_analytic_dimLE (f : M → Λ) (C : Set M)
    (hcut : ∀ b,IsComplexAnalyticSubset (n := n) {x | x ∈ C ∧ b ≤ f x})
    {S : Set M} (hS : IsComplexAnalyticSubset (n := n) S) {q : ℕ}
    (hpure : IsPureDim (n := n) S q) (hSC : S ⊆ C) :
    IsComplexAnalyticSubset (n := n) (actualValueVariationLocus (n := n) f S q) ∧
      DimLE (n := n) (actualValueVariationLocus (n := n) f S q) (q-1) := by
  choose a E hmin hbound he hE hd using
    fun B : globalComponents (n := n) S => exists_actual_component_minimum_analytic_jump f C hcut hS hpure hSC B
  have hEB (B : globalComponents (n := n) S) : E B ⊆ (B : Set M) := by
    intro x hx
    rw [he B] at hx
    exact hx.1
  have hlf : LocallyFinite E := (locallyFinite_globalComponents hS).subset hEB
  obtain ⟨hJa,hdJ⟩ := analytic_dimLE_iUnion_of_actual_locallyFinite E hlf hE hd
  let F := (S \ regularLocus (n := n) S q) ∪ ⋃ B,E B
  obtain ⟨hFa,hdF⟩ := analytic_dimLE_union
    (PureSingularLocus.isComplexAnalyticSubset_diff_regularLocus hS hpure)
    (PureSingularLocus.dimLE_diff_regularLocus hS hpure) hJa hdJ
  have hsub : F ⊆ S := by
    rintro x (hx | hx)
    · exact hx.1
    · obtain ⟨B,hx⟩ := mem_iUnion.mp hx
      exact subset_of_mem_globalComponents hS B.property (hEB B hx)
  have hEq : actualValueVariationLocus (n := n) f S q=F := by
    ext x
    constructor
    · intro hx
      by_contra hxF
      have hreg : RegularAtDim (n := n) S x q := by
        by_contra hh
        exact hxF (Or.inl ⟨hx.1,hh⟩)
      let B : globalComponents (n := n) S :=
        ⟨closure (component (n := n) S x),closure_component_mem_globalComponents hreg⟩
      have hxB : x ∈ (B : Set M) := subset_closure (mem_component_self hreg)
      have hxe : x ∉ E B := fun hh => hxF (Or.inr (mem_iUnion.mpr ⟨B,hh⟩))
      have hfx : f x=a B := (le_of_not_gt (fun hh => hxe ((he B).symm ▸ ⟨hxB,hh⟩))).antisymm (hbound B x hxB)
      obtain ⟨U,hU,hxU,hUC⟩ := exists_open_inter_subset_component hreg (mem_component_self hreg)
      have hloc : ∀ y ∈ S ∩ (U ∩ (E B)ᶜ),f y=f x := by
        rintro y ⟨hyS,hyU,hyE⟩
        have hyB : y ∈ (B : Set M) := subset_closure (hUC ⟨hyS,hyU⟩)
        have hfy : f y=a B := (le_of_not_gt (fun hh => hyE ((he B).symm ▸ ⟨hyB,hh⟩))).antisymm (hbound B y hyB)
        exact hfy.trans hfx.symm
      exact hx.2 ⟨hreg,U ∩ (E B)ᶜ,hU.inter (hE B).isClosed.isOpen_compl,⟨hxU,hxe⟩,hloc⟩
    · intro hxF
      refine ⟨hsub hxF,?_⟩
      rintro ⟨hreg,U,hU,hxU,hval⟩
      rcases hxF with hxSing | hxJ
      · exact hxSing.2 hreg
      · obtain ⟨B,hxE⟩ := mem_iUnion.mp hxJ
        have hxB := hEB B hxE
        have hhigh : a B < f x := by
          rw [he B] at hxE
          exact hxE.2
        obtain ⟨c,_hc,hBC⟩ := B.property
        have hxCl : x ∈ closure (component (n := n) S c) := hBC ▸ hxB
        obtain ⟨y,hyU,hyC⟩ := mem_closure_iff.mp hxCl U hU hxU
        have hcP : component (n := n) S c ⊆ {z | z ∈ C ∧ f x ≤ f z} :=
          component_subset_of_isOpen (hcut (f x)) hU ⟨y,hyU,hyC⟩ (fun z hz =>
            ⟨hSC (component_subset S c hz.2),by rw [hval z ⟨component_subset S c hz.2,hz.1⟩]⟩)
        have hBP : (B : Set M) ⊆ {z | z ∈ C ∧ f x ≤ f z} := by
          rw [hBC]
          exact closure_minimal hcP (hcut (f x)).isClosed
        obtain ⟨z,hz,hza⟩ := hmin B
        exact (not_le_of_gt hhigh) ((hBP hz).2.trans_eq hza)
  rw [hEq]
  exact ⟨hFa,hdF⟩

variable {X Y : CMfd.{u} n}

/-- ONLY original history/domain and a true analytic pure subset supply all
actual full analytic cuts; no variation equations or constancy certificate. -/
theorem original_full_value_variation_locus_analytic (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    {S : Set Y} (hS : IsComplexAnalyticSubset (n := n) S) {q : ℕ}
    (hpure : IsPureDim (n := n) S q) (hsub : S ⊆ (geoTransformAlong m T).cosupp) :
    IsComplexAnalyticSubset (n := n) (actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q) ∧
      DimLE (n := n) (actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q) (q-1) :=
  actualValueVariationLocus_analytic_dimLE ((invFamily hn d).inv m T) (geoTransformAlong m T).cosupp
    (fun b => original_all_depth_full_history_global_analytic hn d m h T hc b) hS hpure hsub

/-- ONLY original reference input internally supplies the actual global pure
extension and a true window avoided by its EXACT global FULL-value bad locus. -/
theorem exists_original_reference_extension_variation_avoids_window (hn : 0<n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ (q : ℕ) (V : Opens Y) (S : Set Y),q ≤ n ∧ x ∈ V ∧ x ∈ S ∧
      IsComplexAnalyticSubset (n := n) S ∧ IsPureDim (n := n) S q ∧
      S ⊆ fullReferenceLocus hn d m T x ∧ S ∩ V=fullReferenceLocus hn d m T x ∩ V ∧
      IsComplexAnalyticSubset (n := n) (actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q) ∧
      DimLE (n := n) (actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q) (q-1) ∧
      actualValueVariationLocus (n := n) ((invFamily hn d).inv m T) S q ∩ V=∅ := by
  obtain ⟨q,U,S,hqn,hxU,hxS,hSa,hpure,hsub,htrace,hreg,_hcomp,_hAdm,_hcoh,_hzero,_hideal⟩ :=
    exists_original_full_reference_pure_global_extension hn d m h T hc x hx
  obtain ⟨W,hW,hWo,hxW⟩ := mem_nhds_iff.mp ((invFamily hn d).isInvValue.usc m h T hc x hx)
  let V : Opens Y := U ⊓ ⟨W,hWo⟩
  have hconst : ∀ y ∈ S,y ∈ V → (invFamily hn d).inv m T y=(invFamily hn d).inv m T x :=
    fun y hy hyV => (hW hyV.2 (hsub hy).1).antisymm (hsub hy).2
  obtain ⟨hFa,hdF⟩ := original_full_value_variation_locus_analytic hn d m h T hc hSa hpure (fun y hy => (hsub hy).1)
  refine ⟨q,V,S,hqn,⟨hxU,hxW⟩,hxS,hSa,hpure,hsub,?_,hFa,hdF,?_⟩
  · ext y
    constructor
    · exact fun hy => ⟨hsub hy.1,hy.2⟩
    · rintro ⟨hy,hyV⟩
      have hh : y ∈ S ∩ U := htrace.symm ▸ (show y ∈ fullReferenceLocus hn d m T x ∩ U from ⟨hy,hyV.1⟩)
      exact ⟨hh.1,hyV⟩
  · apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hy,hyV⟩
    apply hy.2
    refine ⟨hreg y hy.1 hyV.1,(V : Set Y),V.isOpen,hyV,?_⟩
    rintro z ⟨hz,hzV⟩
    exact (hconst z hz hzV).trans (hconst y hy.1 hyV).symm

omit [LinearOrder Λ] [WellFoundedLT Λ] in
/-- Genuine zero-dimensional analytic geometry makes the EXACT bad locus empty,
for ANY actual function; no discreteness or local constancy certificate. -/
theorem actualValueVariationLocus_zero_empty (f : M → Λ) {S : Set M}
    (hS : IsComplexAnalyticSubset (n := n) S) (hpure : IsPureDim (n := n) S 0) :
    actualValueVariationLocus (n := n) f S 0=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hr := HironakaOneDimensionalCanonicalSuperlevels.regularAtDim_zero_of_analytic_dimLE_zero hS hpure.dimLE hx.1
  obtain ⟨U,hU,hxU,hsub⟩ := PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hr
  exact hx.2 ⟨hr,U,hU,hxU,fun y hy => congrArg f (mem_singleton_iff.mp (hsub hy))⟩

end
end Hironaka.HironakaOriginalFullValueVariationLocus
