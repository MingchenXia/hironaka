import Hironaka.Blowup.BlowupTowerSplitSuccessor
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaDimensionTwoStepOneAnalyticSuperlevels
import Hironaka.Resolution.HironakaOrderTupleAnalyticSuperlevels
import Hironaka.Analytic.PureSingularLocus

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Actual finite analytic predicates and historical order runs on analytic curves

Genuinely locally finite global components and their proper analytic
intersections internally produce a zero-dimensional exception. The actual
head-tail nonmonomial ideals yield finite historical predicates, and outside
a produced singular/history exception the literal trailing regime run agrees
on each genuine current component. General2 companion descent and G3 remain open.
Blueprint: `hironaka-curve-analytic-predicates-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaCurveAnalyticPredicates

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GlobalComponents RegularLocusComponent HironakaDimensionGlobalComponents
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaOneDimensionalCanonicalSuperlevels
  AnalyticDimensionBasics HironakaEmbeddedDimensionParts

open Hironaka

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private def presentation_of_inter_eq {A B U : Set M} {x : M}
    (p : ComplexAnalyticPresentationAt (n := n) A x) (hU : IsOpen U) (hxU : x ∈ U)
    (heq : A ∩ U = B ∩ U) : ComplexAnalyticPresentationAt (n := n) B x := by
  let e := (complexChartAt (n := n) x).val
  have hxs : x ∈ e.source := mem_complexChartAt_source x
  refine { generatorCount := p.generatorCount
           generator := p.generator
           coordinateNeighborhood := p.coordinateNeighborhood ∩ (e.target ∩ e.symm ⁻¹' U)
           isOpen_coordinateNeighborhood := p.isOpen_coordinateNeighborhood.inter
             (e.isOpen_inter_preimage_symm hU)
           center_mem_coordinateNeighborhood := ⟨p.center_mem_coordinateNeighborhood,
             e.map_source hxs, ?_⟩
           coordinateNeighborhood_subset_target := fun _ hz => hz.2.1
           generator_holomorphic := fun i => (p.generator_holomorphic i).mono inter_subset_left
           zeroLocus := ?_ }
  · change e.symm (e x) ∈ U
    rwa [e.left_inv hxs]
  · intro y hy hyU
    have hyU' : y ∈ U := by
      have h : e.symm (e y) ∈ U := hyU.2.2
      rwa [e.left_inv hy] at h
    rw [← p.zeroLocus hy hyU.1]
    constructor
    · intro hyB
      have hm : y ∈ A ∩ U := by
        rw [heq]
        exact ⟨hyB, hyU'⟩
      exact hm.1
    · intro hyA
      have hm : y ∈ B ∩ U := by
        rw [← heq]
        exact ⟨hyA, hyU'⟩
      exact hm.1

private theorem analytic_finset_union {ι : Type*} (t : Finset ι)
    (A : ι → Set M) (hA : ∀ i ∈ t, IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t, A i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hA i (Finset.mem_insert_self i t))
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

private theorem exists_open_finite_union_trace {ι : Type*} (A : ι → Set M)
    (hlf : LocallyFinite A) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ t : Finset ι,
      (⋃ i ∈ t, A i) ∩ U = (⋃ i, A i) ∩ U := by
  classical
  obtain ⟨V, hxV, hfin⟩ := hlf x
  obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp hxV
  refine ⟨U, hU, hxU, hfin.toFinset, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨hy, hyU⟩
    obtain ⟨i, -, hyi⟩ := mem_iUnion₂.mp hy
    exact ⟨mem_iUnion.mpr ⟨i, hyi⟩, hyU⟩
  · rintro y ⟨hy, hyU⟩
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    exact ⟨mem_iUnion₂.mpr ⟨i, hfin.mem_toFinset.mpr ⟨y, hyi, hUV hyU⟩, hyi⟩, hyU⟩

/-- Actual locally finite analytic equations produce an analytic union. -/
theorem isComplexAnalyticSubset_iUnion_of_locallyFinite {ι : Type*}
    (A : ι → Set M) (hlf : LocallyFinite A)
    (hA : ∀ i, IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i, A i) := by
  intro x
  obtain ⟨U, hU, hxU, t, heq⟩ := exists_open_finite_union_trace A hlf x
  exact ⟨presentation_of_inter_eq ((analytic_finset_union t A (fun i _ => hA i)) x).some
    hU hxU heq⟩

/-- Local finiteness preserves the genuine zero-dimensional analytic union. -/
theorem analytic_dimzero_iUnion_of_locallyFinite {ι : Type*}
    (A : ι → Set M) (hlf : LocallyFinite A)
    (hA : ∀ i, IsComplexAnalyticSubset (n := n) (A i))
    (hdim : ∀ i, DimLE (n := n) (A i) 0) :
    IsComplexAnalyticSubset (n := n) (⋃ i, A i) ∧ DimLE (n := n) (⋃ i, A i) 0 := by
  refine ⟨isComplexAnalyticSubset_iUnion_of_locallyFinite A hlf hA, ?_⟩
  intro x k hx
  obtain ⟨U, hU, hxU, t, heq⟩ := exists_open_finite_union_trace A hlf x
  have hfinite := analytic_dimzero_finset_union t A (fun i _ => hA i) (fun i _ => hdim i)
  exact hfinite.2 x k (RegularPointDimension.regularAtDim_of_inter_eq hU hxU heq.symm hx)

/-- Analytic continuation internally proves thinness on every genuine
uncontained global component; actual analytic dimension drop then applies. -/
theorem analytic_dimzero_inter_globalComponent_of_not_subset {A B P : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hdim : DimLE (n := n) A 1)
    (hB : B ∈ globalComponents (n := n) A) (hP : IsComplexAnalyticSubset (n := n) P)
    (hnot : ¬ B ⊆ P) :
    IsComplexAnalyticSubset (n := n) (B ∩ P) ∧ DimLE (n := n) (B ∩ P) 0 := by
  have hBa := (isComplexAnalyticallyIrreducible_of_mem_globalComponents hA hB).1
  have hBdim := DimensionMonotone.DimLE.anti hA (subset_of_mem_globalComponents hA hB) hdim
  refine ⟨hBa.inter hP, ThinDimensionDrop.dimLE_pred_of_thin hBa inter_subset_left ?_ hBdim⟩
  obtain ⟨c, -, rfl⟩ := hB
  intro O hO hsub
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxO, hxB⟩
  obtain ⟨y, hyO, hyC⟩ := mem_closure_iff.mp hxB O hO hxO
  have hCP : component (n := n) A c ⊆ P := component_subset_of_isOpen hP hO
    ⟨y, hyO, hyC⟩ (fun z hz => (hsub ⟨hz.1, subset_closure hz.2⟩).2)
  exact hnot (closure_minimal hCP hP.isClosed)

/-- The actual proper intersections with uncontained genuine components. -/
def predicateException (A P : Set M) : Set M :=
  ⋃ B : {B : Set M // B ∈ globalComponents (n := n) A ∧ ¬ B ⊆ P}, B.1 ∩ P

/-- Finite analytic predicates internally yield a genuine analytic
zero-dimensional exception and their literal dictionary on every component. -/
theorem exists_analytic_dimzero_predicate_exception {ι : Type*} [Fintype ι]
    {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) (hdim : DimLE (n := n) A 1)
    (P : ι → Set M) (hP : ∀ i, IsComplexAnalyticSubset (n := n) (P i)) :
    ∃ Z : Set M, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧ Z ⊆ A ∧
      ∀ B ∈ globalComponents (n := n) A, ∀ x ∈ B \ Z, ∀ i,
        x ∈ P i ↔ B ⊆ P i := by
  classical
  have hE : ∀ i, IsComplexAnalyticSubset (n := n) (predicateException (n := n) A (P i)) ∧
      DimLE (n := n) (predicateException (n := n) A (P i)) 0 := by
    intro i
    let f : {B : Set M // B ∈ globalComponents (n := n) A ∧ ¬ B ⊆ P i} →
        globalComponents (n := n) A := fun B => ⟨B.1, B.2.1⟩
    have hf : Function.Injective f := by
      intro B C h
      exact Subtype.ext (congrArg (fun D : globalComponents (n := n) A => D.1) h)
    have hlf := ((locallyFinite_globalComponents hA).comp_injective hf).subset
      (fun _ => inter_subset_left (t := P i))
    exact analytic_dimzero_iUnion_of_locallyFinite _ hlf
      (fun B => (analytic_dimzero_inter_globalComponent_of_not_subset hA hdim B.2.1 (hP i) B.2.2).1)
      (fun B => (analytic_dimzero_inter_globalComponent_of_not_subset hA hdim B.2.1 (hP i) B.2.2).2)
  let Z := ⋃ i ∈ (Finset.univ : Finset ι), predicateException (n := n) A (P i)
  obtain ⟨hZ, hZdim⟩ := analytic_dimzero_finset_union Finset.univ _
    (fun i _ => (hE i).1) (fun i _ => (hE i).2)
  refine ⟨Z, hZ, hZdim, ?_, ?_⟩
  · rintro x hx
    obtain ⟨i, -, hxi⟩ := mem_iUnion₂.mp hx
    obtain ⟨B, hxB⟩ := mem_iUnion.mp hxi
    exact subset_of_mem_globalComponents hA B.2.1 hxB.1
  · intro B hB x hx i
    refine ⟨fun hxi => ?_, fun hBi => hBi hx.1⟩
    by_contra hnot
    exact hx.2 (mem_iUnion₂.mpr ⟨i, Finset.mem_univ i,
      mem_iUnion.mpr ⟨⟨B, hB, hnot⟩, hx.1, hxi⟩⟩)


/-- True global-component dimensions produce the exact two actual dimension parts. -/
theorem eq_dimensionPart_zero_union_one {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hdim : DimLE (n := n) A 1) :
    A = dimensionPart (n := n) A 0 ∪ dimensionPart (n := n) A 1 := by
  apply Subset.antisymm
  · intro x hx
    have hxU : x ∈ ⋃₀ globalComponents (n := n) A := by
      rw [sUnion_globalComponents hA]
      exact hx
    obtain ⟨B, hB, hxB⟩ := hxU
    obtain ⟨c, ⟨k, hc⟩, rfl⟩ := hB
    have hk : k = 0 ∨ k = 1 := by
      have := hdim c k hc
      omega
    have hsub := subset_dimensionPart_of_mem_globalComponents_of_isPureDim
      (closure_component_mem_globalComponents hc) (isPureDim_closure_component hA hc)
    rcases hk with rfl | rfl
    · exact Or.inl (hsub hxB)
    · exact Or.inr (hsub hxB)
  · exact union_subset (dimensionPart_subset hA.isClosed 0) (dimensionPart_subset hA.isClosed 1)

/-- The actual dimension-zero part and actual pure curve singular locus
internally produce a zero-dimensional exception to genuine curve regularity. -/
theorem exists_analytic_dimzero_regular_curve_envelope {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hdim : DimLE (n := n) A 1) :
    ∃ S : Set M, IsComplexAnalyticSubset (n := n) S ∧ DimLE (n := n) S 0 ∧ S ⊆ A ∧
      dimensionPart (n := n) A 0 ⊆ S ∧ ∀ x ∈ A \ S, RegularAtDim (n := n) A x 1 := by
  let A₀ := dimensionPart (n := n) A 0
  let A₁ := dimensionPart (n := n) A 1
  have hA₀ : IsComplexAnalyticSubset (n := n) A₀ := isComplexAnalyticSubset_dimensionPart hA 0
  have hA₁ : IsComplexAnalyticSubset (n := n) A₁ := isComplexAnalyticSubset_dimensionPart hA 1
  have hp₀ := isPureDim_dimensionPart hA 0
  have hp₁ := isPureDim_dimensionPart hA 1
  have hsing := PureSingularLocus.isComplexAnalyticSubset_diff_regularLocus hA₁ hp₁
  have hsingdim : DimLE (n := n) (A₁ \ regularLocus (n := n) A₁ 1) 0 :=
    PureSingularLocus.dimLE_diff_regularLocus hA₁ hp₁
  obtain ⟨hS, hSdim⟩ := analytic_dimzero_union hA₀ hp₀.dimLE hsing hsingdim
  refine ⟨A₀ ∪ (A₁ \ regularLocus (n := n) A₁ 1), hS, hSdim,
    union_subset (dimensionPart_subset hA.isClosed 0)
      (sdiff_subset.trans (dimensionPart_subset hA.isClosed 1)), subset_union_left, ?_⟩
  intro x hx
  have hx₀ : x ∉ A₀ := fun hx₀ => hx.2 (Or.inl hx₀)
  have hx₁ : x ∈ A₁ := by
    have hcover := eq_dimensionPart_zero_union_one hA hdim
    exact (hcover ▸ hx.1).resolve_left hx₀
  have hreg : RegularAtDim (n := n) A₁ x 1 := by
    by_contra hr
    exact hx.2 (Or.inr ⟨hx₁, hr⟩)
  have heq : A₁ ∩ A₀ᶜ = A ∩ A₀ᶜ := by
    ext y
    constructor
    · exact fun hy => ⟨dimensionPart_subset hA.isClosed 1 hy.1, hy.2⟩
    · intro hy
      have hm : y ∈ A₀ ∪ A₁ := eq_dimensionPart_zero_union_one hA hdim ▸ hy.1
      exact ⟨hm.resolve_left hy.2, hy.2⟩
  exact RegularPointDimension.regularAtDim_of_inter_eq hA₀.isClosed.isOpen_compl hx₀ heq hreg

section ActualHistory

universe u
open BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedIdealAlong CodimOneSupportAlong
  NonmonomialOrderLocal NonmonomialOrderRegime CanonicalCentres HironakaOrderTupleAnalyticSuperlevels
  StepOneRegime
variable {X Y : CMfd.{u} n}

/-- The actual head-stage cosupport and nonmonomial comparison pulled back
by the literal tail projection; every historical map and carrier is retained. -/
def historyOrderSuperlevel (𝔪 : MarkedIdeal n X) (T : BlowupTower X Y) (r q : ℕ) : Set Y :=
  (tail T r).proj ⁻¹' {w | w ∈ (geoTransformAlong 𝔪 (head T r)).cosupp ∧
    q ≤ nmOrd (geoTransformAlong 𝔪 (head T r)) w}

/-- Coherence of the actual head-stage nonmonomial ideal and the actual
holomorphic tail projection produce each historical comparison locus. -/
theorem isComplexAnalyticSubset_historyOrderSuperlevel (hn : 0 < n)
    (𝔪 : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 𝔪)
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (r q : ℕ) :
    IsComplexAnalyticSubset (n := n) (historyOrderSuperlevel 𝔪 T r q) := by
  have hhead := ((isGeoTestTower_iff_head_tail 𝔪 T r).mp hT).1
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T r) hhead
  have hcs := isComplexAnalyticSubset_cosupport_along hd.isWellFormed.isCoherent
    hd.isWellFormed.isClosedSubmanifold_N hd.one_le_d
  have hord := isComplexAnalyticSubset_canonical_first_superlevel hn 𝔪 h (head T r) hhead q
  have heq : {w | w ∈ (geoTransformAlong 𝔪 (head T r)).cosupp ∧
      q ≤ nmOrd (geoTransformAlong 𝔪 (head T r)) w} =
      (geoTransformAlong 𝔪 (head T r)).cosupp ∩
        {w | w ∈ (geoTransformAlong 𝔪 (head T r)).N ∧
          q ≤ (ofLex ((invFamily hn 2).inv 𝔪 (head T r) w)).1} := by
    ext w
    constructor
    · exact fun hw => ⟨hw.1, (geoTransformAlong 𝔪 (head T r)).cosupp_subset_N hw.1, hw.2⟩
    · exact fun hw => ⟨hw.1, hw.2.2⟩
  unfold historyOrderSuperlevel
  rw [heq]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail T r).contMDiff_proj
    (hcs.inter hord)

/-- Actual finite historical comparisons on the genuine current cosupport
internally produce the analytic zero-dimensional exception. -/
theorem exists_analytic_dimzero_history_exception (hn : 0 < n)
    (𝔪 : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 𝔪)
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (o : ℕ) :
    ∃ Z : Set Y, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
      Z ⊆ (geoTransformAlong 𝔪 T).cosupp ∧
      ∀ B ∈ globalComponents (n := n) (geoTransformAlong 𝔪 T).cosupp,
        ∀ x ∈ B \ Z, ∀ r : Fin (T.length + 1), ∀ b : Fin 2,
          x ∈ historyOrderSuperlevel 𝔪 T r (o + b) ↔
            B ⊆ historyOrderSuperlevel 𝔪 T r (o + b) := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hcs := isComplexAnalyticSubset_cosupport_along hd.isWellFormed.isCoherent
    hd.isWellFormed.isClosedSubmanifold_N hd.one_le_d
  obtain ⟨Z, hZ, hdim, hsub, hdict⟩ := exists_analytic_dimzero_predicate_exception hcs
    (dimLE_cosupport_of_isInvDomain hd)
    (fun p : Fin (T.length + 1) × Fin 2 => historyOrderSuperlevel 𝔪 T p.1 (o + p.2))
    (fun p => isComplexAnalyticSubset_historyOrderSuperlevel hn 𝔪 h T hT p.1 (o + p.2))
  exact ⟨Z, hZ, hdim, hsub, fun B hB x hx r b => hdict B hB x hx (r, b)⟩


/-- Identical actual head predicates determine the literal trailing run. -/
theorem regimeRun_eq_of_head_predicates (P : Regime X) (T : BlowupTower X Y)
    (x y : Y) (hpred : ∀ r : ℕ, r ≤ T.length →
      (P (head T r) ((tail T r).proj x) ↔ P (head T r) ((tail T r).proj y))) :
    regimeRun P T x = regimeRun P T y := by
  classical
  induction T with
  | refl => rfl
  | @step Y Z T C π hπ ih =>
    have hp : P T (π x) ↔ P T (π y) := by
      cases T <;> simpa only [head_step_succ, tail_step_succ, head, tail, split,
        BlowupTower.proj_step, BlowupTower.proj_refl, Function.comp_apply, id_eq] using
        hpred 1 (by simp)
    have hprev : ∀ r : ℕ, r ≤ T.length →
        (P (head T r) ((tail T r).proj (π x)) ↔
          P (head T r) ((tail T r).proj (π y))) := by
      intro r hr
      exact hpred (r + 1) (by simpa using Nat.succ_le_succ hr)
    have heq := ih (π x) (π y) hprev
    rw [regimeRun_step, regimeRun_step]
    by_cases hx : P T (π x)
    · rw [if_pos hx, if_pos (hp.mp hx), heq]
    · rw [if_neg hx, if_neg (fun hy => hx (hp.mpr hy))]

private theorem ordRegime_head_iff_historyOrderSuperlevel
    (𝔪 : MarkedIdeal n X) (T : BlowupTower X Y) (o r : ℕ) (x : Y) :
    OrdRegime 𝔪 o (head T r) ((tail T r).proj x) ↔
      x ∈ historyOrderSuperlevel 𝔪 T r o ∧ x ∉ historyOrderSuperlevel 𝔪 T r (o + 1) := by
  change (_ ∧ _ = o) ↔ (_ ∧ o ≤ _) ∧ ¬ (_ ∧ o + 1 ≤ _)
  constructor
  · rintro ⟨hc, ho⟩
    exact ⟨⟨hc, ho.ge⟩, fun hh => by omega⟩
  · rintro ⟨⟨hc, hlo⟩, hhi⟩
    refine ⟨hc, ?_⟩
    have hnot : ¬ o + 1 ≤ nmOrd (geoTransformAlong 𝔪 (head T r)) ((tail T r).proj x) :=
      fun hle => hhi ⟨hc, hle⟩
    omega

/-- Original actual historical ideals and actual pure singular geometry
produce a zero-dimensional exception; outside it all points are regular curves
and the literal historical order-regime run agrees on each genuine component. -/
theorem exists_analytic_dimzero_history_regime_exception (hn : 0 < n)
    (𝔪 : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 𝔪)
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (o : ℕ) :
    ∃ Z : Set Y, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
      Z ⊆ (geoTransformAlong 𝔪 T).cosupp ∧
      (∀ x ∈ (geoTransformAlong 𝔪 T).cosupp \ Z,
        RegularAtDim (n := n) (geoTransformAlong 𝔪 T).cosupp x 1) ∧
      ∀ B ∈ globalComponents (n := n) (geoTransformAlong 𝔪 T).cosupp,
        ∀ x ∈ B \ Z, ∀ y ∈ B \ Z,
          regimeRun (OrdRegime 𝔪 o) T x = regimeRun (OrdRegime 𝔪 o) T y := by
  obtain ⟨Z, hZ, hZdim, hZA, hdict⟩ := exists_analytic_dimzero_history_exception hn 𝔪 h T hT o
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hcs := isComplexAnalyticSubset_cosupport_along hd.isWellFormed.isCoherent
    hd.isWellFormed.isClosedSubmanifold_N hd.one_le_d
  obtain ⟨S, hS, hSdim, hSA, -, hreg⟩ := exists_analytic_dimzero_regular_curve_envelope hcs
    (dimLE_cosupport_of_isInvDomain hd)
  obtain ⟨hU, hUdim⟩ := analytic_dimzero_union hZ hZdim hS hSdim
  refine ⟨Z ∪ S, hU, hUdim, union_subset hZA hSA, ?_, ?_⟩
  · intro x hx
    exact hreg x ⟨hx.1, fun hxs => hx.2 (Or.inr hxs)⟩
  · intro B hB x hx y hy
    apply regimeRun_eq_of_head_predicates
    intro r hr
    have hxr : x ∈ B \ Z := ⟨hx.1, fun hxz => hx.2 (Or.inl hxz)⟩
    have hyr : y ∈ B \ Z := ⟨hy.1, fun hyz => hy.2 (Or.inl hyz)⟩
    let rf : Fin (T.length + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
    have hcmp : ∀ b : Fin 2, x ∈ historyOrderSuperlevel 𝔪 T r (o + b) ↔
        y ∈ historyOrderSuperlevel 𝔪 T r (o + b) := by
      intro b
      exact (hdict B hB x hxr rf b).trans (hdict B hB y hyr rf b).symm
    have hzero : x ∈ historyOrderSuperlevel 𝔪 T r o ↔
        y ∈ historyOrderSuperlevel 𝔪 T r o := by simpa using hcmp 0
    have hone : x ∈ historyOrderSuperlevel 𝔪 T r (o + 1) ↔
        y ∈ historyOrderSuperlevel 𝔪 T r (o + 1) := by simpa using hcmp 1
    rw [ordRegime_head_iff_historyOrderSuperlevel, ordRegime_head_iff_historyOrderSuperlevel,
      hzero, hone]

end ActualHistory

end
end Hironaka.HironakaCurveAnalyticPredicates
