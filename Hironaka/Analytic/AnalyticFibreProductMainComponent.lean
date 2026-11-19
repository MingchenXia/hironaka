import Hironaka.Analytic.AnalyticModificationStrongPullback
import Hironaka.Analytic.ConstantRankImage
import Hironaka.Analytic.ProductMapIsomorphismOver
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Resolution.HironakaAuxiliaryGraphGeometry
import Hironaka.Analytic.AnalyticComplementConnected
import Hironaka.Analytic.GlobalComponents
import Hironaka.Analytic.ProductComplexManifold
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.AnalyticFibreProductCarrier

/-! # The actual analytic fibre-product carrier and its main irreducible component

This work source first constructs closedness and actual finite local
holomorphic presentations of the WHOLE equalizer carrier. From the original
two analytic modifications over a connected smooth base it then constructs
the actual main irreducible component, its dimension and its equality with
the common isomorphism graph's closure. No such component or dimension is
supplied. Smooth common resolution, finite-over-base Chow domination and
identification with the original prime quotient remain subsequent work.
Dimensions and original product points are unchanged.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.AnalyticFibreProductMainComponent

open Hironaka.BlowupSequences
  AnalyticModificationLocalDiscrepancy ProductComplexManifold
  RegularLocusComponent GlobalComponents
open Set Filter
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

universe u

section Regularity

variable {n m : ℕ} {X Y₀ Y₁ : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel m) Y₁] [IsComplexManifold m Y₁]

/-- The actual fibre product is regular where the first original map is a
local biholomorphism: it is the literal pullback of the second map's graph. -/
theorem regularAtDim_fibreProduct_of_not_exceptional_left
    {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ c₀)
    (hc₁ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ c₁)
    {p : Y₀ × Y₁} (hp₀ : p.1 ∉ exceptionalLocus n c₀)
    (hp : c₀ p.1 = c₁ p.2) :
    RegularAtDim (n := n + m) {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2} p m := by
  let ν : Y₀ × Y₁ → X × Y₁ := Prod.map c₀ id
  have hν : ContMDiff 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ∞ ν :=
    ProductComplexManifold.contMDiff_prodMap hc₀ contMDiff_id
  have hnp : p ∉ exceptionalLocus (n + m) ν :=
    ProductMapIsomorphismOver.not_mem_exceptionalLocus_prodMap hc₀ hp₀ p.2
  have hreg : RegularAtDim (n := n + m)
      (HironakaAuxiliaryGraphGeometry.graphOn c₁ univ) (ν p) m := by
    have heq : ν p = (c₁ p.2, p.2) := Prod.ext hp rfl
    rw [heq]
    exact HironakaAuxiliaryGraphGeometry.regularAtDim_graph hc₁
      (AnalyticIrreducibleComponents.regularAtDim_univ p.2)
  apply RegularAtDimTransport.regularAtDim_of_preimage hν hnp isOpen_univ
    (mem_univ p) _ hreg
  intro q _hq
  change (c₀ q.1 = c₁ q.2) ↔ (q.2 ∈ (univ : Set Y₁) ∧ c₀ q.1 = c₁ q.2)
  simp only [mem_univ, true_and]

end Regularity

section MainComponent

variable {n : ℕ} {X Y₀ Y₁ : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- Original modification geometry internally produces the actual n-dimensional
main irreducible component as the closure of the SAME common isomorphism graph.
No compactness, desired component, dimension, resolution or reader is assumed. -/
theorem exists_actual_mainComponent {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁) :
    ∃ B : Set X, IsClosed B ∧ IsComplexAnalyticSubset (n := n) B ∧ interior B = ∅ ∧
      ∃ V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁),
        V.dim = n ∧
        V.carrier ∈ globalComponents (n := n + n) {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
        V.carrier = closure {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B} ∧
        V.carrier ⊆ {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} := by
  classical
  obtain ⟨A₀, B₀, s₀, _hA₀c, _hA₀a, _hA₀i, hB₀c, hB₀a, hB₀i,
    hpre₀, hs₀, hright₀, hleft₀⟩ := hc₀.2.2
  obtain ⟨A₁, B₁, s₁, _hA₁c, _hA₁a, _hA₁i, hB₁c, hB₁a, hB₁i,
    hpre₁, hs₁, hright₁, hleft₁⟩ := hc₁.2.2
  obtain ⟨D, hDc, hDa, hDi, _hpreDa, _hpreDi, hiso⟩ :=
    AnalyticModificationStrongPullback.exists_isIsomorphismOver_of_isAnalyticModification hc₀
  let B : Set X := (B₀ ∪ B₁) ∪ D
  have hBc : IsClosed B := (hB₀c.union hB₁c).union hDc
  have hBa : IsComplexAnalyticSubset (n := n) B :=
    ConstantRankImage.IsComplexAnalyticSubset.union
      (ConstantRankImage.IsComplexAnalyticSubset.union hB₀a hB₁a) hDa
  have hBi : interior B = ∅ := by
    dsimp only [B]
    rw [interior_union_isClosed_of_interior_empty (hB₀c.union hB₁c) hDi,
      interior_union_isClosed_of_interior_empty hB₀c hB₁i]
    exact hB₀i
  have hUne : (Bᶜ).Nonempty := (interior_eq_empty_iff_dense_compl.mp hBi).nonempty
  have hBne : B ≠ univ := by
    intro heq
    obtain ⟨x, hx⟩ := hUne
    exact hx (heq.symm ▸ mem_univ x)
  let F : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2}
  let S : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B}
  let γ : X → Y₀ × Y₁ := fun x => (s₀ x, s₁ x)
  have hSimage : S = γ '' Bᶜ := by
    ext p
    constructor
    · rintro ⟨hpF, hpB⟩
      have hpB₀ : c₀ p.1 ∉ B₀ := fun h => hpB (Or.inl (Or.inl h))
      have hpB₁ : c₁ p.2 ∉ B₁ := by
        intro h
        apply hpB
        apply Or.inl
        apply Or.inr
        rwa [hpF]
      have hpA₀ : p.1 ∉ A₀ := by
        intro h
        apply hpB₀
        change p.1 ∈ c₀ ⁻¹' B₀
        rwa [hpre₀]
      have hpA₁ : p.2 ∉ A₁ := by
        intro h
        apply hpB₁
        change p.2 ∈ c₁ ⁻¹' B₁
        rwa [hpre₁]
      refine ⟨c₀ p.1, hpB, ?_⟩
      apply Prod.ext
      · exact hleft₀ p.1 hpA₀
      · change s₁ (c₀ p.1) = p.2
        rw [hpF]
        exact hleft₁ p.2 hpA₁
    · rintro ⟨x, hx, rfl⟩
      have hx₀ : x ∉ B₀ := fun h => hx (Or.inl (Or.inl h))
      have hx₁ : x ∉ B₁ := fun h => hx (Or.inl (Or.inr h))
      change c₀ (s₀ x) = c₁ (s₁ x) ∧ c₀ (s₀ x) ∉ B
      rw [hright₀ x hx₀, hright₁ x hx₁]
      exact ⟨rfl, hx⟩
  have hU₀ : Bᶜ ⊆ B₀ᶜ := by
    intro x hx h
    exact hx (Or.inl (Or.inl h))
  have hU₁ : Bᶜ ⊆ B₁ᶜ := by
    intro x hx h
    exact hx (Or.inl (Or.inr h))
  have hγ : ContinuousOn γ Bᶜ :=
    (hs₀.continuousOn.mono hU₀).prodMk (hs₁.continuousOn.mono hU₁)
  have hSconn : IsPreconnected S := by
    rw [hSimage]
    exact (AnalyticComplementConnected.isPreconnected_compl hBa hBne).image γ hγ
  have hSne : S.Nonempty := by
    rw [hSimage]
    exact hUne.image γ
  have hSreg (p : Y₀ × Y₁) (hp : p ∈ S) : RegularAtDim (n := n + n) F p n := by
    have hpD : c₀ p.1 ∈ Dᶜ := fun h => hp.2 (Or.inr h)
    have hnp : p.1 ∉ exceptionalLocus n c₀ := Set.disjoint_left.mp hiso.2 hpD
    exact regularAtDim_fibreProduct_of_not_exceptional_left hc₀.1 hc₁.1 hnp hp.1
  obtain ⟨c, hcS⟩ := hSne
  have hc : RegularAtDim (n := n + n) F c n := hSreg c hcS
  let C : Set (Y₀ × Y₁) := component (n := n + n) F c
  have hSC : S ⊆ C := subset_component_of_isPreconnected hSconn
    (fun p hp => ⟨n, hSreg p hp⟩) ⟨c, hcS, mem_component_self hc⟩
  have hFa : IsComplexAnalyticSubset (n := n + n) F :=
    AnalyticFibreProductCarrier.isComplexAnalyticSubset_fibreProduct hc₀.1 hc₁.1
  let T : Set (Y₀ × Y₁) := (fun p => c₀ p.1) ⁻¹' B
  have hTa : IsComplexAnalyticSubset (n := n + n) T :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (hc₀.1.comp ProductComplexManifold.contMDiff_fst) hBa
  have hCT : ¬ C ⊆ T := fun h => hcS.2 (h (mem_component_self hc))
  have hCS : C \ T ⊆ S := fun p hp => ⟨component_subset F c hp.1, hp.2⟩
  have hCdense := (ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
    hFa hTa hc hCT).2
  have hclosure : closure C = closure S := by
    apply Set.Subset.antisymm
    · exact closure_minimal (hCdense.trans (closure_mono hCS)) isClosed_closure
    · exact closure_mono hSC
  let V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁) :=
    { carrier := closure C
      isClosed_carrier := isClosed_closure
      irreducible_carrier := isComplexAnalyticallyIrreducible_closure_component hFa hc
      dim := n
      dim_le := Nat.le_add_right n n
      regularLocus_nonempty := ⟨c, regularAtDim_closure_component hc (mem_component_self hc)⟩ }
  exact ⟨B, hBc, hBa, hBi, V, rfl, closure_component_mem_globalComponents hc,
    hclosure, closure_minimal (component_subset F c) hFa.isClosed⟩

end MainComponent
end Hironaka.AnalyticFibreProductMainComponent
