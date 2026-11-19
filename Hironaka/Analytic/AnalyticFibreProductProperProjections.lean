import Mathlib.Topology.Maps.Proper.Basic
import Hironaka.Analytic.AnalyticFibreProductMainComponent

/-! # Proper projections of the actual analytic fibre-product main component

Both coordinate projections from any actual closed subset of the literal
fibre product are proper, using the original opposite map's properness.
The final consumer obtains the genuine main component from the two original
analytic modifications and constructs properness of both actual subtype
projections. No manifold instance is imposed on the possibly singular carrier.
No compactness, component, dimension or projection properness is supplied.
Smooth resolution and holomorphic resolved projection maps remain subsequent
geometric constructions.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.AnalyticFibreProductProperProjections

section Topological

variable {X Y₀ Y₁ : Type*}
  [TopologicalSpace X] [TopologicalSpace Y₀] [TopologicalSpace Y₁]

/-- The first actual coordinate projection of any closed subset of the literal
fibre product is proper when the original second map is proper. -/
theorem isProperMap_fst_of_closed_fibreProduct
    {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : Continuous c₀) (hc₁ : IsProperMap c₁)
    {S : Set (Y₀ × Y₁)} (hS : IsClosed S)
    (hSF : S ⊆ {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2}) :
    IsProperMap (fun p : S => p.val.1) := by
  let π : S → Y₀ := fun p => p.val.1
  let j : Y₀ → Y₀ × X := fun y => (y, c₀ y)
  have hπ : Continuous π := continuous_fst.comp continuous_subtype_val
  have hj : Continuous j := continuous_id.prodMk hc₀
  have hprod : IsProperMap (Prod.map (id : Y₀ → Y₀) c₁) :=
    isProperMap_id.prodMap hc₁
  have hcomp : IsProperMap (j ∘ π) := by
    have heq : j ∘ π = fun p : S => Prod.map (id : Y₀ → Y₀) c₁ p.val := by
      funext p
      exact Prod.ext rfl (hSF p.property)
    rw [heq]
    exact hprod.restrict hS
  exact isProperMap_of_comp_of_inj hπ hj hcomp
    (fun _ _ h => congrArg Prod.fst h)

/-- The second actual coordinate projection of any closed subset of the literal
fibre product is proper when the original first map is proper. -/
theorem isProperMap_snd_of_closed_fibreProduct
    {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsProperMap c₀) (hc₁ : Continuous c₁)
    {S : Set (Y₀ × Y₁)} (hS : IsClosed S)
    (hSF : S ⊆ {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2}) :
    IsProperMap (fun p : S => p.val.2) := by
  let π : S → Y₁ := fun p => p.val.2
  let j : Y₁ → X × Y₁ := fun y => (c₁ y, y)
  have hπ : Continuous π := continuous_snd.comp continuous_subtype_val
  have hj : Continuous j := hc₁.prodMk continuous_id
  have hprod : IsProperMap (Prod.map c₀ (id : Y₁ → Y₁)) :=
    hc₀.prodMap isProperMap_id
  have hcomp : IsProperMap (j ∘ π) := by
    have heq : j ∘ π = fun p : S => Prod.map c₀ (id : Y₁ → Y₁) p.val := by
      funext p
      exact Prod.ext (hSF p.property).symm rfl
    rw [heq]
    exact hprod.restrict hS
  exact isProperMap_of_comp_of_inj hπ hj hcomp
    (fun _ _ h => congrArg Prod.snd h)

end Topological

open Hironaka.BlowupSequences
  AnalyticModificationLocalDiscrepancy GlobalComponents

universe u

section MainComponent

variable {n : ℕ} {X Y₀ Y₁ : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- The original proper modification maps internally produce the actual main
irreducible component, with all its geometric clauses and BOTH proper actual
subtype coordinate projections. The possibly singular carrier has only its
inherited topology in the projection conclusions. -/
theorem exists_actual_mainComponent_proper_projections
    {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁) :
    ∃ B : Set X, IsClosed B ∧ IsComplexAnalyticSubset (n := n) B ∧ interior B = ∅ ∧
      ∃ V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁),
        V.dim = n ∧
        V.carrier ∈ globalComponents (n := n + n) {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
        V.carrier = closure {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B} ∧
        V.carrier ⊆ {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
        IsProperMap (fun p : V.carrier => p.val.1) ∧
        IsProperMap (fun p : V.carrier => p.val.2) := by
  obtain ⟨B, hBc, hBa, hBi, V, hVdim, hVglobal, hVclosure, hVF⟩ :=
    AnalyticFibreProductMainComponent.exists_actual_mainComponent hc₀ hc₁
  refine ⟨B, hBc, hBa, hBi, V, hVdim, hVglobal, hVclosure, hVF, ?_, ?_⟩
  · exact isProperMap_fst_of_closed_fibreProduct hc₀.1.continuous hc₁.2.1
      V.isClosed_carrier hVF
  · exact isProperMap_snd_of_closed_fibreProduct hc₀.2.1 hc₁.1.continuous
      V.isClosed_carrier hVF

end MainComponent
end Hironaka.AnalyticFibreProductProperProjections
