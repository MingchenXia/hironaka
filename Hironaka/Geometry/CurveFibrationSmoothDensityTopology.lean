import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Separation.Basic

/-! # Density outside a discrete subset of a space without isolated points -/

namespace Hironaka.Geometry.CurveFibrationSmoothDensity

universe u

/-- A discrete subset has dense complement if the ambient space has no open singleton. -/
theorem dense_compl_of_isDiscrete_of_no_open_singleton
    {T : Type u} [TopologicalSpace T] {B : Set T}
    (hB : IsDiscrete B) (hT : ∀ x : T, ¬ IsOpen ({x} : Set T)) : Dense Bᶜ := by
  intro x
  by_contra hx
  let V : Set T := (closure Bᶜ)ᶜ
  have hV : IsOpen V := isClosed_closure.isOpen_compl
  have hxV : x ∈ V := hx
  have hVB : V ⊆ B := by
    intro y hy
    by_contra hyB
    exact hy (subset_closure hyB)
  obtain ⟨W, hW, hWB⟩ := isOpen_inter_eq_singleton_of_mem_discrete hB (hVB hxV)
  have hVW : V ∩ W = {x} := by
    apply Set.Subset.antisymm
    · rintro y ⟨hyV, hyW⟩
      exact hWB ▸ ⟨hyW, hVB hyV⟩
    · intro y hy
      have hyx := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨hxV, (show x ∈ W ∩ B from hWB.symm ▸ Set.mem_singleton x).1⟩
  exact hT x (hVW ▸ hV.inter hW)

end Hironaka.Geometry.CurveFibrationSmoothDensity
