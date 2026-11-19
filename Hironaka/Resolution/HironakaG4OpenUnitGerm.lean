import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.HomogenizedIdeal

/-! Unit and nonunit ideal germs are unchanged by open inclusion. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OpenUnitGerm
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdealRestrictOpen RelativePrincipalizationSpan

variable {n : ℕ} {X : CMfd.{u} n}

/-- The pullback of a coherent ideal to an open has a unit germ exactly at
the points where the ambient ideal has a unit germ. -/
theorem pullback_val_unit_iff (U : Opens X) (I : GermIdeal n X) (hI : I.IsCoherent) (x : U) :
    (GermIdeal.pullback (m := n) (Subtype.val : U → X) I).mem x 1 ↔ I.mem x.val 1 := by
  rw [mem_pullback_val_iff U hI]
  have he : extendOpens U (1 : U → ℂ) =ᶠ[𝓝 x.val] (1 : X → ℂ) := by
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    exact extendOpens_val U (1 : U → ℂ) ⟨y,hy⟩
  exact ⟨fun h => HomogenizedIdeal.mem_congr hI h he,
    fun h => HomogenizedIdeal.mem_congr hI h he.symm⟩

end
end Hironaka.HironakaG4OpenUnitGerm
