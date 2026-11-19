import Hironaka.Geometry.AlterationBasic

/-!
# Generic étaleness from an actual target isomorphism open

An actual isomorphism over a nonempty target open gives a dense étale open
in the integral source. No perfection or ground-field hypothesis is needed.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace Hironaka

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A dominant map with integral source which is an isomorphism over a
nonempty target open is generically étale in the source-open sense of 2.6. -/
theorem isGenericallyEtale_of_nonempty_isomorphism_open {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegral X] [IsDominant f] (U : Y.Opens)
    (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)] : IsGenericallyEtale f := by
  obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open U.isOpen hU
  refine ⟨f ⁻¹ᵁ U, (f ⁻¹ᵁ U).isOpen.dense ⟨x, hx⟩, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

end Hironaka
