import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenPullback
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf

/-!
# The native global centre ideal on actual original embedded charts is the SAME ambient I_C

Actual chart j OI +ordinary original centre containment/point trace internally
derive ENTIRE stalk ideal equality and FULL native component/module-sheaf
comparison to the EXISTING actual canonical ambient centre image module.
No ideal dictionary/iso/factorization supplied; original maps/source retained.
Arbitrary later pulled ideals retain full images and nonradical multiplicities.

Blueprint: `hironaka-intrinsic-reduced-centre-chart-ideal.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaIntrinsicReducedCentreChartIdeal

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreOpenPullback HironakaNativePulledIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf

noncomputable section
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : LocallyRingedSpace} {W C₀ : Set M}

/-- Ordinary ORIGINAL centre point trace yields the literal source subset equality. -/
theorem centre_trace_preimage_eq
    (j : actualSubspaceLocallyRingedSpace (n := n) W ⟶ Z) (C : Set Z)
    (htrace : ∀ w : W, j.base w ∈ C ↔ w.val ∈ C₀) :
    j.base ⁻¹' C = (Subtype.val : W → M) ⁻¹' C₀ := by
  ext w
  exact htrace w

/-- The actual native global target centre pullback is EXACTLY SAME ambient whole I_C₀ image. -/
theorem chart_pulled_stalkIdeal_eq
    (j : actualSubspaceLocallyRingedSpace (n := n) W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Z) (hCW : C₀ ⊆ W)
    (htrace : ∀ w : W, j.base w ∈ C ↔ w.val ∈ C₀) (w : W) :
    nativePulledIdealStalkIdeal j (intrinsicReducedCentreIdealModule Z C)
      (intrinsicReducedCentreIdealInclusion Z C) w =
      Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap w).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C₀) w.val) := by
  calc
    _ = intrinsicCentreStalkRange (actualSubspaceLocallyRingedSpace (n := n) W)
        (j.base ⁻¹' C) w := openImmersion_pulled_stalkIdeal_eq j C w
    _ = intrinsicCentreStalkRange (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C₀) w :=
      congrArg (fun D => intrinsicCentreStalkRange
        (actualSubspaceLocallyRingedSpace (n := n) W) D w) (centre_trace_preimage_eq j C htrace)
    _ = _ := intrinsicReducedCentreStalkInclusion_range_model hCW w

/-- EVERY original component is the EXISTING canonical ambient centre image section ideal. -/
theorem chart_pulled_sectionIdeal_eq
    (j : actualSubspaceLocallyRingedSpace (n := n) W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Z) (hCW : C₀ ⊆ W)
    (htrace : ∀ w : W, j.base w ∈ C ↔ w.val ∈ C₀)
    (U : Opens (actualSubspaceLocallyRingedSpace (n := n) W).toTopCat) :
    nativePulledIdealSectionIdeal j (intrinsicReducedCentreIdealModule Z C)
      (intrinsicReducedCentreIdealInclusion Z C) U =
      actualPulledCentreSectionIdeal (actualSubspaceInclusion (n := n) W) C₀ U := by
  ext s
  constructor
  · intro hs w hw
    exact (chart_pulled_stalkIdeal_eq j C hCW htrace w) ▸ hs w hw
  · intro hs w hw
    exact (chart_pulled_stalkIdeal_eq j C hCW htrace w).symm ▸ hs w hw

/-- The actual native original unit submodules are SAME, not a supplied certificate. -/
theorem chart_pulled_submodule_eq
    (j : actualSubspaceLocallyRingedSpace (n := n) W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Z) (hCW : C₀ ⊆ W)
    (htrace : ∀ w : W, j.base w ∈ C ↔ w.val ∈ C₀) :
    nativePulledIdealSubmodule j (intrinsicReducedCentreIdealModule Z C)
      (intrinsicReducedCentreIdealInclusion Z C) =
      actualPulledCentreSubmodule (actualSubspaceInclusion (n := n) W) C₀ := by
  apply PresheafOfModules.Submodule.ext
  intro U
  exact chart_pulled_sectionIdeal_eq j C hCW htrace (unop U)

/-- FULL native actual sheaf iso to the EXISTING canonical ambient centre ideal module. -/
def chart_pulled_idealIso
    (j : actualSubspaceLocallyRingedSpace (n := n) W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Z) (hCW : C₀ ⊆ W)
    (htrace : ∀ w : W, j.base w ∈ C ↔ w.val ∈ C₀) :
    nativePulledIdealModule j (intrinsicReducedCentreIdealModule Z C)
      (intrinsicReducedCentreIdealInclusion Z C) ≅
      actualPulledCentreIdealModule (actualSubspaceInclusion (n := n) W) C₀ where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (chart_pulled_submodule_eq j C hCW htrace).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (chart_pulled_submodule_eq j C hCW htrace).ge⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

@[simp] theorem chart_pulled_idealIso_hom_app_val
    (j : actualSubspaceLocallyRingedSpace (n := n) W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Z) (hCW : C₀ ⊆ W)
    (htrace : ∀ w : W, j.base w ∈ C ↔ w.val ∈ C₀)
    (U : Opens (actualSubspaceLocallyRingedSpace (n := n) W).toTopCat)
    (s : nativePulledIdealSectionIdeal j (intrinsicReducedCentreIdealModule Z C)
      (intrinsicReducedCentreIdealInclusion Z C) U) :
    ((chart_pulled_idealIso j C hCW htrace).hom.val.app (op U) s).val = s.val := rfl

@[simp] theorem chart_pulled_idealIso_inv_app_val
    (j : actualSubspaceLocallyRingedSpace (n := n) W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Z) (hCW : C₀ ⊆ W)
    (htrace : ∀ w : W, j.base w ∈ C ↔ w.val ∈ C₀)
    (U : Opens (actualSubspaceLocallyRingedSpace (n := n) W).toTopCat)
    (s : actualPulledCentreSectionIdeal (actualSubspaceInclusion (n := n) W) C₀ U) :
    ((chart_pulled_idealIso j C hCW htrace).inv.val.app (op U) s).val = s.val := rfl

/-- The actual WHOLE original inclusion triangle into O_W commutes. -/
theorem chart_pulled_idealIso_hom_comp_inclusion
    (j : actualSubspaceLocallyRingedSpace (n := n) W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Z) (hCW : C₀ ⊆ W)
    (htrace : ∀ w : W, j.base w ∈ C ↔ w.val ∈ C₀) :
    (chart_pulled_idealIso j C hCW htrace).hom ≫
      actualPulledCentreIdealInclusion (actualSubspaceInclusion (n := n) W) C₀ =
      nativePulledIdealInclusion j (intrinsicReducedCentreIdealModule Z C)
        (intrinsicReducedCentreIdealInclusion Z C) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (chart_pulled_submodule_eq j C hCW htrace).le

/-- The inverse actual WHOLE original inclusion triangle also commutes. -/
theorem chart_pulled_idealIso_inv_comp_inclusion
    (j : actualSubspaceLocallyRingedSpace (n := n) W ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Z) (hCW : C₀ ⊆ W)
    (htrace : ∀ w : W, j.base w ∈ C ↔ w.val ∈ C₀) :
    (chart_pulled_idealIso j C hCW htrace).inv ≫
      nativePulledIdealInclusion j (intrinsicReducedCentreIdealModule Z C)
        (intrinsicReducedCentreIdealInclusion Z C) =
      actualPulledCentreIdealInclusion (actualSubspaceInclusion (n := n) W) C₀ := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (chart_pulled_submodule_eq j C hCW htrace).ge

end
end Hironaka.HironakaIntrinsicReducedCentreChartIdeal
