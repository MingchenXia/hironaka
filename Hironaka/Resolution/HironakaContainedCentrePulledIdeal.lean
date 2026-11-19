import Hironaka.Resolution.HironakaIntrinsicReducedCentreIdealModel
import Hironaka.Resolution.HironakaNativePulledIdealSheaf
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf

/-!
# SAME intrinsic contained-centre ideal pulled through ANY full original source map

Containment C⊆W is essential. The source T and its map need no native analytic
charts, global countability or open-immersion certificate. All source ideals
remain the entire image, which can be nonradical. Blueprint FIRST:
`hironaka-contained-centre-pulled-ideal.tex`.
-/

noncomputable section
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaContainedCentrePulledIdeal

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaNativePulledIdealSheaf HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {T : LocallyRingedSpace.{0}} {W C : Set M}
  (F : T ⟶ actualSubspaceLocallyRingedSpace (n := n) W)

/-- Both ENTIRE ideal images follow from actual containment and full stalk composition. -/
theorem pulled_stalkIdeal_eq (hCW : C ⊆ W) (t : T) :
    nativePulledIdealStalkIdeal F
      (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C)) t =
      Ideal.map ((F ≫ actualSubspaceInclusion (n := n) W).stalkMap t).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F.base t).val) := by
  change Ideal.map (F.stalkMap t).hom
    (LinearMap.range (intrinsicReducedCentreStalkInclusion
      (actualSubspaceLocallyRingedSpace (n := n) W)
      ((Subtype.val : W → M) ⁻¹' C) (F.base t))) = _
  rw [intrinsicReducedCentreStalkInclusion_range_model hCW (F.base t),
    Ideal.map_map,LocallyRingedSpace.stalkMap_comp]
  rfl

/-- EVERY actual source section is the SAME canonical original centre-image section. -/
theorem pulled_sectionIdeal_eq (hCW : C ⊆ W) (U : Opens T.toTopCat) :
    nativePulledIdealSectionIdeal F
      (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C)) U =
      actualPulledCentreSectionIdeal (F ≫ actualSubspaceInclusion (n := n) W) C U := by
  ext s
  constructor
  · intro hs t ht
    exact (pulled_stalkIdeal_eq F hCW t) ▸ hs t ht
  · intro hs t ht
    exact (pulled_stalkIdeal_eq F hCW t).symm ▸ hs t ht

/-- Native original unit submodules, including restrictions and actions, coincide. -/
theorem pulled_submodule_eq (hCW : C ⊆ W) :
    nativePulledIdealSubmodule F
      (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C)) =
      actualPulledCentreSubmodule (F ≫ actualSubspaceInclusion (n := n) W) C := by
  apply PresheafOfModules.Submodule.ext
  intro U
  exact pulled_sectionIdeal_eq F hCW (unop U)

/-- FULL native sheaf iso, derived without an incoming ideal/comparison certificate. -/
def pulled_idealIso (hCW : C ⊆ W) :
    nativePulledIdealModule F
      (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C)) ≅
      actualPulledCentreIdealModule (F ≫ actualSubspaceInclusion (n := n) W) C where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (pulled_submodule_eq F hCW).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (pulled_submodule_eq F hCW).ge⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

@[simp] theorem pulled_idealIso_hom_app_val (hCW : C ⊆ W) (U : Opens T.toTopCat)
    (s : nativePulledIdealSectionIdeal F
      (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C)) U) :
    ((pulled_idealIso F hCW).hom.val.app (op U) s).val = s.val := rfl

@[simp] theorem pulled_idealIso_inv_app_val (hCW : C ⊆ W) (U : Opens T.toTopCat)
    (s : actualPulledCentreSectionIdeal (F ≫ actualSubspaceInclusion (n := n) W) C U) :
    ((pulled_idealIso F hCW).inv.val.app (op U) s).val = s.val := rfl

/-- The ENTIRE original structure-unit inclusion triangle commutes. -/
theorem pulled_idealIso_hom_comp_inclusion (hCW : C ⊆ W) :
    (pulled_idealIso F hCW).hom ≫
      actualPulledCentreIdealInclusion (F ≫ actualSubspaceInclusion (n := n) W) C =
      nativePulledIdealInclusion F
        (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
          ((Subtype.val : W → M) ⁻¹' C))
        (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
          ((Subtype.val : W → M) ⁻¹' C)) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (pulled_submodule_eq F hCW).le

/-- The inverse FULL original structure-unit inclusion triangle also commutes. -/
theorem pulled_idealIso_inv_comp_inclusion (hCW : C ⊆ W) :
    (pulled_idealIso F hCW).inv ≫
      nativePulledIdealInclusion F
        (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
          ((Subtype.val : W → M) ⁻¹' C))
        (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
          ((Subtype.val : W → M) ⁻¹' C)) =
      actualPulledCentreIdealInclusion (F ≫ actualSubspaceInclusion (n := n) W) C := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (pulled_submodule_eq F hCW).ge

end Hironaka.HironakaContainedCentrePulledIdeal
