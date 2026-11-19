import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
import Hironaka.Resolution.HironakaSingularModuleSheafStalk
import Hironaka.Resolution.HironakaActualAnalyticSubspaceMaps

/-!
# The actual canonical ideal-module stalk is EXACTLY the original pulled ideal

The actual sheaf inclusion induces the native linear stalk map; its image
is proved equal to the SAME original Ideal.map, by true centre sections and
the SAME original H.c.app. No stalk dictionary or alternative ideal is input.
Native scalar actions, unit-stalk comparison and injectivity are reused.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-ideal-stalk.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalIdealStalk

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf HironakaSingularModuleSheafStalk

noncomputable section

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {X : LocallyRingedSpace}

/-- A transparent forwarding alias for the SAME native module-stalk action. -/
abbrev actualPulledCentreNativeStalkModule
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) (x : X) :
    Module (X.presheaf.stalk x).carrier
      ↑(TopCat.Presheaf.stalk (actualPulledCentreIdealModule H C).val.presheaf x) :=
  nativeSheafStalkModule X.toSheafedSpace.sheaf (actualPulledCentreIdealModule H C) x

attribute [instance] actualPulledCentreNativeStalkModule

/-- The SAME actual sheaf inclusion, on native original module stalks. -/
def actualPulledCentreStalkInclusion
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) (x : X) :
    ↑(TopCat.Presheaf.stalk (actualPulledCentreIdealModule H C).val.presheaf x) →ₗ[
      (X.presheaf.stalk x).carrier] (X.presheaf.stalk x).carrier :=
  stalkInclusionLinearMap X.toSheafedSpace.sheaf (actualPulledCentreIdealModule H C)
    (actualPulledCentreIdealInclusion H C) x

/-- Every actual module germ retains its ORIGINAL inclusion germ formula. -/
@[simp] theorem actualPulledCentreStalkInclusion_germ
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M)
    (x : X) (U : Opens X.toTopCat) (hx : x ∈ U) (s : actualPulledCentreSectionIdeal H C U) :
    actualPulledCentreStalkInclusion H C x
      (TopCat.Presheaf.germ (actualPulledCentreIdealModule H C).val.presheaf U x hx s) =
      X.presheaf.germ U x hx s.val :=
  stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf (actualPulledCentreIdealModule H C)
    (actualPulledCentreIdealInclusion H C) x U hx s

/-- BOTH ENTIRE actual ideal inclusions are proved from the original actual
centre section germ dictionary and the same full original H.c.app. -/
theorem actualPulledCentreStalkInclusion_range
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) (x : X) :
    LinearMap.range (actualPulledCentreStalkInclusion H C x) =
      Ideal.map (H.stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base x)) := by
  apply le_antisymm
  · rintro r ⟨m, rfl⟩
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (actualPulledCentreIdealModule H C).val.presheaf m
    exact (actualPulledCentreStalkInclusion_germ H C x U hxU s).symm ▸ s.property x hxU
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    have hsection : a ∈ actualIdealSectionGermImage (vanishingIdeal (n := n) C) (H.base x) := by
      rw [actualCentreIdealSectionGermImage_eq_whole]
      exact ha
    obtain ⟨V, hxV, t, ht⟩ := hsection
    refine ⟨TopCat.Presheaf.germ (actualPulledCentreIdealModule H C).val.presheaf
      ((Opens.map H.base).obj V) x hxV (actualPulledCentreSection H C V t), ?_⟩
    exact (actualPulledCentreStalkInclusion_germ H C x _ hxV
      (actualPulledCentreSection H C V t)).trans
      ((actualPulledCentreSection_germ H C V t x hxV).trans
        (congrArg (H.stalkMap x).hom ht))

/-- Native componentwise subtype inclusion proves actual stalk injectivity. -/
theorem actualPulledCentreStalkInclusion_injective
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) (x : X) :
    Function.Injective (actualPulledCentreStalkInclusion H C x) :=
  stalkInclusionLinearMap_injective X.toSheafedSpace.sheaf (actualPulledCentreIdealModule H C)
    (actualPulledCentreIdealInclusion H C) (fun _ => Subtype.val_injective) x

/-- The actual native module stalk is linearly the SAME original whole
pulled ideal, with no supplied dictionary or equivalence certificate. -/
def actualPulledCentreStalkIdealEquiv
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) (x : X) :
    ↑(TopCat.Presheaf.stalk (actualPulledCentreIdealModule H C).val.presheaf x) ≃ₗ[
      (X.presheaf.stalk x).carrier]
      Ideal.map (H.stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base x)) := by
  let f := (actualPulledCentreStalkInclusion H C x).codRestrict
    (Ideal.map (H.stalkMap x).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base x)))
    (fun m => by rw [← actualPulledCentreStalkInclusion_range H C x]; exact ⟨m, rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b hab
    exact actualPulledCentreStalkInclusion_injective H C x (congrArg Subtype.val hab)
  · intro r
    have hr : r.val ∈ LinearMap.range (actualPulledCentreStalkInclusion H C x) := by
      rw [actualPulledCentreStalkInclusion_range]
      exact r.property
    obtain ⟨m, hm⟩ := hr
    exact ⟨m, Subtype.ext hm⟩

/-- The actual linear equivalence keeps every original actual section germ. -/
@[simp] theorem actualPulledCentreStalkIdealEquiv_germ
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M)
    (x : X) (U : Opens X.toTopCat) (hx : x ∈ U) (s : actualPulledCentreSectionIdeal H C U) :
    (actualPulledCentreStalkIdealEquiv H C x
      (TopCat.Presheaf.germ (actualPulledCentreIdealModule H C).val.presheaf U x hx s)).val =
      X.presheaf.germ U x hx s.val := actualPulledCentreStalkInclusion_germ H C x U hx s

/-- For ORIGINAL subspace maps this is precisely the SAME original nested
projection/inclusion image ideal used by the global universal property. -/
theorem actualPulledCentreStalkInclusion_range_subspace {W : Set M}
    (F : X ⟶ actualSubspaceLocallyRingedSpace (n := n) W) (C : Set M) (x : X) :
    LinearMap.range (actualPulledCentreStalkInclusion (F ≫ actualSubspaceInclusion (n := n) W) C x) =
      Ideal.map (F.stalkMap x).hom
        (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.base x)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F.base x).val)) := by
  rw [actualPulledCentreStalkInclusion_range]
  let P : ((actualSubspaceSheaf (n := n) W).presheaf.stalk (F.base x)).carrier →+*
      (X.presheaf.stalk x).carrier := (F.stalkMap x).hom
  let Q : actualComplexStructureStalk (n := n) (F.base x).val →+*
      ((actualSubspaceSheaf (n := n) W).presheaf.stalk (F.base x)).carrier :=
    ((actualSubspaceInclusion (n := n) W).stalkMap (F.base x)).hom
  let H : actualComplexStructureStalk (n := n) (F.base x).val →+*
      (X.presheaf.stalk x).carrier := ((F ≫ actualSubspaceInclusion (n := n) W).stalkMap x).hom
  have hcomp : H = P.comp Q := by
    apply RingHom.ext
    intro r
    exact ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp F
      (actualSubspaceInclusion (n := n) W) x) r
  change Ideal.map H _ = Ideal.map P (Ideal.map Q _)
  rw [hcomp, Ideal.map_map]
  rfl

/-- Native actual module-stalk invertibility passes to the SAME original
pulled ideal by the internally proved actual linear equivalence. -/
theorem moduleInvertible_actual_pulled_ideal_of_module_stalk
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) (x : X)
    (hInv : Module.Invertible (X.presheaf.stalk x).carrier
      ↑(TopCat.Presheaf.stalk (actualPulledCentreIdealModule H C).val.presheaf x)) :
    Module.Invertible (X.presheaf.stalk x).carrier
      (Ideal.map (H.stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base x))) := by
  let : Module.Invertible (X.presheaf.stalk x).carrier
      ↑(TopCat.Presheaf.stalk (actualPulledCentreIdealModule H C).val.presheaf x) := hInv
  exact Module.Invertible.congr (actualPulledCentreStalkIdealEquiv H C x)

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalIdealStalk
