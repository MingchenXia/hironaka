import Hironaka.Resolution.HironakaIntrinsicReducedCentreIdealSheaf
import Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions

/-!
# The intrinsic REDUCED-centre ideal is the SAME entire original embedded ideal

For the ORIGINAL containment C⊆W⊆M, the actual native intrinsic ideal-stalk
inclusion image equals precisely Ideal.map of the SAME original inclusion
stalk map and ENTIRE original ambient I_C. All local ambient representatives
are derived using actual quotient sections and native eval kernel=maximalIdeal.
No stalk dictionary, radical replacement, ambient lift or rank certificate input.

Blueprint: `hironaka-intrinsic-reduced-centre-ideal-model.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaIntrinsicReducedCentreIdealModel

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceResidue HironakaActualAnalyticSubspaceLocalFunctions
  HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreIdealSheaf

noncomputable section

section NativeStalk
universe u
variable (X : LocallyRingedSpace.{u})

/-- Transparent forwarding of the SAME existing native module-stalk action. -/
abbrev intrinsicReducedCentreNativeStalkModule (C : Set X) (x : X) :
    Module (X.presheaf.stalk x).carrier
      ↑(TopCat.Presheaf.stalk (intrinsicReducedCentreIdealModule X C).val.presheaf x) :=
  nativeSheafStalkModule X.toSheafedSpace.sheaf (intrinsicReducedCentreIdealModule X C) x

attribute [instance] intrinsicReducedCentreNativeStalkModule

/-- The actual intrinsic inclusion on native original module stalks. -/
def intrinsicReducedCentreStalkInclusion (C : Set X) (x : X) :
    ↑(TopCat.Presheaf.stalk (intrinsicReducedCentreIdealModule X C).val.presheaf x) →ₗ[
      (X.presheaf.stalk x).carrier] (X.presheaf.stalk x).carrier :=
  stalkInclusionLinearMap X.toSheafedSpace.sheaf (intrinsicReducedCentreIdealModule X C)
    (intrinsicReducedCentreIdealInclusion X C) x

@[simp] theorem intrinsicReducedCentreStalkInclusion_germ (C : Set X)
    (x : X) (U : Opens X.toTopCat) (hx : x ∈ U) (s : intrinsicReducedCentreSectionIdeal X C U) :
    intrinsicReducedCentreStalkInclusion X C x
      (TopCat.Presheaf.germ (intrinsicReducedCentreIdealModule X C).val.presheaf U x hx s) =
      X.presheaf.germ U x hx s.val :=
  stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf (intrinsicReducedCentreIdealModule X C)
    (intrinsicReducedCentreIdealInclusion X C) x U hx s

/-- Native componentwise subtype injectivity gives actual stalk injectivity. -/
theorem intrinsicReducedCentreStalkInclusion_injective (C : Set X) (x : X) :
    Function.Injective (intrinsicReducedCentreStalkInclusion X C x) :=
  stalkInclusionLinearMap_injective X.toSheafedSpace.sheaf (intrinsicReducedCentreIdealModule X C)
    (intrinsicReducedCentreIdealInclusion X C) (fun _ => Subtype.val_injective) x

end NativeStalk

section Model
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private instance actualStalkLocal (W : Set M) (x : W) :
    IsLocalRing ((actualSubspaceSheaf (n := n) W).presheaf.stalk x).carrier :=
  actualSubspaceStalk_isLocalRing (n := n) W x

/-- An original ambient centre section gives a genuine intrinsic ideal section
using the SAME original inclusion.c.app and native maximal-ideal definition. -/
def intrinsicReducedCentreModelSection (W C : Set M) (V : Opens M)
    (t : actualSectionIdeal (vanishingIdeal (n := n) C) V) :
    intrinsicReducedCentreSectionIdeal
      (actualSubspaceLocallyRingedSpace (n := n) W) ((Subtype.val : W → M) ⁻¹' C)
      ((Opens.map (actualSubspaceInclusion (n := n) W).base).obj V) := by
  let j := actualSubspaceInclusion (n := n) W
  refine ⟨j.c.app (op V) t.val, ?_⟩
  intro y hy hyC
  change (actualSubspaceSheaf (n := n) W).presheaf.germ _ y hy (j.c.app (op V) t.val) ∈
    IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := n) W).presheaf.stalk y).carrier
  rw [← actualSubspaceStalkEval_ker, RingHom.mem_ker]
  have hg := (LocallyRingedSpace.stalkMap_germ_apply j V y hy t.val).symm
  exact (congrArg (actualSubspaceStalkEval (n := n) W y) hg).trans
    ((actualSubspaceStalkEval_inclusion_germ W V t.val y hy).trans
      ((actualSectionIdeal_vanishing_iff C V t.val).mp t.property y.val hy hyC))

/-- The actual intrinsic section retains the original full inclusion germ formula. -/
theorem intrinsicReducedCentreModelSection_germ (W C : Set M) (V : Opens M)
    (t : actualSectionIdeal (vanishingIdeal (n := n) C) V) (x : W) (hx : x.val ∈ V) :
    (actualSubspaceLocallyRingedSpace (n := n) W).presheaf.germ
      ((Opens.map (actualSubspaceInclusion (n := n) W).base).obj V) x hx
      (intrinsicReducedCentreModelSection W C V t).val =
      (actualSubspaceInclusion (n := n) W).stalkMap x
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ V x.val hx t.val) := by
  change (actualSubspaceLocallyRingedSpace (n := n) W).presheaf.germ
    ((Opens.map (actualSubspaceInclusion (n := n) W).base).obj V) x hx
      ((actualSubspaceInclusion (n := n) W).c.app (op V) t.val) = _
  exact (LocallyRingedSpace.stalkMap_germ_apply
    (actualSubspaceInclusion (n := n) W) V x hx t.val).symm

/-- The ESSENTIAL original containment turns an intrinsic section's ACTUAL
local ambient representative into an actual original centre ideal section. -/
theorem intrinsicReducedCentreModelSection_germ_mem_image {W C : Set M} (hCW : C ⊆ W)
    (U : Opens (actualSubspaceLocallyRingedSpace (n := n) W).toTopCat)
    (s : ((actualSubspaceLocallyRingedSpace (n := n) W).presheaf.obj (op U)).carrier)
    (hs : s ∈ intrinsicReducedCentreSectionIdeal
      (actualSubspaceLocallyRingedSpace (n := n) W) ((Subtype.val : W → M) ⁻¹' C) U)
    (x : W) (hx : x ∈ U) :
    (actualSubspaceLocallyRingedSpace (n := n) W).presheaf.germ U x hx s ∈
      Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val) := by
  obtain ⟨O, hxO, t, hOU, ht⟩ := actualSubspaceSection_local_ambient W U s x hx
  have hvan : t ∈ actualSectionIdeal (vanishingIdeal (n := n) C) O := by
    apply (actualSectionIdeal_vanishing_iff C O t).mpr
    intro z hzO hzC
    let y : W := ⟨z, hCW hzC⟩
    have hm : actualSubspaceStalkEval (n := n) W y
        ((actualSubspaceSheaf (n := n) W).presheaf.germ U y (hOU y hzO) s) = 0 := by
      have hm := hs y (hOU y hzO) hzC
      change (actualSubspaceSheaf (n := n) W).presheaf.germ U y (hOU y hzO) s ∈
        IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := n) W).presheaf.stalk y).carrier at hm
      rw [← actualSubspaceStalkEval_ker, RingHom.mem_ker] at hm
      exact hm
    calc
      t ⟨z, hzO⟩ = actualSubspaceStalkEval (n := n) W y
          ((actualSubspaceInclusion (n := n) W).stalkMap y
            ((actualComplexStructureSheaf (n := n) M).presheaf.germ O z hzO t)) :=
        (actualSubspaceStalkEval_inclusion_germ W O t y hzO).symm
      _ = actualSubspaceStalkEval (n := n) W y
          ((actualSubspaceSheaf (n := n) W).presheaf.germ U y (hOU y hzO) s) :=
        congrArg (actualSubspaceStalkEval (n := n) W y) (ht y hzO).symm
      _ = 0 := hm
  exact (ht x hxO).symm ▸ Ideal.mem_map_of_mem
    ((actualSubspaceInclusion (n := n) W).stalkMap x).hom (hvan x.val hxO)

/-- BOTH ENTIRE ideal directions are proved: the actual intrinsic inclusion
stalk range is exactly the SAME original whole ambient centre ideal image. -/
theorem intrinsicReducedCentreStalkInclusion_range_model {W C : Set M}
    (hCW : C ⊆ W) (x : W) :
    LinearMap.range (intrinsicReducedCentreStalkInclusion
      (actualSubspaceLocallyRingedSpace (n := n) W) ((Subtype.val : W → M) ⁻¹' C) x) =
      Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val) := by
  let X := actualSubspaceLocallyRingedSpace (n := n) W
  let D : Set X := (Subtype.val : W → M) ⁻¹' C
  apply le_antisymm
  · rintro r ⟨m, rfl⟩
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (intrinsicReducedCentreIdealModule X D).val.presheaf m
    exact (intrinsicReducedCentreStalkInclusion_germ X D x U hxU s).symm ▸
      intrinsicReducedCentreModelSection_germ_mem_image hCW U s.val s.property x hxU
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    have hsection : a ∈ actualIdealSectionGermImage (vanishingIdeal (n := n) C) x.val := by
      rw [actualCentreIdealSectionGermImage_eq_whole]
      exact ha
    obtain ⟨V, hxV, t, ht⟩ := hsection
    refine ⟨TopCat.Presheaf.germ (intrinsicReducedCentreIdealModule X D).val.presheaf
      ((Opens.map (actualSubspaceInclusion (n := n) W).base).obj V) x hxV
        (intrinsicReducedCentreModelSection W C V t), ?_⟩
    exact (intrinsicReducedCentreStalkInclusion_germ X D x _ hxV
      (intrinsicReducedCentreModelSection W C V t)).trans
      ((intrinsicReducedCentreModelSection_germ W C V t x hxV).trans
        (congrArg ((actualSubspaceInclusion (n := n) W).stalkMap x).hom ht))

/-- The actual native intrinsic ideal-module stalk is linearly the SAME
original ENTIRE inclusion image ideal, without an incoming dictionary. -/
def intrinsicReducedCentreStalkIdealEquiv_model {W C : Set M} (hCW : C ⊆ W) (x : W) :
    ↑(TopCat.Presheaf.stalk (intrinsicReducedCentreIdealModule
      (actualSubspaceLocallyRingedSpace (n := n) W) ((Subtype.val : W → M) ⁻¹' C)).val.presheaf x) ≃ₗ[
        ((actualSubspaceLocallyRingedSpace (n := n) W).presheaf.stalk x).carrier]
      Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val) := by
  let X := actualSubspaceLocallyRingedSpace (n := n) W
  let D : Set X := (Subtype.val : W → M) ⁻¹' C
  let f := (intrinsicReducedCentreStalkInclusion X D x).codRestrict
    (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap x).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val))
    (fun m => by rw [← intrinsicReducedCentreStalkInclusion_range_model hCW x]; exact ⟨m, rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b hab
    exact intrinsicReducedCentreStalkInclusion_injective X D x (congrArg Subtype.val hab)
  · intro r
    have hr : r.val ∈ LinearMap.range (intrinsicReducedCentreStalkInclusion X D x) := by
      rw [intrinsicReducedCentreStalkInclusion_range_model hCW x]
      exact r.property
    obtain ⟨m, hm⟩ := hr
    exact ⟨m, Subtype.ext hm⟩

@[simp] theorem intrinsicReducedCentreStalkIdealEquiv_model_germ {W C : Set M}
    (hCW : C ⊆ W) (x : W)
    (U : Opens (actualSubspaceLocallyRingedSpace (n := n) W).toTopCat) (hx : x ∈ U)
    (s : intrinsicReducedCentreSectionIdeal
      (actualSubspaceLocallyRingedSpace (n := n) W) ((Subtype.val : W → M) ⁻¹' C) U) :
    (intrinsicReducedCentreStalkIdealEquiv_model hCW x
      (TopCat.Presheaf.germ (intrinsicReducedCentreIdealModule
        (actualSubspaceLocallyRingedSpace (n := n) W) ((Subtype.val : W → M) ⁻¹' C)).val.presheaf
          U x hx s)).val =
      (actualSubspaceLocallyRingedSpace (n := n) W).presheaf.germ U x hx s.val :=
  intrinsicReducedCentreStalkInclusion_germ
    (actualSubspaceLocallyRingedSpace (n := n) W) ((Subtype.val : W → M) ⁻¹' C) x U hx s

end Model
end

end Hironaka.HironakaIntrinsicReducedCentreIdealModel
