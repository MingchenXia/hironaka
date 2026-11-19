import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualIdealPresheaf
import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The canonical actual pulled-centre ideal is a native module subsheaf

Original sections are tested at their SAME actual original stalks against
Ideal.map of the SAME full original H.stalkMap and original whole centre ideal.
The native presheaf-submodule constructor supplies all module operations and
inclusion maps. No private stalk action, alternate ideal family or desired
stalk dictionary is supplied. The next leaf proves the exact actual stalk image.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-ideal-sheaf.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf

noncomputable section

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {X : LocallyRingedSpace}

/-- Original actual sections whose EVERY actual germ belongs to the SAME
canonical original pulled centre ideal. No stalk-ideal family is supplied. -/
def actualPulledCentreSectionIdeal
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M)
    (C : Set M) (U : Opens X.toTopCat) : Ideal (X.presheaf.obj (op U)).carrier where
  carrier := {s | ∀ (x : X) (hx : x ∈ U),
    X.presheaf.germ U x hx s ∈
      Ideal.map (H.stalkMap x).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base x))}
  zero_mem' := by
    intro x hx
    rw [map_zero]
    exact Ideal.zero_mem _
  add_mem' := by
    intro s t hs ht x hx
    rw [map_add]
    exact Ideal.add_mem _ (hs x hx) (ht x hx)
  smul_mem' := by
    intro r s hs x hx
    change X.presheaf.germ U x hx (r * s) ∈ _
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hs x hx)

/-- The original germ restriction identity preserves the same canonical ideal. -/
theorem actualPulledCentreSectionIdeal_restrict
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M)
    (C : Set M) (U V : Opens X.toTopCat) (hUV : U ≤ V)
    (s : (X.presheaf.obj (op V)).carrier) (hs : s ∈ actualPulledCentreSectionIdeal H C V) :
    X.presheaf.map (homOfLE hUV).op s ∈ actualPulledCentreSectionIdeal H C U := by
  intro x hx
  rw [X.presheaf.germ_res_apply (homOfLE hUV) x hx s]
  exact hs x (hUV hx)

/-- The SAME actual section ideals as a native submodule of the original
unit module presheaf; no module restrictions or scalar actions are copied. -/
def actualPulledCentreSubmodule
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) :
    (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).Submodule where
  obj U := actualPulledCentreSectionIdeal H C (unop U)
  map f := by
    intro s hs
    exact actualPulledCentreSectionIdeal_restrict H C _ _ (leOfHom f.unop) s hs

/-- The native associated module presheaf of the canonical actual section ideals. -/
def actualPulledCentreModulePresheaf
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  (actualPulledCentreSubmodule H C).toPresheafOfModules

/-- The native associated-presheaf restrictions retain the original section map. -/
@[simp] theorem actualPulledCentreModulePresheaf_map_val
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M)
    {U V : (Opens X.toTopCat)ᵒᵖ} (f : U ⟶ V)
    (s : actualPulledCentreSectionIdeal H C (unop U)) :
    (((actualPulledCentreModulePresheaf H C).presheaf.map f s) :
      actualPulledCentreSectionIdeal H C (unop V)).val = X.presheaf.map f s.val := rfl

/-- The canonical ideal-module presheaf is already an actual sheaf: gluing
is performed in the ORIGINAL structure sheaf and ideal membership is local. -/
theorem actualPulledCentreModulePresheaf_isSheaf
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) :
    TopCat.Presheaf.IsSheaf (X := X.toTopCat) (actualPulledCentreModulePresheaf H C).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.toTopCat) _).mpr
  intro ι U sf hcpt
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U (fun i => (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hcpt i j)
  obtain ⟨s, hglue, huniq⟩ := X.toSheafedSpace.IsSheaf.isSheafUniqueGluing U
    (fun i => (sf i).val) hcompat
  have hs : s ∈ actualPulledCentreSectionIdeal H C (iSup U) := by
    intro x hx
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
    have hg := congrArg (X.presheaf.germ (U i) x hxi) (hglue i)
    rw [X.presheaf.germ_res_apply] at hg
    rw [hg]
    exact (sf i).property x hxi
  refine ⟨⟨s, hs⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hglue i
  · intro t ht
    apply Subtype.ext
    apply huniq t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- The canonical actual ideal as a GENUINE native sheaf of modules over the
original structure sheaf with the standard CommRing→Ring forgetful functor. -/
def actualPulledCentreIdealModule
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) :
    SheafOfModules ((sheafCompose (Opens.grothendieckTopology X.toTopCat)
      (forget₂ CommRingCat RingCat)).obj X.toSheafedSpace.sheaf) where
  val := actualPulledCentreModulePresheaf H C
  isSheaf := actualPulledCentreModulePresheaf_isSheaf H C

/-- The native module-subsheaf inclusion is the SAME original section subtype. -/
def actualPulledCentreIdealInclusion
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) :
    actualPulledCentreIdealModule H C ⟶ SheafOfModules.unit _ :=
  ⟨(actualPulledCentreSubmodule H C).ι⟩

@[simp] theorem actualPulledCentreIdealInclusion_app
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M)
    (U : Opens X.toTopCat) (s : actualPulledCentreSectionIdeal H C U) :
    (actualPulledCentreIdealInclusion H C).val.app (op U) s = s.val := rfl

instance actualPulledCentreIdealInclusion_mono
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M) :
    Mono (actualPulledCentreIdealInclusion H C) := by
  have hmono : Mono ((SheafOfModules.forget _).map (actualPulledCentreIdealInclusion H C)) := by
    change Mono (actualPulledCentreSubmodule H C).ι
    infer_instance
  exact (SheafOfModules.forget _).mono_of_mono_map hmono

/-- An actual original centre ideal section pulls into the canonical actual
ideal by the SAME full H.c.app, at every source point of the genuine preimage. -/
def actualPulledCentreSection
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M)
    (V : Opens M) (t : actualSectionIdeal (vanishingIdeal (n := n) C) V) :
    actualPulledCentreSectionIdeal H C ((Opens.map H.base).obj V) := by
  refine ⟨H.c.app (op V) t.val, ?_⟩
  intro x hx
  rw [← LocallyRingedSpace.stalkMap_germ_apply H V x hx t.val]
  exact Ideal.mem_map_of_mem _ (t.property (H.base x) hx)

/-- The canonical section pullback retains the complete original germ formula. -/
theorem actualPulledCentreSection_germ
    (H : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) (C : Set M)
    (V : Opens M) (t : actualSectionIdeal (vanishingIdeal (n := n) C) V)
    (x : X) (hx : H.base x ∈ V) :
    X.presheaf.germ ((Opens.map H.base).obj V) x hx (actualPulledCentreSection H C V t).val =
      H.stalkMap x ((actualComplexStructureSheaf (n := n) M).presheaf.germ V (H.base x) hx t.val) :=
  (LocallyRingedSpace.stalkMap_germ_apply H V x hx t.val).symm

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
