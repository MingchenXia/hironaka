import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualIdealModuleStalk
import Hironaka.Resolution.HironakaSingularModuleSheafStalk
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Bundle the EXACT existing legacy ideal-module presheaf as a native sheaf

No ideal carrier, section restriction or scalar action is changed. The only
missing bundle field is proved from original sheaf gluing and all-germ membership.
Blueprint FIRST: `hironaka-legacy-coherent-ideal-sheaf.tex`.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaLegacyCoherentIdealSheaf

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualIdealModuleStalk HironakaSingularModuleSheafStalk

noncomputable section
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The SAME old all-germ section presheaf already glues in the original sheaf. -/
theorem actualIdealModulePresheaf_isSheaf (A : GermIdeal n M) :
    TopCat.Presheaf.IsSheaf (X := TopCat.of M) (actualIdealModulePresheaf A).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := TopCat.of M) _).mpr
  intro ι U sf hcpt
  let R := actualComplexStructureSheaf (n := n) M
  have hcompat : TopCat.Presheaf.IsCompatible R.presheaf U (fun i => (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hcpt i j)
  obtain ⟨s,hglue,huniq⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing R.property U (fun i => (sf i).val) hcompat
  have hs : s ∈ actualSectionIdeal A (iSup U) := by
    intro y hy
    obtain ⟨i,hyi⟩ := Opens.mem_iSup.mp hy
    have hg := congrArg (R.presheaf.germ (U i) y hyi) (hglue i)
    rw [R.presheaf.germ_res_apply] at hg
    rw [hg]
    exact (sf i).property y hyi
  refine ⟨⟨s,hs⟩,?_,?_⟩
  · intro i
    apply Subtype.ext
    exact hglue i
  · intro t ht
    apply Subtype.ext
    apply huniq t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- A native SHEAF bundle on the EXACT existing module presheaf. -/
def actualIdealModuleSheaf (A : GermIdeal n M) :
    SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M)) where
  val := actualIdealModulePresheaf A
  isSheaf := actualIdealModulePresheaf_isSheaf A

/-- No sheafification, new module or transported action is introduced. -/
theorem actualIdealModuleSheaf_val (A : GermIdeal n M) :
    (actualIdealModuleSheaf A).val = actualIdealModulePresheaf A := rfl

/-- The original actual section subtype inclusion as a full native module map. -/
def actualIdealModuleInclusion (A : GermIdeal n M) :
    actualIdealModuleSheaf A ⟶ SheafOfModules.unit (forgetRing (actualComplexStructureSheaf (n := n) M)) :=
  ⟨{ app := fun U => by
       change ModuleCat.of (actualComplexSection (n := n) (unop U))
           (actualSectionIdeal A (unop U)) ⟶
         ModuleCat.of (actualComplexSection (n := n) (unop U))
           (actualComplexSection (n := n) (unop U))
       exact ModuleCat.ofHom (actualSectionIdeal A (unop U)).subtype
     naturality := by intro U V f; ext s; rfl }⟩

@[simp] theorem actualIdealModuleInclusion_app (A : GermIdeal n M)
    (U : Opens M) (s : actualSectionIdeal A U) :
    (actualIdealModuleInclusion A).val.app (op U) s = s.val := rfl

instance actualIdealModuleInclusion_mono (A : GermIdeal n M) :
    Mono (actualIdealModuleInclusion A) := by
  have : Mono ((SheafOfModules.forget _).map (actualIdealModuleInclusion A)) :=
    PresheafOfModules.mono_of_injective (by intro U; exact Subtype.val_injective)
  exact (SheafOfModules.forget _).mono_of_mono_map this

/-- Expose precisely the existing native colimit action for the unchanged bundle. -/
abbrev actualIdealModule_nativeStalkModule (A : GermIdeal n M) (y : M) :
    Module ↑(TopCat.Presheaf.stalk (actualComplexStructureSheaf (n := n) M).obj y)
      ↑(TopCat.Presheaf.stalk (actualIdealModuleSheaf A).val.presheaf y) :=
  nativeSheafStalkModule (actualComplexStructureSheaf (n := n) M) (actualIdealModuleSheaf A) y

attribute [instance] actualIdealModule_nativeStalkModule

/-- The native stalk action and entire ideal equivalence are EXACTLY the old ones. -/
def actualIdealModule_stalkEquiv (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    ↑(TopCat.Presheaf.stalk (actualIdealModuleSheaf A).val.presheaf y) ≃ₗ[
      ↑(TopCat.Presheaf.stalk (actualComplexStructureSheaf (n := n) M).obj y)]
      actualWholeSheafStalkIdeal A y :=
  actualIdealStalkWholeLinearEquiv A hA y

/-- The SAME actual inclusion sends every original germ to its whole ideal value. -/
private theorem inclusion_stalk_apply (A : GermIdeal n M) (hA : A.IsCoherent) (y : M)
    (m : ↑(TopCat.Presheaf.stalk (actualIdealModuleSheaf A).val.presheaf y)) :
    stalkInclusionLinearMap (actualComplexStructureSheaf (n := n) M)
      (actualIdealModuleSheaf A) (actualIdealModuleInclusion A) y m =
      (actualIdealModule_stalkEquiv A hA y m).val := by
  obtain ⟨U,hy,s,rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (actualIdealModuleSheaf A).val.presheaf m
  exact (stalkInclusionLinearMap_germ (actualComplexStructureSheaf (n := n) M)
    (actualIdealModuleSheaf A) (actualIdealModuleInclusion A) y U hy s).trans
      (congrArg Subtype.val (actualIdealStalkWholeLinearEquiv_germ A hA U y hy s)).symm

/-- BOTH entire ideal inclusions preserve all nonradical original multiplicities. -/
theorem actualIdealModule_stalkRange (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    LinearMap.range (stalkInclusionLinearMap (actualComplexStructureSheaf (n := n) M)
      (actualIdealModuleSheaf A) (actualIdealModuleInclusion A) y) = actualWholeSheafStalkIdeal A y := by
  apply le_antisymm
  · rintro a ⟨m,rfl⟩
    rw [inclusion_stalk_apply A hA y m]
    exact (actualIdealModule_stalkEquiv A hA y m).property
  · intro a ha
    obtain ⟨m,hm⟩ := (actualIdealModule_stalkEquiv A hA y).surjective ⟨a,ha⟩
    exact ⟨m,(inclusion_stalk_apply A hA y m).trans (congrArg Subtype.val hm)⟩

end
end Hironaka.HironakaLegacyCoherentIdealSheaf
