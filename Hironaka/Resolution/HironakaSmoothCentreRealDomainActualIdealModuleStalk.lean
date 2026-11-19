import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualIdealPresheaf
import Mathlib.Algebra.Category.ModuleCat.Stalk
/-! Actual ideal module presheaves and independently constructed true stalk actions.
Complete two-node Mathematics.tex precedes code. Literal section multiplication
and genuine colimit module actions precede any whole-ideal linear equivalence. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualIdealModuleStalk
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSmoothCentreRealDomainActualIdealPresheaf
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
/-- The REAL actual ideal sections with their independently inherited section-ring multiplication. -/
def actualIdealModulePresheaf (A : GermIdeal n M) :
    PresheafOfModules ((actualComplexStructureSheaf (n := n) M).presheaf ⋙ forget₂ CommRingCat RingCat) := by
  letI (U : (Opens M)ᵒᵖ) :
      Module (((actualComplexStructureSheaf (n := n) M).presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
        ((actualIdealSectionPresheaf A).obj U) := by
    change Module (actualComplexSection (n := n) (unop U)) (actualSectionIdeal A (unop U))
    infer_instance
  apply PresheafOfModules.ofPresheaf (actualIdealSectionPresheaf A)
  intro U V i r s
  change actualComplexSection (n := n) (unop U) at r
  change actualSectionIdeal A (unop U) at s
  apply Subtype.ext
  change ((actualComplexStructureSheaf (n := n) M).presheaf.map i).hom (r*s.val) =
    ((actualComplexStructureSheaf (n := n) M).presheaf.map i).hom r *
      ((actualComplexStructureSheaf (n := n) M).presheaf.map i).hom s.val
  exact ((actualComplexStructureSheaf (n := n) M).presheaf.map i).hom.map_mul r s.val

/-- This genuine module presheaf retains the EXACT original additive ideal presheaf. -/
theorem actualIdealModulePresheaf_presheaf (A : GermIdeal n M) :
    (actualIdealModulePresheaf A).presheaf = actualIdealSectionPresheaf A := rfl

/-- The actual neighbourhood COLIMIT action, independently of every whole-ideal equivalence. -/
instance actualIdealStalkModule (A : GermIdeal n M) (y : M) :
    Module (actualComplexStructureStalk (n := n) y) (actualIdealSectionStalk A y) := by
  change Module (((actualComplexStructureSheaf (n := n) M).presheaf.stalk y).carrier)
    ((TopCat.Presheaf.stalk (actualIdealModulePresheaf A).presheaf y).carrier)
  exact (actualIdealModulePresheaf A).instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier y

/-- EVERY literal ideal section product gives the genuine actual colimit scalar action formula. -/
theorem actualIdealStalk_germ_smul (A : GermIdeal n M) (U : Opens M) (y : M) (hy : y ∈ U)
    (r : actualComplexSection (n := n) U) (s : actualSectionIdeal A U) :
    (actualIdealSectionPresheaf A).germ U y hy (r • s) =
      (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy r •
        (actualIdealSectionPresheaf A).germ U y hy s := by
  exact (actualIdealModulePresheaf A).germ_smul y U hy r s

/-- ALL actual ring-stalk scalars and true ideal-colimit elements obey the independently defined scalar action. -/
theorem actualIdealStalkToWholeHom_smul (A : GermIdeal n M) (y : M)
    (r : actualComplexStructureStalk (n := n) y) (v : actualIdealSectionStalk A y) :
    actualIdealStalkToWholeHom A y (r • v) = r • actualIdealStalkToWholeHom A y v := by
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  let I := actualIdealSectionPresheaf A
  obtain ⟨V,hyV,s,hs⟩ := I.exists_germ_eq v
  obtain ⟨U,hUV,hyU,t,ht⟩ := F.exists_le_germ_eq r hyV
  change actualSectionIdeal A V at s
  change actualComplexSection (n := n) U at t
  let su := actualIdealSectionRestrict A U V hUV s
  have hsv : I.germ U y hyU su = v := by
    exact (I.germ_res_apply (homOfLE hUV) y hyU s).trans hs
  rw [← ht,← hsv,← actualIdealStalk_germ_smul A U y hyU t su,
    actualIdealStalkToWholeHom_germ A U y hyU (t • su),actualIdealStalkToWholeHom_germ A U y hyU su]
  apply Subtype.ext
  change (F.germ U y hyU).hom (t*su.val) = (F.germ U y hyU).hom t * (F.germ U y hyU).hom su.val
  exact (F.germ U y hyU).hom.map_mul t su.val

/-- The genuine colimit-to-whole map is linear for its true actual scalar action, not a transported action. -/
def actualIdealStalkToWholeLinear (A : GermIdeal n M) (y : M) :
    actualIdealSectionStalk A y →ₗ[actualComplexStructureStalk (n := n) y] actualWholeSheafStalkIdeal A y where
  toFun := actualIdealStalkToWholeHom A y
  map_add' := (actualIdealStalkToWholeHom A y).map_add
  map_smul' := actualIdealStalkToWholeHom_smul A y

/-- EVERY original actual ideal section germ retains its formula under the genuine linear map. -/
theorem actualIdealStalkToWholeLinear_germ (A : GermIdeal n M) (U : Opens M) (y : M)
    (hy : y ∈ U) (s : actualSectionIdeal A U) :
    actualIdealStalkToWholeLinear A y ((actualIdealSectionPresheaf A).germ U y hy s) =
      actualIdealSectionGermHom A U y hy s := actualIdealStalkToWholeHom_germ A U y hy s

/-- Original coherence INTERNALLY supplies true WHOLE ideal stalk linear equivalence. -/
def actualIdealStalkWholeLinearEquiv (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    actualIdealSectionStalk A y ≃ₗ[actualComplexStructureStalk (n := n) y] actualWholeSheafStalkIdeal A y :=
  LinearEquiv.ofBijective (actualIdealStalkToWholeLinear A y)
    ⟨actualIdealStalkToWholeHom_injective A y,actualIdealStalkToWholeHom_surjective A hA y⟩

/-- EVERY genuine ideal section has the SAME original germ under the whole linear equivalence. -/
theorem actualIdealStalkWholeLinearEquiv_germ (A : GermIdeal n M) (hA : A.IsCoherent)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualSectionIdeal A U) :
    actualIdealStalkWholeLinearEquiv A hA y ((actualIdealSectionPresheaf A).germ U y hy s) =
      actualIdealSectionGermHom A U y hy s := actualIdealStalkToWholeHom_germ A U y hy s

/-- ANY original centre vanishing ideal INTERNALLY supplies the same WHOLE linear equivalence, no global coherence premise. -/
def actualCentreIdealStalkWholeLinearEquiv (C : Set M) (y : M) :
    actualIdealSectionStalk (vanishingIdeal (n := n) C) y ≃ₗ[actualComplexStructureStalk (n := n) y]
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y :=
  LinearEquiv.ofBijective (actualIdealStalkToWholeLinear _ y)
    ⟨actualIdealStalkToWholeHom_injective _ y,actualCentreIdealStalkToWholeHom_surjective C y⟩

/-- EVERY actual original centre ideal section has its genuine whole original germ formula. -/
theorem actualCentreIdealStalkWholeLinearEquiv_germ (C : Set M) (U : Opens M) (y : M)
    (hy : y ∈ U) (s : actualSectionIdeal (vanishingIdeal (n := n) C) U) :
    actualCentreIdealStalkWholeLinearEquiv C y ((actualIdealSectionPresheaf _).germ U y hy s) =
      actualIdealSectionGermHom (vanishingIdeal (n := n) C) U y hy s := actualIdealStalkToWholeHom_germ _ U y hy s

end
end Hironaka.HironakaSmoothCentreRealDomainActualIdealModuleStalk
