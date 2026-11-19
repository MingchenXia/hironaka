import Hironaka.Geometry.ProperSteinGlobalSectionsAffine
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The actual original structure sheaf is the actual proper pushforward

The affine-to-sheaf argument follows the native sheaf-basis route in the
same workspace's `EnvelopeProperty/ProperBirationalSheaf.lean`; here the
original canonical no-further-constants condition replaces birationality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace Hironaka.Geometry.ProperSteinGlobalSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ORIGINAL scheme structure map as a genuine morphism of actual sheaves. -/
def sectionSheafMap {X S : Scheme.{u}} (f : X ⟶ S) :
    S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf := ⟨f.c⟩

private theorem nonemptyAffineBasis (S : Scheme.{u}) :
    Opens.IsBasis (Set.range (fun U : {U : S.affineOpens // Nonempty U.1} => U.1.1)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨U, ⟨⟨⟨U, hU⟩, ⟨⟨x, hxU⟩⟩⟩, rfl⟩, hxU, hUV⟩

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f] [UniversallyClosed f] (hnormal : IsNormalScheme S)
  (hconstants : letI := FiniteBirationalNormal.functionFieldAlgebra f
    algebraicClosure S.functionField X.functionField = ⊥)

include hnormal hconstants

/-- ORIGINAL properness, actual normality and canonical constants derive the actual sheaf pushforward identity. -/
theorem isIso_sectionSheafMap : IsIso (sectionSheafMap f) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis (nonemptyAffineBasis S)
  intro U
  let : Nonempty U.1.1 := U.2
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (affine_app_bijective f hnormal hconstants U.1.1 U.1.2)

/-- EVERY original open-section component is an isomorphism, including nonaffine and empty opens. -/
theorem isIso_app (U : S.Opens) : IsIso (f.app U) := by
  let : IsIso (sectionSheafMap f) := isIso_sectionSheafMap f hnormal hconstants
  let : IsIso f.c := (TopCat.Sheaf.forget CommRingCat S).map_isIso (sectionSheafMap f)
  exact NatIso.isIso_app_of_isIso f.c (op U)

/-- The ENTIRE original section map is bijective on EVERY original open. -/
theorem app_bijective (U : S.Opens) : Function.Bijective (f.app U).hom := by
  let := isIso_app f hnormal hconstants U
  exact ConcreteCategory.bijective_of_isIso (f.app U)

/-- The actual inverse equivalence is built from the ORIGINAL section map. -/
def appEquiv (U : S.Opens) : Γ(S, U) ≃+* Γ(X, f ⁻¹ᵁ U) :=
  RingEquiv.ofBijective (f.app U).hom (app_bijective f hnormal hconstants U)

/-- Its ENTIRE forward map is literally the ORIGINAL map on sections. -/
theorem appEquiv_apply (U : S.Opens) (a : Γ(S, U)) :
    appEquiv f hnormal hconstants U a = (f.app U) a := rfl

/-- The actual inverse maps commute with the ORIGINAL restrictions on both schemes. -/
theorem appEquiv_symm_restrict {U V : S.Opens} (hVU : V ≤ U) (b : Γ(X, f ⁻¹ᵁ U)) :
    S.presheaf.map (homOfLE hVU).op ((appEquiv f hnormal hconstants U).symm b) =
      (appEquiv f hnormal hconstants V).symm
        (X.presheaf.map (homOfLE (f.preimage_mono hVU)).op b) := by
  let eU := appEquiv f hnormal hconstants U
  let eV := appEquiv f hnormal hconstants V
  apply eV.injective
  change (f.app V) (S.presheaf.map (homOfLE hVU).op (eU.symm b)) =
    (f.app V) (eV.symm (X.presheaf.map (homOfLE (f.preimage_mono hVU)).op b))
  have hn := ConcreteCategory.congr_hom (f.naturality (homOfLE hVU).op) (eU.symm b)
  change (f.app V) (S.presheaf.map (homOfLE hVU).op (eU.symm b)) =
    X.presheaf.map (homOfLE (f.preimage_mono hVU)).op ((f.app U) (eU.symm b)) at hn
  rw [hn, show (f.app U) (eU.symm b) = b from eU.apply_symm_apply b,
    show (f.app V) (eV.symm (X.presheaf.map (homOfLE (f.preimage_mono hVU)).op b)) =
      X.presheaf.map (homOfLE (f.preimage_mono hVU)).op b from eV.apply_symm_apply _]

end Hironaka.Geometry.ProperSteinGlobalSections
