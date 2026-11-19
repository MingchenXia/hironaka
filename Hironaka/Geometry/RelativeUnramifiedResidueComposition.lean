import Hironaka.Geometry.RelativeUnramifiedFinite
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Original point-residue finite separability from an actual unramified composite

The intermediate map is arbitrary. Only the composite has unramified/LFT
hypotheses. Both scalar actions are the unchanged actual native residue maps.
This does not construct a singular subscheme or prove its unramifiedness.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace Hironaka.Geometry.RelativeUnramified
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) (z : Z)

/-- The actual residue map of i, linear for BOTH entire original canonical base actions. -/
def intermediateResidueAlgHom :
    letI : Algebra (S.residueField (f (i z))) (X.residueField (i z)) :=
      (f.residueFieldMap (i z)).hom.toAlgebra
    letI : Algebra (S.residueField (f (i z))) (Z.residueField z) :=
      ((i ≫ f).residueFieldMap z).hom.toAlgebra
    X.residueField (i z) →ₐ[S.residueField (f (i z))] Z.residueField z := by
  letI : Algebra (S.residueField (f (i z))) (X.residueField (i z)) :=
    (f.residueFieldMap (i z)).hom.toAlgebra
  letI : Algebra (S.residueField (f (i z))) (Z.residueField z) :=
    ((i ≫ f).residueFieldMap z).hom.toAlgebra
  exact { (i.residueFieldMap z).hom with
    commutes' := fun a ↦ (congrArg (fun g => g a) (Scheme.residueFieldMap_comp i f z)).symm }

/-- The original native residue map is retained on EVERY original residue element. -/
theorem intermediateResidueAlgHom_apply (a : X.residueField (i z)) :
    letI : Algebra (S.residueField (f (i z))) (X.residueField (i z)) :=
      (f.residueFieldMap (i z)).hom.toAlgebra
    letI : Algebra (S.residueField (f (i z))) (Z.residueField z) :=
      ((i ≫ f).residueFieldMap z).hom.toAlgebra
    (intermediateResidueAlgHom i f z).toRingHom a = (i.residueFieldMap z).hom a := rfl

/-- Actual composite unramifiedness suffices for finite separability at the ORIGINAL intermediate point. -/
theorem pointResidue_finite_separable_of_comp
    [LocallyOfFiniteType (i ≫ f)] [FormallyUnramified (i ≫ f)] :
    letI : Algebra (S.residueField (f (i z))) (X.residueField (i z)) :=
      (f.residueFieldMap (i z)).hom.toAlgebra
    Module.Finite (S.residueField (f (i z))) (X.residueField (i z)) ∧
      Algebra.IsSeparable (S.residueField (f (i z))) (X.residueField (i z)) := by
  let : Algebra (S.residueField (f (i z))) (X.residueField (i z)) :=
    (f.residueFieldMap (i z)).hom.toAlgebra
  let : Algebra (S.residueField (f (i z))) (Z.residueField z) :=
    ((i ≫ f).residueFieldMap z).hom.toAlgebra
  let : Module.Finite (S.residueField (f (i z))) (Z.residueField z) :=
    (pointResidue_finite_separable (i ≫ f) z).1
  let : Algebra.IsSeparable (S.residueField (f (i z))) (Z.residueField z) :=
    (pointResidue_finite_separable (i ≫ f) z).2
  exact ⟨FiniteDimensional.of_injective (intermediateResidueAlgHom i f z).toLinearMap
      (intermediateResidueAlgHom i f z).injective,
    Algebra.IsSeparable.of_algHom (S.residueField (f (i z))) (Z.residueField z)
      (intermediateResidueAlgHom i f z)⟩

end Hironaka.Geometry.RelativeUnramified
