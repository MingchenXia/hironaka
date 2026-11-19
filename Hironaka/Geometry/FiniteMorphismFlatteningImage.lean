import Hironaka.Geometry.FiniteMorphismFlatteningCharts
import Hironaka.Geometry.FiniteMorphismFlatteningLocality

/-!
# The affine algebra image is the literal scheme-theoretic image

Equality of original ring kernels implies equality of the native kernel
ideal sheaves after the actual global-coordinate isomorphisms. This
identifies the actual closed chart transform with the native image,
preserving its literal closed immersion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Hironaka.Geometry.FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native ideal kernel of an affine spectrum map is computed from its original ring kernel. -/
theorem ker_specMap_eq_of_ker_eq {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    (f : B →+* C) (g : B →+* D) (h : RingHom.ker f = RingHom.ker g) :
    (Spec.map (CommRingCat.ofHom f)).ker = (Spec.map (CommRingCat.ofHom g)).ker := by
  have hker {E : Type u} [CommRing E] (φ : B →+* E) :
      RingHom.ker (Spec.map (CommRingCat.ofHom φ)).appTop.hom =
        (RingHom.ker φ).comap (Scheme.ΓSpecIso (.of B)).hom.hom := by
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (.of E)).commRingCatIsoToRingEquiv]
    change RingHom.ker
      (((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso (.of E)).hom).hom) = _
    rw [Scheme.ΓSpecIso_naturality]
    rfl
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  change RingHom.ker (Spec.map (CommRingCat.ofHom f)).appTop.hom =
    RingHom.ker (Spec.map (CommRingCat.ofHom g)).appTop.hom
  rw [hker f, hker g, h]

open Algebra.FiniteMorphismFlattening

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The actual closed chart transform has exactly the original generic tensor map's kernel ideal sheaf. -/
theorem chartTransformInclusion_ker (S : Subalgebra R (FractionRing R)) :
    (chartTransformInclusion R A S).ker =
      (Spec.map (CommRingCat.ofHom (R := S ⊗[R] A) (S := FractionRing R ⊗[R] A)
        (tensorAlgMap R A S).toRingHom)).ker :=
  ker_specMap_eq_of_ker_eq _ _ (AlgHom.ker_rangeRestrict _)

/-- The actual algebra-image chart is canonically the native scheme-theoretic image. -/
def chartTransformImageIso (S : Subalgebra R (FractionRing R)) :
    Spec (.of (pureTransformAlgebra R A S)) ≅
      (Spec.map (CommRingCat.ofHom (R := S ⊗[R] A) (S := FractionRing R ⊗[R] A)
        (tensorAlgMap R A S).toRingHom)).image :=
  asIso (chartTransformInclusion R A S).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (chartTransformInclusion_ker R A S))

/-- The native scheme-theoretic image comparison preserves the original literal closed immersion. -/
@[reassoc (attr := simp)]
theorem chartTransformImageIso_hom_inclusion (S : Subalgebra R (FractionRing R)) :
    (chartTransformImageIso R A S).hom ≫
      (Spec.map (CommRingCat.ofHom (R := S ⊗[R] A) (S := FractionRing R ⊗[R] A)
        (tensorAlgMap R A S).toRingHom)).imageι =
      chartTransformInclusion R A S := by
  unfold chartTransformImageIso
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  have hι {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
      eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
    subst J
    simp
  change (chartTransformInclusion R A S).toImage ≫
    eqToHom (congrArg Scheme.IdealSheafData.subscheme (chartTransformInclusion_ker R A S)) ≫
      (Spec.map (CommRingCat.ofHom (R := S ⊗[R] A) (S := FractionRing R ⊗[R] A)
        (tensorAlgMap R A S).toRingHom)).ker.subschemeι = _
  rw [hι _ _ (chartTransformInclusion_ker R A S)]
  exact Scheme.Hom.toImage_imageι _

end Hironaka.Geometry.FiniteMorphismFlattening
