/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Projectivity.RelativeCoverFinite
import DeJongAlterations.StableModification.CurvesField.OmegaDegree
import DeJongAlterations.StableModification.Cohomology.CechPushforward

/-! # Actual original line-bundle sections and Euler characteristics under scheme isomorphisms -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace DeJongAlterations.StableModification

set_option backward.isDefEq.respectTransparency false

namespace Cohomology

variable {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] {k : Type u} [Field k]

/-- A native module isomorphism preserves the entire original coefficient-field Euler sum. -/
theorem eulerCharOf_eq_of_iso {M N : X.Modules} (e : M ≅ N) (c : k →+* Γ(X, ⊤)) :
    CurvesField.DualityScheme.eulerCharOf M c =
      CurvesField.DualityScheme.eulerCharOf N c := by
  unfold CurvesField.DualityScheme.eulerCharOf HomologicalComplex.homologyEulerChar
    GradedObject.eulerChar
  apply finsum_congr
  intro i
  congr 2
  exact ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    ((cechComplexFunctor (FiniteAffineCover.choose X).U c).mapIso e)).toLinearEquiv.finrank_eq

/-- The native affine pushforward comparison preserves the whole original field action. -/
theorem eulerCharOf_pushforward_eq (π : X ⟶ Y) [IsAffineHom π] (G : X.Modules)
    [G.IsQuasicoherent] (c : k →+* Γ(Y, ⊤)) :
    CurvesField.DualityScheme.eulerCharOf ((Scheme.Modules.pushforward π).obj G) c =
      CurvesField.DualityScheme.eulerCharOf G (π.appTop.hom.comp c) := by
  unfold CurvesField.DualityScheme.eulerCharOf HomologicalComplex.homologyEulerChar
    GradedObject.eulerChar
  apply finsum_congr
  intro i
  congr 2
  exact (cohomologyPushforwardIso π G c i).toLinearEquiv.finrank_eq

end Cohomology

namespace Projectivity.LineBundleData

variable {X Y Z : Scheme.{u}}

/-- Actual original transition data and all chart coefficients respect composition. -/
theorem pullback_comp_eq (L : LineBundleData Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (L.pullback g).pullback f = L.pullback (f ≫ g) := rfl

/-- Apply the original section homomorphisms to every compatible chart coefficient. -/
def twistSectionsPullbackHom (L : LineBundleData Y) (m : ℤ) (f : X ⟶ Y) :
    L.twist (unitModule Y) m ⟶
      (Scheme.Modules.pushforward f).obj ((L.pullback f).twist (unitModule X) m) where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun s : L.Sections m W.unop => s.pullback f
          map_zero' := by
            apply Subtype.ext
            funext i
            exact map_zero (f.app (W.unop ⊓ L.U i)).hom
          map_add' := Sections.pullback_add L m f }
      naturality := fun {W W'} h => by
        ext s
        exact Sections.pullback_restrict L m f (leOfHom h.unop) s }
    (fun W r s => Sections.pullback_smul L m f r s)

/-- The original compatible-family pullback is an isomorphism for an actual scheme iso. -/
instance isIso_twistSectionsPullbackHom (L : LineBundleData Y) (m : ℤ)
    (f : X ⟶ Y) [IsIso f] : IsIso (twistSectionsPullbackHom L m f) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  exact L.bijective_pullback_of_isOpenImmersion m f (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)

variable [CompactSpace X] [CompactSpace Y]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] {k : Type u} [Field k]

/-- No Euler comparison is supplied: the original whole structure triangle and actual sections
construct it for every original integer power. -/
theorem eulerCharOf_twist_pullback_iso (L : LineBundleData Y) (m : ℤ) (e : X ≅ Y)
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (he : e.hom ≫ pY = pX) :
    CurvesField.DualityScheme.eulerCharOf
        ((L.pullback e.hom).twist (unitModule X) m) (Cohomology.structureCoeff pX) =
      CurvesField.DualityScheme.eulerCharOf (L.twist (unitModule Y) m)
        (Cohomology.structureCoeff pY) := by
  have hc : e.hom.appTop.hom.comp (Cohomology.structureCoeff pY) =
      Cohomology.structureCoeff pX := by
    rw [← he]
    ext a
    simp [Cohomology.structureCoeff]
  rw [← hc, ← Cohomology.eulerCharOf_pushforward_eq]
  exact (Cohomology.eulerCharOf_eq_of_iso (asIso (twistSectionsPullbackHom L m e.hom)) _).symm

end Projectivity.LineBundleData

end DeJongAlterations.StableModification
