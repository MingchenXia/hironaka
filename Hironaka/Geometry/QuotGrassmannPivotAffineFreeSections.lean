import Hironaka.Geometry.QuotGrassmannPivotTildeCoefficients
import Hironaka.Geometry.QuotGrassmannPivotAffineQuotientSections

/-!
# SAME original affine free section coordinates and EVERY original native basis

The frame is the original tilde--Gamma unit followed by Gamma of the ORIGINAL
coordinate-sheaf isomorphism. Its actual basis values are proved from frozen
original tilde coordinate inclusions and genuine native unit naturality.
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine original affine finite-coordinate section frame, constructed from original native tilde data. -/
def originalAffineFreeSectionsCoordinateIso (A : CommRingCat.{u}) (E : Type u) [Finite E] :
    ModuleCat.of A (E → A) ≅ moduleSpecΓFunctor.obj
      (SheafOfModules.free (R := (Spec A).ringCatSheaf) E) :=
  tilde.isoTop (ModuleCat.of A (E → A)) ≪≫
    moduleSpecΓFunctor.mapIso (coordinateSheafIsoFree A E)

/-- EVERY ORIGINAL coordinate unit vector maps to the SAME actual native free-sheaf inclusion on the original unit section. -/
theorem originalAffineFreeSectionsCoordinateIso_basis (A : CommRingCat.{u})
    (E : Type u) [Finite E] [DecidableEq E] (i : E) :
    (originalAffineFreeSectionsCoordinateIso A E).hom (Pi.single i (1 : A)) =
      (SheafOfModules.ιFree (R := (Spec A).ringCatSheaf) i).val.app (op ⊤)
        (1 : Γ(Spec A, ⊤)) := by
  let l : ModuleCat.of A A ⟶ ModuleCat.of A (E → A) :=
    ModuleCat.ofHom (LinearMap.single A (fun _ : E => A) i)
  have ht := ConcreteCategory.congr_hom (tilde.toOpen_map_app (R := A) l ⊤) (1 : A)
  change (tilde.map l).val.app (op ⊤)
      (tilde.toOpen (ModuleCat.of A A) ⊤ (1 : A)) =
    tilde.toOpen (ModuleCat.of A (E → A)) ⊤ (Pi.single i (1 : A)) at ht
  have hone : tilde.toOpen (ModuleCat.of A A) ⊤ (1 : A) = (1 : Γ(Spec A, ⊤)) :=
    (originalTildeSelf_toOpen A ⊤ 1).trans (map_one (originalAffineCoefficientMap A ⊤))
  rw [hone] at ht
  have hc := originalCoordinateSheafIso_inclusion A E i
  have hv := congrArg (fun h => h.val.app (op (⊤ : (Spec A).Opens)) (1 : Γ(Spec A, ⊤))) hc
  change (coordinateSheafIsoFree A E).hom.val.app (op ⊤)
      ((tilde.map l).val.app (op ⊤) (1 : Γ(Spec A, ⊤))) =
    (SheafOfModules.ιFree (R := (Spec A).ringCatSheaf) i).val.app (op ⊤)
      (1 : Γ(Spec A, ⊤)) at hv
  change (coordinateSheafIsoFree A E).hom.val.app (op ⊤)
    (tilde.toOpen (ModuleCat.of A (E → A)) ⊤ (Pi.single i (1 : A))) = _
  exact (congrArg ((coordinateSheafIsoFree A E).hom.val.app (op ⊤)) ht.symm).trans hv

/-- The EXACT original universal quotient source frame uses SAME original affine coordinate frame and canonical native free pullback. -/
theorem originalGlobalAffinePullbackSourceSectionsIso_eq_coordinate
    (R : Type u) [CommRing R] (ι ν : Type u) [Fintype ι] [Fintype ν] [DecidableEq ι]
    {A : CommRingCat.{u}} (f : Spec A ⟶ projectiveModel R ι ν) :
    originalGlobalAffinePullbackSourceSectionsIso R ι ν f =
      originalAffineFreeSectionsCoordinateIso A (ι ⊕ ν) ≪≫
        moduleSpecΓFunctor.mapIso (originalPullbackFreeIso f (ι ⊕ ν)).symm := rfl

end Hironaka.Geometry.QuotGrassmann
