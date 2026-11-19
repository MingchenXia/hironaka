import Hironaka.Geometry.QuotGrassmannPivotAffineFreeSections
import Hironaka.Geometry.QuotGrassmannPivotAffineFreeUnit
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# SAME original native affine free-coordinate scalar-extension triangle

The canonical actual tensor-coordinate isomorphism is used. Original basis
values, the SAME native affine-section comparison naturality, and actual
original canonical unit/free frames derive the exact original basis triangle.
-/

noncomputable section

open scoped TensorProduct

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical native scalar-extension isomorphism on the SAME original finite coordinate module. -/
def originalAffineFreeScalarCoordinateIso {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (I : Type u) [Finite I] :
    (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of A (I → A)) ≅ ModuleCat.of B (I → B) := by
  classical
  let : Algebra A B := φ.hom.toAlgebra
  let : Fintype I := Fintype.ofFinite I
  exact (TensorProduct.piScalarRight A B B I).toModuleIso

/-- EVERY original basis under original scalar-extension unit is the SAME actual coordinate unit vector. -/
theorem originalAffineFreeScalarCoordinateIso_basis {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (I : Type u) [Finite I] [DecidableEq I] (i : I) :
    (originalAffineFreeScalarCoordinateIso φ I).hom
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (ModuleCat.of A (I → A))
        (Pi.single i (1 : A))) = Pi.single i (1 : B) := by
  classical
  let : Algebra A B := φ.hom.toAlgebra
  let : Fintype I := Fintype.ofFinite I
  change (TensorProduct.piScalarRight A B B I)
    ((1 : B) ⊗ₜ[A] Pi.single i (1 : A)) = Pi.single i (1 : B)
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  ext j
  simp [Pi.single_apply, Algebra.smul_def]

/-- Actual native affine-section pullback and ORIGINAL canonical free frame preserve EVERY ORIGINAL coordinate basis. -/
theorem originalSpecPullbackFreeSections_basis {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (I : Type u) [Finite I] [DecidableEq I] (i : I) :
    moduleSpecΓFunctor.map (originalPullbackFreeIso (Spec.map φ) I).hom
      ((originalSpecPullbackSectionsIso φ
        (SheafOfModules.free (R := (Spec A).ringCatSheaf) I)).hom
          ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
            (moduleSpecΓFunctor.obj (SheafOfModules.free (R := (Spec A).ringCatSheaf) I))
              ((originalAffineFreeSectionsCoordinateIso A I).hom (Pi.single i (1 : A))))) =
      (originalAffineFreeSectionsCoordinateIso B I).hom (Pi.single i (1 : B)) := by
  let UA := SheafOfModules.unit (Spec A).ringCatSheaf
  let : UA.IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ UA).mpr
      (inferInstanceAs (IsIso (Scheme.Modules.fromTildeΓ (R := A)
        (SheafOfModules.unit (Spec A).ringCatSheaf))))
  let SA := SheafOfModules.free (R := (Spec A).ringCatSheaf) I
  let UB := SheafOfModules.unit (Spec B).ringCatSheaf
  let lA : UA ⟶ SA := SheafOfModules.ιFree i
  let lB := SheafOfModules.ιFree (R := (Spec B).ringCatSheaf) i
  let E := ModuleCat.extendScalars φ.hom
  let η := (ModuleCat.extendRestrictScalarsAdj φ.hom).unit
  let P := pullback (Spec.map φ)
  let q := moduleSpecΓFunctor.map (originalPullbackFreeIso (Spec.map φ) I).hom
  let v := originalSpecPullbackUnitTop φ UA (1 : Γ(Spec A, ⊤))
  have hbA : (originalAffineFreeSectionsCoordinateIso A I).hom (Pi.single i (1 : A)) =
      moduleSpecΓFunctor.map lA (1 : Γ(Spec A, ⊤)) :=
    originalAffineFreeSectionsCoordinateIso_basis A I i
  have hbB : (originalAffineFreeSectionsCoordinateIso B I).hom (Pi.single i (1 : B)) =
      moduleSpecΓFunctor.map lB (1 : Γ(Spec B, ⊤)) :=
    originalAffineFreeSectionsCoordinateIso_basis B I i
  have hη := ConcreteCategory.congr_hom (η.naturality (moduleSpecΓFunctor.map lA))
    (1 : Γ(Spec A, ⊤))
  have hn := ConcreteCategory.congr_hom (originalSpecPullbackSectionsIso_naturality φ lA)
    (η.app (moduleSpecΓFunctor.obj UA) (1 : Γ(Spec A, ⊤)))
  have hu : (originalSpecPullbackSectionsIso φ UA).hom
      (η.app (moduleSpecΓFunctor.obj UA) (1 : Γ(Spec A, ⊤))) = v :=
    originalSpecPullbackSectionsIso_one_tmul φ UA (1 : Γ(Spec A, ⊤))
  have hmap := congrArg moduleSpecΓFunctor.map (originalPullbackFreeIso_inclusion (Spec.map φ) i)
  simp only [Functor.map_comp] at hmap
  have hframe := ConcreteCategory.congr_hom hmap v
  change q (moduleSpecΓFunctor.map (P.map lA) v) =
    moduleSpecΓFunctor.map lB
      (moduleSpecΓFunctor.map (originalPullbackUnitIso (Spec.map φ)).hom v) at hframe
  change η.app (moduleSpecΓFunctor.obj SA)
      (moduleSpecΓFunctor.map lA (1 : Γ(Spec A, ⊤))) =
    E.map (moduleSpecΓFunctor.map lA)
      (η.app (moduleSpecΓFunctor.obj UA) (1 : Γ(Spec A, ⊤))) at hη
  change (originalSpecPullbackSectionsIso φ SA).hom
      (E.map (moduleSpecΓFunctor.map lA)
        (η.app (moduleSpecΓFunctor.obj UA) (1 : Γ(Spec A, ⊤)))) =
    moduleSpecΓFunctor.map (P.map lA)
      ((originalSpecPullbackSectionsIso φ UA).hom
        (η.app (moduleSpecΓFunctor.obj UA) (1 : Γ(Spec A, ⊤)))) at hn
  calc
    _ = q ((originalSpecPullbackSectionsIso φ SA).hom
        (η.app (moduleSpecΓFunctor.obj SA)
          (moduleSpecΓFunctor.map lA (1 : Γ(Spec A, ⊤))))) :=
      congrArg (fun a => q ((originalSpecPullbackSectionsIso φ SA).hom
        (η.app (moduleSpecΓFunctor.obj SA) a))) hbA
    _ = q ((originalSpecPullbackSectionsIso φ SA).hom
        (E.map (moduleSpecΓFunctor.map lA)
          (η.app (moduleSpecΓFunctor.obj UA) (1 : Γ(Spec A, ⊤))))) :=
      congrArg (fun a => q ((originalSpecPullbackSectionsIso φ SA).hom a)) hη
    _ = q (moduleSpecΓFunctor.map (P.map lA)
        ((originalSpecPullbackSectionsIso φ UA).hom
          (η.app (moduleSpecΓFunctor.obj UA) (1 : Γ(Spec A, ⊤))))) := congrArg q hn
    _ = q (moduleSpecΓFunctor.map (P.map lA) v) :=
      congrArg (fun a => q (moduleSpecΓFunctor.map (P.map lA) a)) hu
    _ = moduleSpecΓFunctor.map lB
        (moduleSpecΓFunctor.map (originalPullbackUnitIso (Spec.map φ)).hom v) := hframe
    _ = moduleSpecΓFunctor.map lB (1 : Γ(Spec B, ⊤)) :=
      congrArg (moduleSpecΓFunctor.map lB) (originalSpecPullbackUnitTop_frame_one φ)
    _ = _ := hbB.symm

end Hironaka.Geometry.QuotGrassmann
