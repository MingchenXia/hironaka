/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedCartierAlgebra
import DeJongAlterations.StableModification.Omega.InvertibleSmooth
import DeJongAlterations.Geometry.NodeCompletedLocalOriginalStalkOmega
import DeJongAlterations.Algebra.NodeFittingIdealSheafQuotient

/-!
# Regular kernel generators at the actual original marked stalks

No equation, Cartier certificate, or differential comparison is an input.
The original smooth/étale marking and normal generic-smooth nodal source give
all local inputs internally, with the full original coefficient triangle.

Blueprint: `stable-marked-cartier-stalk.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing TensorProduct

namespace DeJongAlterations.StableModificationBridge.StableMarkedCartierStalk

open StableModification
open Algebra.NodeFittingOmegaCharts Algebra.NodeFittingOmegaStalk

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

private theorem exists_local_differential_equiv {X S : Scheme.{u}} (f : X ⟶ S)
    [DeJong.IsNodalCurve f] {x : X} (hx : x ∈ f.smoothLocus) :
    letI := stalkAlgebra f x
    Nonempty (KaehlerDifferential (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) := by
  obtain ⟨V, hV, W, hW, hWV, hxW, -, hstd⟩ :=
    Omega.exists_isStandardSmoothOfRelativeDimension_one f
      (fun K _ _ a Z hZ => DeJong.IsNodalCurve.pureGeometricFibers K a Z hZ) hx
  let C : Chart f := ⟨⟨W, hW⟩, ⟨V, hV⟩, hWV⟩
  let := C.algebra f
  let := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  let := stalkAlgebra f x
  have : Nontrivial Γ(X, W) := Omega.nontrivial_sections_of_mem hxW
  obtain ⟨eΩ⟩ := Omega.kaehler_linearEquiv_of_isStandardSmoothOfRelativeDimension_one _ hstd
  exact ⟨(Geometry.NodeCompletedLocalOriginalStalkOmega.chartLocalOmegaEquiv f C x hxW).symm ≪≫ₗ
    eΩ.baseChange Γ(X, W) (X.presheaf.stalk x) _ _ ≪≫ₗ
      AlgebraTensorModule.rid Γ(X, W) (X.presheaf.stalk x) (X.presheaf.stalk x)⟩

/-- The original semistable marking has an actual regular kernel generator at
every original marked stalk, with no local equation or coefficient certificate. -/
theorem exists_regular_stalk_kernel_generator {X S : Scheme.{u}} (f : X ⟶ S)
    [DeJong.IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S]
    (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → DeJong.IsSmoothAt f x)
    (D : X.IdealSheafData) (hD : DeJong.IsSemistablePair f D) (z : D.subscheme) :
    ∃ t : X.presheaf.stalk (D.subschemeι z), IsRegular t ∧
      RingHom.ker (D.subschemeι.stalkMap z).hom = Ideal.span {t} := by
  let x := D.subschemeι z
  let A := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let C := D.subscheme.presheaf.stalk z
  let : Algebra A B := stalkAlgebra f x
  let : Algebra B C := (D.subschemeι.stalkMap z).hom.toAlgebra
  let : Algebra A C := ((D.subschemeι ≫ f).stalkMap z).hom.toAlgebra
  let : IsScalarTower A B C := by
    apply IsScalarTower.of_algebraMap_eq'
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp D.subschemeι f z)
  have hxD : x ∈ (D.support : Set X) := by
    rw [← D.range_subschemeι]
    exact ⟨z, rfl⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsDomain B := (Curves.SemistableNormal.isNormalScheme_of_isNodalCurve f hS hgen x).1
  let : Algebra.FormallySmooth A B := hD.smoothAlong x hxD
  let := hD.etale
  let : Algebra.FormallySmooth A C := Curves.isSmoothAt_of_smooth (D.subschemeι ≫ f) z
  let : Algebra.FormallyUnramified A C := FormallyUnramified.stalkMap (D.subschemeι ≫ f) z
  let : Algebra.FormallyEtale A C := .of_formallyUnramified_and_formallySmooth
  obtain ⟨eΩ⟩ := exists_local_differential_equiv f (hD.support_subset_smoothLocus hxD)
  exact StableMarkedCartierAlgebra.exists_regular_kernel_generator
    (D.subschemeι.stalkMap_surjective z) eΩ

end DeJongAlterations.StableModificationBridge.StableMarkedCartierStalk
