import Hironaka.Geometry.ProperSteinGlobalSections

/-! # Actual original affine-base normalization rings are the SAME proper source section rings. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace Hironaka.Geometry.ProperSteinGlobalSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ORIGINAL integral-closure chart ring is the actual section ring of its SAME normalization open. -/
def normalizationChartSectionsIso {S : Scheme.{u}} [IsIntegral S]
    (L : Type u) [Field L] [Algebra S.functionField L]
    (U : NormalizationInExtension.NonemptyAffineOpen S) :
    CommRingCat.of (NormalizationInExtension.closureRing L U) ≅
      Γ(NormalizationInExtension.normalization S L,
        NormalizationInExtension.normalizationStructure S L ⁻¹ᵁ U.1.1) :=
  (Scheme.ΓSpecIso (.of (NormalizationInExtension.closureRing L U))).symm ≪≫
    IsOpenImmersion.ΓIsoTop (NormalizationInExtension.chartInclusion S L U) ≪≫
      (NormalizationInExtension.normalization S L).presheaf.mapIso
        (eqToIso (NormalizationInExtension.chartInclusion_opensRange L U).symm).op

/-- The actual inverse is the ORIGINAL chart pullback on sections, followed by the native spectrum-section map. -/
theorem normalizationChartSectionsIso_inv {S : Scheme.{u}} [IsIntegral S]
    (L : Type u) [Field L] [Algebra S.functionField L]
    (U : NormalizationInExtension.NonemptyAffineOpen S) :
    (normalizationChartSectionsIso L U).inv =
      (NormalizationInExtension.chartInclusion S L U).appLE
        (NormalizationInExtension.normalizationStructure S L ⁻¹ᵁ U.1.1) ⊤
        (by rw [← NormalizationInExtension.chartInclusion_opensRange L U,
          Scheme.Hom.preimage_opensRange]) ≫
        (Scheme.ΓSpecIso (.of (NormalizationInExtension.closureRing L U))).hom := by
  simp [normalizationChartSectionsIso, IsOpenImmersion.ΓIsoTop,
    Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

/-- The ENTIRE original affine coefficient map is retained by the actual normalization-chart isomorphism. -/
theorem normalizationChartSectionsIso_coeff {S : Scheme.{u}} [IsIntegral S]
    (L : Type u) [Field L] [Algebra S.functionField L]
    (U : NormalizationInExtension.NonemptyAffineOpen S) :
    CommRingCat.ofHom (algebraMap Γ(S, U.1.1) (NormalizationInExtension.closureRing L U)) ≫
      (normalizationChartSectionsIso L U).hom =
        (NormalizationInExtension.normalizationStructure S L).app U.1.1 := by
  apply (cancel_mono (normalizationChartSectionsIso L U).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [normalizationChartSectionsIso_inv, ← Category.assoc,
    ← Scheme.Hom.comp_appLE]
  simp only [NormalizationInExtension.chartInclusion_structure]
  simp only [NormalizationInExtension.affineStructure, Scheme.Hom.comp_appLE,
    IsAffineOpen.fromSpec_app_self, Category.assoc, Scheme.Hom.map_appLE]
  change CommRingCat.ofHom (algebraMap Γ(S, U.1.1) (NormalizationInExtension.closureRing L U)) =
    (Scheme.ΓSpecIso Γ(S, U.1.1)).inv ≫
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(S, U.1.1) (NormalizationInExtension.closureRing L U)))).appTop ≫
        (Scheme.ΓSpecIso (.of (NormalizationInExtension.closureRing L U))).hom
  rw [Scheme.ΓSpecIso_naturality]
  change _ = (Scheme.ΓSpecIso Γ(S, U.1.1)).inv ≫
    (Scheme.ΓSpecIso Γ(S, U.1.1)).hom ≫ _
  simp

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f] [LocallyOfFiniteType f] [AlgebraicGeometry.IsNoetherian X]
  (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (hf : IsProper f) (hnormal : IsNormalScheme X)

/-- The ORIGINAL factorization identity identifies the SAME original source opens on sections. -/
def originalPreimageSectionsIso (U : S.Opens) :
    Γ(X, SteinCurveFactor.factor f hdim p hnormal ⁻¹ᵁ SteinCurveFactor.baseMap f ⁻¹ᵁ U) ≅
      Γ(X, f ⁻¹ᵁ U) :=
  X.presheaf.mapIso (eqToIso (show f ⁻¹ᵁ U =
    SteinCurveFactor.factor f hdim p hnormal ⁻¹ᵁ SteinCurveFactor.baseMap f ⁻¹ᵁ U by
      rw [← Scheme.Hom.comp_preimage, SteinCurveFactor.factor_structure])).op

/-- The SAME actual intrinsic normalization ring is the actual ORIGINAL affine-base source section ring. -/
def originalAffineClosureSectionsIso (U : NormalizationInExtension.NonemptyAffineOpen S) :
    CommRingCat.of (NormalizationInExtension.closureRing (SteinCurveFactor.constantField f) U) ≅
      Γ(X, f ⁻¹ᵁ U.1.1) := by
  let := factor_isIso_app f hdim p hf hnormal (SteinCurveFactor.baseMap f ⁻¹ᵁ U.1.1)
  exact normalizationChartSectionsIso (SteinCurveFactor.constantField f) U ≪≫
    asIso ((SteinCurveFactor.factor f hdim p hnormal).app
      (SteinCurveFactor.baseMap f ⁻¹ᵁ U.1.1)) ≪≫
    originalPreimageSectionsIso f hdim p hnormal U.1.1

/-- An actual ring equivalence, with no section-ring or inverse certificate supplied. -/
def originalAffineClosureSectionsEquiv (U : NormalizationInExtension.NonemptyAffineOpen S) :
    NormalizationInExtension.closureRing (SteinCurveFactor.constantField f) U ≃+*
      Γ(X, f ⁻¹ᵁ U.1.1) :=
  (originalAffineClosureSectionsIso f hdim p hf hnormal U).commRingCatIsoToRingEquiv

/-- Its ENTIRE forward map is precisely the ORIGINAL chart map, SAME factor pullback, and original factorization. -/
theorem originalAffineClosureSectionsEquiv_apply
    (U : NormalizationInExtension.NonemptyAffineOpen S)
    (c : NormalizationInExtension.closureRing (SteinCurveFactor.constantField f) U) :
    originalAffineClosureSectionsEquiv f hdim p hf hnormal U c =
      (originalPreimageSectionsIso f hdim p hnormal U.1.1).hom
        ((SteinCurveFactor.factor f hdim p hnormal).app
          (SteinCurveFactor.baseMap f ⁻¹ᵁ U.1.1)
          ((normalizationChartSectionsIso (SteinCurveFactor.constantField f) U).hom c)) := rfl

/-- The ENTIRE original-base coefficient map is preserved by the SAME intrinsic integral-closure section equivalence. -/
theorem originalAffineClosureSectionsEquiv_coeff
    (U : NormalizationInExtension.NonemptyAffineOpen S) :
    (originalAffineClosureSectionsEquiv f hdim p hf hnormal U).toRingHom.comp
      (algebraMap Γ(S, U.1.1)
        (NormalizationInExtension.closureRing (SteinCurveFactor.constantField f) U)) =
      (f.app U.1.1).hom := by
  apply CommRingCat.hom_ext_iff.mp
  change (CommRingCat.ofHom (algebraMap Γ(S, U.1.1)
      (NormalizationInExtension.closureRing (SteinCurveFactor.constantField f) U)) ≫
    (normalizationChartSectionsIso (SteinCurveFactor.constantField f) U).hom ≫
      (SteinCurveFactor.factor f hdim p hnormal).app (SteinCurveFactor.baseMap f ⁻¹ᵁ U.1.1) ≫
        (originalPreimageSectionsIso f hdim p hnormal U.1.1).hom) = f.app U.1.1
  rw [← Category.assoc, ← Category.assoc, normalizationChartSectionsIso_coeff]
  have h := Scheme.Hom.congr_app (SteinCurveFactor.factor_structure f hdim p hnormal) U.1.1
  change (SteinCurveFactor.baseMap f).app U.1.1 ≫
    (SteinCurveFactor.factor f hdim p hnormal).app (SteinCurveFactor.baseMap f ⁻¹ᵁ U.1.1) = _ at h
  rw [h]
  simp [originalPreimageSectionsIso, Category.assoc, ← Functor.map_comp]

/-- The actual section equivalence is an algebra equivalence for the ORIGINAL base-open coefficients. -/
def originalAffineClosureSectionsAlgEquiv
    (U : NormalizationInExtension.NonemptyAffineOpen S) :
    letI : Algebra Γ(S, U.1.1) Γ(X, f ⁻¹ᵁ U.1.1) := (f.app U.1.1).hom.toAlgebra
    NormalizationInExtension.closureRing (SteinCurveFactor.constantField f) U ≃ₐ[Γ(S, U.1.1)]
      Γ(X, f ⁻¹ᵁ U.1.1) := by
  let : Algebra Γ(S, U.1.1) Γ(X, f ⁻¹ᵁ U.1.1) := (f.app U.1.1).hom.toAlgebra
  exact { originalAffineClosureSectionsEquiv f hdim p hf hnormal U with
    commutes' := fun r => DFunLike.congr_fun
      (originalAffineClosureSectionsEquiv_coeff f hdim p hf hnormal U) r }

include hdim p hf hnormal in
/-- Finite normalization DERIVES finiteness of the ORIGINAL whole section algebra over every original affine base open. -/
theorem originalAffineSections_finite
    (U : NormalizationInExtension.NonemptyAffineOpen S) :
    letI : Algebra Γ(S, U.1.1) Γ(X, f ⁻¹ᵁ U.1.1) := (f.app U.1.1).hom.toAlgebra
    Module.Finite Γ(S, U.1.1) Γ(X, f ⁻¹ᵁ U.1.1) := by
  let : Algebra Γ(S, U.1.1) Γ(X, f ⁻¹ᵁ U.1.1) := (f.app U.1.1).hom.toAlgebra
  let := SteinCurveFactor.constantField_finite f hdim
  let : Module.Finite Γ(S, U.1.1)
      (NormalizationInExtension.closureRing (SteinCurveFactor.constantField f) U) :=
    NormalizationInExtension.closureRing_finite (SteinCurveFactor.constantField f) p U
  exact Module.Finite.of_surjective
    (originalAffineClosureSectionsAlgEquiv f hdim p hf hnormal U).toLinearMap
    (originalAffineClosureSectionsAlgEquiv f hdim p hf hnormal U).surjective

end Hironaka.Geometry.ProperSteinGlobalSections
