/-
The minimal actual affine tensor-scheme comparison and its whole projection formulas
adapt EnvelopeProperty/Berkovich/SchemeScalarBaseChange.lean (affineTensorIso and its
first two projection lemmas), SHA256
3811e2359e503fdba175f1e130335cdcee839d890b95a1817648823df2343f57.
Copyright (c) 2026 EnvelopeProperty contributors; repository license.
Modified: retain only the three affine pullback cores, with no analytic or valuation imports.
All geometric/native-coefficient/stalk differential arguments here are new.
-/
import DeJongAlterations.Algebra.NodeGeometricCompletionOriginalBaseChangeUV
import DeJongAlterations.Geometry.NodeCompletedLocalCoherentUV
import Mathlib.AlgebraicGeometry.Pullbacks

/-! Actual affine scheme scalar base change, actual original point stalk localization,
and ORIGINAL family differential completion. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalAffineBaseChangeUV

open Algebra.NodeGeometricCompletionOriginalBaseChange
  Algebra.NodeGeometricCompletionOriginalBaseChangeUV
  Algebra.NodeGeometricCompletionDifferentialTransport
  Algebra.NodeGeometricCompletionFormalUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The actual native tensor-spectrum stalk localization action, exposed without
changing the adopted scheme field or original-family coefficient actions. -/
@[instance_reducible]
def nativeSpecStalkAlgebra (T : Type u) [CommRing T] (y : PrimeSpectrum T) :
    Algebra T ((Spec (.of T)).presheaf.stalk y) :=
  (StructureSheaf.toStalk T y).hom.toAlgebra

/-- Native actual point-stalk localization for this SAME explicitly exposed action. -/
theorem nativeSpecStalkLocalization (T : Type u) [CommRing T] (y : PrimeSpectrum T) :
    letI := nativeSpecStalkAlgebra T y
    IsLocalization y.asIdeal.primeCompl ((Spec (.of T)).presheaf.stalk y) := by
  exact inferInstanceAs (IsLocalization y.asIdeal.primeCompl
    ((Spec.structureSheaf T).presheaf.stalk y))

/-- The native affine field-stalk action is the SAME coefficient action obtained by
composing the actual spectrum coefficient map and the native actual stalk localization. -/
theorem specStalk_scalarTower (B T : Type u) [CommRing B] [CommRing T] [Algebra B T]
    (y : PrimeSpectrum T) :
    letI := nativeSpecStalkAlgebra T y
    letI := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap B T))) y
    IsScalarTower B T ((Spec (.of T)).presheaf.stalk y) := by
  let := nativeSpecStalkAlgebra T y
  let := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap B T))) y
  apply IsScalarTower.of_algebraMap_eq'
  have hid : Scheme.baseToStalk (𝟙 (Spec (.of T))) y = StructureSheaf.toStalk T y := by
    simp only [Scheme.baseToStalk, Scheme.Modules.baseRingHom,
      Scheme.Hom.id_appTop, Category.comp_id, Scheme.ΓSpecIso_inv]
    rfl
  have h := Scheme.baseToStalk_comp (CommRingCat.ofHom (algebraMap B T)) (𝟙 (Spec (.of T))) y
  rw [Category.id_comp, hid] at h
  exact congrArg CommRingCat.Hom.hom h.symm

variable (A R K : Type u) [CommRing A] [CommRing R] [Field K]
  [Algebra A R] [Algebra A K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual affine ORIGINAL family. -/
abbrev originalFamily : Spec (.of R) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A R))

/-- Its literal actual scheme scalar base change. -/
abbrev ActualBaseChange : Scheme.{u} :=
  pullback (originalFamily A R) (Spec.map (CommRingCat.ofHom (algebraMap A K)))

/-- The literal original tensor spectrum is the ACTUAL affine scheme pullback. -/
def actualTensorIso : ActualBaseChange A R K ≅ Spec (.of (ScalarExtension A R K)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A K R

/-- The SAME actual tensor comparison retains the WHOLE original family projection. -/
theorem actualTensorIso_hom_original :
    (actualTensorIso A R K).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (ScalarExtension A R K))) = pullback.fst _ _ := by
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso A K R).hom) ≫ _ = _
  rw [Category.assoc]
  erw [pullbackSpecIso_hom_snd]
  exact pullbackSymmetry_hom_comp_snd _ _

/-- The SAME actual tensor comparison retains the WHOLE field coefficient projection. -/
theorem actualTensorIso_hom_field :
    (actualTensorIso A R K).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (ScalarExtension A R K))) = pullback.snd _ _ := by
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso A K R).hom) ≫ _ = _
  rw [Category.assoc, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]

variable [Algebra.FiniteType A R]

/-- The actual ORIGINAL-family Ω completed on the actual tensor-spectrum stalk, then
identified through the ACTUAL coefficient-compatible completed field-node model. -/
def actualAffineStalkRelativeUVEquiv (y : PrimeSpectrum (ScalarExtension A R K)) :
    letI := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom
      (algebraMap R (ScalarExtension A R K)))) y
    letI := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom
      (algebraMap K (ScalarExtension A R K)))) y
    letI := Scheme.completedLocalRingAlgebra (Spec.map (CommRingCat.ofHom
      (algebraMap K (ScalarExtension A R K)))) y
    (e : (Spec (.of (ScalarExtension A R K))).completedLocalRing y ≃ₐ[K] FormalUV K) →
      letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
      letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv
      ((Spec (.of (ScalarExtension A R K))).completedLocalRing y ⊗[R] KaehlerDifferential A R)
        ≃ₛₗ[e.toRingHom] DifferentialModule K := by
  letI := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom
    (algebraMap R (ScalarExtension A R K)))) y
  letI := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom
    (algebraMap K (ScalarExtension A R K)))) y
  letI := Scheme.completedLocalRingAlgebra (Spec.map (CommRingCat.ofHom
    (algebraMap K (ScalarExtension A R K)))) y
  letI := nativeSpecStalkAlgebra (ScalarExtension A R K) y
  letI := nativeSpecStalkLocalization (ScalarExtension A R K) y
  letI := specStalk_scalarTower R (ScalarExtension A R K) y
  letI := specStalk_scalarTower K (ScalarExtension A R K) y
  exact originalCompletedUVEquiv A R K
    ((Spec (.of (ScalarExtension A R K))).presheaf.stalk y) y.asIdeal

end DeJongAlterations.Geometry.NodeCompletedLocalAffineBaseChangeUV
