/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.ConductorLocalization
import DeJongAlterations.Algebra.NodeFittingIdealSheafAffinePullback
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The intrinsic conductor ideal sheaf of the original finite morphism

Its affine ideals are the annihilators of the original structure-map cokernels. Their actual
restriction maps satisfy the localization identities required by native `IdealSheafData`.
No alternative algebra, coefficient preimage, or section-lift certificate is supplied.

Blueprint: `scheme-conductor.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace DeJongAlterations.StableModificationBridge.SchemeConductor

theorem baseIdeal_away {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (ρ : A →+* A') (σ : B →+* B') (φ' : A' →+* B')
    (hcomm : φ'.comp ρ = σ.comp φ) (hfin : φ.Finite) (f : A)
    (hρ : letI := ρ.toAlgebra; IsLocalization.Away f A')
    (hσ : letI := σ.toAlgebra; IsLocalization.Away (φ f) B') :
    letI := φ.toAlgebra
    letI := φ'.toAlgebra
    (FiniteAlgebraConductor.baseIdeal A B).map ρ =
      FiniteAlgebraConductor.baseIdeal A' B' := by
  let := φ.toAlgebra
  let := ρ.toAlgebra
  let := σ.toAlgebra
  let := φ'.toAlgebra
  let : Algebra A B' := (σ.comp φ).toAlgebra
  let : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A A' B' :=
    IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun hcomm a).symm
  let : IsLocalization.Away f A' := hρ
  let : IsLocalization.Away (algebraMap A B f) B' := hσ
  let : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) B' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  let : Module.Finite A B := hfin
  exact ConductorLocalization.baseIdeal_map_eq A' B' (Submonoid.powers f)

variable {X Y : Scheme.{u}} (ν : Y ⟶ X)

def affineIdeal (U : X.affineOpens) : Ideal Γ(X, U) :=
  letI := (ν.app U).hom.toAlgebra
  FiniteAlgebraConductor.baseIdeal Γ(X, U) Γ(Y, ν ⁻¹ᵁ U)

theorem affineIdeal_basicOpen [IsFinite ν] (U : X.affineOpens) (f : Γ(X, U)) :
    (affineIdeal ν U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      affineIdeal ν (X.affineBasicOpen f) := by
  let ρ := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let σ := (Y.presheaf.map (homOfLE (ν.preimage_mono (X.basicOpen_le f))).op).hom
  have hcomm : (ν.app (X.basicOpen f)).hom.comp ρ = σ.comp (ν.app U).hom := by
    exact congrArg CommRingCat.Hom.hom (ν.naturality (homOfLE (X.basicOpen_le f)).op)
  have hρ : letI := ρ.toAlgebra; IsLocalization.Away f Γ(X, X.basicOpen f) :=
    U.2.isLocalization_basicOpen f
  have hσ : letI := σ.toAlgebra;
      IsLocalization.Away ((ν.app U).hom f) Γ(Y, ν ⁻¹ᵁ X.basicOpen f) :=
    (U.2.preimage ν).isLocalization_of_eq_basicOpen ((ν.app U).hom f)
      (homOfLE (ν.preimage_mono (X.basicOpen_le f))) (Scheme.preimage_basicOpen ν f)
  exact baseIdeal_away (ν.app U).hom ρ σ (ν.app (X.basicOpen f)).hom hcomm
    (ν.finite_app U U.2) f hρ hσ

def idealSheaf [IsFinite ν] : X.IdealSheafData where
  ideal := affineIdeal ν
  map_ideal_basicOpen := affineIdeal_basicOpen ν

@[simp]
theorem idealSheaf_ideal [IsFinite ν] (U : X.affineOpens) :
    (idealSheaf ν).ideal U = affineIdeal ν U := rfl

noncomputable def sourceIdealSheaf [IsFinite ν] : Y.IdealSheafData :=
  (idealSheaf ν).comap ν

theorem sourceIdealSheaf_ideal_preimage [IsFinite ν] (U : X.affineOpens) :
    letI := (ν.app U).hom.toAlgebra
    (sourceIdealSheaf ν).ideal ⟨ν ⁻¹ᵁ U.1, U.2.preimage ν⟩ =
      FiniteAlgebraConductor.ideal Γ(X, U) Γ(Y, ν ⁻¹ᵁ U.1) := by
  let := (ν.app U).hom.toAlgebra
  rw [sourceIdealSheaf, Algebra.NodeFittingIdealSheaf.ideal_comap_of_le (idealSheaf ν)
    ν U ⟨ν ⁻¹ᵁ U.1, U.2.preimage ν⟩ le_rfl]
  change (FiniteAlgebraConductor.baseIdeal Γ(X, U) Γ(Y, ν ⁻¹ᵁ U.1)).map
    (ν.appLE U.1 (ν ⁻¹ᵁ U.1) le_rfl).hom = _
  rw [Scheme.Hom.appLE_eq_app]
  exact FiniteAlgebraConductor.map_baseIdeal_eq _ _

end DeJongAlterations.StableModificationBridge.SchemeConductor
