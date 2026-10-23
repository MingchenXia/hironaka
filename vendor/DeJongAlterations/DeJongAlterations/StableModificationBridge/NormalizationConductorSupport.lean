/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.SchemeConductor
import DeJongAlterations.StableModification.CurvesField.GenusReduced
import Mathlib.RingTheory.Support
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite support of the actual canonical normalization conductor

The conductor support is identified with the native original delta support. Finiteness then
comes from the proved finite-dimensional canonical normalization cokernels and genus theorem.

Blueprint: `normalization-conductor-support.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Module
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.CurvesField.Genus
open DeJongAlterations.StableModification.Cohomology

namespace DeJongAlterations.StableModificationBridge.NormalizationConductorSupport

theorem baseIdeal_le_iff_deltaAt_ne_zero {K A B : Type u}
    [Field K] [CommRing A] [CommRing B] (ψ : K →+* A) (φ : A →+* B)
    (hfin : φ.Finite) (hcoker : IsFiniteCoker ψ φ) (q : PrimeSpectrum A) :
    letI := φ.toAlgebra
    FiniteAlgebraConductor.baseIdeal A B ≤ q.asIdeal ↔ deltaAt ψ φ q ≠ 0 := by
  let := ψ.toAlgebra
  let := φ.toAlgebra
  let := (φ.comp ψ).toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite A B := hfin
  let : FiniteDimensional K (Coker A B) := hcoker
  let hd := isLocalDecomposition (k := K) (A := A) (Coker A B)
  let : FiniteDimensional K (LocalizedModule q.asIdeal.primeCompl (Coker A B)) :=
    hd.finiteDimensional q
  change Module.annihilator A (Coker A B) ≤ q.asIdeal ↔
    finrank K (LocalizedModule q.asIdeal.primeCompl (Coker A B)) ≠ 0
  rw [← Module.mem_support_iff_of_finite, Module.mem_support_iff,
    ← finrank_pos_iff (R := K), Nat.pos_iff_ne_zero]

variable {X Y : Scheme.{u}} (ν : Y ⟶ X) [IsFinite ν] {K : Type u} [Field K]
  (c : K →+* Γ(X, ⊤))

theorem mem_support_iff_deltaInvariant_ne_zero
    (hcoker : ∀ (U : X.Opens), IsAffineOpen U →
      IsFiniteCoker (sectionsRingHom c (le_top : U ≤ ⊤)) (ν.app U).hom) (x : X) :
    x ∈ (SchemeConductor.idealSheaf ν).support ↔ deltaInvariant ν c x ≠ 0 := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  let q := hU.primeIdealOf ⟨x, hx⟩
  have hz : x ∈ X.zeroLocus (U := U) (SchemeConductor.affineIdeal ν ⟨U, hU⟩) ↔
      SchemeConductor.affineIdeal ν ⟨U, hU⟩ ≤ q.asIdeal := by
    have h := Set.ext_iff.mp
      (hU.fromSpec_preimage_zeroLocus (SchemeConductor.affineIdeal ν ⟨U, hU⟩)) q
    change hU.fromSpec q ∈ X.zeroLocus (U := U) (SchemeConductor.affineIdeal ν ⟨U, hU⟩) ↔
      SchemeConductor.affineIdeal ν ⟨U, hU⟩ ≤ q.asIdeal at h
    rw [show hU.fromSpec q = x from hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
    exact h
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hx]
  change x ∈ X.zeroLocus (U := U) (SchemeConductor.affineIdeal ν ⟨U, hU⟩) ↔ _
  rw [hz]
  change (letI := (ν.app U).hom.toAlgebra
      FiniteAlgebraConductor.baseIdeal Γ(X, U) Γ(Y, ν ⁻¹ᵁ U) ≤ q.asIdeal) ↔ _
  rw [baseIdeal_le_iff_deltaAt_ne_zero (sectionsRingHom c (le_top : U ≤ ⊤))
    (ν.app U).hom (ν.finite_app U hU) (hcoker U hU) q]
  change chartDelta ν c U hU x hx ≠ 0 ↔ _
  rw [chartDelta_eq_deltaInvariant U hU x hx]

theorem finite_support_normalizationPoints [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsReduced X]
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] (S : Set X) [Finite S]
    (hS : S = genericPoints X) (hdim : topologicalKrullDim X ≤ 1) (hp : IsProjectiveOver p) :
    letI : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap p
    ((SchemeConductor.idealSheaf (normalizationPointsMap S)).support : Set X).Finite := by
  let : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap p
  have heq : ((SchemeConductor.idealSheaf (normalizationPointsMap S)).support : Set X) =
      Function.support (deltaInvariant (normalizationPointsMap S) (structureCoeff p)) := by
    ext x
    exact mem_support_iff_deltaInvariant_ne_zero _ (structureCoeff p)
      (fun U hU => normalizationPoints_isFiniteCoker p hS hdim U hU) x
  rw [heq]
  exact (arithmeticGenus_eq_normalizationPoints p S hS hdim hp).2.1

theorem finite_source_support_normalizationPoints [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsReduced X]
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] (S : Set X) [Finite S]
    (hS : S = genericPoints X) (hdim : topologicalKrullDim X ≤ 1) (hp : IsProjectiveOver p) :
    letI : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap p
    ((SchemeConductor.sourceIdealSheaf (normalizationPointsMap S)).support :
      Set (normalizationPoints S)).Finite := by
  let : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap p
  change (((SchemeConductor.idealSheaf (normalizationPointsMap S)).comap
    (normalizationPointsMap S)).support : Set (normalizationPoints S)).Finite
  rw [Scheme.IdealSheafData.support_comap]
  exact (normalizationPointsMap S).finite_preimage
    (finite_support_normalizationPoints p S hS hdim hp)

theorem isClosed_singleton_of_mem_finite_closed {Z : Type u} [TopologicalSpace Z]
    [JacobsonSpace Z] (T : Closeds Z) (hT : (T : Set Z).Finite) {x : Z} (hx : x ∈ T) :
    IsClosed ({x} : Set Z) := by
  let : Finite T := hT
  let : JacobsonSpace T := JacobsonSpace.of_isClosedEmbedding T.isClosed.isClosedEmbedding_subtypeVal
  have h : IsClosed ({(⟨x, hx⟩ : T)} : Set T) := isClosed_singleton
  have hi := T.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ h
  simpa only [Set.image_singleton] using hi

theorem isClosed_source_support_points_normalizationPoints [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsReduced X]
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] (S : Set X) [Finite S]
    (hS : S = genericPoints X) (hdim : topologicalKrullDim X ≤ 1) (hp : IsProjectiveOver p) :
    letI : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap p
    ∀ x ∈ (SchemeConductor.sourceIdealSheaf (normalizationPointsMap S)).support,
      IsClosed ({x} : Set (normalizationPoints S)) := by
  let : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap p
  let : JacobsonSpace (normalizationPoints S) :=
    LocallyOfFiniteType.jacobsonSpace (normalizationPointsMap S ≫ p)
  intro x hx
  exact isClosed_singleton_of_mem_finite_closed _
    (finite_source_support_normalizationPoints p S hS hdim hp) hx

end DeJongAlterations.StableModificationBridge.NormalizationConductorSupport
