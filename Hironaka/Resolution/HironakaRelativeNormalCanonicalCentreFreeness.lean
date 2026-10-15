/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalCentreScalars
import Hironaka.Resolution.HironakaRelativeNormalCoefficientAlgebraNearbyFreeness

/-! # Canonical centre-ring free and flat modules on the original SAME open
The centre action is the preceding intrinsically descended action. Actual
identity semilinear equivalences only compare it with the old tangent action.
Original coherent input internally supplies the same actual U for whole and
all degree canonical centre modules. No truncation centre action, sheaf or
centre-containment certificate is introduced.
-/
set_option autoImplicit false
open Set Filter
open scoped DirectSum Topology
namespace Hironaka.HironakaRelativeNormalCanonicalCentreFreeness
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalCentreScalars HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations

private theorem planeQuotientRingHomInvPair (d t : ℕ) :
    RingHomInvPair (planeQuotientAlgEquiv d t).toRingHom (planeQuotientAlgEquiv d t).symm.toRingHom := by
  constructor
  ·
    apply RingHom.ext
    intro x
    exact (planeQuotientAlgEquiv d t).symm_apply_apply x
  ·
    apply RingHom.ext
    intro x
    exact (planeQuotientAlgEquiv d t).apply_symm_apply x

private theorem planeQuotientRingHomInvPairSymm (d t : ℕ) :
    RingHomInvPair (planeQuotientAlgEquiv d t).symm.toRingHom (planeQuotientAlgEquiv d t).toRingHom := by
  constructor
  ·
    apply RingHom.ext
    intro x
    exact (planeQuotientAlgEquiv d t).apply_symm_apply x
  ·
    apply RingHom.ext
    intro x
    exact (planeQuotientAlgEquiv d t).symm_apply_apply x

attribute [local instance] planeQuotientRingHomInvPair planeQuotientRingHomInvPairSymm

/-- The identity on the OLD original layer is genuinely semilinear for the TRUE centre trace. -/
def originalNormalGradedPieceCentreTraceEquiv (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
    letI := originalNormalGradedPieceCentreModule d t I q
    LinearEquiv (σ' := (planeQuotientAlgEquiv d t).symm.toRingHom)
      (planeQuotientAlgEquiv d t).toRingHom
      (originalNormalGradedPiece d t I q) (originalNormalGradedPiece d t I q) := by
  letI := tangentAlgebra d t
  letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
  letI := originalNormalGradedPieceCentreModule d t I q
  exact { Equiv.refl _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun c x => originalNormalGradedPieceCentre_smul_eq_planeQuotient d t q I c x }

/-- Every actual original power class is retained literally by the semilinear comparison. -/
theorem originalNormalGradedPieceCentreTraceEquiv_apply (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (x : originalNormalGradedPiece d t I q) :
    originalNormalGradedPieceCentreTraceEquiv d t q I x = x := rfl

/-- The inverse comparison also retains every original layer element literally. -/
theorem originalNormalGradedPieceCentreTraceEquiv_symm_apply (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (x : originalNormalGradedPiece d t I q) :
    (originalNormalGradedPieceCentreTraceEquiv d t q I).symm x = x := rfl

/-- The WHOLE original graded additive group has the true identity semilinear centre dictionary. -/
def originalNormalAssociatedGradedCentreTraceEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalAssociatedGraded d t I) := (originalNormalAssociatedGradedCentreModule d t I).toSMul
    letI := originalNormalAssociatedGradedCentreModule d t I
    LinearEquiv (σ' := (planeQuotientAlgEquiv d t).symm.toRingHom)
      (planeQuotientAlgEquiv d t).toRingHom
      (originalNormalAssociatedGraded d t I) (originalNormalAssociatedGraded d t I) := by
  letI := tangentAlgebra d t
  letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalAssociatedGraded d t I) := (originalNormalAssociatedGradedCentreModule d t I).toSMul
  letI := originalNormalAssociatedGradedCentreModule d t I
  exact { Equiv.refl _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun c x => originalNormalAssociatedGradedCentre_smul_eq_planeQuotient d t I c x }

theorem originalNormalAssociatedGradedCentreTraceEquiv_apply (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (x : originalNormalAssociatedGraded d t I) :
    originalNormalAssociatedGradedCentreTraceEquiv d t I x = x := rfl

theorem originalNormalAssociatedGradedCentreTraceEquiv_symm_apply (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (x : originalNormalAssociatedGraded d t I) :
    (originalNormalAssociatedGradedCentreTraceEquiv d t I).symm x = x := rfl

/-- A true old tangent basis is a basis for the independently descended centre action. -/
theorem originalNormalGradedPieceCentre_free_flat_of_tangent_free (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
    letI := originalNormalGradedPieceCentreModule d t I q
    Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) →
      Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t I q) ∧
      Module.Flat (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t I q) := by
  let := tangentAlgebra d t
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
  let := originalNormalGradedPieceCentreModule d t I q
  intro hfree
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) := hfree
  let : Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t I q) :=
    Module.Free.of_equiv (originalNormalGradedPieceCentreTraceEquiv d t q I).symm
  exact ⟨inferInstance, inferInstance⟩

/-- The actual identity inverse sends a finite tangent generating family to centre generators. -/
theorem originalNormalGradedPieceCentre_finite_of_tangent_finite (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
    letI := originalNormalGradedPieceCentreModule d t I q
    Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) →
      Module.Finite (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t I q) := by
  let := tangentAlgebra d t
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalGradedPiece d t I q) := (originalNormalGradedPieceCentreModule d t I q).toSMul
  let := originalNormalGradedPieceCentreModule d t I q
  intro hfinite
  let : Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I q) := hfinite
  exact Module.Finite.of_surjective
    (originalNormalGradedPieceCentreTraceEquiv d t q I).symm.toLinearMap
    (originalNormalGradedPieceCentreTraceEquiv d t q I).symm.surjective

/-- A whole tangent basis gives whole canonical centre freeness and flatness. -/
theorem originalNormalAssociatedGradedCentre_free_flat_of_tangent_free (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalAssociatedGraded d t I) := (originalNormalAssociatedGradedCentreModule d t I).toSMul
    letI := originalNormalAssociatedGradedCentreModule d t I
    Module.Free (HolGerm (ComplexModel d)) (originalNormalAssociatedGraded d t I) →
      Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalAssociatedGraded d t I) ∧
      Module.Flat (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalAssociatedGraded d t I) := by
  let := tangentAlgebra d t
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalAssociatedGraded d t I) := (originalNormalAssociatedGradedCentreModule d t I).toSMul
  let := originalNormalAssociatedGradedCentreModule d t I
  intro hfree
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalAssociatedGraded d t I) := hfree
  let : Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalAssociatedGraded d t I) :=
    Module.Free.of_equiv (originalNormalAssociatedGradedCentreTraceEquiv d t I).symm
  exact ⟨inferInstance, inferInstance⟩

/-- Original coherence supplies a single nonvacuous open for the actual canonical centre actions. -/
theorem exists_original_nearby_canonical_centre_free_flat_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U,
        let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
        letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
          (originalNormalAssociatedGraded d t Ia) := (originalNormalAssociatedGradedCentreModule d t Ia).toSMul
        letI := originalNormalAssociatedGradedCentreModule d t Ia
        (Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalAssociatedGraded d t Ia) ∧
          Module.Flat (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalAssociatedGraded d t Ia)) ∧
        ∀ q : ℕ,
          letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
            (originalNormalGradedPiece d t Ia q) := (originalNormalGradedPieceCentreModule d t Ia q).toSMul
          letI := originalNormalGradedPieceCentreModule d t Ia q
          Module.Finite (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t Ia q) ∧
          Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t Ia q) ∧
          Module.Flat (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t) (originalNormalGradedPiece d t Ia q) := by
  let := tangentAlgebra d t
  obtain ⟨U, hU, hmeet, hwhole⟩ := exists_original_nearby_associated_free_open d t I hI
  refine ⟨U, hU, hmeet, ?_⟩
  intro a ha
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
  have hb : Module.Free (HolGerm (ComplexModel d)) (originalNormalAssociatedGraded d t Ia) := hwhole a ha
  refine ⟨originalNormalAssociatedGradedCentre_free_flat_of_tangent_free d t Ia hb, ?_⟩
  intro q
  obtain ⟨hfree, hfinite⟩ := all_originalNormalGradedPiece_finite_free_of_associated_free d t Ia hb q
  exact ⟨originalNormalGradedPieceCentre_finite_of_tangent_finite d t q Ia hfinite,
    originalNormalGradedPieceCentre_free_flat_of_tangent_free d t q Ia hfree⟩

end
end Hironaka.HironakaRelativeNormalCanonicalCentreFreeness
