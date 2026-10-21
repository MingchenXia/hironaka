/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalVertexDivision
import Hironaka.Resolution.HironakaActualOriginalFormalNaturality
import Hironaka.Resolution.HironakaActualTriangularSubstitutionHS

/-! Internally constructed original polynomial ideals transfer actual raw HS comparisons to all formal ideals. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualFormalPolynomialJetTransfer
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalTaylor HironakaActualFormalIdealContraction
  HironakaActualOriginalFormalHSTransfer HironakaActualOriginalFormalNaturality
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualCoordinateSpecializationHS HironakaActualTriangularSubstitutionHS
variable {m n : ℕ}

/-- The finite ORIGINAL polynomial ideal is constructed from the SAME actual formal vertices. -/
def actualPolynomialJetIdeal (K : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ) :
    Ideal (HolGerm (ComplexModel (0+n))) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex K =>
    actualFormalApproximation n ℓ (actualVertexSeries MonomialOrder.degLex K a))

/-- Every literal original polynomial generator has the genuine whole formal remainder power. -/
theorem actualPolynomialJetIdeal_generator_remainder (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (ℓ : ℕ) (a : actualInitialVertices MonomialOrder.degLex K) :
    originalTaylorAlgHom n (actualFormalApproximation n ℓ (actualVertexSeries MonomialOrder.degLex K a))-
      actualVertexSeries MonomialOrder.degLex K a ∈ genuineFormalVariables n ^ (ℓ+1) := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n (ℓ+1) _).mpr
  intro α hα
  rw [map_sub,actualFormalApproximation_coefficient n ℓ _ α hα,sub_self]

/-- BOTH whole jet thickenings agree, by actual vertex generation and true polynomial remainders. -/
theorem actualPolynomialJetIdeal_whole_thickening (K : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ) :
    K ⊔ genuineFormalVariables n ^ (ℓ+1)=
      Ideal.map (originalTaylorAlgHom n).toRingHom (actualPolynomialJetIdeal K ℓ) ⊔
        genuineFormalVariables n ^ (ℓ+1) := by
  apply le_antisymm
  · apply sup_le _ le_sup_right
    calc K=Ideal.span (range (actualVertexSeries MonomialOrder.degLex K)) :=
          actual_formal_ideal_eq_span_vertex_series MonomialOrder.degLex K
      _ ≤ _ := by
        apply Ideal.span_le.mpr
        rintro F ⟨a,rfl⟩
        have hga : actualFormalApproximation n ℓ (actualVertexSeries MonomialOrder.degLex K a) ∈
            actualPolynomialJetIdeal K ℓ := Ideal.subset_span ⟨a,rfl⟩
        have hg := Ideal.mem_map_of_mem (originalTaylorAlgHom n).toRingHom hga
        have hr := actualPolynomialJetIdeal_generator_remainder K ℓ a
        have he : originalTaylorAlgHom n (actualFormalApproximation n ℓ (actualVertexSeries MonomialOrder.degLex K a))-
            (originalTaylorAlgHom n (actualFormalApproximation n ℓ (actualVertexSeries MonomialOrder.degLex K a))-
              actualVertexSeries MonomialOrder.degLex K a)=actualVertexSeries MonomialOrder.degLex K a := by abel
        rw [← he]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left hg) (Ideal.mem_sup_right hr)
  · apply sup_le _ le_sup_right
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro g ⟨a,rfl⟩
    change originalTaylorAlgHom n (actualFormalApproximation n ℓ (actualVertexSeries MonomialOrder.degLex K a)) ∈
      K ⊔ genuineFormalVariables n ^ (ℓ+1)
    have hr := actualPolynomialJetIdeal_generator_remainder K ℓ a
    have he : actualVertexSeries MonomialOrder.degLex K a+
        (originalTaylorAlgHom n (actualFormalApproximation n ℓ (actualVertexSeries MonomialOrder.degLex K a))-
          actualVertexSeries MonomialOrder.degLex K a)=
        originalTaylorAlgHom n (actualFormalApproximation n ℓ (actualVertexSeries MonomialOrder.degLex K a)) := by abel
    rw [← he]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (actualVertexSeries_spec MonomialOrder.degLex K a).1)
      (Ideal.mem_sup_right hr)

/-- The SAME original polynomial ideal also gives BOTH whole image-jet directions for the actual map. -/
theorem actualPolynomialJetIdeal_pullback_thickening
    (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ) :
    Ideal.map (actualFormalPullback η hη hη0).toRingHom K ⊔ genuineFormalVariables m ^ (ℓ+1)=
      Ideal.map (originalTaylorAlgHom m).toRingHom
        (Ideal.map (compAlgHom η hη hη0).toRingHom (actualPolynomialJetIdeal K ℓ)) ⊔
          genuineFormalVariables m ^ (ℓ+1) := by
  have hp := map_variables_pow_actualFormalPullback_le η hη hη0 (ℓ+1)
  have he := congrArg (fun Q : Ideal (MvPowerSeries (Fin n) ℂ) =>
    Ideal.map (actualFormalPullback η hη hη0).toRingHom Q ⊔ genuineFormalVariables m ^ (ℓ+1))
      (actualPolynomialJetIdeal_whole_thickening K ℓ)
  simp only [Ideal.map_sup,sup_assoc,sup_eq_right.mpr hp] at he
  rw [map_whole_original_ideal_formal_pullback] at he
  exact he

/-- The actual original polynomial ideal supplies the source's true HS value at the chosen order. -/
theorem actualPolynomialJetIdeal_source_hs (K : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n K ℓ=hilbertSamuelValue (actualPolynomialJetIdeal K ℓ) ℓ := by
  rw [hilbertSamuelValue_eq_genuine_formal_extension]
  unfold genuineFormalHilbertSamuelValue
  rw [actualPolynomialJetIdeal_whole_thickening K ℓ]

/-- True source and target use the SAME internally chosen original polynomial ideal, with no HS premise. -/
theorem actualPolynomialJetIdeal_pullback_hs (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue m (Ideal.map (actualFormalPullback η hη hη0).toRingHom K) ℓ=
      hilbertSamuelValue (Ideal.map (compAlgHom η hη hη0).toRingHom (actualPolynomialJetIdeal K ℓ)) ℓ := by
  rw [hilbertSamuelValue_eq_genuine_formal_extension]
  unfold genuineFormalHilbertSamuelValue
  rw [actualPolynomialJetIdeal_pullback_thickening η hη hη0 K ℓ]

private theorem formal_comparison_from_original
    (η : ComplexModel (0+m) → ComplexModel (0+n))
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (hcomp : ∀ (J : Ideal (HolGerm (ComplexModel (0+n)))) (ℓ : ℕ),
      hilbertSamuelValue J ℓ ≤ hilbertSamuelValue (Ideal.map (compAlgHom η hη hη0).toRingHom J) ℓ)
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n K ℓ ≤
      genuineFormalHilbertSamuelValue m (Ideal.map (actualFormalPullback η hη hη0).toRingHom K) ℓ := by
  rw [actualPolynomialJetIdeal_source_hs K ℓ,actualPolynomialJetIdeal_pullback_hs]
  exact hcomp (actualPolynomialJetIdeal K ℓ) ℓ

-- Retain map and proof together while normalizing the harmless original zero-block dimension.
private def centeredComparisonProducer (m n : ℕ) :
    { f : (η : ComplexModel (0+m) → ComplexModel (0+n)) →
        (∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) →
        (η 0=0) → (MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin m) ℂ) //
      ∀ (η : ComplexModel (0+m) → ComplexModel (0+n))
        (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+m)), DifferentiableAt ℂ η z) (hη0 : η 0=0),
        (∀ (J : Ideal (HolGerm (ComplexModel (0+n)))) (ℓ : ℕ),
          hilbertSamuelValue J ℓ ≤ hilbertSamuelValue (Ideal.map (compAlgHom η hη hη0).toRingHom J) ℓ) →
        ∀ (K : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ),
          genuineFormalHilbertSamuelValue n K ℓ ≤
            genuineFormalHilbertSamuelValue m (Ideal.map (f η hη hη0).toRingHom K) ℓ } :=
  ⟨@actualFormalPullback m n,@formal_comparison_from_original m n⟩

private def normalizedComparisonProducer (m n : ℕ) :
    { f : (η : ComplexModel m → ComplexModel n) →
        (∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z) →
        (η 0=0) → (MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin m) ℂ) //
      ∀ (η : ComplexModel m → ComplexModel n)
        (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z) (hη0 : η 0=0),
        (∀ (J : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ),
          hilbertSamuelValue J ℓ ≤ hilbertSamuelValue (Ideal.map (compAlgHom η hη hη0).toRingHom J) ℓ) →
        ∀ (K : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ),
          genuineFormalHilbertSamuelValue n K ℓ ≤
            genuineFormalHilbertSamuelValue m (Ideal.map (f η hη hη0).toRingHom K) ℓ } := by
  have f := centeredComparisonProducer m n
  rw [Nat.zero_add,Nat.zero_add] at f
  exact f

/-- The genuine formal map is induced by the literal original zero-block contraction. -/
def actualFormalCoordinateSpecialization (r n : ℕ) :
    MvPowerSeries (Fin (r+n)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (r+n)) ℂ :=
  (normalizedComparisonProducer (r+n) (r+n)).val (actualBlockContraction r n 0)
    (actualBlockContraction_holomorphic r n 0) (actualBlockContraction_zero r n 0)

/-- The genuine formal map is induced by the literal original triangular substitution. -/
def actualFormalTriangularSubstitution (n : ℕ) (b : ℂ) :
    MvPowerSeries (Fin (2+n)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (2+n)) ℂ :=
  (normalizedComparisonProducer (2+n) (2+n)).val (actualTriangularDeformation n b 0)
    (Eventually.of_forall fun _ =>
      ((actualTriangularDeformation_contDiff n b 0).differentiable (by simp)).differentiableAt)
    (actualTriangularDeformation_zero n b 0)

/-- Every ACTUAL formal ideal satisfies raw first-block specialization, without a convergent-model premise. -/
theorem genuineFormalHilbertSamuelValue_coordinate_specialization (r n : ℕ)
    (K : Ideal (MvPowerSeries (Fin (r+n)) ℂ)) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue (r+n) K ℓ ≤
      genuineFormalHilbertSamuelValue (r+n)
        (Ideal.map (actualFormalCoordinateSpecialization r n).toRingHom K) ℓ := by
  exact (normalizedComparisonProducer (r+n) (r+n)).property
    (actualBlockContraction r n 0) (actualBlockContraction_holomorphic r n 0)
    (actualBlockContraction_zero r n 0) (hilbertSamuelValue_actual_coordinate_specialization r n) K ℓ

/-- Every ACTUAL formal ideal satisfies raw triangular substitution in ANY direction, before exceptional division. -/
theorem genuineFormalHilbertSamuelValue_triangular_substitution (n : ℕ) (b : ℂ)
    (K : Ideal (MvPowerSeries (Fin (2+n)) ℂ)) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue (2+n) K ℓ ≤
      genuineFormalHilbertSamuelValue (2+n)
        (Ideal.map (actualFormalTriangularSubstitution n b).toRingHom K) ℓ := by
  exact (normalizedComparisonProducer (2+n) (2+n)).property (actualTriangularDeformation n b 0)
    (Eventually.of_forall fun _ =>
      ((actualTriangularDeformation_contDiff n b 0).differentiable (by simp)).differentiableAt)
    (actualTriangularDeformation_zero n b 0) (hilbertSamuelValue_actual_triangular_substitution n b) K ℓ

end
end Hironaka.HironakaActualFormalPolynomialJetTransfer
