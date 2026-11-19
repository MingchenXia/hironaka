import Hironaka.Resolution.HironakaActualZeroSectionFormalBasis
import Hironaka.Resolution.HironakaActualAnalyticCanonicalVertices

/-!
# Original analytic zero-section canonical families

The input is the original analytic ideal. Its genuine entire zero-section
ideal, formal extension, actual vertex labels and canonical series are all
identified internally. There is no canonical-algorithm or transformed
presentation hypothesis. All six blueprint nodes remain source-only.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualZeroSectionCanonicalFamily

noncomputable section

open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualRelativeTaylorCoefficients
  HironakaActualTaylorCoordinateNaturality HironakaActualZeroSectionStabilization
  HironakaActualZeroSectionFormalBasis HironakaActualFormalInitialDiagram
  HironakaActualFormalVertexDivision HironakaActualReducedFormalStandardBasis
  HironakaActualWeightedVertexSmallTails HironakaActualAnalyticCanonicalVertices
  HironakaActualOriginalFormalTaylor HironakaActualFormalIdealContraction

variable {d t : ℕ}

private theorem unshifted_extension_injective (n : ℕ) :
    Function.Injective (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    Function.Injective (Ideal.map f.toRingHom)
  have hc {m : ℕ} (hm : m = n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) (original_formal_ideal_extension_injective n)

/-- Genuine whole Taylor extension reflects the unit ideal; no properness certificate is lost. -/
theorem actualTaylor_ideal_eq_top_iff (I : Ideal (HolGerm (ComplexModel d))) :
    Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I = ⊤ ↔ I = ⊤ := by
  constructor
  · intro h
    apply unshifted_extension_injective d
    rw [h, Ideal.map_top]
  · intro h
    rw [h, Ideal.map_top]

theorem actualTaylor_ideal_ne_top (I : Ideal (HolGerm (ComplexModel d))) (hI : I ≠ ⊤) :
    Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I ≠ ⊤ :=
  fun h => hI ((actualTaylor_ideal_eq_top_iff I).mp h)

/-- The exact whole diagram of the ORIGINAL analytic J, not a supplied formal model. -/
theorem actualInitialDiagram_actualZeroSectionIdeal_iff
    (I : Ideal (HolGerm (ComplexModel d))) (a : Fin d →₀ ℕ) (c : Fin t →₀ ℕ) :
    actualJoinedExponent a c ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I)) ↔
      c ≠ 0 ∨ a ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I) := by
  rw [actualTaylor_zeroSectionIdeal]
  exact mem_actualInitialDiagram_zeroSection_joined_iff _ _ _

private def originalVertexMap (I : Ideal (HolGerm (ComplexModel d))) :
    ZeroSectionVertexIndex (t := t) (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I) →
      ActualVertexIndex (d+t) (actualZeroSectionIdeal d t I)
  | .inl a => ⟨(zeroSectionLiftVertex (t := t) _ a).val, by
      change _ ∈ actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I))
      rw [actualTaylor_zeroSectionIdeal]
      exact (zeroSectionLiftVertex (t := t) _ a).property⟩
  | .inr j => ⟨(zeroSectionNormalVertex _ j.property j.val).val, by
      change _ ∈ actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I))
      rw [actualTaylor_zeroSectionIdeal]
      exact (zeroSectionNormalVertex _ j.property j.val).property⟩

private theorem originalVertexMap_val (I : Ideal (HolGerm (ComplexModel d)))
    (a : ZeroSectionVertexIndex (t := t) (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I)) :
    (originalVertexMap I a).val =
      (zeroSectionVertexEquiv (t := t) (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I) a).val := by
  cases a <;> rfl

/-- The actual original analytic zero-section has the complete produced vertex bijection. -/
def originalZeroSectionVertexEquiv (I : Ideal (HolGerm (ComplexModel d))) :
    ZeroSectionVertexIndex (t := t) (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I) ≃
      ActualVertexIndex (d+t) (actualZeroSectionIdeal d t I) :=
  Equiv.ofBijective (originalVertexMap I) ⟨by
    intro a b hab
    apply (zeroSectionVertexEquiv (t := t)
      (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I)).injective
    apply Subtype.ext
    rw [← originalVertexMap_val I a, ← originalVertexMap_val I b]
    exact congrArg Subtype.val hab, by
    intro a
    let b : actualInitialVertices MonomialOrder.degLex
        (formalZeroSectionIdeal d t (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I)) :=
      ⟨a.val, by simpa only [actualTaylor_zeroSectionIdeal] using a.property⟩
    obtain ⟨x, hx⟩ := (zeroSectionVertexEquiv (t := t)
      (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I)).surjective b
    refine ⟨x, Subtype.ext ?_⟩
    rw [originalVertexMap_val]
    exact congrArg Subtype.val hx⟩

private theorem original_lift_label (I : Ideal (HolGerm (ComplexModel d)))
    (a : ActualVertexIndex d I) :
    (originalZeroSectionVertexEquiv (t := t) I (.inl a)).val =
      actualJoinedExponent a.val (0 : Fin t →₀ ℕ) := by
  rfl

private theorem original_normal_label (I : Ideal (HolGerm (ComplexModel d)))
    (hI : Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I ≠ ⊤) (j : Fin t) :
    (originalZeroSectionVertexEquiv (t := t) I (.inr ⟨j, hI⟩)).val =
      Finsupp.single (j.natAdd d) 1 := by
  rfl

private theorem actualTaylor_lift_canonical (I : Ideal (HolGerm (ComplexModel d)))
    (B : ActualVertexIndex d I → HolGerm (ComplexModel d))
    (hB : ∀ a, actualUnshiftedTaylorAlgHom d (B a) = actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I) a)
    (a : ActualVertexIndex d I) :
    actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t (B a)) =
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I))
        (originalZeroSectionVertexEquiv I (.inl a)) := by
  have ht := congrArg (fun f : HolGerm (ComplexModel d) →ₐ[ℂ]
      MvPowerSeries (Fin (d+t)) ℂ => f (B a)) (actualUnshiftedTaylor_tangentPullback d t)
  change actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t (B a)) =
    MvPowerSeries.rename (Fin.castAdd t) (actualUnshiftedTaylorAlgHom d (B a)) at ht
  have hseries : actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I))
      (originalZeroSectionVertexEquiv I (.inl a)) =
      actualReducedVertexSeries MonomialOrder.degLex
        (formalZeroSectionIdeal d t (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I))
        (zeroSectionLiftVertex _ a) := by
    simp only [actualReducedVertexSeries, original_lift_label, actualTaylor_zeroSectionIdeal,
      zeroSectionLiftVertex]
  rw [ht, hB a, hseries]
  exact (actualReducedVertexSeries_zeroSection_lift _ a).symm

private theorem actualTaylor_normal_canonical (I : Ideal (HolGerm (ComplexModel d)))
    (hI : Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I ≠ ⊤) (j : Fin t) :
    actualUnshiftedTaylorAlgHom (d+t) (normalCoordinate d t j) =
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I))
        (originalZeroSectionVertexEquiv I (.inr ⟨j, hI⟩)) := by
  have hseries : actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I))
      (originalZeroSectionVertexEquiv I (.inr ⟨j, hI⟩)) =
      actualReducedVertexSeries MonomialOrder.degLex
        (formalZeroSectionIdeal d t (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I))
        (zeroSectionNormalVertex _ hI j) := by
    simp only [actualReducedVertexSeries, original_normal_label, actualTaylor_zeroSectionIdeal,
      zeroSectionNormalVertex]
  rw [originalTaylor_normalCoordinate, hseries]
  exact (actualReducedVertexSeries_zeroSection_normal _ hI j).symm

/-- ONLY original analytic input produces the SAME full canonical zero-section
augmentation, whole ideal generation and actual exhaustive vertex labels. -/
theorem exists_original_zeroSection_canonical_family (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) :
    ∃ B : ActualVertexIndex d I → HolGerm (ComplexModel d),
      (∀ a, B a ∈ I ∧ actualUnshiftedTaylorAlgHom d (B a) =
        actualReducedVertexSeries MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I) a) ∧
      Ideal.span (range B) = I ∧
      (∀ a, tangentPullback d t (B a) ∈ actualZeroSectionIdeal d t I ∧
        (originalZeroSectionVertexEquiv (t := t) I (.inl a)).val =
          actualJoinedExponent a.val (0 : Fin t →₀ ℕ) ∧
        actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t (B a)) =
          actualReducedVertexSeries MonomialOrder.degLex
            (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I))
            (originalZeroSectionVertexEquiv I (.inl a))) ∧
      (∀ (hI : I ≠ ⊤) (j : Fin t),
        normalCoordinate d t j ∈ actualZeroSectionIdeal d t I ∧
        (originalZeroSectionVertexEquiv (t := t) I (.inr ⟨j, actualTaylor_ideal_ne_top I hI⟩)).val =
          Finsupp.single (j.natAdd d) 1 ∧
        actualUnshiftedTaylorAlgHom (d+t) (normalCoordinate d t j) =
          actualReducedVertexSeries MonomialOrder.degLex
            (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (actualZeroSectionIdeal d t I))
            (originalZeroSectionVertexEquiv I (.inr ⟨j, actualTaylor_ideal_ne_top I hI⟩))) ∧
      Ideal.span (range (fun a => tangentPullback d t (B a)) ∪ range (normalCoordinate d t)) =
        actualZeroSectionIdeal d t I := by
  obtain ⟨B, hB, hspan⟩ := exists_actualAnalyticCanonicalVertexFamily d I
  have hcanonical : ∀ a, actualUnshiftedTaylorAlgHom d (B a) =
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom d).toRingHom I) a := fun a => (hB a).2.1
  refine ⟨B, (fun a => ⟨(hB a).1, hcanonical a⟩), hspan, ?_, ?_, ?_⟩
  · intro a
    refine ⟨Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (hB a).1),
      original_lift_label I a, actualTaylor_lift_canonical I B hcanonical a⟩
  · intro hI j
    exact ⟨Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩),
      original_normal_label I (actualTaylor_ideal_ne_top I hI) j,
      actualTaylor_normal_canonical I (actualTaylor_ideal_ne_top I hI) j⟩
  · have hbase : Ideal.span (range (fun a => tangentPullback d t (B a))) =
        Ideal.map (tangentPullback d t).toRingHom I := by
      calc
        _ = Ideal.map (tangentPullback d t).toRingHom (Ideal.span (range B)) := by
          rw [Ideal.map_span, ← Set.range_comp]
          rfl
        _ = _ := congrArg (Ideal.map (tangentPullback d t).toRingHom) hspan
    rw [Ideal.span_union, hbase]
    rfl

end

end Hironaka.HironakaActualZeroSectionCanonicalFamily
