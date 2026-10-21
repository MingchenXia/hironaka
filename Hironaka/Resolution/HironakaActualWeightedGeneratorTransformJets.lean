/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalAxisDehomogenization
import Hironaka.Resolution.HironakaActualStandardNormalIndependence
import Hironaka.Resolution.HironakaActualReducedCentreBennett
/-!
# Whole exceptional jets of genuine weighted analytic generator transforms

The literal normal Taylor band of an actual power member has the genuine
higher normal-power remainder. Actual homogeneous blowup factorization and
analytic-domain cancellation identify every exceptional jet of its weighted
quotient with a finite sum of the original dehomogenized normal components.

For prescribed actual analytic vertex data the same source generators give
genuine quotients generating the whole analytic normalized-member ideal.
Every exceptional jet image of that whole ideal is exactly the span of the
literal finite weighted jets. The original-only endpoint fixes one actual
constant-HS centre flattening, origin ideal and coefficient family before
all normal charts and all jet orders. No persistent-HS tracking, transformed
coefficient cosupport, strict decrease or terminal phase is asserted.
-/

set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWeightedGeneratorTransformJets
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualNormalHomogeneousComponents HironakaActualNormalQuotientExceptionalRestriction
  HironakaActualNormalAxisDehomogenization HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticFormalNormalPowers
  HironakaHolomorphicJetMonomialSpan HironakaActualAnalyticVertexCoefficientData
  HironakaActualReducedCentreBennett HironakaActualAnalyticStrictGenerators
  HironakaActualFormalFamilyStrictGenerators HironakaActualFormalStrictGenerators
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalInitialDiagram
  HironakaActualReducedBasisDivision HironakaActualFormalCoordinatePowerDivision

theorem actualNormalTaylorPolynomial_succ (d t q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    actualNormalTaylorPolynomial d t (q+1) g =
      actualNormalTaylorPolynomial d t q g + actualNormalHomogeneousPolynomial d t q g := by
  apply MvPolynomial.ext
  intro γ
  rw [MvPolynomial.coeff_add,actualNormalHomogeneousPolynomial_coefficient]
  by_cases hlo : normalExponentDegree γ < q
  · rw [actualNormalTaylorPolynomial_coefficient_eq_germ d t (q+1) g γ (by omega),
      actualNormalTaylorPolynomial_coefficient_eq_germ d t q g γ hlo,
      if_neg (Nat.ne_of_lt hlo),add_zero]
  · by_cases he : normalExponentDegree γ=q
    · rw [actualNormalTaylorPolynomial_coefficient_eq_germ d t (q+1) g γ (by omega),
        actualNormalTaylorPolynomial_coefficient_high d t q g γ (by omega),if_pos he,zero_add]
    · rw [actualNormalTaylorPolynomial_coefficient_high d t (q+1) g γ (by omega),
        actualNormalTaylorPolynomial_coefficient_high d t q g γ (by omega),if_neg he,zero_add]

private theorem normalTaylorPolynomial_zero_of_mem (d t m : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t^m) :
    actualNormalTaylorPolynomial d t m g=0 := by
  apply MvPolynomial.ext
  intro γ
  rw [MvPolynomial.coeff_zero]
  by_cases hγ : normalExponentDegree γ < m
  · rw [actualNormalTaylorPolynomial_coefficient_eq_germ d t m g γ hγ]
    exact (mem_normalIdeal_pow_iff_actual_relative_coefficients_zero d t m g).mp hg γ hγ
  · exact actualNormalTaylorPolynomial_coefficient_high d t m g γ (by omega)

def normalBandPolynomial (d t m q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  ∑ r ∈ Finset.range q, actualNormalHomogeneousPolynomial d t (m+r) g

theorem normalBandPolynomial_eq_Taylor (d t m q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t^m) :
    normalBandPolynomial d t m q g=actualNormalTaylorPolynomial d t (m+q) g := by
  induction q with
  | zero =>
    simpa only [normalBandPolynomial,Finset.range_zero,Finset.sum_empty,Nat.add_zero] using
      (normalTaylorPolynomial_zero_of_mem d t m g hg).symm
  | succ q ih =>
    calc
      normalBandPolynomial d t m (q+1) g = normalBandPolynomial d t m q g +
          actualNormalHomogeneousPolynomial d t (m+q) g := Finset.sum_range_succ _ q
      _ = actualNormalTaylorPolynomial d t (m+q) g +
          actualNormalHomogeneousPolynomial d t (m+q) g := congrArg (fun P => P+_) ih
      _ = actualNormalTaylorPolynomial d t ((m+q)+1) g :=
        (actualNormalTaylorPolynomial_succ d t (m+q) g).symm
      _ = actualNormalTaylorPolynomial d t (m+(q+1)) g := by rw [Nat.add_assoc]

theorem normalBand_remainder (d t m q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t^m) :
    g-normalPolynomialEval d t (normalBandPolynomial d t m q g) ∈ normalIdeal d t^(m+q) := by
  rw [normalBandPolynomial_eq_Taylor d t m q g hg]
  exact actualNormalTaylorPolynomial_remainder d t (m+q) g


def weightedTransformJet (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (m q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) : HolGerm (ComplexModel (d+t)) :=
  ∑ r ∈ Finset.range q, (coordinateGerm (j.natAdd d))^r *
    actualDehomogenizedNormalPolynomialEval d t j b (actualNormalHomogeneousPolynomial d t (m+r) g)

theorem blowup_normalBand_factorization (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (m q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b
      (normalPolynomialEval d t (normalBandPolynomial d t m q g)) =
      (coordinateGerm (j.natAdd d))^m * weightedTransformJet d t j b m q g := by
  rw [normalBandPolynomial,map_sum,map_sum,weightedTransformJet,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [actualAnalyticBlowupPullback_normalPolynomial_homogeneous d t j b
    (actualNormalHomogeneousPolynomial d t (m+r) g) (m+r)
    (actualNormalHomogeneousPolynomial_isHomogeneous d t (m+r) g)]
  change (coordinateGerm (j.natAdd d))^(m+r) *
    actualDehomogenizedNormalPolynomialEval d t j b (actualNormalHomogeneousPolynomial d t (m+r) g) = _
  rw [pow_add,mul_assoc]

theorem actual_weighted_quotient_jet_remainder (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (m q : ℕ) (g H : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t^m)
    (hH : (coordinateGerm (j.natAdd d))^m*H =
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b g) :
    H-weightedTransformJet d t j b m q g ∈ Ideal.span {(coordinateGerm (j.natAdd d))^q} := by
  let B := actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b
  have hr := normalBand_remainder d t m q g hg
  rw [← actualAnalyticCoordinateIdeal_normal d t] at hr
  have hm := Ideal.mem_map_of_mem B.toRingHom hr
  rw [map_actualAnalyticCoordinateIdeal_pow_blowup (actualTangentCentreVariables d t)
    (j.natAdd d) (show j.natAdd d ∈ actualTangentCentreVariables d t from ⟨j,rfl⟩) b (m+q)] at hm
  obtain ⟨K,hK⟩ := Ideal.mem_span_singleton'.mp hm
  have hp : (coordinateGerm (j.natAdd d))^m * (H-weightedTransformJet d t j b m q g) =
      (coordinateGerm (j.natAdd d))^m * ((coordinateGerm (j.natAdd d))^q*K) := by
    calc
      _ = B (g-normalPolynomialEval d t (normalBandPolynomial d t m q g)) := by
        rw [map_sub,← hH,blowup_normalBand_factorization]
        ring
      _ = K*(coordinateGerm (j.natAdd d))^(m+q) := hK.symm
      _ = _ := by rw [pow_add];ring
  have he0 : (coordinateGerm (j.natAdd d) : HolGerm (ComplexModel (d+t))) ≠ 0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd d)
  have he : H-weightedTransformJet d t j b m q g = (coordinateGerm (j.natAdd d))^q*K :=
    mul_left_cancel₀ (pow_ne_zero m he0) hp
  rw [he]
  exact Ideal.mem_span_singleton'.mpr ⟨K,mul_comm K _⟩

theorem actual_weighted_quotient_jet_class (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (m q : ℕ) (g H : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t^m)
    (hH : (coordinateGerm (j.natAdd d))^m*H =
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b g) :
    Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}) H =
      Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}) (weightedTransformJet d t j b m q g) :=
  Ideal.Quotient.eq.mpr (actual_weighted_quotient_jet_remainder d t j b m q g H hg hH)


private theorem unshifted_extension_injective (n : ℕ) :
    Function.Injective (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    Function.Injective (Ideal.map f.toRingHom)
  have h : P (0+n) (HironakaActualOriginalFormalTaylor.originalTaylorAlgHom n) :=
    HironakaActualFormalIdealContraction.original_formal_ideal_extension_injective n
  have hc (m : ℕ) (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (0+n) (Nat.zero_add n) _ h

theorem exists_actual_weighted_transform_jets_of_vertex_data (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (hP : ∀ a, P.generator a ∈ normalIdeal d t^
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (j : Fin t) (b : Fin (d+t) → ℂ) :
    ∃ H : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) → HolGerm (ComplexModel (d+t)),
      (∀ a, (coordinateGerm (j.natAdd d))^
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val * H a =
        actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (P.generator a)) ∧
      actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b =
        Ideal.span (range H) ∧
      (∀ a q, Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}) (H a) =
        Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
          (weightedTransformJet d t j b
            (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) ∧
      ∀ q : ℕ,
        Ideal.map (Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}))
          (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b) =
        Ideal.span (range fun a => Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
          (weightedTransformJet d t j b
            (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) := by
  let A := actualTangentCentreVariables d t
  let e := j.natAdd d
  have he : e ∈ A := ⟨j,rfl⟩
  let K := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I
  let w (a : actualInitialVertices MonomialOrder.degLex K) :=
    Finsupp.weight (actualCoordinateWeight A) a.val
  have hPa (a : actualInitialVertices MonomialOrder.degLex K) :
      P.generator a ∈ actualAnalyticCoordinateIdeal A ^ w a := by
    rw [actualAnalyticCoordinateIdeal_normal]
    exact hP a
  have hq (a : actualInitialVertices MonomialOrder.degLex K) :=
    exists_actualAnalyticBlowup_quotient A e he b (w a) (P.generator a) (hPa a)
  choose H hH using hq
  let B : ActualMonicVertexFamily MonomialOrder.degLex K :=
    { series := fun a => actualUnshiftedTaylorAlgHom (d+t) (P.generator a)
      mem := fun a => Ideal.mem_map_of_mem _ (P.member a)
      monic := P.monic
      lower := fun a β hβ => coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _
        (P.nonzero a) β (by rwa [P.initial a]) }
  have hB (a : actualInitialVertices MonomialOrder.degLex K) :
      familyVertexSeries MonomialOrder.degLex K B a ∈ actualFormalCoordinateIdeal (d+t) A ^ w a :=
    actualTaylor_mem_coordinateCentre_pow A (w a) (P.generator a) (hPa a)
  have hf : familyNormalizedFormalVertex MonomialOrder.degLex K B A e he b hB =
      fun a => actualUnshiftedTaylorAlgHom (d+t) (H a) := by
    funext a
    exact (hH a).2.symm
  have hspanle : Ideal.span (range H) ≤ actualAnalyticNormalizedMemberIdeal I A e b := by
    apply Ideal.span_le.mpr
    rintro h ⟨a,rfl⟩
    exact Ideal.subset_span ⟨w a,P.generator a,P.member a,hPa a,(hH a).1⟩
  have hm : Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (Ideal.span (range H)) =
      actualFormalStrictTransform K A e he b := by
    rw [Ideal.map_span,← Set.range_comp]
    change Ideal.span (range (fun a => actualUnshiftedTaylorAlgHom (d+t) (H a))) = _
    rw [← hf]
    exact (actualFormalStrictTransform_eq_family_span MonomialOrder.degLex K B A e he b hB).symm
  have hmap : Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
      (actualAnalyticNormalizedMemberIdeal I A e b) = actualFormalStrictTransform K A e he b := by
    apply le_antisymm (map_actualAnalyticNormalizedMemberIdeal_le_formalStrictTransform I A e he b)
    rw [← hm]
    exact Ideal.map_mono hspanle
  have hspan : actualAnalyticNormalizedMemberIdeal I A e b=Ideal.span (range H) :=
    (unshifted_extension_injective (d+t) (hm.trans hmap.symm)).symm
  have hclass (a : actualInitialVertices MonomialOrder.degLex K) (q : ℕ) :=
    actual_weighted_quotient_jet_class d t j b (w a) q (P.generator a) (H a) (hP a) (hH a).1
  refine ⟨H,fun a => (hH a).1,hspan,hclass,?_⟩
  intro q
  rw [hspan,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact hclass a q

theorem exists_actual_weighted_vertex_transform_jets (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I),
      HironakaActualReducedFormalStandardBasis.actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a ∈
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) :
    ∃ P : ActualAnalyticVertexCoefficientData d 0 t I,
      (∀ a, P.generator a ∈ normalIdeal d t^
        Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) ∧
      ∀ (j : Fin t) (b : Fin (d+t) → ℂ),
      ∃ H : actualInitialVertices MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) → HolGerm (ComplexModel (d+t)),
        (∀ a, (coordinateGerm (j.natAdd d))^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val * H a =
          actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (P.generator a)) ∧
        actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b =
          Ideal.span (range H) ∧
        (∀ a q, Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}) (H a) =
          Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
            (weightedTransformJet d t j b
              (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) ∧
        ∀ q : ℕ,
          Ideal.map (Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}))
            (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b) =
          Ideal.span (range fun a => Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
            (weightedTransformJet d t j b
              (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) := by
  obtain ⟨P,hP⟩ := exists_actual_reduced_centre_vertex_data d t I hV
  exact ⟨P,hP,fun j b => exists_actual_weighted_transform_jets_of_vertex_data d t I P hP j b⟩


section OriginalCentre
open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaActualStandardNormalIndependence
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

theorem exists_original_hs_constant_centre_weighted_transform_jets
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
    ∃ P : ActualAnalyticVertexCoefficientData d 0 t I0,
      (∀ a, P.generator a ∈ normalIdeal d t^
        Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) ∧
      ∀ (j : Fin t) (b : Fin (d+t) → ℂ),
      ∃ H : actualInitialVertices MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) → HolGerm (ComplexModel (d+t)),
        (∀ a, (coordinateGerm (j.natAdd d))^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val * H a =
          actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (P.generator a)) ∧
        actualAnalyticNormalizedMemberIdeal I0 (actualTangentCentreVariables d t) (j.natAdd d) b =
          Ideal.span (range H) ∧
        (∀ a q, Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}) (H a) =
          Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
            (weightedTransformJet d t j b
              (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) ∧
        ∀ q : ℕ,
          Ideal.map (Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q}))
            (actualAnalyticNormalizedMemberIdeal I0 (actualTangentCentreVariables d t) (j.natAdd d) b) =
          Ideal.span (range fun a => Ideal.Quotient.mk (Ideal.span {(coordinateGerm (j.natAdd d))^q})
            (weightedTransformJet d t j b
              (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) q (P.generator a))) := by
  obtain ⟨Φ,hsrc,h0,hflat,hV⟩ :=
    exists_original_hs_constant_centre_reduced_normal_powers C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,?_⟩
  exact exists_actual_weighted_vertex_transform_jets d t _ hV

end OriginalCentre
end
end Hironaka.HironakaActualWeightedGeneratorTransformJets
