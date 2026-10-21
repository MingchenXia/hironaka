/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOwnerAnalyticDivision
import Hironaka.Resolution.HironakaActualNormalHomogeneousComponents
import Hironaka.Resolution.HironakaActualCanonicalNormalCoefficientData

/-!
# Genuine normal-filtered analytic division for the SAME prescribed canonical family

Exact canonical Taylor images identify every prescribed analytic generator with
its genuine original canonical member. Literal actual owner quotients then
retain whole shifted ORIGINAL normal powers through the true formal recursion
and analytic/formal normal-power contraction. Actual relation errors are
corrected to whole analytic syzygies. A literal homogeneous polynomial relation
over the entire analytic tangent germ ring internally gives the next normal
order and its genuine initial-syzygy lift. Original HS-constant regular-centre
geometry chooses ONE flattening and canonical coefficient datum before all
numerators/orders and supplies the required actual generator powers internally.

No relative exceptional regularity, normalized saturation, transformed maximal-
ideal standardness or reverse current Hilbert--Samuel persistence is inferred.
Blueprint: `hironaka-actual-normal-filtered-owner-division-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualNormalFilteredOwnerDivision
noncomputable section
open HolGerm HironakaActualOriginalFormalTaylor HironakaActualOriginalReducedVertexBasis
  HironakaActualOwnerAnalyticDivision HironakaActualFormalInitialDiagram HironakaActualReducedBasisDivision
  HironakaActualFormalVertexDivision HironakaActualReducedFormalStandardBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticFormalNormalPowers
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualNormalHomogeneousComponents HironakaActualRelativeCoefficientGerms
  HironakaActualRelativeTaylorCoefficients HironakaRelativeNormalPolynomialJetAlgebra
  HironakaActualWeightedVertexHS HironakaActualCanonicalNormalCoefficientData
variable {d t n : ℕ}
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem prescribed_canonical_span (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n))
    (hG : ∀ a,actualUnshiftedTaylorAlgHom n (G a)=actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a) : Ideal.span (range G)=I := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (J : Ideal (HolGerm (ComplexModel m)))
      (B : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map f.toRingHom J) →
        HolGerm (ComplexModel m)),
      (∀ a,f (B a)=actualReducedVertexSeries MonomialOrder.degLex (Ideal.map f.toRingHom J) a) →
        Ideal.span (range B)=J
  have h : P (0+n) (originalTaylorAlgHom n) := by
    intro J B hB
    have he : B=originalReducedVertexBasis J := by
      funext a
      apply originalTaylorAlgHom_injective n
      rw [hB,originalReducedVertexBasis_taylor]
    rw [he]
    exact originalReducedVertexBasis_span J
  exact unshiftedTaylor_property n P h I G hG

/-- EVERY prescribed actual canonical analytic family retains the literal recursive owner quotients. -/
theorem exists_prescribed_canonical_owner_division (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n))
    (hG : ∀ a,actualUnshiftedTaylorAlgHom n (G a)=actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a)
    (g : HolGerm (ComplexModel n)) :
    ∃ (Q : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n))
      (s : HolGerm (ComplexModel n)),
      g=(∑ a,G a*Q a)+s ∧
      actualUnshiftedTaylorAlgHom n s=actualFormalRemainder MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) (actualUnshiftedTaylorAlgHom n g) ∧
      ∀ a,actualUnshiftedTaylorAlgHom n (Q a)=familyFormalQuotient MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)
        (actualReducedVertexFamily MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
        (actualUnshiftedTaylorAlgHom n g) a := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (J : Ideal (HolGerm (ComplexModel m)))
      (B : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map f.toRingHom J) →
        HolGerm (ComplexModel m)),
      (∀ a,f (B a)=actualReducedVertexSeries MonomialOrder.degLex (Ideal.map f.toRingHom J) a) →
      ∀ F : HolGerm (ComplexModel m),
      ∃ (Q : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map f.toRingHom J) →
          HolGerm (ComplexModel m)) (s : HolGerm (ComplexModel m)),
        F=(∑ a,B a*Q a)+s ∧
        f s=actualFormalRemainder MonomialOrder.degLex (Ideal.map f.toRingHom J) (f F) ∧
        ∀ a,f (Q a)=familyFormalQuotient MonomialOrder.degLex (Ideal.map f.toRingHom J)
          (actualReducedVertexFamily MonomialOrder.degLex (Ideal.map f.toRingHom J)) (f F) a
  have h : P (0+n) (originalTaylorAlgHom n) := by
    intro J B hB F
    have he : B=originalReducedVertexBasis J := by
      funext a
      apply originalTaylorAlgHom_injective n
      rw [hB,originalReducedVertexBasis_taylor]
    rw [he]
    obtain ⟨Q,s,hdiv,hs,hQ,_hpow⟩ := exists_original_filtered_reduced_vertex_division J F 0 (by simp)
    exact ⟨Q,s,hdiv,hs,hQ⟩
  exact unshiftedTaylor_property n P h I G hG g

/-- SAME prescribed canonical generators give actual analytic quotients in WHOLE shifted normal powers. -/
theorem exists_normal_filtered_canonical_division (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (G : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) → HolGerm (ComplexModel (d+t)))
    (hG : ∀ a,actualUnshiftedTaylorAlgHom (d+t) (G a)=actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a)
    (hpower : ∀ a,G a∈normalIdeal d t ^
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (g : HolGerm (ComplexModel (d+t))) (q : ℕ) (hg : g∈normalIdeal d t ^ q) :
    ∃ (Q : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) → HolGerm (ComplexModel (d+t)))
      (s : HolGerm (ComplexModel (d+t))),
      g=(∑ a,G a*Q a)+s ∧
      actualUnshiftedTaylorAlgHom (d+t) s=actualFormalRemainder MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) (actualUnshiftedTaylorAlgHom (d+t) g) ∧
      (∀ a,actualUnshiftedTaylorAlgHom (d+t) (Q a)=familyFormalQuotient MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)
        (actualReducedVertexFamily MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I))
        (actualUnshiftedTaylorAlgHom (d+t) g) a) ∧
      ∀ a,Q a∈normalIdeal d t ^
        (q-Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) := by
  obtain ⟨Q,s,hdiv,hs,hQ⟩ := exists_prescribed_canonical_owner_division (d+t) I G hG g
  refine ⟨Q,s,hdiv,hs,hQ,?_⟩
  intro a
  apply (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t _ (Q a)).mpr
  rw [hQ]
  apply familyFormalQuotient_mem_coordinate_power MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)
    (actualReducedVertexFamily MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I))
    (actualTangentCentreVariables d t) q (actualUnshiftedTaylorAlgHom (d+t) g) ?_
    ((mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t q g).mp hg) a
  intro b
  change actualReducedVertexSeries MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) b∈_
  rw [←hG b]
  exact (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t _ (G b)).mp (hpower b)


attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- A whole actual normal-order relation error has a genuine SAME-family analytic syzygy correction. -/
theorem exists_normal_filtered_canonical_syzygy (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (G : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) → HolGerm (ComplexModel (d+t)))
    (hG : ∀ a,actualUnshiftedTaylorAlgHom (d+t) (G a)=actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a)
    (hpower : ∀ a,G a∈normalIdeal d t ^
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (P : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) → HolGerm (ComplexModel (d+t)))
    (q : ℕ) (hP : (∑ a,G a*P a)∈normalIdeal d t ^ q) :
    ∃ C : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) → HolGerm (ComplexModel (d+t)),
      (∑ a,G a*C a)=0 ∧ ∀ a,P a-C a∈normalIdeal d t ^
        (q-Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) := by
  let E := ∑ a,G a*P a
  have hE : E∈I := by
    rw [←prescribed_canonical_span (d+t) I G hG]
    exact (Ideal.span (range G)).sum_mem (fun a _ =>
      (Ideal.span (range G)).mul_mem_right (P a) (Ideal.subset_span ⟨a,rfl⟩))
  obtain ⟨Q,s,hdiv,hs,_hQ,hpow⟩ := exists_normal_filtered_canonical_division d t I G hG hpower E q hP
  have hs0 : s=0 := by
    apply actualUnshiftedTaylorAlgHom_injective (d+t)
    rw [map_zero,hs,actualFormalRemainder_eq_zero_of_mem]
    exact Ideal.mem_map_of_mem _ hE
  rw [hs0,add_zero] at hdiv
  refine ⟨fun a => P a-Q a,?_,?_⟩
  · simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←hdiv,sub_self]
  · intro a
    simpa only [sub_sub_cancel] using hpow a

private theorem normal_homogeneous_remainder (d t q : ℕ) (g : HolGerm (ComplexModel (d+t)))
    (hg : g∈normalIdeal d t ^ q) :
    g-normalPolynomialEval d t (actualNormalHomogeneousPolynomial d t q g)∈normalIdeal d t ^(q+1) := by
  apply (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t _ _).mpr
  rw [map_sub,actualTaylor_normalHomogeneousPolynomial]
  apply (mem_actualFormalCoordinateIdeal_pow_iff (actualTangentCentreVariables d t) (q+1) _).mpr
  intro α hα
  rw [map_sub,actualWeightedComponent_coefficient]
  by_cases ha : Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) α=q
  · rw [if_pos ha,sub_self]
  · rw [if_neg ha,sub_zero]
    exact (mem_actualFormalCoordinateIdeal_pow_iff (actualTangentCentreVariables d t) q _).mp
      ((mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t q g).mp hg) α (by omega)

private theorem homogeneous_normalPolynomialEval_mem (d t q : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (hP : P.IsHomogeneous q) :
    normalPolynomialEval d t P∈normalIdeal d t ^ q := by
  apply (normalPolynomialEval_mem_power_iff d t q P).mpr
  apply (actualPolynomialNormalIdeal_power_iff_coefficients d t q P).mpr
  intro α hα
  by_contra hc
  have hd := hP hc
  change Finsupp.weight (fun _ : Fin t => (1 : ℕ)) α=q at hd
  have heq : normalExponentDegree α=q := by
    simpa only [←Finsupp.degree_eq_weight_one,Finsupp.degree_eq_sum,normalExponentDegree] using hd
  omega

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- A WHOLE homogeneous polynomial relation on genuine relative normal initial forms internally supplies its next-order analytic syzygy lift. -/
theorem exists_normal_homogeneous_initial_syzygy (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (G : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) → HolGerm (ComplexModel (d+t)))
    (hG : ∀ a,actualUnshiftedTaylorAlgHom (d+t) (G a)=actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a)
    (hpower : ∀ a,G a∈normalIdeal d t ^
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (D : ℕ) (p : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
        MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hD : ∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I),
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val≤D)
    (hp : ∀ a,(p a).IsHomogeneous
      (D-Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val))
    (hrel : (∑ a,p a*actualNormalHomogeneousPolynomial d t
      (Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) (G a))=0) :
    ∃ C : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) → HolGerm (ComplexModel (d+t)),
      (∑ a,G a*C a)=0 ∧ ∀ a,normalPolynomialEval d t (p a)-C a∈normalIdeal d t ^
        (D+1-Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) := by
  let w := fun a : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) =>
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val
  let f := fun a => actualNormalHomogeneousPolynomial d t (w a) (G a)
  have hsum : (∑ a,normalPolynomialEval d t (p a)*normalPolynomialEval d t (f a))=0 := by
    have h := congrArg (normalPolynomialEval d t) hrel
    simpa only [map_sum,map_mul,map_zero,f,w] using h
  have herr : (∑ a,normalPolynomialEval d t (p a)*(G a-normalPolynomialEval d t (f a)))∈
      normalIdeal d t ^(D+1) := by
    apply Ideal.sum_mem
    intro a _
    have hm := Ideal.mul_mem_mul (homogeneous_normalPolynomialEval_mem d t (D-w a) (p a) (hp a))
      (normal_homogeneous_remainder d t (w a) (G a) (hpower a))
    rw [←pow_add,show D-w a+(w a+1)=D+1 by have hle : w a≤D := hD a;omega] at hm
    exact hm
  have hE : (∑ a,G a*normalPolynomialEval d t (p a))∈normalIdeal d t ^(D+1) := by
    convert herr using 1
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    rw [hsum,sub_zero]
    apply Finset.sum_congr rfl
    intro a _
    ring
  exact exists_normal_filtered_canonical_syzygy d t I G hG hpower
    (fun a => normalPolynomialEval d t (p a)) (D+1) hE


section OriginalCentre
open Hironaka.HolomorphicIdealSheaves HironakaActualAnalyticVertexCoefficientData
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original regular-centre HSconstancy internally fixes ONE actual chart/canonical family and all actual normal-filtered analytic divisions. -/
theorem exists_original_hs_centre_normal_filtered_division
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y∈C,∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source⊆(chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y∈(chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y∈Φ.source →
        (y∈C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y)∈complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      let K0 := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0
      ∃ P : ActualAnalyticVertexCoefficientData d 0 t I0,
        (∀ a,actualUnshiftedTaylorAlgHom (d+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex K0 a) ∧
        (∀ a,P.generator a∈normalIdeal d t ^
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) ∧
        ∀ (g : HolGerm (ComplexModel (d+t))) (q : ℕ),g∈normalIdeal d t ^ q →
        ∃ (Q : actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t))) K0 → HolGerm (ComplexModel (d+t)))
          (s : HolGerm (ComplexModel (d+t))),
          g=(∑ a,P.generator a*Q a)+s ∧
          actualUnshiftedTaylorAlgHom (d+t) s=actualFormalRemainder MonomialOrder.degLex K0
            (actualUnshiftedTaylorAlgHom (d+t) g) ∧
          (∀ a,actualUnshiftedTaylorAlgHom (d+t) (Q a)=familyFormalQuotient MonomialOrder.degLex K0
            (actualReducedVertexFamily MonomialOrder.degLex K0) (actualUnshiftedTaylorAlgHom (d+t) g) a) ∧
          ∀ a,Q a∈normalIdeal d t ^
            (q-Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) := by
  obtain ⟨Φ,hsrc,h0,hflat,P,hPG,_hcoeff,hpower⟩ :=
    exists_original_hs_constant_centre_canonical_coefficient_data C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,P,hPG,hpower,?_⟩
  intro g q hg
  exact exists_normal_filtered_canonical_division d t _ P.generator hPG hpower g q hg

end OriginalCentre
end
end Hironaka.HironakaActualNormalFilteredOwnerDivision
