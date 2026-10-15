/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.HolGermMulExact
import Hironaka.Resolution.HironakaRelativeNormalGraphCentralFiniteModel

/-! Four complete mathematical proofs preceded literal polynomial functions.
Nearby ORIGINAL normal cones and a single all-q free open remain OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphCentralPolynomialModel
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalDeformationFiniteRelationsSpread HironakaRelativeNormalAnalyticCoefficients
  HironakaRelativeNormalGraphCentralFiniteModel HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance

def actualNormalMonomialFunction (d t : ℕ) (α : Fin t →₀ ℕ) : ComplexModel (d+t) → ℂ :=
  fun z => ∏ i : Fin t, z (i.natAdd d)^α i

private theorem actual_finite_product_differentiable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} (s : Finset ι) (f : ι → E → ℂ) (z : E)
    (hf : ∀ i ∈ s, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun y => ∏ i ∈ s, f i y) z := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.prod_empty] using (differentiableAt_const (1 : ℂ) :
      DifferentiableAt ℂ (fun _ : E => (1 : ℂ)) z)
  | @insert i s hi ih =>
    intro hf
    have he : (fun y => ∏ j ∈ insert i s, f j y) =
        (fun y => f i y * ∏ j ∈ s, f j y) := funext fun y => Finset.prod_insert hi
    rw [he]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem actualNormalMonomialFunction_differentiableAt (d t : ℕ) (α : Fin t →₀ ℕ)
    (z : ComplexModel (d+t)) : DifferentiableAt ℂ (actualNormalMonomialFunction d t α) z := by
  classical
  exact
    actual_finite_product_differentiable Finset.univ
      (fun i : Fin t => fun z : ComplexModel (d+t) => z (i.natAdd d)^α i) z
      (fun i _ => (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt.fun_pow (α i))

private theorem actual_mk_function_product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z)
      (((eventually_all_finset s).mpr fun i _ => hf i).mono fun _ h =>
        actual_finite_product_differentiable s f _ h) =
          ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_finsetProd]
  change (Germ.coeRingHom (𝓝 (0 : E))) (fun z => ∏ i ∈ s, f i z) =
    ∏ i ∈ s, (Germ.coeRingHom (𝓝 (0 : E))) (f i)
  rw [← map_prod]
  congr 1
  funext z
  exact (Finset.prod_apply z s f).symm

theorem actualNormalMonomialFunction_whole_germ (d t : ℕ) (α : Fin t →₀ ℕ) :
    HolGerm.mk (actualNormalMonomialFunction d t α)
      (Eventually.of_forall (actualNormalMonomialFunction_differentiableAt d t α)) =
        normalExponentMonomial d t α := by
  classical
  change HolGerm.mk (fun z : ComplexModel (d+t) => ∏ i : Fin t, z (i.natAdd d)^α i) _ = _
  have hc (i : Fin t) : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),
      DifferentiableAt ℂ (fun z : ComplexModel (d+t) => z (i.natAdd d)^α i) z :=
    Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt.fun_pow (α i)
  rw [actual_mk_function_product Finset.univ _ hc]
  unfold normalExponentMonomial
  apply Finset.prod_congr rfl
  intro i _
  rw [normalCoordinate,coordinateGerm,← HolGerm.mk_pow]

def actualNormalPolynomialFunction (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) : ComplexModel (d+t) → ℂ := by
  classical
  exact fun z => ∑ α ∈ P.support,
    actualCoefficientRepresentative (P.coeff α) (tangentProjection d t z) *
      actualNormalMonomialFunction d t α z

theorem actualCoefficientFunctionPullback_holomorphic (d t : ℕ) (a : HolGerm (ComplexModel d)) :
    HolAt (actualCoefficientRepresentative a ∘ tangentProjection d t) 0 :=
  eventually_differentiableAt_comp_clm (tangentProjection d t)
    (actualCoefficientRepresentative_holomorphic a)

theorem actualCoefficientFunctionPullback_whole_germ (d t : ℕ) (a : HolGerm (ComplexModel d)) :
    HolGerm.mk (actualCoefficientRepresentative a ∘ tangentProjection d t)
      (actualCoefficientFunctionPullback_holomorphic d t a) = tangentPullback d t a := by
  calc
    _ = tangentPullback d t (HolGerm.mk (actualCoefficientRepresentative a)
        (actualCoefficientRepresentative_holomorphic a)) := by
      rw [tangentPullback,compAlgHom_mk]
    _ = tangentPullback d t a := by
      congr 1
      apply Subtype.ext
      exact actualCoefficientRepresentative_germ a

theorem actualNormalPolynomialFunction_holomorphic (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    HolAt (actualNormalPolynomialFunction d t P) 0 := by
  classical
  exact eventually_differentiableAt_sum P.support fun α =>
    (actualCoefficientFunctionPullback_holomorphic d t (P.coeff α)).mul
      (Eventually.of_forall (actualNormalMonomialFunction_differentiableAt d t α))

theorem actualNormalPolynomialFunction_whole_germ (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    HolGerm.mk (actualNormalPolynomialFunction d t P)
      (actualNormalPolynomialFunction_holomorphic d t P) = normalPolynomialEval d t P := by
  classical
  let f := fun α : Fin t →₀ ℕ => fun z : ComplexModel (d+t) =>
    actualCoefficientRepresentative (P.coeff α) (tangentProjection d t z) *
      actualNormalMonomialFunction d t α z
  have hf (α : Fin t →₀ ℕ) : HolAt (f α) 0 :=
    (actualCoefficientFunctionPullback_holomorphic d t (P.coeff α)).mul
      (Eventually.of_forall (actualNormalMonomialFunction_differentiableAt d t α))
  change HolGerm.mk (fun z => ∑ α ∈ P.support, f α z) _ = _
  rw [HolGerm.mk_sum P.support f hf]
  calc
    _ = ∑ α ∈ P.support, normalPolynomialEval d t (MvPolynomial.monomial α (P.coeff α)) := by
      apply Finset.sum_congr rfl
      intro α _
      change HolGerm.mk ((actualCoefficientRepresentative (P.coeff α) ∘ tangentProjection d t) *
        actualNormalMonomialFunction d t α) _ = _
      rw [HolGerm.mk_mul' _ _ (actualCoefficientFunctionPullback_holomorphic d t (P.coeff α))
          (Eventually.of_forall (actualNormalMonomialFunction_differentiableAt d t α)),
        actualCoefficientFunctionPullback_whole_germ,
        actualNormalMonomialFunction_whole_germ,normalPolynomialEval_monomial]
    _ = normalPolynomialEval d t P := by
      conv_rhs => rw [P.as_sum,map_sum]

theorem actualNormalPolynomialFunction_differentiableAt (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (z : ComplexModel (d+t))
    (hcoeff : ∀ α : Fin t →₀ ℕ,
      DifferentiableAt ℂ (actualCoefficientRepresentative (P.coeff α)) (tangentProjection d t z)) :
    DifferentiableAt ℂ (actualNormalPolynomialFunction d t P) z := by
  classical
  apply DifferentiableAt.fun_sum
  intro α _
  exact ((hcoeff α).comp z (tangentProjection d t).differentiableAt).mul
    (actualNormalMonomialFunction_differentiableAt d t α z)

theorem actualNormalPolynomialFunction_specialization (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (z : ComplexModel (d+t)) :
    actualNormalPolynomialFunction d t P z =
      MvPolynomial.eval (fun i : Fin t => z (i.natAdd d))
        (actualPolynomialSpecialization P (tangentProjection d t z)) := by
  classical
  rw [actualPolynomialSpecialization,actualPolynomialRepresentative,map_sum,map_sum]
  unfold actualNormalPolynomialFunction
  apply Finset.sum_congr rfl
  intro α _
  rw [MvPolynomial.map_monomial,MvPolynomial.eval_monomial]
  change actualCoefficientRepresentative (P.coeff α) (tangentProjection d t z) *
    (∏ i : Fin t, z (i.natAdd d)^α i) =
    actualCoefficientRepresentative (P.coeff α) (tangentProjection d t z) *
      α.prod (fun i k => z (i.natAdd d)^k)
  rw [α.prod_fintype (fun i k => z (i.natAdd d)^k) (fun _ => pow_zero _)]

theorem exists_actual_original_polynomial_function_comparison_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    ∃ W : Set (ComplexModel (d+t)), IsOpen W ∧ 0 ∈ W ∧
      ∀ P ∈ actualOriginalRelationFamily d t I, ∀ z ∈ W,
        actualNormalPolynomialFunction d t P z = actualRelationFunction d t P z := by
  classical
  have he (P : ↥(actualOriginalRelationFamily d t I)) :
      actualNormalPolynomialFunction d t P.val =ᶠ[𝓝 (0 : ComplexModel (d+t))]
        actualRelationFunction d t P.val := by
    apply HolGerm.mk_eq_mk_iff.mp
    rw [actualNormalPolynomialFunction_whole_germ,actualRelationFunction_whole_germ]
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),
      ∀ P : ↥(actualOriginalRelationFamily d t I),
        actualNormalPolynomialFunction d t P.val z = actualRelationFunction d t P.val z :=
    eventually_all.mpr he
  obtain ⟨W,hWe,hW,h0W⟩ := mem_nhds_iff.mp hall
  exact ⟨W,hW,h0W,fun P hP z hz => hWe hz ⟨P,hP⟩⟩

def actualNormalPolynomialSpan (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (y : ComplexModel (d+t))
    (g : ComplexModel (d+t) → ℂ) : Prop :=
  InSpanAt (fun P : ↥(actualOriginalRelationFamily d t I) => actualNormalPolynomialFunction d t P.val) y g

private theorem actual_span_of_eventually_equal_functions {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    (f k : ι → E → ℂ) (y : E) (hfk : ∀ i, f i =ᶠ[𝓝 y] k i) (g : E → ℂ) :
    InSpanAt f y g ↔ InSpanAt k y g := by
  have hall := eventually_all.mpr hfk
  constructor
  · rintro ⟨hg,a,ha,he⟩
    refine ⟨hg,a,ha,?_⟩
    filter_upwards [he,hall] with z hz hzk
    rw [hz]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun v => a i z*v) (hzk i))
  · rintro ⟨hg,a,ha,he⟩
    refine ⟨hg,a,ha,?_⟩
    filter_upwards [he,hall] with z hz hzk
    rw [hz]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun v => a i z*v) (hzk i).symm)

theorem exists_actual_original_polynomial_span_comparison_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    ∃ W : Set (ComplexModel (d+t)), IsOpen W ∧ 0 ∈ W ∧
      ∀ y ∈ W, ∀ g, actualNormalPolynomialSpan d t I y g ↔ actualFiniteRelationSpan d t I y g := by
  obtain ⟨W,hW,h0W,heq⟩ := exists_actual_original_polynomial_function_comparison_open d t I
  refine ⟨W,hW,h0W,?_⟩
  intro y hy g
  have hWe : ∀ᶠ z in 𝓝 y, z ∈ W := hW.mem_nhds hy
  exact actual_span_of_eventually_equal_functions _ _ y
    (fun P : ↥(actualOriginalRelationFamily d t I) => hWe.mono
      (fun z hz => heq P.val P.property z hz)) g

theorem exists_original_whole_central_polynomial_model (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ V : Set (ComplexModel (d+t)), IsOpen V ∧ 0 ∈ V ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ P ∈ actualOriginalRelationFamily d t I, ∀ α : Fin t →₀ ℕ, ∀ y ∈ V,
        DifferentiableAt ℂ (actualCoefficientRepresentative (P.coeff α)) (tangentProjection d t y)) ∧
      (∀ P ∈ actualOriginalRelationFamily d t I, ∀ y ∈ V,
        HolAt (actualNormalPolynomialFunction d t P) y) ∧
      (∀ P ∈ actualOriginalRelationFamily d t I, ∃ q : ℕ, P.IsHomogeneous q ∧
        ∀ y ∈ V, (actualPolynomialSpecialization P (tangentProjection d t y)).IsHomogeneous q) ∧
      (∀ y ∈ V, IdealFGAt (actualNormalPolynomialSpan d t I) y) ∧
      (∀ y ∈ V, ∀ g, actualNormalPolynomialSpan d t I y g ↔
        (originalDeformationCentralIdeal d t I N).mem y g) ∧
      (∀ y ∈ V, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem (deformationCentralInclusion d t y) g ↔
          (originalDeformationColonIdeal d t I N).mem (deformationCentralInclusion d t y) g) ∧
      (∀ y ∈ V, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g (deformationCentralInclusion d t y) →
        ((originalDeformationIdeal d t I).mem (deformationCentralInclusion d t y)
          (fun z => g z*deformationParameter d t z^q) ↔
          (originalDeformationIdeal d t I).mem (deformationCentralInclusion d t y)
          (fun z => g z*deformationParameter d t z^N))) ∧
      ∀ y ∈ V, ∀ g,
        (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem (deformationCentralInclusion d t y) g) ↔
          (originalDeformationColonIdeal d t I N).mem (deformationCentralInclusion d t y) g := by
  classical
  obtain ⟨N,A,hA,h0A,hcent,_hhol,_hfg,hcentral,hchain,hpow,hsat⟩ :=
    exists_original_whole_central_finite_model d t I hI
  obtain ⟨W,hW,h0W,hcompare⟩ := exists_actual_original_polynomial_span_comparison_open d t I
  obtain ⟨B,hB,h0B,hcoeff⟩ := exists_common_polynomial_coefficient_open (actualOriginalRelationFamily d t I)
  let V := (A ∩ W) ∩ tangentProjection d t ⁻¹' B
  have hV : IsOpen V := (hA.inter hW).inter (hB.preimage (tangentProjection d t).continuous)
  have h0V : (0 : ComplexModel (d+t)) ∈ V :=
    ⟨⟨h0A,h0W⟩,by change tangentProjection d t 0 ∈ B; simpa only [map_zero] using h0B⟩
  have hc : ∀ P ∈ actualOriginalRelationFamily d t I, ∀ α : Fin t →₀ ℕ, ∀ y ∈ V,
      DifferentiableAt ℂ (actualCoefficientRepresentative (P.coeff α)) (tangentProjection d t y) := by
    intro P hP α y hy
    simpa only [actualPolynomialRepresentative_coeff] using hcoeff P hP α _ hy.2
  have hpoly : ∀ P ∈ actualOriginalRelationFamily d t I, ∀ y ∈ V,
      HolAt (actualNormalPolynomialFunction d t P) y := by
    intro P hP y hy
    have hVe : ∀ᶠ z in 𝓝 y, z ∈ V := hV.mem_nhds hy
    exact hVe.mono fun z hz =>
      actualNormalPolynomialFunction_differentiableAt d t P z (fun α => hc P hP α z hz)
  refine ⟨N,V,hV,h0V,hcent,hc,hpoly,?_,?_,?_,?_,?_,?_⟩
  · intro P hP
    obtain ⟨q,hq⟩ := actualOriginalHomogeneousRelations_homogeneous d t (originalCoherentOriginIdeal I) P hP
    exact ⟨q,hq,fun y _ => actualPolynomialSpecialization_homogeneous P hq (tangentProjection d t y)⟩
  · intro y hy
    exact ⟨V,hV,hy,↥(actualOriginalRelationFamily d t I),inferInstance,
      (fun P => actualNormalPolynomialFunction d t P.val),
      (fun P z hz => (hpoly P.val P.property z hz).self_of_nhds.differentiableWithinAt),
      fun _ _ _ => Iff.rfl⟩
  · intro y hy g
    exact (hcompare y hy.1.2 g).trans (hcentral y hy.1.1 g)
  · exact fun y hy => hchain y hy.1.1
  · exact fun y hy => hpow y hy.1.1
  · exact fun y hy => hsat y hy.1.1

end
end Hironaka.HironakaRelativeNormalGraphCentralPolynomialModel
