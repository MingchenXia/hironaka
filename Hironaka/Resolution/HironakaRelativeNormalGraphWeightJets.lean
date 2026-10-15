/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalPolynomialJetAlgebra
import Hironaka.Resolution.HironakaRelativeNormalAnalyticGraphQuotient

/-! Actual whole graph scaling and literal multiplicative parameter/fibre jets.
Four complete mathematical proofs preceded Lean. OWN OFFLIB only.
Reverse saturated-central initial ideal and nearby whole cone/Rees/allq free OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphWeightJets
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis HironakaRelativeNormalIdealMatrices
  HironakaRelativeNormalAnalyticGraphQuotient HironakaRelativeNormalPolynomialJetAlgebra
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan

def actualGraphScaling (d t : ℕ) : ComplexModel (graphDimension d t) → ComplexModel (d+t) :=
  tangentProjection (d+t) (1+t) ∘ graphEmbedding d t

theorem actualGraphScaling_tangent (d t : ℕ) (z : ComplexModel (graphDimension d t)) (i : Fin d) :
    actualGraphScaling d t z (i.castAdd t) = z (i.castAdd (1+t)) :=
  graphEmbedding_tangent d t z i

theorem actualGraphScaling_normal (d t : ℕ) (z : ComplexModel (graphDimension d t)) (i : Fin t) :
    actualGraphScaling d t z (i.natAdd d) = graphParameter d t z * graphFiberCoordinate d t i z :=
  graphEmbedding_normal d t z i

theorem actualGraphScaling_holomorphic (d t : ℕ) : Differentiable ℂ (actualGraphScaling d t) :=
  (tangentProjection (d+t) (1+t)).differentiable.comp (graphEmbedding_holomorphic d t)

theorem actualGraphScaling_zero (d t : ℕ) : actualGraphScaling d t 0 = 0 := by
  simp only [actualGraphScaling,Function.comp_apply,graphEmbedding_zero,map_zero]

def actualGraphScalingGerm (d t : ℕ) :
    HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel (graphDimension d t)) :=
  compAlgHom (actualGraphScaling d t)
    (Eventually.of_forall fun _ => (actualGraphScaling_holomorphic d t).differentiableAt)
    (actualGraphScaling_zero d t)

theorem actualGraphScalingGerm_tangentPullback (d t : ℕ) (a : HolGerm (ComplexModel d)) :
    actualGraphScalingGerm d t (tangentPullback d t a) = tangentPullback d (1+t) a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    unfold actualGraphScalingGerm tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg f
    ext i
    exact actualGraphScaling_tangent d t z i

def actualGraphParameterIndex (t : ℕ) : Fin (1+t) := ⟨0,by omega⟩

def actualGraphFiberIndex (t : ℕ) (i : Fin t) : Fin (1+t) := ⟨1+i.val,by omega⟩

theorem actualGraphScalingGerm_normalCoordinate (d t : ℕ) (i : Fin t) :
    actualGraphScalingGerm d t (normalCoordinate d t i) =
      normalCoordinate d (1+t) (actualGraphParameterIndex t) *
        normalCoordinate d (1+t) (actualGraphFiberIndex t i) := by
  unfold actualGraphScalingGerm normalCoordinate coordinateGerm
  rw [compAlgHom_mk,← HolGerm.mk_mul,HolGerm.mk_eq_mk_iff]
  apply Eventually.of_forall
  intro z
  change actualGraphScaling d t z (i.natAdd d) =
    z ((actualGraphParameterIndex t).natAdd d) * z ((actualGraphFiberIndex t i).natAdd d)
  rw [actualGraphScaling_normal]
  change graphParameter d t z * graphFiberCoordinate d t i z =
    z ((actualGraphParameterIndex t).natAdd d) * z ((actualGraphFiberIndex t i).natAdd d)
  apply congrArg₂ (· * ·)
  · apply congrArg (fun j : Fin (graphDimension d t) => z j)
    exact Fin.ext (by simp only [actualGraphParameterIndex,Fin.val_natAdd]; omega)
  · apply congrArg (fun j : Fin (graphDimension d t) => z j)
    exact Fin.ext (by simp only [actualGraphFiberIndex,Fin.val_natAdd]; omega)

def actualGraphScalingBaseAlgHom (d t : ℕ) :
    let := tangentAlgebra d t
    let := tangentAlgebra d (1+t)
    HolGerm (ComplexModel (d+t)) →ₐ[HolGerm (ComplexModel d)]
      HolGerm (ComplexModel (graphDimension d t)) := by
  let := tangentAlgebra d t
  let := tangentAlgebra d (1+t)
  exact { (actualGraphScalingGerm d t).toRingHom with
    commutes' := actualGraphScalingGerm_tangentPullback d t }

def actualGraphPolynomialSubstitution (d t : ℕ) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)]
      MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)) :=
  MvPolynomial.aeval (fun i => MvPolynomial.X (actualGraphParameterIndex t) *
    MvPolynomial.X (actualGraphFiberIndex t i))

theorem actualGraphPolynomialSubstitution_monomial (d t : ℕ) (α : Fin t →₀ ℕ)
    (a : HolGerm (ComplexModel d)) :
    actualGraphPolynomialSubstitution d t (MvPolynomial.monomial α a) =
      MvPolynomial.C a * ((MvPolynomial.X (actualGraphParameterIndex t)) ^ normalExponentDegree α *
        ∏ i : Fin t, MvPolynomial.X (actualGraphFiberIndex t i) ^ α i) := by
  classical
  rw [actualGraphPolynomialSubstitution,MvPolynomial.aeval_monomial]
  change MvPolynomial.C a * α.prod
    (fun i k => (MvPolynomial.X (actualGraphParameterIndex t) * MvPolynomial.X (actualGraphFiberIndex t i)) ^ k) = _
  rw [α.prod_fintype _ (fun _ => pow_zero _)]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rfl

theorem actualGraphScalingGerm_polynomialEval (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualGraphScalingGerm d t (normalPolynomialEval d t P) =
      normalPolynomialEval d (1+t) (actualGraphPolynomialSubstitution d t P) := by
  let := tangentAlgebra d t
  let := tangentAlgebra d (1+t)
  have h : (actualGraphScalingBaseAlgHom d t).comp (normalPolynomialEval d t) =
      (normalPolynomialEval d (1+t)).comp (actualGraphPolynomialSubstitution d t) := by
    apply MvPolynomial.algHom_ext
    intro i
    change actualGraphScalingGerm d t ((normalPolynomialEval d t) (MvPolynomial.X i)) =
      normalPolynomialEval d (1+t) (actualGraphPolynomialSubstitution d t (MvPolynomial.X i))
    rw [normalPolynomialEval,MvPolynomial.aeval_X,actualGraphPolynomialSubstitution,MvPolynomial.aeval_X,map_mul]
    simp only [normalPolynomialEval,MvPolynomial.aeval_X]
    exact actualGraphScalingGerm_normalCoordinate d t i
  exact DFunLike.congr_fun h P

theorem actualGraphScaling_map_normalIdeal_le_square (d t : ℕ) :
    Ideal.map (actualGraphScalingGerm d t).toRingHom (normalIdeal d t) ≤ normalIdeal d (1+t) ^ 2 := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro g ⟨i,rfl⟩
  change actualGraphScalingGerm d t (normalCoordinate d t i) ∈ normalIdeal d (1+t) ^ 2
  rw [actualGraphScalingGerm_normalCoordinate,pow_two]
  exact Ideal.mul_mem_mul (Ideal.subset_span ⟨actualGraphParameterIndex t,rfl⟩)
    (Ideal.subset_span ⟨actualGraphFiberIndex t i,rfl⟩)

theorem actualGraphScaling_mem_double_normal_power (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t ^ q) :
    actualGraphScalingGerm d t g ∈ normalIdeal d (1+t) ^ (2*q) := by
  have hm := Ideal.mem_map_of_mem (actualGraphScalingGerm d t).toRingHom hg
  rw [Ideal.map_pow] at hm
  have hpow := pow_le_pow_left' (actualGraphScaling_map_normalIdeal_le_square d t) q
  have h := hpow hm
  change actualGraphScalingGerm d t g ∈ (normalIdeal d (1+t) ^ 2) ^ q at h
  rw [← pow_mul] at h
  exact h

theorem exists_actual_graph_scaled_whole_polynomial_jet (d t L : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d (1+t)
    ∃ P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)),
      g-normalPolynomialEval d t P ∈ normalIdeal d t ^ L ∧
      actualWholePolynomialJet d (1+t) L (actualGraphScalingGerm d t g) =
        Ideal.Quotient.mk (actualPolynomialNormalIdeal d (1+t) ^ L)
          (actualGraphPolynomialSubstitution d t P) := by
  classical
  let := tangentAlgebra d t
  let := tangentAlgebra d (1+t)
  let := normalExponentFintype t L
  dsimp only
  obtain ⟨a,ha⟩ := exists_normalMonomial_coefficient_representative d t L g
  let P := ∑ α : normalExponentIndex t L, MvPolynomial.monomial α.val (a α)
  have hP : g-normalPolynomialEval d t P ∈ normalIdeal d t ^ L := by
    simpa only [P,map_sum,normalPolynomialEval_monomial] using ha
  refine ⟨P,hP,?_⟩
  apply (actualPolynomialJetAlgebraEquiv d (1+t) L).injective
  change (actualPolynomialJetAlgebraEquiv d (1+t) L)
    ((actualPolynomialJetAlgebraEquiv d (1+t) L).symm (Ideal.Quotient.mk (normalIdeal d (1+t) ^ L)
      (actualGraphScalingGerm d t g))) = _
  rw [AlgEquiv.apply_symm_apply,actualPolynomialJetAlgebraEquiv_mk]
  apply Ideal.Quotient.eq.mpr
  have hs := actualGraphScaling_mem_double_normal_power d t L (g-normalPolynomialEval d t P) hP
  rw [map_sub,actualGraphScalingGerm_polynomialEval] at hs
  exact Ideal.pow_le_pow_right (by omega : L ≤ 2*L) hs

end
end Hironaka.HironakaRelativeNormalGraphWeightJets
