/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalFormalTaylor
import Hironaka.Resolution.HironakaActualAnalyticVertexPerturbation
import Hironaka.Resolution.HironakaActualHomogeneousCoefficientSummability
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
/-!
# Genuine multilinear analytic expansions and actual original Taylor coefficient mass

Literal finite coordinate word polynomials evaluate to the actual multilinear
diagonal. True analytic finite truncations give original whole maximal-power
remainders and identify the already constructed original Taylor polynomials
and coefficients. Their exponential ordinary coefficient-mass bound, combined
with actual degree-band summation, internally produces a positive uniform mass
radius for EVERY original holomorphic germ. No supplied coefficient/jet/radius
or desired mass certificate enters the original endpoint. Faithful evaluation
reconstruction and transformed HS tracking remain separate consumers.

Blueprint: `hironaka-actual-multilinear-taylor-coordinates-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped BigOperators Topology
namespace Hironaka.HironakaActualMultilinearTaylorCoordinates
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalTaylor
  HironakaActualMonomialDivisionBounds HironakaActualAnalyticVertexPerturbation
variable {n k : ℕ}

def coordinateWordExponent (w : Fin k → Fin n) : Fin n →₀ ℕ := ∑ j,Finsupp.single (w j) 1

private theorem coordinateWordExponent_degree (w : Fin k → Fin n) :
    (coordinateWordExponent w).degree=k := by simp [coordinateWordExponent,map_sum]

def multilinearCoordinatePolynomial
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => ComplexModel (0+n)) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ w : Fin k → Fin n, MvPolynomial.monomial (coordinateWordExponent w)
    (p (fun j => EuclideanSpace.single ((w j).natAdd 0) 1))

theorem multilinearCoordinatePolynomial_homogeneous
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => ComplexModel (0+n)) ℂ) :
    (multilinearCoordinatePolynomial p).IsHomogeneous k :=
  MvPolynomial.IsHomogeneous.sum _ _ _ fun w _ =>
    MvPolynomial.isHomogeneous_monomial _ (coordinateWordExponent_degree w)

/-- Literal support of the actual coordinate polynomial has exactly the multilinear degree. -/
theorem multilinearCoordinatePolynomial_coeff_ne_zero_degree
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => ComplexModel (0+n)) ℂ)
    (α : Fin n →₀ ℕ) (hα : MvPolynomial.coeff α (multilinearCoordinatePolynomial p)≠0) : α.degree=k := by
  by_contra hne
  exact hα ((multilinearCoordinatePolynomial_homogeneous p).coeff_eq_zero hne)

private theorem word_monomial_eval (w : Fin k → Fin n) (c : ℂ) (z : ComplexModel (0+n)) :
    MvPolynomial.eval (fun i : Fin n => z (i.natAdd 0)) (MvPolynomial.monomial (coordinateWordExponent w) c)=
      c*∏ j,z ((w j).natAdd 0) := by
  have hx (i : Fin n) : (MvPolynomial.monomial (Finsupp.single i 1) (1 : ℂ))=MvPolynomial.X i := rfl
  rw [coordinateWordExponent,MvPolynomial.monomial_sum_index]
  simp only [hx,map_mul,map_prod,MvPolynomial.eval_C,MvPolynomial.eval_X]

theorem multilinearCoordinatePolynomial_eval
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => ComplexModel (0+n)) ℂ)
    (z : ComplexModel (0+n)) :
    MvPolynomial.eval (fun i : Fin n => z (i.natAdd 0)) (multilinearCoordinatePolynomial p)=p (fun _ => z) := by
  have hz : z=∑ i : Fin n,z (i.natAdd 0) • EuclideanSpace.single (i.natAdd 0) (1 : ℂ) := by
    ext j
    obtain ⟨i,rfl⟩ : ∃ i : Fin n,i.natAdd 0=j := by
      exact ⟨⟨j.val,by have := j.isLt;omega⟩,Fin.ext (by simp)⟩
    change (EuclideanSpace.proj (i.natAdd 0) : ComplexModel (0+n) →L[ℂ] ℂ) z=
      (EuclideanSpace.proj (i.natAdd 0) : ComplexModel (0+n) →L[ℂ] ℂ)
        (∑ x : Fin n,z (x.natAdd 0) • EuclideanSpace.single (x.natAdd 0) (1 : ℂ))
    rw [map_sum]
    simp only [map_smul]
    change z (i.natAdd 0)=∑ x : Fin n,z (x.natAdd 0)*(Pi.single (x.natAdd 0) (1 : ℂ) : Fin (0+n) → ℂ) (i.natAdd 0)
    simp [Pi.single_apply]
  rw [multilinearCoordinatePolynomial,map_sum]
  simp_rw [word_monomial_eval]
  have hExp := p.map_sum (fun (_ : Fin k) (i : Fin n) => z (i.natAdd 0) • EuclideanSpace.single (i.natAdd 0) (1 : ℂ))
  have hArg : (fun (_ : Fin k) => ∑ i : Fin n,z (i.natAdd 0) • EuclideanSpace.single (i.natAdd 0) (1 : ℂ))=(fun _ => z) :=
    funext fun _ => hz.symm
  rw [hArg] at hExp
  rw [hExp]
  apply Finset.sum_congr rfl
  intro w _
  rw [p.map_smul_univ]
  simp only [smul_eq_mul,mul_comm]

def polynomialFunction (P : MvPolynomial (Fin n) ℂ) : ComplexModel (0+n) → ℂ :=
  fun z => MvPolynomial.eval (fun i : Fin n => z (i.natAdd 0)) P

private theorem polynomialFunction_holomorphic (P : MvPolynomial (Fin n) ℂ) :
    ∀ z, DifferentiableAt ℂ (polynomialFunction P) z := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro z
    have he : polynomialFunction (MvPolynomial.C c : MvPolynomial (Fin n) ℂ)=(fun _ => c) := by
      funext x
      simp [polynomialFunction]
    rw [he]
    exact differentiableAt_const c
  | add P Q hP hQ =>
    intro z
    have he : polynomialFunction (P+Q)=polynomialFunction P+polynomialFunction Q := by
      funext x
      simp [polynomialFunction]
    rw [he]
    exact (hP z).add (hQ z)
  | mul_X P i hP =>
    intro z
    have he : polynomialFunction (P*MvPolynomial.X i)=polynomialFunction P*(fun x => x (i.natAdd 0)) := by
      funext x
      simp [polynomialFunction]
    rw [he]
    exact (hP z).mul (EuclideanSpace.proj (i.natAdd 0) : ComplexModel (0+n) →L[ℂ] ℂ).differentiableAt

private theorem originalPolynomialEval_mk (P : MvPolynomial (Fin n) ℂ) :
    originalPolynomialEval n P=HolGerm.mk (polynomialFunction P) (Eventually.of_forall (polynomialFunction_holomorphic P)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [originalPolynomialEval,MvPolynomial.aeval_C]
    change HolGerm.mk (fun _ : ComplexModel (0+n) => c) (eventually_differentiableAt_const c)=_
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp [polynomialFunction]
  | add P Q hP hQ =>
    rw [map_add,hP,hQ,←HolGerm.mk_add]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp [polynomialFunction]
  | mul_X P i hP =>
    rw [map_mul,hP]
    have hX : originalPolynomialEval n (MvPolynomial.X i)=
        HolGerm.mk (fun z : ComplexModel (0+n) => z (i.natAdd 0))
          (Eventually.of_forall fun _ => (EuclideanSpace.proj (i.natAdd 0) : ComplexModel (0+n) →L[ℂ] ℂ).differentiableAt) := by
      simp only [originalPolynomialEval,MvPolynomial.aeval_X,normalCoordinate]
      rfl
    rw [hX,←HolGerm.mk_mul]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp [polynomialFunction]

def multilinearPartialPolynomial (p : FormalMultilinearSeries ℂ (ComplexModel (0+n)) ℂ) (k : ℕ) :
    MvPolynomial (Fin n) ℂ := ∑ j∈Finset.range (k+1),multilinearCoordinatePolynomial (p j)

private theorem multilinearPartialPolynomial_eval (p : FormalMultilinearSeries ℂ (ComplexModel (0+n)) ℂ)
    (k : ℕ) (z : ComplexModel (0+n)) :
    polynomialFunction (multilinearPartialPolynomial p k) z=∑ j∈Finset.range (k+1),p j (fun _ => z) := by
  simp only [polynomialFunction,multilinearPartialPolynomial,map_sum,multilinearCoordinatePolynomial_eval]


theorem originalTaylorPolynomial_eq_multilinearPartial (n k : ℕ)
    (f : ComplexModel (0+n) → ℂ) (hf : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ f z)
    (p : FormalMultilinearSeries ℂ (ComplexModel (0+n)) ℂ) (hp : HasFPowerSeriesAt f p 0) :
    originalTaylorPolynomial n k (HolGerm.mk f hf)=multilinearPartialPolynomial p k := by
  let q : FormalMultilinearSeries ℂ (ComplexModel (0+n)) ℂ := fun j => if j<k+1 then p j else 0
  have hfinite : ∀ j,k+1≤j → q j=0 := by
    intro j hj
    dsimp [q]
    rw [if_neg (by omega)]
  have hPoly : HasFiniteFPowerSeriesOnBall (polynomialFunction (multilinearPartialPolynomial p k)) q 0 (k+1) ⊤ := by
    apply HasFiniteFPowerSeriesOnBall.mk' hfinite (by simp)
    intro z _
    rw [zero_add z,multilinearPartialPolynomial_eval]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [q]
    rw [if_pos (Finset.mem_range.mp hj)]
  obtain ⟨r,hsub⟩ := hp.sub hPoly.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
  have hrem : HolGerm.mk f hf-originalPolynomialEval n (multilinearPartialPolynomial p k)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(k+1) := by
    rw [originalPolynomialEval_mk,←HolGerm.mk_sub']
    apply (HironakaHolomorphicPointJets.mem_maximalIdeal_pow_iff_iteratedFDeriv _ (k+1)).mpr
    intro j hj
    apply ContinuousMultilinearMap.ext
    intro v
    rw [hsub.iteratedFDeriv_eq_sum_of_completeSpace v]
    have hq : (p-q) j=0 := by
      change p j-q j=0
      dsimp [q]
      rw [if_pos hj,sub_self]
    simp only [hq,zero_apply,Finset.sum_const_zero]
  apply (originalTaylorPolynomial_unique n k (HolGerm.mk f hf) (multilinearPartialPolynomial p k) ?_ hrem).symm
  intro α hα
  rw [multilinearPartialPolynomial,MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply (multilinearCoordinatePolynomial_homogeneous (p j)).coeff_eq_zero
  have hj' := Finset.mem_range.mp hj
  have he : α.degree=normalExponentDegree α := by simp only [Finsupp.degree_eq_sum,normalExponentDegree]
  omega

theorem originalTaylor_coefficient_eq_multilinearCoordinatePolynomial (n : ℕ)
    (f : ComplexModel (0+n) → ℂ) (hf : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ f z)
    (p : FormalMultilinearSeries ℂ (ComplexModel (0+n)) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (originalTaylorAlgHom n (HolGerm.mk f hf))=
      MvPolynomial.coeff α (multilinearCoordinatePolynomial (p α.degree)) := by
  have he : α.degree=normalExponentDegree α := by simp only [Finsupp.degree_eq_sum,normalExponentDegree]
  rw [originalTaylorAlgHom_coefficient,
    originalTaylorCoefficientMap_eq_coefficient n α.degree (HolGerm.mk f hf) α (by omega),
    originalTaylorPolynomial_eq_multilinearPartial n α.degree f hf p hp,
    multilinearPartialPolynomial,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single α.degree]
  · intro j _ hj
    exact (multilinearCoordinatePolynomial_homogeneous (p j)).coeff_eq_zero (Ne.symm hj)
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))


private theorem monomial_finiteMass (ρ : Fin n → ℝ) (α : Fin n →₀ ℕ) (c : ℂ) :
    HasFiniteCoefficientMass ρ (MvPowerSeries.monomial α c) := by
  apply summable_of_ne_finset_zero (s := {α})
  intro β hβ
  have hne : β≠α := by simpa only [Finset.mem_singleton] using hβ
  simp [MvPowerSeries.coeff_monomial,hne]

private theorem monomial_uniform_mass (r : ℝ) (α : Fin n →₀ ℕ) (c : ℂ) :
    coefficientMass (fun _ => r) (MvPowerSeries.monomial α c)=‖c‖*r^α.degree := by
  unfold coefficientMass
  rw [tsum_eq_single α]
  · rw [MvPowerSeries.coeff_monomial_same]
    simp only [radiusMonomial,Finset.prod_pow_eq_pow_sum,Finsupp.degree_eq_sum]
  · intro β hβ
    rw [MvPowerSeries.coeff_monomial_ne hβ,norm_zero,zero_mul]

private theorem multilinearCoordinatePolynomial_coe
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => ComplexModel (0+n)) ℂ) :
    (multilinearCoordinatePolynomial p : MvPowerSeries (Fin n) ℂ)=
      ∑ w : Fin k → Fin n,MvPowerSeries.monomial (coordinateWordExponent w)
        (p (fun j => EuclideanSpace.single ((w j).natAdd 0) 1)) := by
  unfold multilinearCoordinatePolynomial
  change (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := ℂ))
    (∑ w : Fin k → Fin n,MvPolynomial.monomial (coordinateWordExponent w)
      (p (fun j => EuclideanSpace.single ((w j).natAdd 0) 1)))=_
  rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => MvPolynomial.coe_monomial _ _

theorem multilinearCoordinatePolynomial_finiteMass
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => ComplexModel (0+n)) ℂ)
    (r : ℝ) (hr : 0<r) :
    HasFiniteCoefficientMass (fun _ => r) (multilinearCoordinatePolynomial p : MvPowerSeries (Fin n) ℂ) := by
  rw [multilinearCoordinatePolynomial_coe]
  exact finiteCoefficientMass_sum Finset.univ _ (fun _ => hr) _ (fun w _ => monomial_finiteMass _ _ _)

theorem multilinearCoordinatePolynomial_mass_le
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => ComplexModel (0+n)) ℂ)
    (r : ℝ) (hr : 0<r) :
    coefficientMass (fun _ => r) (multilinearCoordinatePolynomial p : MvPowerSeries (Fin n) ℂ)≤
      (n : ℝ)^k*‖p‖*r^k := by
  rw [multilinearCoordinatePolynomial_coe]
  calc
    _ ≤ ∑ w : Fin k → Fin n,coefficientMass (fun _ => r)
        (MvPowerSeries.monomial (coordinateWordExponent w) (p (fun j => EuclideanSpace.single ((w j).natAdd 0) 1))) :=
      coefficientMass_sum_le Finset.univ _ (fun _ => hr) _ (fun w _ => monomial_finiteMass _ _ _)
    _ = ∑ w : Fin k → Fin n,‖p (fun j => EuclideanSpace.single ((w j).natAdd 0) 1)‖*r^k := by
      apply Finset.sum_congr rfl
      intro w _
      rw [monomial_uniform_mass,coordinateWordExponent_degree]
    _ ≤ ∑ _w : Fin k → Fin n,‖p‖*r^k := by
      apply Finset.sum_le_sum
      intro w _
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_of_lt hr) _)
      simpa only [PiLp.norm_single,norm_one,Finset.prod_const_one,mul_one] using
        p.le_opNorm (fun j => EuclideanSpace.single ((w j).natAdd 0) 1)
    _ = _ := by simp [nsmul_eq_mul,Nat.cast_pow,mul_assoc]


/-- Actual original holomorphy internally PRODUCES positive-radius Taylor coefficient mass. -/
theorem exists_originalTaylor_finiteMass (n : ℕ) (g : HolGerm (ComplexModel (0+n))) :
    ∃ r : ℝ,0<r ∧ HasFiniteCoefficientMass (fun _ : Fin n => r) (originalTaylorAlgHom n g) := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    have hanalytic : AnalyticAt ℂ f 0 := by
      obtain ⟨U,hUf,hU,h0⟩ := eventually_nhds_iff.mp hf
      exact HolomorphicAnalytic.analyticAt_of_differentiableOn hU
        (fun z hz => (hUf z hz).differentiableWithinAt) h0
    obtain ⟨p,hp⟩ := hanalytic
    obtain ⟨r,hr,hall⟩ := HironakaActualHomogeneousCoefficientSummability.exists_uniform_radius_of_multilinear_bands
      (n := n) p hp.radius_pos (fun j => multilinearCoordinatePolynomial (p j))
      (fun s hs j => multilinearCoordinatePolynomial_mass_le (p j) s hs)
    exact ⟨r,hr,hall _ (fun α => originalTaylor_coefficient_eq_multilinearCoordinatePolynomial n f hf p hp α)⟩

end
end Hironaka.HironakaActualMultilinearTaylorCoordinates
