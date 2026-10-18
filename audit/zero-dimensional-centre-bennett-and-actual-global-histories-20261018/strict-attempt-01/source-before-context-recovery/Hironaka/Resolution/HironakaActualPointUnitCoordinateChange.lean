/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.HolGermSubExact
import Hironaka.Resolution.HironakaActualPointDehomogenizedInitial
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPointUnitCoordinateChange
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaActualPointDehomogenizedInitial HironakaHolomorphicJetMonomialSpan
variable {n : ℕ}

/-- The true rational point-chart change, defined on the original ambient space. -/
def actualPointUnitForward (e : Fin n) (b : Fin n → ℂ) : ComplexModel n → ComplexModel n :=
  fun z => (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm
    (fun i => if i=e then z e else (b i+z i)/(1+z e)-b i)

/-- The actual polynomial inverse, with the same unchanged exceptional coordinate. -/
def actualPointUnitInverse (e : Fin n) (b : Fin n → ℂ) : ComplexModel n → ComplexModel n :=
  fun w => (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm
    (fun i => if i=e then w e else (1+w e)*(b i+w i)-b i)

/-- The genuine denominator-nonzero neighbourhood, rather than a supplied domain. -/
def actualPointUnitDomain (e : Fin n) : Set (ComplexModel n) := {z | 1+z e ≠ 0}

/-- The actual nonzero point whose exceptional coordinate is one. -/
def actualPointUnitBasePoint (e : Fin n) (b : Fin n → ℂ) : ComplexModel n :=
  (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm (fun i => if i=e then 1 else b i)

theorem actualPointUnitForward_apply (e : Fin n) (b : Fin n → ℂ) (z : ComplexModel n) (i : Fin n) :
    actualPointUnitForward e b z i=if i=e then z e else (b i+z i)/(1+z e)-b i := rfl

theorem actualPointUnitInverse_apply (e : Fin n) (b : Fin n → ℂ) (z : ComplexModel n) (i : Fin n) :
    actualPointUnitInverse e b z i=if i=e then z e else (1+z e)*(b i+z i)-b i := rfl

theorem actualPointUnitBasePoint_apply (e : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    actualPointUnitBasePoint e b i=if i=e then 1 else b i := rfl

theorem actualPointUnitForward_zero (e : Fin n) (b : Fin n → ℂ) :
    actualPointUnitForward e b 0=0 := by
  ext i
  simp [actualPointUnitForward_apply]

theorem actualPointUnitInverse_zero (e : Fin n) (b : Fin n → ℂ) :
    actualPointUnitInverse e b 0=0 := by
  ext i
  simp [actualPointUnitInverse_apply]

theorem isOpen_actualPointUnitDomain (e : Fin n) : IsOpen (actualPointUnitDomain e) :=
  isOpen_ne.preimage (continuous_const.add (EuclideanSpace.proj e).continuous)

theorem zero_mem_actualPointUnitDomain (e : Fin n) : (0 : ComplexModel n) ∈ actualPointUnitDomain e := by
  simp [actualPointUnitDomain]

theorem actualPointUnitForward_mapsTo (e : Fin n) (b : Fin n → ℂ) :
    MapsTo (actualPointUnitForward e b) (actualPointUnitDomain e) (actualPointUnitDomain e) := by
  intro z hz
  simpa [actualPointUnitDomain,actualPointUnitForward_apply] using hz

theorem actualPointUnitInverse_mapsTo (e : Fin n) (b : Fin n → ℂ) :
    MapsTo (actualPointUnitInverse e b) (actualPointUnitDomain e) (actualPointUnitDomain e) := by
  intro z hz
  simpa [actualPointUnitDomain,actualPointUnitInverse_apply] using hz

theorem actualPointUnitInverse_forward (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (hz : z ∈ actualPointUnitDomain e) :
    actualPointUnitInverse e b (actualPointUnitForward e b z)=z := by
  change 1+z e ≠ 0 at hz
  ext i
  by_cases hi : i=e
  · subst i
    simp [actualPointUnitForward_apply,actualPointUnitInverse_apply]
  · simp [actualPointUnitForward_apply,actualPointUnitInverse_apply,hi]
    field_simp [hz]
    ring

theorem actualPointUnitForward_inverse (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (hz : z ∈ actualPointUnitDomain e) :
    actualPointUnitForward e b (actualPointUnitInverse e b z)=z := by
  change 1+z e ≠ 0 at hz
  ext i
  by_cases hi : i=e
  · subst i
    simp [actualPointUnitForward_apply,actualPointUnitInverse_apply]
  · simp [actualPointUnitForward_apply,actualPointUnitInverse_apply,hi]
    field_simp [hz]
    ring


/-- Actual coordinate quotients are holomorphic on their true nonzero-denominator domain. -/
theorem differentiableOn_actualPointUnitForward (e : Fin n) (b : Fin n → ℂ) :
    DifferentiableOn ℂ (actualPointUnitForward e b) (actualPointUnitDomain e) := by
  intro z hz
  change 1+z e ≠ 0 at hz
  have hp (i : Fin n) : Differentiable ℂ (fun w : ComplexModel n => w i) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiable
  have hc (i : Fin n) : DifferentiableAt ℂ
      (fun w : ComplexModel n => if i=e then w e else (b i+w i)/(1+w e)-b i) z := by
    by_cases hi : i=e
    · simpa only [if_pos hi] using (hp e).differentiableAt
    · simp only [if_neg hi]
      have hn : DifferentiableAt ℂ (fun w : ComplexModel n => b i+w i) z :=
        (differentiableAt_const (b i)).add (hp i).differentiableAt
      have hd : DifferentiableAt ℂ (fun w : ComplexModel n => 1+w e) z :=
        (differentiableAt_const 1).add (hp e).differentiableAt
      have hv : DifferentiableAt ℂ (fun w : ComplexModel n => (1+w e)⁻¹) z := hd.inv hz
      have hm : DifferentiableAt ℂ (fun w : ComplexModel n => (b i+w i)*(1+w e)⁻¹) z := hn.mul hv
      have hs : DifferentiableAt ℂ (fun w : ComplexModel n =>
          (b i+w i)*(1+w e)⁻¹-b i) z := hm.sub (differentiableAt_const (b i))
      simpa only [div_eq_mul_inv] using hs
  exact ((EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm.differentiableAt.comp z
    (differentiableAt_pi.mpr hc)).differentiableWithinAt

/-- The actual inverse is a genuine global polynomial, hence holomorphic everywhere. -/
theorem differentiable_actualPointUnitInverse (e : Fin n) (b : Fin n → ℂ) :
    Differentiable ℂ (actualPointUnitInverse e b) := by
  have hp (i : Fin n) : Differentiable ℂ (fun w : ComplexModel n => w i) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiable
  have hc (i : Fin n) : Differentiable ℂ
      (fun w : ComplexModel n => if i=e then w e else (1+w e)*(b i+w i)-b i) := by
    by_cases hi : i=e
    · simpa only [if_pos hi] using hp e
    · simp only [if_neg hi]
      exact (((differentiable_const 1).add (hp e)).mul
        ((differentiable_const (b i)).add (hp i))).sub (differentiable_const (b i))
  exact (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm.differentiable.comp
    (differentiable_pi.mpr hc)

/-- Every original local-biholomorphism field is supplied by the actual coordinate formulas. -/
def actualPointUnitLocalEquiv (e : Fin n) (b : Fin n → ℂ) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := actualPointUnitDomain e
  target := actualPointUnitDomain e
  isOpen_source := isOpen_actualPointUnitDomain e
  isOpen_target := isOpen_actualPointUnitDomain e
  center_mem_source := zero_mem_actualPointUnitDomain e
  toFun := actualPointUnitForward e b
  invFun := actualPointUnitInverse e b
  toFun_holomorphic := differentiableOn_actualPointUnitForward e b
  invFun_holomorphic := (differentiable_actualPointUnitInverse e b).differentiableOn
  mapsTo_toFun := actualPointUnitForward_mapsTo e b
  mapsTo_invFun := actualPointUnitInverse_mapsTo e b
  left_inv := actualPointUnitInverse_forward e b
  right_inv := actualPointUnitForward_inverse e b

/-- The original whole germ algebra equivalence is induced by the proved actual local coordinates. -/
def actualPointUnitGermEquiv (e : Fin n) (b : Fin n → ℂ) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  localGermAlgEquiv (actualPointUnitLocalEquiv e b) (actualPointUnitForward_zero e b)

/-- The same actual original coordinate equivalence preserves EVERY original HS value. -/
theorem hilbertSamuelValue_actualPointUnitGermEquiv (e : Fin n) (b : Fin n → ℂ)
    (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map (actualPointUnitGermEquiv e b).toRingEquiv.toRingHom I) ℓ=
      hilbertSamuelValue I ℓ :=
  hilbertSamuelValue_map_eq (actualPointUnitLocalEquiv e b) (actualPointUnitForward_zero e b) I ℓ


/-- The actual reciprocal is holomorphic near zero because its denominator equals one there. -/
private theorem actualPointUnitReciprocal_holomorphic (e : Fin n) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun w : ComplexModel n => (1+w e)⁻¹) z := by
  apply eventually_differentiableAt_inv
    (eventually_differentiableAt_add (eventually_differentiableAt_const 1)
      (Eventually.of_forall fun _ =>
        (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt))
  simp

/-- The true reciprocal germ, represented by the analytic function, not a supplied inverse. -/
def actualPointUnitReciprocal (e : Fin n) : HolGerm (ComplexModel n) :=
  HolGerm.mk (fun z : ComplexModel n => (1+z e)⁻¹) (actualPointUnitReciprocal_holomorphic e)

/-- The original denominator and the constructed reciprocal multiply to one in the entire germ ring. -/
theorem actualPointUnit_mul_reciprocal (e : Fin n) :
    (1+coordinateGerm e)*actualPointUnitReciprocal e=1 := by
  have hu : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun w : ComplexModel n => 1+w e) z :=
    eventually_differentiableAt_add (eventually_differentiableAt_const 1)
      (Eventually.of_forall fun _ =>
        (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt)
  change HolGerm.mk (fun z : ComplexModel n => 1+z e) hu *
    HolGerm.mk (fun z : ComplexModel n => (1+z e)⁻¹) (actualPointUnitReciprocal_holomorphic e)=1
  rw [← HolGerm.mk_mul,← HolGerm.mk_one,HolGerm.mk_eq_mk_iff]
  filter_upwards [(isOpen_actualPointUnitDomain e).mem_nhds (zero_mem_actualPointUnitDomain e)]
    with z hz
  exact mul_inv_cancel₀ hz

/-- The same genuine inverse identity in the opposite order. -/
theorem actualPointUnit_reciprocal_mul (e : Fin n) :
    actualPointUnitReciprocal e*(1+coordinateGerm e)=1 := by
  rw [mul_comm,actualPointUnit_mul_reciprocal]

/-- Both displayed whole original germs are units. -/
theorem isUnit_actualPointUnit (e : Fin n) : IsUnit (1+coordinateGerm e) :=
  IsUnit.of_mul_eq_one (actualPointUnitReciprocal e) (actualPointUnit_mul_reciprocal e)

theorem isUnit_actualPointUnitReciprocal (e : Fin n) : IsUnit (actualPointUnitReciprocal e) :=
  IsUnit.of_mul_eq_one (1+coordinateGerm e) (actualPointUnit_reciprocal_mul e)

private theorem homogeneous_aeval_scaled {A : Type*} [CommRing A] [Algebra ℂ A]
    (P : MvPolynomial (Fin n) ℂ) (d : ℕ) (hP : P.IsHomogeneous d)
    (x : Fin n → A) (c : A) :
    MvPolynomial.aeval (fun i => c*x i) P=c^d*MvPolynomial.aeval x P := by
  rw [← P.support_sum_monomial_coeff,map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [MvPolynomial.aeval_monomial,Finsupp.prod,mul_pow,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [← hP.degree_eq_sum_deg_support ha]
  ac_rfl

/-- Exact finite homogeneous point-chart dictionary on the actual neighbourhood. -/
theorem actualPointUnitForward_dehomogenization (e : Fin n) (b : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) (d : ℕ) (hP : P.IsHomogeneous d)
    (z : ComplexModel n) (hz : z ∈ actualPointUnitDomain e) :
    MvPolynomial.aeval (fun i => actualPointUnitForward e b z i)
        (actualPointDehomogenization e b P)=
      ((1+z e)⁻¹)^d*MvPolynomial.aeval (fun i => actualPointUnitBasePoint e b i+z i) P := by
  rw [actualPointDehomogenization,MvPolynomial.comp_aeval_apply]
  have hc : (fun i : Fin n => MvPolynomial.aeval (fun j => actualPointUnitForward e b z j)
      (if i=e then 1 else MvPolynomial.C (b i)+MvPolynomial.X i))=
      (fun i => (1+z e)⁻¹*(actualPointUnitBasePoint e b i+z i)) := by
    funext i
    by_cases hi : i=e
    · subst i
      simp only [actualPointUnitBasePoint_apply,if_true,map_one]
      exact (inv_mul_cancel₀ hz).symm
    · simp only [map_add,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
        actualPointUnitBasePoint_apply,actualPointUnitForward_apply,if_neg hi]
      simp only [Algebra.algebraMap_self_apply,div_eq_mul_inv]
      ring
  rw [hc,homogeneous_aeval_scaled P d hP]


/-- The whole original germ pullback acts by the actual F coordinates, with the true reciprocal. -/
theorem actualPointUnitGermEquiv_coordinate (e : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    actualPointUnitGermEquiv e b (coordinateGerm i)=
      if i=e then coordinateGerm e else
        ((algebraMap ℂ (HolGerm (ComplexModel n))) (b i)+coordinateGerm i)*
          actualPointUnitReciprocal e-(algebraMap ℂ (HolGerm (ComplexModel n))) (b i) := by
  have hp : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun w : ComplexModel n => w i) z :=
    Eventually.of_forall fun _ =>
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hcomp := holomorphic_comp (actualPointUnitForward e b)
    (local_toFun_holomorphic (actualPointUnitLocalEquiv e b)) (actualPointUnitForward_zero e b) hp
  change HolGerm.mk ((fun z : ComplexModel n => z i) ∘ actualPointUnitForward e b) hcomp=_
  by_cases hi : i=e
  · subst i
    simp only [if_true]
    change _=HolGerm.mk (fun z : ComplexModel n => z e) hp
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [] with z
    simp [actualPointUnitForward_apply]
  · simp only [if_neg hi]
    change _=(HolGerm.mk (fun _ : ComplexModel n => b i) (eventually_differentiableAt_const (b i))+
        HolGerm.mk (fun z : ComplexModel n => z i) hp)*
        HolGerm.mk (fun z : ComplexModel n => (1+z e)⁻¹) (actualPointUnitReciprocal_holomorphic e)-
        HolGerm.mk (fun _ : ComplexModel n => b i) (eventually_differentiableAt_const (b i))
    rw [← HolGerm.mk_add,← HolGerm.mk_mul,← HolGerm.mk_sub,HolGerm.mk_eq_mk_iff]
    filter_upwards [] with z
    simp [actualPointUnitForward_apply,hi,div_eq_mul_inv]

/-- Every finite homogeneous polynomial is transported in the ENTIRE original germ algebra.
The forward orientation is F pullback, exactly as required for the dehomogenized initial ideal. -/
theorem actualPointUnitGermEquiv_dehomogenization (e : Fin n) (b : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) (d : ℕ) (hP : P.IsHomogeneous d) :
    actualPointUnitGermEquiv e b
        (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
          (actualPointDehomogenization e b P))=
      (actualPointUnitReciprocal e)^d*
        MvPolynomial.aeval (fun i => coordinateGerm i+
          (algebraMap ℂ (HolGerm (ComplexModel n))) (actualPointUnitBasePoint e b i)) P := by
  change (actualPointUnitGermEquiv e b).toAlgHom
    (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
      (actualPointDehomogenization e b P))=_
  rw [MvPolynomial.comp_aeval_apply,actualPointDehomogenization,MvPolynomial.comp_aeval_apply]
  have hc : (fun i : Fin n =>
      MvPolynomial.aeval (fun j => actualPointUnitGermEquiv e b (coordinateGerm j))
        (if i=e then 1 else MvPolynomial.C (b i)+MvPolynomial.X i))=
      (fun i => actualPointUnitReciprocal e*(coordinateGerm i+
        (algebraMap ℂ (HolGerm (ComplexModel n))) (actualPointUnitBasePoint e b i))) := by
    funext i
    by_cases hi : i=e
    · subst i
      simp only [if_true,map_one,actualPointUnitBasePoint_apply,map_one]
      simpa only [add_comm] using (actualPointUnit_reciprocal_mul e).symm
    · simp only [map_add,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
        actualPointUnitBasePoint_apply,actualPointUnitGermEquiv_coordinate,if_neg hi]
      ring
  exact (congrArg (fun x : Fin n → HolGerm (ComplexModel n) => MvPolynomial.aeval x P) hc).trans
    (homogeneous_aeval_scaled P d hP _ _)


end
end Hironaka.HironakaActualPointUnitCoordinateChange
