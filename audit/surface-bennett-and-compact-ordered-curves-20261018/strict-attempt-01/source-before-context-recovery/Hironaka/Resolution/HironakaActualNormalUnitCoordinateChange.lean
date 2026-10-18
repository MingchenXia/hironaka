/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointUnitCoordinateChange
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalUnitCoordinateChange
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaActualPointUnitCoordinateChange
  HironakaActualFormalCoordinatePowerDivision
variable {n : ℕ}

/-- Genuine normal-coordinate unit change, fixing all tangent coordinates. -/
def actualNormalUnitForward (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ComplexModel n → ComplexModel n :=
  fun z => (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm
    (fun i => if i=e then z e else if i ∈ A then (b i+z i)/(1+z e)-b i else z i)

/-- Its actual polynomial inverse, also fixing the tangent coordinates. -/
def actualNormalUnitInverse (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ComplexModel n → ComplexModel n :=
  fun w => (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm
    (fun i => if i=e then w e else if i ∈ A then (1+w e)*(b i+w i)-b i else w i)

theorem actualNormalUnitForward_apply (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (i : Fin n) :
    actualNormalUnitForward A e b z i=
      if i=e then z e else if i ∈ A then (b i+z i)/(1+z e)-b i else z i := rfl

theorem actualNormalUnitInverse_apply (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (i : Fin n) :
    actualNormalUnitInverse A e b z i=
      if i=e then z e else if i ∈ A then (1+z e)*(b i+z i)-b i else z i := rfl

theorem actualNormalUnitForward_zero (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    actualNormalUnitForward A e b 0=0 := by
  ext i
  by_cases hi : i ∈ A <;> simp [actualNormalUnitForward_apply,hi]

theorem actualNormalUnitInverse_zero (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    actualNormalUnitInverse A e b 0=0 := by
  ext i
  by_cases hi : i ∈ A <;> simp [actualNormalUnitInverse_apply,hi]

theorem actualNormalUnitForward_mapsTo (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    MapsTo (actualNormalUnitForward A e b) (actualPointUnitDomain e) (actualPointUnitDomain e) := by
  intro z hz
  simpa [actualPointUnitDomain,actualNormalUnitForward_apply] using hz

theorem actualNormalUnitInverse_mapsTo (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    MapsTo (actualNormalUnitInverse A e b) (actualPointUnitDomain e) (actualPointUnitDomain e) := by
  intro z hz
  simpa [actualPointUnitDomain,actualNormalUnitInverse_apply] using hz

theorem actualNormalUnitInverse_forward (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (hz : z ∈ actualPointUnitDomain e) :
    actualNormalUnitInverse A e b (actualNormalUnitForward A e b z)=z := by
  change 1+z e ≠ 0 at hz
  ext i
  by_cases hi : i=e
  · subst i
    simp [actualNormalUnitForward_apply,actualNormalUnitInverse_apply]
  · by_cases hiA : i ∈ A
    · simp [actualNormalUnitForward_apply,actualNormalUnitInverse_apply,hi,hiA]
      field_simp [hz]
      ring
    · simp [actualNormalUnitForward_apply,actualNormalUnitInverse_apply,hi,hiA]

theorem actualNormalUnitForward_inverse (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (hz : z ∈ actualPointUnitDomain e) :
    actualNormalUnitForward A e b (actualNormalUnitInverse A e b z)=z := by
  change 1+z e ≠ 0 at hz
  ext i
  by_cases hi : i=e
  · subst i
    simp [actualNormalUnitForward_apply,actualNormalUnitInverse_apply]
  · by_cases hiA : i ∈ A
    · simp [actualNormalUnitForward_apply,actualNormalUnitInverse_apply,hi,hiA]
      field_simp [hz]
      ring
    · simp [actualNormalUnitForward_apply,actualNormalUnitInverse_apply,hi,hiA]

/-- Actual normal quotients are holomorphic on their genuine denominator open. -/
theorem differentiableOn_actualNormalUnitForward (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    DifferentiableOn ℂ (actualNormalUnitForward A e b) (actualPointUnitDomain e) := by
  intro z hz
  change 1+z e ≠ 0 at hz
  have hp (i : Fin n) : Differentiable ℂ (fun w : ComplexModel n => w i) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiable
  have hc (i : Fin n) : DifferentiableAt ℂ
      (fun w : ComplexModel n => if i=e then w e else
        if i ∈ A then (b i+w i)/(1+w e)-b i else w i) z := by
    by_cases hi : i=e
    · simpa only [if_pos hi] using (hp e).differentiableAt
    · simp only [if_neg hi]
      by_cases hiA : i ∈ A
      · simp only [if_pos hiA]
        have hn : DifferentiableAt ℂ (fun w : ComplexModel n => b i+w i) z :=
          (differentiableAt_const (b i)).add (hp i).differentiableAt
        have hd : DifferentiableAt ℂ (fun w : ComplexModel n => 1+w e) z :=
          (differentiableAt_const 1).add (hp e).differentiableAt
        have hv : DifferentiableAt ℂ (fun w : ComplexModel n => (1+w e)⁻¹) z := hd.inv hz
        have hm : DifferentiableAt ℂ (fun w : ComplexModel n => (b i+w i)*(1+w e)⁻¹) z := hn.mul hv
        have hs : DifferentiableAt ℂ (fun w : ComplexModel n =>
            (b i+w i)*(1+w e)⁻¹-b i) z := hm.sub (differentiableAt_const (b i))
        simpa only [div_eq_mul_inv] using hs
      · simpa only [if_neg hiA] using (hp i).differentiableAt
  exact ((EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm.differentiableAt.comp z
    (differentiableAt_pi.mpr hc)).differentiableWithinAt

/-- The true inverse uses only polynomial operations in the normal coordinates. -/
theorem differentiable_actualNormalUnitInverse (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    Differentiable ℂ (actualNormalUnitInverse A e b) := by
  have hp (i : Fin n) : Differentiable ℂ (fun w : ComplexModel n => w i) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiable
  have hc (i : Fin n) : Differentiable ℂ
      (fun w : ComplexModel n => if i=e then w e else
        if i ∈ A then (1+w e)*(b i+w i)-b i else w i) := by
    by_cases hi : i=e
    · simpa only [if_pos hi] using hp e
    · simp only [if_neg hi]
      by_cases hiA : i ∈ A
      · simp only [if_pos hiA]
        exact (((differentiable_const 1).add (hp e)).mul
          ((differentiable_const (b i)).add (hp i))).sub (differentiable_const (b i))
      · simpa only [if_neg hiA] using hp i
  exact (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm.differentiable.comp
    (differentiable_pi.mpr hc)

/-- Every original local-biholomorphism field is constructed by the genuine normal formulas. -/
def actualNormalUnitLocalEquiv (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := actualPointUnitDomain e
  target := actualPointUnitDomain e
  isOpen_source := isOpen_actualPointUnitDomain e
  isOpen_target := isOpen_actualPointUnitDomain e
  center_mem_source := zero_mem_actualPointUnitDomain e
  toFun := actualNormalUnitForward A e b
  invFun := actualNormalUnitInverse A e b
  toFun_holomorphic := differentiableOn_actualNormalUnitForward A e b
  invFun_holomorphic := (differentiable_actualNormalUnitInverse A e b).differentiableOn
  mapsTo_toFun := actualNormalUnitForward_mapsTo A e b
  mapsTo_invFun := actualNormalUnitInverse_mapsTo A e b
  left_inv := actualNormalUnitInverse_forward A e b
  right_inv := actualNormalUnitForward_inverse A e b

/-- The whole original germ automorphism is actual pullback by the proved F coordinates. -/
def actualNormalUnitGermEquiv (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  localGermAlgEquiv (actualNormalUnitLocalEquiv A e b) (actualNormalUnitForward_zero A e b)

theorem hilbertSamuelValue_actualNormalUnitGermEquiv (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map (actualNormalUnitGermEquiv A e b).toRingEquiv.toRingHom I) ℓ=
      hilbertSamuelValue I ℓ :=
  hilbertSamuelValue_map_eq (actualNormalUnitLocalEquiv A e b) (actualNormalUnitForward_zero A e b) I ℓ

/-- Literal entire germ formula, with every tangent coordinate fixed. -/
theorem actualNormalUnitGermEquiv_coordinate (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (i : Fin n) :
    actualNormalUnitGermEquiv A e b (coordinateGerm i)=
      if i=e then coordinateGerm e else if i ∈ A then
        ((algebraMap ℂ (HolGerm (ComplexModel n))) (b i)+coordinateGerm i)*
          actualPointUnitReciprocal e-(algebraMap ℂ (HolGerm (ComplexModel n))) (b i)
        else coordinateGerm i := by
  have hp : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun w : ComplexModel n => w i) z :=
    Eventually.of_forall fun _ =>
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hcomp := holomorphic_comp (actualNormalUnitForward A e b)
    (local_toFun_holomorphic (actualNormalUnitLocalEquiv A e b))
    (actualNormalUnitForward_zero A e b) hp
  change HolGerm.mk ((fun z : ComplexModel n => z i) ∘ actualNormalUnitForward A e b) hcomp=_
  by_cases hi : i=e
  · subst i
    simp only [if_true]
    change _=HolGerm.mk (fun z : ComplexModel n => z e) hp
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp [actualNormalUnitForward_apply]
  · simp only [if_neg hi]
    by_cases hiA : i ∈ A
    · simp only [if_pos hiA]
      obtain ⟨v,hvhol,hvrep⟩ := HolGerm.exists_eq_mk (actualPointUnitReciprocal e)
      have hvactual : ∀ᶠ z in 𝓝 (0 : ComplexModel n), v z=(1+z e)⁻¹ := by
        apply HolGerm.mk_eq_mk_iff.mp
        exact hvrep.symm
      change _=(HolGerm.mk (fun _ : ComplexModel n => b i) (eventually_differentiableAt_const (b i))+
          HolGerm.mk (fun z : ComplexModel n => z i) hp)*actualPointUnitReciprocal e-
          HolGerm.mk (fun _ : ComplexModel n => b i) (eventually_differentiableAt_const (b i))
      rw [show actualPointUnitReciprocal e=HolGerm.mk v hvhol from hvrep,
        ← HolGerm.mk_add,← HolGerm.mk_mul,← HolGerm.mk_sub,HolGerm.mk_eq_mk_iff]
      filter_upwards [hvactual] with z hvz
      simp [actualNormalUnitForward_apply,hi,hiA,hvz,div_eq_mul_inv]
    · simp only [if_neg hiA]
      change _=HolGerm.mk (fun z : ComplexModel n => z i) hp
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => by simp [actualNormalUnitForward_apply,hi,hiA]

theorem actualNormalUnitGermEquiv_tangent (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (i : Fin n) (hi : i ∉ A) :
    actualNormalUnitGermEquiv A e b (coordinateGerm i)=coordinateGerm i := by
  have hie : i ≠ e := fun h => hi (h ▸ he)
  simp [actualNormalUnitGermEquiv_coordinate,hie,hi]

/-- Ordinary finite polynomial dehomogenization; no nonzero formal-series evaluation. -/
def actualNormalDehomogenization (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => if i=e then 1 else
    if i ∈ A then MvPolynomial.C (b i)+MvPolynomial.X i else MvPolynomial.X i)

/-- The actual nonzero exceptional base point has zero tangent coordinates. -/
def actualNormalUnitBasePoint (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) : ComplexModel n :=
  (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm
    (fun i => if i=e then 1 else if i ∈ A then b i else 0)

theorem actualNormalUnitBasePoint_apply (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (i : Fin n) : actualNormalUnitBasePoint A e b i=if i=e then 1 else if i ∈ A then b i else 0 := rfl

private theorem weightedHomogeneous_aeval_scaled {R : Type*} [CommRing R] [Algebra ℂ R]
    (w : Fin n → ℕ) (P : MvPolynomial (Fin n) ℂ) (d : ℕ)
    (hP : P.IsWeightedHomogeneous w d) (x : Fin n → R) (c : R) :
    MvPolynomial.aeval (fun i => c^(w i)*x i) P=c^d*MvPolynomial.aeval x P := by
  rw [← P.support_sum_monomial_coeff,map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hw : ∑ i ∈ a.support, w i*a i=d := by
    simpa only [Finsupp.weight_apply,Finsupp.sum,smul_eq_mul,Nat.mul_comm] using
      hP (MvPolynomial.mem_support_iff.mp ha)
  simp only [MvPolynomial.aeval_monomial,Finsupp.prod,mul_pow,← pow_mul,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hw]
  ac_rfl

/-- Every genuine finite normal-weight homogeneous polynomial has the exact actual coordinate identity. -/
theorem actualNormalUnitForward_dehomogenization (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) (d : ℕ)
    (hP : P.IsWeightedHomogeneous (actualCoordinateWeight A) d)
    (z : ComplexModel n) (hz : z ∈ actualPointUnitDomain e) :
    MvPolynomial.aeval (fun i => actualNormalUnitForward A e b z i)
        (actualNormalDehomogenization A e b P)=
      ((1+z e)⁻¹)^d*MvPolynomial.aeval (fun i => actualNormalUnitBasePoint A e b i+z i) P := by
  rw [actualNormalDehomogenization,MvPolynomial.comp_aeval_apply]
  have hc : (fun i : Fin n => MvPolynomial.aeval (fun j => actualNormalUnitForward A e b z j)
      (if i=e then 1 else if i ∈ A then MvPolynomial.C (b i)+MvPolynomial.X i else MvPolynomial.X i))=
      (fun i => ((1+z e)⁻¹)^(actualCoordinateWeight A i)*(actualNormalUnitBasePoint A e b i+z i)) := by
    funext i
    by_cases hi : i=e
    · subst i
      simp only [actualNormalUnitBasePoint_apply,if_true,map_one,actualCoordinateWeight,if_pos he,pow_one]
      exact (inv_mul_cancel₀ hz).symm
    · by_cases hiA : i ∈ A
      · simp only [if_neg hi,if_pos hiA,map_add,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
          actualNormalUnitBasePoint_apply,actualNormalUnitForward_apply,actualCoordinateWeight,pow_one]
        simp only [Algebra.algebraMap_self_apply,div_eq_mul_inv]
        ring
      · simp [hi,hiA,actualNormalUnitBasePoint_apply,actualNormalUnitForward_apply,actualCoordinateWeight]
  rw [hc,weightedHomogeneous_aeval_scaled _ P d hP]

/-- The same finite weighted dictionary holds in the entire original germ algebra, with true inverse unit. -/
theorem actualNormalUnitGermEquiv_dehomogenization (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) (d : ℕ)
    (hP : P.IsWeightedHomogeneous (actualCoordinateWeight A) d) :
    actualNormalUnitGermEquiv A e b
        (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
          (actualNormalDehomogenization A e b P))=
      (actualPointUnitReciprocal e)^d*
        MvPolynomial.aeval (fun i => coordinateGerm i+
          (algebraMap ℂ (HolGerm (ComplexModel n))) (actualNormalUnitBasePoint A e b i)) P := by
  change (actualNormalUnitGermEquiv A e b).toAlgHom
    (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
      (actualNormalDehomogenization A e b P))=_
  rw [MvPolynomial.comp_aeval_apply,actualNormalDehomogenization,MvPolynomial.comp_aeval_apply]
  have hc : (fun i : Fin n =>
      MvPolynomial.aeval (fun j => actualNormalUnitGermEquiv A e b (coordinateGerm j))
        (if i=e then 1 else if i ∈ A then MvPolynomial.C (b i)+MvPolynomial.X i else MvPolynomial.X i))=
      (fun i => (actualPointUnitReciprocal e)^(actualCoordinateWeight A i)*(coordinateGerm i+
        (algebraMap ℂ (HolGerm (ComplexModel n))) (actualNormalUnitBasePoint A e b i))) := by
    funext i
    by_cases hi : i=e
    · subst i
      simp only [if_true,map_one,actualNormalUnitBasePoint_apply,actualCoordinateWeight,if_pos he,pow_one,map_one]
      simpa only [add_comm] using (actualPointUnit_reciprocal_mul e).symm
    · by_cases hiA : i ∈ A
      · simp only [if_neg hi,if_pos hiA,map_add,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
          actualNormalUnitBasePoint_apply,actualNormalUnitGermEquiv_coordinate,actualCoordinateWeight,pow_one]
        ring
      · simp [hi,hiA,actualNormalUnitBasePoint_apply,actualNormalUnitGermEquiv_coordinate,actualCoordinateWeight]
  exact (congrArg (fun x : Fin n → HolGerm (ComplexModel n) => MvPolynomial.aeval x P) hc).trans
    (weightedHomogeneous_aeval_scaled _ P d hP _ _)

end
end Hironaka.HironakaActualNormalUnitCoordinateChange
