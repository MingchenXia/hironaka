import Hironaka.Resolution.HironakaActualCentrePrincipalPartsOrderSystem
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!
# Canonical horizontal differentiation of actual joint principal parts

The constant joint direction `(a, -T a)` keeps the original ambient point fixed.
Its actual derivation preserves the whole jointly pulled-back ideal and lowers
all displacement-power denominators. It gives canonical complex-linear
principal-parts operators with the whole tangent-germ Leibniz rule, every
truncation square and zero curvature. No pivot, splitting, or flatness
certificate is assumed. This does not identify displacement graded layers with
the normal cone of the original centre or prove general normal flatness.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaActualPrincipalPartsCompatibility
open HolGerm OkaRelationSheaf HolomorphicTaylorTail HironakaRelativeNormalTaylorCoefficients
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualCentrePrincipalParts
  HironakaActualCentrePrincipalPartsOrderSystem
noncomputable section

/-- Directional differentiation on the whole holomorphic germ ring is a derivation. -/
def actualDirectionalDerivation {n : ℕ} (v : ComplexModel n) :
    Derivation ℂ (HolGerm (ComplexModel n)) (HolGerm (ComplexModel n)) :=
  Derivation.mk' (iteratedDerivativeGerm [v]) (by
    intro g h
    induction g using HolGerm.induction_on with
    | h f hf =>
      induction h using HolGerm.induction_on with
      | h g hg =>
        simp only [smul_eq_mul, ← HolGerm.mk_mul, iteratedDerivativeGerm_mk,
          ← HolGerm.mk_add]
        apply HolGerm.mk_eq_mk_iff.mpr
        filter_upwards [hf, hg] with z hdf hdg
        simp only [iterDeriv_cons, iterDeriv_nil, dirDeriv]
        rw [fderiv_fun_mul hdf hdg]
        rfl)

/-- The actual derivative commutes with any true linear origin-preserving pullback. -/
theorem actualDirectionalDerivation_comp {m n : ℕ}
    (F : ComplexModel m →L[ℂ] ComplexModel n) (v : ComplexModel m)
    (g : HolGerm (ComplexModel n)) :
    actualDirectionalDerivation v
        (HironakaHolomorphicJetChartInvariance.compAlgHom F
          (Eventually.of_forall fun _ => F.differentiableAt) (map_zero F) g) =
      HironakaHolomorphicJetChartInvariance.compAlgHom F
        (Eventually.of_forall fun _ => F.differentiableAt) (map_zero F)
        (actualDirectionalDerivation (F v) g) := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    change iteratedDerivativeGerm [v] _ =
      HironakaHolomorphicJetChartInvariance.compAlgHom F _ _ (iteratedDerivativeGerm [F v] _)
    rw [HironakaHolomorphicJetChartInvariance.compAlgHom_mk,
      iteratedDerivativeGerm_mk, iteratedDerivativeGerm_mk,
      HironakaHolomorphicJetChartInvariance.compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    have hT : Tendsto F (𝓝 0) (𝓝 0) := by simpa using F.continuous.tendsto (0 : ComplexModel m)
    filter_upwards [hT.eventually hf] with z hz
    simp only [iterDeriv_cons, iterDeriv_nil, dirDeriv, Function.comp_apply]
    rw [fderiv_comp z hz F.differentiableAt, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.fderiv]

/-- The zero direction has zero actual derivative on every whole germ. -/
theorem actualDirectionalDerivation_zero {n : ℕ} (g : HolGerm (ComplexModel n)) :
    actualDirectionalDerivation (0 : ComplexModel n) g = 0 := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    change iteratedDerivativeGerm [0] (HolGerm.mk f hf) = 0
    rw [iteratedDerivativeGerm_mk, ← HolGerm.mk_zero]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => map_zero (fderiv ℂ f z)


/-- Genuine constant-direction mixed derivatives commute on the whole holomorphic germ ring. -/
theorem actualDirectionalDerivation_commute {n : ℕ} (a b : ComplexModel n)
    (g : HolGerm (ComplexModel n)) :
    actualDirectionalDerivation a (actualDirectionalDerivation b g) =
      actualDirectionalDerivation b (actualDirectionalDerivation a g) := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    change iteratedDerivativeGerm [a] (iteratedDerivativeGerm [b] (HolGerm.mk f hf)) =
      iteratedDerivativeGerm [b] (iteratedDerivativeGerm [a] (HolGerm.mk f hf))
    rw [iteratedDerivativeGerm_mk, iteratedDerivativeGerm_mk,
      iteratedDerivativeGerm_mk, iteratedDerivativeGerm_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    obtain ⟨U, hfU, hU, h0⟩ := eventually_nhds_iff.mp hf
    have hdiff : DifferentiableOn ℂ f U := fun z hz => (hfU z hz).differentiableWithinAt
    filter_upwards [hU.mem_nhds h0] with z hz
    have hAn := HolomorphicAnalytic.analyticAt_of_differentiableOn hU hdiff hz
    have hD := hAn.fderiv.differentiableAt
    have he (v w : ComplexModel n) :
        fderiv ℂ (fun y => fderiv ℂ f y v) z w = fderiv ℂ (fderiv ℂ f) z w v := by
      rw [fderiv_clm_apply hD (differentiableAt_const v)]
      simp
    simp only [iterDeriv_cons, iterDeriv_nil, dirDeriv]
    change fderiv ℂ (fun y => fderiv ℂ f y b) z a =
      fderiv ℂ (fun y => fderiv ℂ f y a) z b
    rw [he, he]
    exact (hAn.contDiffAt (n := 2)).isSymmSndFDerivAt (by simp) a b


/-- Every derivation lowers every whole ideal-power filtration by at most one. -/
theorem derivation_mem_ideal_pow {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (D : Derivation K R R) (N : Ideal R)
    (q : ℕ) {f : R} (hf : f ∈ N^(q+1)) : D f ∈ N^q := by
  induction q generalizing f with
  | zero => simp
  | succ q ih =>
    rw [pow_succ'] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro u hu v hv
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      apply (N^(q+1)).add_mem
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hu (ih hv)
      · exact (N^(q+1)).mul_mem_right _ hv
    · intro u v hu hv
      simpa only [map_add] using (N^(q+1)).add_mem hu hv


/-- The genuine joint tangent direction which keeps the original ambient point fixed. -/
def actualHorizontalVector (d t : ℕ) (a : ComplexModel d) : ComplexModel (d+(d+t)) :=
  tangentInclusion d (d+t) a -
    actualJointNormalInclusion d (d+t) (tangentInclusion d t a)

@[simp] theorem actualHorizontalVector_jointMap (d t : ℕ) (a : ComplexModel d) :
    actualCentreJointMap d t (actualHorizontalVector d t a) = 0 := by
  simp [actualHorizontalVector, actualCentreJointMap,
    tangentProjection_tangentInclusion]

@[simp] theorem actualHorizontalVector_tangentProjection (d t : ℕ) (a : ComplexModel d) :
    tangentProjection d (d+t) (actualHorizontalVector d t a) = a := by
  simp [actualHorizontalVector, tangentProjection_tangentInclusion]

/-- The actual horizontal derivation of the unchanged whole joint germ ring. -/
def actualHorizontalDerivative (d t : ℕ) (a : ComplexModel d) :
    Derivation ℂ (HolGerm (ComplexModel (d+(d+t)))) (HolGerm (ComplexModel (d+(d+t)))) :=
  actualDirectionalDerivation (actualHorizontalVector d t a)

/-- The horizontal derivation kills every original jointly pulled-back whole germ. -/
theorem actualHorizontalDerivative_jointPullback (d t : ℕ) (a : ComplexModel d)
    (g : HolGerm (ComplexModel (d+t))) :
    actualHorizontalDerivative d t a (actualCentreJointPullback d t g) = 0 := by
  rw [actualHorizontalDerivative, actualCentreJointPullback,
    actualDirectionalDerivation_comp, actualHorizontalVector_jointMap,
    actualDirectionalDerivation_zero, map_zero]

/-- Whole tangent coefficient germs obey the actual tangent chain rule. -/
theorem actualHorizontalDerivative_tangentPullback (d t : ℕ) (a : ComplexModel d)
    (b : HolGerm (ComplexModel d)) :
    actualHorizontalDerivative d t a (tangentPullback d (d+t) b) =
      tangentPullback d (d+t) (actualDirectionalDerivation a b) := by
  rw [actualHorizontalDerivative, tangentPullback, actualDirectionalDerivation_comp,
    actualHorizontalVector_tangentProjection]

/-- Actual generator annihilation preserves the entire original joint ideal. -/
theorem actualHorizontalDerivative_jointIdeal (d t : ℕ) (a : ComplexModel d)
    {ι : Type*} (H : ι → ComplexModel (d+t) → ℂ) (hH0 : ∀ i, HolAt (H i) 0)
    {g : HolGerm (ComplexModel (d+(d+t)))} (hg : g ∈ actualCentreJointIdeal d t H hH0) :
    actualHorizontalDerivative d t a g ∈ actualCentreJointIdeal d t H hH0 := by
  change g ∈ Ideal.span _ at hg
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    rw [actualHorizontalDerivative_jointPullback]
    exact Ideal.zero_mem _
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add f g _ _ hf hg => simpa only [map_add] using (actualCentreJointIdeal d t H hH0).add_mem hf hg
  | smul c f hf ih =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact (actualCentreJointIdeal d t H hH0).add_mem
      ((actualCentreJointIdeal d t H hH0).mul_mem_left c ih)
      ((actualCentreJointIdeal d t H hH0).mul_mem_right _ hf)

/-- The true derivative lowers the full actual principal-parts denominator. -/
theorem actualHorizontalDerivative_denominator (d t q : ℕ) (a : ComplexModel d)
    {ι : Type*} (H : ι → ComplexModel (d+t) → ℂ) (hH0 : ∀ i, HolAt (H i) 0)
    {g : HolGerm (ComplexModel (d+(d+t)))}
    (hg : g ∈ actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^(q+1)) :
    actualHorizontalDerivative d t a g ∈ actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^q := by
  obtain ⟨f, hf, h, hh, rfl⟩ := Submodule.mem_sup.mp hg
  rw [map_add]
  exact (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^q).add_mem
    (Ideal.mem_sup_left (actualHorizontalDerivative_jointIdeal d t a H hH0 hf))
    (Ideal.mem_sup_right (derivation_mem_ideal_pow (actualHorizontalDerivative d t a)
      (normalIdeal d (d+t)) q hh))

/-- The canonical complex-linear horizontal connection on whole original principal parts. -/
def actualPrincipalPartsHorizontal (d t q : ℕ) (a : ComplexModel d)
    {ι : Type*} (H : ι → ComplexModel (d+t) → ℂ) (hH0 : ∀ i, HolAt (H i) 0) :
    (HolGerm (ComplexModel (d+(d+t))) ⧸
      (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^(q+1))) →ₗ[ℂ]
    (HolGerm (ComplexModel (d+(d+t))) ⧸
      (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^q)) :=
  ((actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^(q+1)).restrictScalars ℂ).liftQ
    ((Ideal.Quotient.mkₐ ℂ (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^q)).toLinearMap.comp
      (actualHorizontalDerivative d t a).toLinearMap)
    (by
      intro g hg
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact actualHorizontalDerivative_denominator d t q a H hH0 hg)

@[simp] theorem actualPrincipalPartsHorizontal_mk (d t q : ℕ) (a : ComplexModel d)
    {ι : Type*} (H : ι → ComplexModel (d+t) → ℂ) (hH0 : ∀ i, HolAt (H i) 0)
    (g : HolGerm (ComplexModel (d+(d+t)))) :
    actualPrincipalPartsHorizontal d t q a H hH0
      (Ideal.Quotient.mk (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^(q+1)) g) =
    Ideal.Quotient.mk (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^q)
      (actualHorizontalDerivative d t a g) := rfl

/-- The genuine connection commutes with all original principal-parts truncations. -/
theorem actualPrincipalPartsHorizontal_truncation (d t q r : ℕ) (hqr : q ≤ r)
    (a : ComplexModel d) {ι : Type*} (H : ι → ComplexModel (d+t) → ℂ)
    (hH0 : ∀ i, HolAt (H i) 0) :
    letI := tangentAlgebra d (d+t)
    let J := actualCentreJointIdeal d t H hH0
    ∀ v : (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t)^(r+1))),
      actualPrincipalPartsHorizontal d t q a H hH0
        (actualPrincipalPartsTruncation d (d+t) (q+1) (r+1) J (Nat.succ_le_succ hqr) v) =
      actualPrincipalPartsTruncation d (d+t) q r J hqr
        (actualPrincipalPartsHorizontal d t r a H hH0 v) := by
  let := tangentAlgebra d (d+t)
  dsimp only
  intro v
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
  rfl

/-- The whole original tangent-germ Leibniz rule; the operator is first order over the base. -/
theorem actualPrincipalPartsHorizontal_leibniz (d t q : ℕ) (a : ComplexModel d)
    {ι : Type*} (H : ι → ComplexModel (d+t) → ℂ) (hH0 : ∀ i, HolAt (H i) 0) :
    letI := tangentAlgebra d (d+t)
    let J := actualCentreJointIdeal d t H hH0
    ∀ (b : HolGerm (ComplexModel d))
      (v : (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t)^(q+1)))),
      actualPrincipalPartsHorizontal d t q a H hH0 (b • v) =
        actualDirectionalDerivation a b •
          actualPrincipalPartsTruncation d (d+t) q (q+1) J (Nat.le_succ q) v +
        b • actualPrincipalPartsHorizontal d t q a H hH0 v := by
  let := tangentAlgebra d (d+t)
  dsimp only
  intro b v
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
  let P := actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t)^q
  change Ideal.Quotient.mk P (actualHorizontalDerivative d t a (tangentPullback d (d+t) b * g)) =
    Ideal.Quotient.mk P (tangentPullback d (d+t) (actualDirectionalDerivation a b) * g) +
    Ideal.Quotient.mk P (tangentPullback d (d+t) b * actualHorizontalDerivative d t a g)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    actualHorizontalDerivative_tangentPullback, map_add,
    mul_comm g (tangentPullback d (d+t) (actualDirectionalDerivation a b))]
  exact add_comm _ _


/-- The canonical actual horizontal principal-parts connection has zero curvature at every order. -/
theorem actualPrincipalPartsHorizontal_integrable (d t q : ℕ) (a b : ComplexModel d)
    {ι : Type*} (H : ι → ComplexModel (d+t) → ℂ) (hH0 : ∀ i, HolAt (H i) 0) :
    (actualPrincipalPartsHorizontal d t q a H hH0).comp
      (actualPrincipalPartsHorizontal d t (q+1) b H hH0) =
    (actualPrincipalPartsHorizontal d t q b H hH0).comp
      (actualPrincipalPartsHorizontal d t (q+1) a H hH0) := by
  apply LinearMap.ext
  intro v
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
  simp only [LinearMap.comp_apply, actualPrincipalPartsHorizontal_mk,
    actualHorizontalDerivative]
  rw [actualDirectionalDerivation_commute]

end
end Hironaka.HironakaActualPrincipalPartsCompatibility
