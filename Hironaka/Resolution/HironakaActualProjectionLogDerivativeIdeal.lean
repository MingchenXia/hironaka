import Hironaka.Resolution.HironakaActualExceptionalLogDerivativeIdeal
import Hironaka.Resolution.HironakaRelativeNormalIdeal

/-! Actual n-to-n+1 projection with its recentered horizontal logarithmic
coefficient, ALL original germs and WHOLE analytic image ideals.
Blueprint FIRST: hironaka-actual-projection-log-derivative-ideal.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology
namespace Hironaka.HironakaActualProjectionLogDerivativeIdeal
noncomputable section
open HolGerm HolomorphicGermCoordinateDerivation
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalTaylorCoefficients
  HironakaActualExceptionalLogDerivativeIdeal
variable {n : ℕ}

/-- Original coefficients through the ACTUAL analytic projection, with the
new horizontal coefficient at ANY recentered target point. -/
def projectionWeight (a : Fin n → HolGerm (ComplexModel n)) (c : ℂ) :
    Fin (n+1) → HolGerm (ComplexModel (n+1)) :=
  Fin.lastCases (HolGerm.constHom c+coordinateGerm (Fin.last n))
    (fun i=>tangentPullback n 1 (a i))

/-- The actual horizontal member is absent through the point exactly when
its recentering is nonzero. -/
theorem horizontal_weight_isUnit_iff (a : Fin n → HolGerm (ComplexModel n)) (c : ℂ) :
    IsUnit (projectionWeight a c (Fin.last n)) ↔ c≠0 := by
  simp [projectionWeight,HolGerm.isUnit_iff_eval_ne_zero,coordinateGerm]

private theorem projection_old_vector (i : Fin n) :
    tangentProjection n 1 (EuclideanSpace.single i.castSucc (1 : ℂ))=
      EuclideanSpace.single i 1 := by
  ext j
  simp only [tangentProjection_apply,PiLp.single_apply]
  change (if j.castAdd 1=i.castAdd 1 then (1 : ℂ) else 0)=
    if j=i then 1 else 0
  simp only [Fin.castAdd_inj]

private theorem projection_last_vector :
    tangentProjection n 1 (EuclideanSpace.single (Fin.last n) (1 : ℂ))=0 := by
  ext j
  have hne : j.castAdd 1≠Fin.last n := by
    intro h
    have hv:=congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_last] at hv
    omega
  simp only [tangentProjection_apply,PiLp.single_apply,if_neg hne,PiLp.zero_apply]

private theorem partial_projection_old (f : HolGerm (ComplexModel n)) (i : Fin n) :
    coordinatePartial i.castSucc (tangentPullback n 1 f)=
      tangentPullback n 1 (coordinatePartial i f) := by
  induction f using HolGerm.induction_on with
  | h F hF =>
    have hcomp : ∀ᶠ z in 𝓝 (0 : ComplexModel (n+1)),
        DifferentiableAt ℂ
          (fun z=>fderiv ℂ F (tangentProjection n 1 z) (EuclideanSpace.single i 1)) z :=
      holomorphic_comp (tangentProjection n 1)
        (Eventually.of_forall fun _=>(tangentProjection n 1).differentiableAt) (map_zero _)
        (eventually_holomorphic_iterDeriv hF [EuclideanSpace.single i 1])
    simp only [tangentPullback,compAlgHom_mk,coordinatePartial_mk]
    change HolGerm.mk _ _=HolGerm.mk
      (fun z=>fderiv ℂ F (tangentProjection n 1 z) (EuclideanSpace.single i 1)) hcomp
    apply HolGerm.mk_eq_mk_iff.mpr
    have ht : Tendsto (tangentProjection n 1) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using
        (tangentProjection n 1).continuous.tendsto (0 : ComplexModel (n+1))
    filter_upwards [ht.eventually hF] with z hz
    rw [fderiv_comp z hz (tangentProjection n 1).differentiableAt,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.fderiv,projection_old_vector]

private theorem partial_projection_last (f : HolGerm (ComplexModel n)) :
    coordinatePartial (Fin.last n) (tangentPullback n 1 f)=0 := by
  induction f using HolGerm.induction_on with
  | h F hF =>
    unfold tangentPullback
    rw [compAlgHom_mk,coordinatePartial_mk]
    change HolGerm.mk _ _=HolGerm.mk (fun _ : ComplexModel (n+1)=>(0 : ℂ))
      (eventually_differentiableAt_const 0)
    apply HolGerm.mk_eq_mk_iff.mpr
    have ht : Tendsto (tangentProjection n 1) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using
        (tangentProjection n 1).continuous.tendsto (0 : ComplexModel (n+1))
    filter_upwards [ht.eventually hF] with z hz
    rw [fderiv_comp z hz (tangentProjection n 1).differentiableAt,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.fderiv,projection_last_vector,map_zero]

/-- ALL original germs retain the original old logarithmic derivatives;
the new horizontal direction annihilates every original image for ANY c. -/
theorem projection_log_direction_formula (a : Fin n → HolGerm (ComplexModel n))
    (c : ℂ) (f : HolGerm (ComplexModel n)) (i : Fin (n+1)) :
    logDirection (projectionWeight a c) i (tangentPullback n 1 f)=
      Fin.lastCases 0 (fun j=>tangentPullback n 1 (logDirection a j f)) i := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [Fin.lastCases_last]
    change projectionWeight a c (Fin.last n)*
        coordinatePartial (Fin.last n) (tangentPullback n 1 f)=0
    rw [partial_projection_last,mul_zero]
  · simp only [Fin.lastCases_castSucc]
    change projectionWeight a c j.castSucc*
        coordinatePartial j.castSucc (tangentPullback n 1 f)=_
    rw [partial_projection_old]
    simp only [projectionWeight,Fin.lastCases_castSucc,logDirection,
      Derivation.smul_apply,smul_eq_mul,map_mul]

private theorem direction_mem (a : Fin n → HolGerm (ComplexModel n))
    (I : Ideal (HolGerm (ComplexModel n))) (i : Fin n) (f : HolGerm (ComplexModel n)) (hf : f∈I) :
    logDirection a i f∈logIdeal a I := by
  exact (show Ideal.span _ ≤ logIdeal a I from le_sup_right)
    (Ideal.subset_span ⟨i,f,hf,rfl⟩)

/-- Repeated private stable-ideal algebra from248; no new engine credit. -/
private theorem deriv_map_mem {R A : Type*} [CommRing R] [Algebra ℂ R] [CommRing A] [Algebra ℂ A]
    (φ : A →ₐ[ℂ] R) (D : Derivation ℂ R R) (I : Ideal A) (J : Ideal R)
    (hbase : Ideal.map φ.toRingHom I≤J)
    (hgen : ∀ f∈I,D (φ f)∈J) {g : R} (hg : g∈Ideal.map φ.toRingHom I) : D g∈J := by
  let K : Ideal R :=
    { carrier := {x | x∈J ∧ D x∈J}
      zero_mem' := ⟨J.zero_mem,by rw [map_zero];exact J.zero_mem⟩
      add_mem' := by
        intro x y hx hy
        exact ⟨J.add_mem hx.1 hy.1,by rw [map_add];exact J.add_mem hx.2 hy.2⟩
      smul_mem' := by
        intro c x hx
        refine ⟨J.mul_mem_left c hx.1,?_⟩
        rw [smul_eq_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul]
        exact J.add_mem (J.mul_mem_left c hx.2) (J.mul_mem_right _ hx.1) }
  have hIK : Ideal.map φ.toRingHom I≤K := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    exact ⟨hbase (Ideal.mem_map_of_mem φ.toRingHom hf),hgen f hf⟩
  exact (hIK hg).2

/-- WHOLE analytic image log ideals commute with the actual dimension-changing
projection with the recentered horizontal member, including ALL coefficients. -/
theorem projection_log_derivative_ideal_eq (a : Fin n → HolGerm (ComplexModel n))
    (c : ℂ) (I : Ideal (HolGerm (ComplexModel n))) :
    Ideal.map (tangentPullback n 1).toRingHom (logIdeal a I)=
      logIdeal (projectionWeight a c) (Ideal.map (tangentPullback n 1).toRingHom I) := by
  let φ:=tangentPullback n 1
  let a':=projectionWeight a c
  apply le_antisymm
  · rw [logIdeal,Ideal.map_sup]
    refine sup_le le_sup_left ?_
    rw [Ideal.map_span,Ideal.span_le]
    rintro g ⟨h,⟨i,f,hf,rfl⟩,rfl⟩
    change φ (logDirection a i f)∈logIdeal a' (Ideal.map φ.toRingHom I)
    have he : logDirection a' i.castSucc (φ f)=φ (logDirection a i f) :=
      by simpa only [Fin.lastCases_castSucc] using projection_log_direction_formula a c f i.castSucc
    rw [←he]
    exact direction_mem a' (Ideal.map φ.toRingHom I) i.castSucc (φ f)
      (Ideal.mem_map_of_mem φ.toRingHom hf)
  · rw [logIdeal]
    refine sup_le (Ideal.map_mono le_sup_left) ?_
    apply Ideal.span_le.mpr
    rintro g ⟨i,f,hf,rfl⟩
    apply deriv_map_mem φ (logDirection a' i) I (Ideal.map φ.toRingHom (logIdeal a I))
      (Ideal.map_mono le_sup_left) ?_ hf
    intro h hh
    rw [projection_log_direction_formula]
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [Fin.lastCases_last] using (Ideal.map φ.toRingHom (logIdeal a I)).zero_mem
    · simp only [Fin.lastCases_castSucc]
      change φ.toRingHom (logDirection a j h)∈Ideal.map φ.toRingHom (logIdeal a I)
      exact Ideal.mem_map_of_mem φ.toRingHom (direction_mem a I j h hh)

end
end Hironaka.HironakaActualProjectionLogDerivativeIdeal
