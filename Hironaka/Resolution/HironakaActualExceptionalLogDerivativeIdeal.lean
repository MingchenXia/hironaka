import Hironaka.Analytic.HolomorphicGermCoordinateDerivation
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-! WHOLE logarithmic derivative ideals through the actual recentered ordinary
exceptional chart. No ordinary hom mixed-equivalence or future packet.
Blueprint FIRST: hironaka-actual-exceptional-log-derivative-ideal.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology BigOperators
namespace Hironaka.HironakaActualExceptionalLogDerivativeIdeal
noncomputable section
open HolGerm HolomorphicGermCoordinateDerivation
  HironakaHolomorphicJetMonomialSpan HironakaActualAnalyticBlowupTaylor
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalTaylorCoefficients
variable {n : ℕ}

/-- Actual coefficient times the EXISTING native analytic coordinate derivation. -/
def logDirection (a : Fin n → HolGerm (ComplexModel n)) (i : Fin n) :
    Derivation ℂ (HolGerm (ComplexModel n)) (HolGerm (ComplexModel n)) :=
  a i • coordinatePartial i

/-- Original whole ideal plus derivatives of EVERY original ideal member. -/
def logIdeal (a : Fin n → HolGerm (ComplexModel n))
    (I : Ideal (HolGerm (ComplexModel n))) : Ideal (HolGerm (ComplexModel n)) :=
  I ⊔ Ideal.span {h | ∃ (i : Fin n) (f : HolGerm (ComplexModel n)),f∈I ∧ h=logDirection a i f}

/-- Actual source coordinate boundary mask, ordinary directions elsewhere. -/
def sourceWeight (S : Finset (Fin n)) (i : Fin n) : HolGerm (ComplexModel n) :=
  if i∈S then coordinateGerm i else 1

/-- New exceptional weight, ACTUAL recentered old j weight, all other directions. -/
def targetWeight (S : Finset (Fin n)) (e j : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    HolGerm (ComplexModel n) :=
  if i=e then coordinateGerm e else if i=j then HolGerm.constHom (b j)+coordinateGerm j
    else sourceWeight S i

private abbrev chartMap (e j : Fin n) (b : Fin n → ℂ) :=
  actualAnalyticBlowupMap ({e,j} : Set (Fin n)) e b
private abbrev chartPullback (e j : Fin n) (b : Fin n → ℂ) :=
  actualAnalyticBlowupPullback ({e,j} : Set (Fin n)) e b

private theorem chart_differential (e j : Fin n) (hij : e≠j) (b : Fin n → ℂ)
    (i : Fin n) (z : ComplexModel n) :
    fderiv ℂ (chartMap e j b) z (EuclideanSpace.single i 1)=
      if i=e then EuclideanSpace.single e 1+(b j+z j) • EuclideanSpace.single j 1
      else if i=j then z e • EuclideanSpace.single j 1 else EuclideanSpace.single i 1 := by
  have hp:=differentiable_actualAnalyticBlowupMap ({e,j} : Set (Fin n)) e b z
  ext k
  have ht : HasFDerivAt (fun w : ComplexModel n=>chartMap e j b w k)
      (if k=e then EuclideanSpace.proj (𝕜 := ℂ) e else if k=j then
        z e • EuclideanSpace.proj (𝕜 := ℂ) j+(b j+z j) • EuclideanSpace.proj (𝕜 := ℂ) e
        else EuclideanSpace.proj (𝕜 := ℂ) k) z := by
    by_cases hke : k=e
    · subst k
      simpa [chartMap,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate] using
        (EuclideanSpace.proj (𝕜 := ℂ) e).hasFDerivAt (x := z)
    · by_cases hkj : k=j
      · subst k
        have hde : HasFDerivAt (fun w : ComplexModel n=>w e)
            (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ) z :=
          (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).hasFDerivAt
        have hdj : HasFDerivAt (fun w : ComplexModel n=>b j+w j)
            (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ) z := by
          convert (hasFDerivAt_const (b j) z).add
            (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).hasFDerivAt
            using 1 <;> first | rfl | simp only [zero_add]
        convert hde.mul hdj using 1
        all_goals solve
        | rfl
        | simp only [if_neg (Ne.symm hij),ite_true]
        | (funext w;
            simp [chartMap,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,Ne.symm hij])
      · simpa [chartMap,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hke,hkj] using
          (EuclideanSpace.proj (𝕜 := ℂ) k).hasFDerivAt (x := z)
  have hc := (EuclideanSpace.proj (𝕜 := ℂ) k).hasFDerivAt.comp z hp.hasFDerivAt
  have hv:=congrArg (fun L=>L (EuclideanSpace.single i (1 : ℂ))) (ht.unique hc).symm
  change fderiv ℂ (chartMap e j b) z (EuclideanSpace.single i 1) k=_
  change fderiv ℂ (chartMap e j b) z (EuclideanSpace.single i 1) k=_ at hv
  rw [hv]
  by_cases hie : i=e <;> by_cases hij' : i=j <;> by_cases hke : k=e <;> by_cases hkj : k=j <;>
    simp_all [PiLp.single_apply,smul_eq_mul]

private theorem partial_pullback (e j : Fin n) (hij : e≠j) (b : Fin n → ℂ)
    (f : HolGerm (ComplexModel n)) (i : Fin n) :
    coordinatePartial i (chartPullback e j b f)=
      if i=e then chartPullback e j b (coordinatePartial e f)+
        (HolGerm.constHom (b j)+coordinateGerm j)*chartPullback e j b (coordinatePartial j f)
      else if i=j then coordinateGerm e*chartPullback e j b (coordinatePartial j f)
      else chartPullback e j b (coordinatePartial i f) := by
  induction f using HolGerm.induction_on with
  | h F hF =>
    have hp:=differentiable_actualAnalyticBlowupMap ({e,j} : Set (Fin n)) e b
    have ht : Tendsto (chartMap e j b) (𝓝 0) (𝓝 0) := by
      simpa only [chartMap,actualAnalyticBlowupMap_zero] using hp.continuous.tendsto (0 : ComplexModel n)
    have hcomp (k : Fin n) : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
        DifferentiableAt ℂ
          (fun z=>fderiv ℂ F (chartMap e j b z) (EuclideanSpace.single k 1)) z :=
      holomorphic_comp (chartMap e j b) (Eventually.of_forall hp)
        (actualAnalyticBlowupMap_zero _ _ _)
        (eventually_holomorphic_iterDeriv hF [EuclideanSpace.single k 1])
    have hcoord (k : Fin n) : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
        DifferentiableAt ℂ (fun z : ComplexModel n=>z k) z :=
      Eventually.of_forall fun _=>(EuclideanSpace.proj (𝕜 := ℂ) k).differentiableAt
    have hratio := eventually_differentiableAt_add
      (eventually_differentiableAt_const (b j)) (hcoord j)
    by_cases hie : i=e
    · subst i
      simp only [chartPullback,actualAnalyticBlowupPullback,compAlgHom_mk,
        coordinatePartial_mk]
      change HolGerm.mk _ _=HolGerm.mk
        (fun z=>fderiv ℂ F (chartMap e j b z) (EuclideanSpace.single e 1)+
          (b j+z j)*fderiv ℂ F (chartMap e j b z) (EuclideanSpace.single j 1))
        (eventually_differentiableAt_add (hcomp e)
          (eventually_differentiableAt_mul hratio (hcomp j)))
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [ht.eventually hF] with z hz
      rw [fderiv_comp z hz (hp z),ContinuousLinearMap.comp_apply,chart_differential e j hij b e z]
      simp [map_add,map_smul,smul_eq_mul]
    · by_cases hij' : i=j
      · subst i
        simp only [if_neg (Ne.symm hij),chartPullback,actualAnalyticBlowupPullback,
          compAlgHom_mk,coordinatePartial_mk]
        change HolGerm.mk _ _=HolGerm.mk
          (fun z=>z e*fderiv ℂ F (chartMap e j b z) (EuclideanSpace.single j 1))
          (eventually_differentiableAt_mul (hcoord e) (hcomp j))
        apply HolGerm.mk_eq_mk_iff.mpr
        filter_upwards [ht.eventually hF] with z hz
        rw [fderiv_comp z hz (hp z),ContinuousLinearMap.comp_apply,chart_differential e j hij b j z]
        simp [Ne.symm hij,map_smul,smul_eq_mul]
      · simp only [if_neg hie,if_neg hij',chartPullback,actualAnalyticBlowupPullback,
          compAlgHom_mk,coordinatePartial_mk]
        change HolGerm.mk _ _=HolGerm.mk
          (fun z=>fderiv ℂ F (chartMap e j b z) (EuclideanSpace.single i 1)) (hcomp i)
        apply HolGerm.mk_eq_mk_iff.mpr
        filter_upwards [ht.eventually hF] with z hz
        rw [fderiv_comp z hz (hp z),ContinuousLinearMap.comp_apply,chart_differential e j hij b i z]
        simp [hie,hij']

/-- EVERY original whole germ obeys the actual recentered logarithmic chain rule. -/
theorem exceptional_log_direction_formula (S : Finset (Fin n)) (e j : Fin n)
    (hij : e≠j) (he : e∈S) (hj : j∈S) (b : Fin n → ℂ)
    (f : HolGerm (ComplexModel n)) (i : Fin n) :
    logDirection (targetWeight S e j b) i (chartPullback e j b f)=
      if i=e then chartPullback e j b (logDirection (sourceWeight S) e f)+
        chartPullback e j b (logDirection (sourceWeight S) j f)
      else chartPullback e j b (logDirection (sourceWeight S) i f) := by
  change targetWeight S e j b i*coordinatePartial i (chartPullback e j b f)=_
  rw [partial_pullback e j hij b f i]
  by_cases hie : i=e
  · subst i
    simp only [targetWeight,logDirection,sourceWeight,if_pos he,if_pos hj,
      Derivation.smul_apply,smul_eq_mul,map_mul]
    rw [actualAnalyticBlowupPullback_coordinate,actualAnalyticBlowupPullback_coordinate]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,true_or,or_true,
      if_neg (Ne.symm hij),if_true]
    ring
  · by_cases hij' : i=j
    · subst i
      simp only [if_neg (Ne.symm hij),targetWeight,logDirection,sourceWeight,
        if_pos hj,Derivation.smul_apply,smul_eq_mul,map_mul]
      rw [actualAnalyticBlowupPullback_coordinate]
      simp [Ne.symm hij]
      ring
    · have hw : chartPullback e j b (sourceWeight S i)=sourceWeight S i := by
        by_cases hi : i∈S
        · simp [sourceWeight,hi,chartPullback,actualAnalyticBlowupPullback_coordinate,hie,hij']
        · simp [sourceWeight,hi]
      simp only [hie,hij',if_false,targetWeight,logDirection,Derivation.smul_apply,smul_eq_mul,map_mul]
      rw [hw]

private theorem direction_mem (a : Fin n → HolGerm (ComplexModel n))
    (I : Ideal (HolGerm (ComplexModel n))) (i : Fin n) (f : HolGerm (ComplexModel n)) (hf : f∈I) :
    logDirection a i f∈logIdeal a I := by
  exact (show Ideal.span _ ≤ logIdeal a I from le_sup_right)
    (Ideal.subset_span ⟨i,f,hf,rfl⟩)

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

/-- Exact equality of WHOLE ordinary image logarithmic ideals, with arbitrary b. -/
theorem exceptional_log_derivative_ideal_eq (S : Finset (Fin n)) (e j : Fin n)
    (hij : e≠j) (he : e∈S) (hj : j∈S) (b : Fin n → ℂ)
    (I : Ideal (HolGerm (ComplexModel n))) :
    Ideal.map (chartPullback e j b).toRingHom (logIdeal (sourceWeight S) I)=
      logIdeal (targetWeight S e j b) (Ideal.map (chartPullback e j b).toRingHom I) := by
  let φ:=chartPullback e j b
  let a:=sourceWeight S
  let a':=targetWeight S e j b
  have hfor (f : HolGerm (ComplexModel n)) (i : Fin n) :=
    exceptional_log_direction_formula S e j hij he hj b f i
  apply le_antisymm
  · rw [logIdeal,Ideal.map_sup]
    refine sup_le le_sup_left ?_
    rw [Ideal.map_span,Ideal.span_le]
    rintro g ⟨h,⟨i,f,hf,rfl⟩,rfl⟩
    change φ (logDirection a i f)∈logIdeal a' (Ideal.map φ.toRingHom I)
    have hfi : φ f∈Ideal.map φ.toRingHom I:=Ideal.mem_map_of_mem φ.toRingHom hf
    have hEi:=direction_mem a' (Ideal.map φ.toRingHom I) i (φ f) hfi
    by_cases hie : i=e
    · subst i
      have hEj:=direction_mem a' (Ideal.map φ.toRingHom I) j (φ f) hfi
      have hcE : logDirection a' e (φ f)=φ (logDirection a e f)+φ (logDirection a j f) := by
        simpa only [ite_true] using hfor f e
      have hcJ : logDirection a' j (φ f)=φ (logDirection a j f) := by
        simpa only [if_neg (Ne.symm hij)] using hfor f j
      have hx : φ (logDirection a e f)=
          logDirection a' e (φ f)-logDirection a' j (φ f) := by
        rw [hcE,hcJ];ring
      rw [hx]
      exact (logIdeal a' (Ideal.map φ.toRingHom I)).sub_mem hEi hEj
    · have hc:=hfor f i
      rw [if_neg hie] at hc
      rw [←hc]
      exact hEi
  · rw [logIdeal]
    refine sup_le (Ideal.map_mono le_sup_left) ?_
    apply Ideal.span_le.mpr
    rintro g ⟨i,f,hf,rfl⟩
    apply deriv_map_mem φ (logDirection a' i) I (Ideal.map φ.toRingHom (logIdeal a I))
      (Ideal.map_mono le_sup_left) ?_ hf
    intro h hh
    rw [hfor h i]
    split_ifs with hie
    · exact (Ideal.map φ.toRingHom (logIdeal a I)).add_mem
        (Ideal.mem_map_of_mem φ.toRingHom (direction_mem a I e h hh))
        (Ideal.mem_map_of_mem φ.toRingHom (direction_mem a I j h hh))
    · exact Ideal.mem_map_of_mem φ.toRingHom (direction_mem a I i h hh)

end
end Hironaka.HironakaActualExceptionalLogDerivativeIdeal
