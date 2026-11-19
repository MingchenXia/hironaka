import Hironaka.Resolution.HironakaActualNormalCentreChartTransition
import Hironaka.Resolution.HironakaActualNormalAllDirectionAnalyticSaturation

/-! Genuine analytic target-chart germs are constructed from coordinate germs
and the inverse of the actual nonzero pivot unit. Actual holomorphic coordinate
representatives construct both pullback maps. Their ENTIRE Taylor dictionaries
and formal inverses prove an actual analytic germ equivalence; no analytic
realization or inverse certificate is supplied. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticNormalTargetTransition
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
 HironakaActualCoefficientPresentationCentrePower HironakaActualTaylorCoordinateNaturality
 HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticFormalNormalPowers
 HironakaActualNormalZeroAnalyticSaturation HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
 HironakaActualOriginalFormalHSTransfer HironakaActualNormalCentreChartTransition
 HironakaActualAnalyticStrictGenerators
variable {n : ℕ}

def actualTargetTransverseGerm (e i : Fin n) : HolGerm (ComplexModel n) :=
  if i=e then 0 else coordinateGerm i

def actualTargetPivotGerm (e f : Fin n) (v : Fin n → ℂ) : HolGerm (ComplexModel n) :=
  HolGerm.constHom (v f)+actualTargetTransverseGerm e f

def actualTargetCoordinateGerm (A : Set (Fin n)) (e f : Fin n) (v : Fin n → ℂ)
    (i : Fin n) : HolGerm (ComplexModel n) :=
  if i∈A then if i=f then coordinateGerm e*actualTargetPivotGerm e f v else
    (HolGerm.constHom (v i)+actualTargetTransverseGerm e i)*
      Ring.inverse (actualTargetPivotGerm e f v)-HolGerm.constHom (v i/v f)
  else coordinateGerm i

private theorem eval_transverse (e i : Fin n) : HolGerm.eval (actualTargetTransverseGerm e i)=0 := by
  by_cases hi : i=e <;> simp [actualTargetTransverseGerm,hi,coordinateGerm]

private theorem eval_pivot (e f : Fin n) (v : Fin n → ℂ) :
    HolGerm.eval (actualTargetPivotGerm e f v)=v f := by
  simp [actualTargetPivotGerm,eval_transverse]

theorem actualTargetPivotGerm_isUnit (e f : Fin n) (v : Fin n → ℂ) (hf : v f≠0) :
    IsUnit (actualTargetPivotGerm e f v) :=
  (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa only [eval_pivot] using hf)

private theorem eval_pivot_inverse (e f : Fin n) (v : Fin n → ℂ) (hf : v f≠0) :
    HolGerm.eval (Ring.inverse (actualTargetPivotGerm e f v))=(v f)⁻¹ := by
  have h:=congrArg HolGerm.eval
    (Ring.inverse_mul_cancel _ (actualTargetPivotGerm_isUnit e f v hf))
  rw [map_mul,map_one,eval_pivot] at h
  apply mul_right_cancel₀ hf
  exact h.trans (inv_mul_cancel₀ hf).symm

private theorem eval_coordinate (A : Set (Fin n)) (e f : Fin n) (v : Fin n → ℂ)
    (hf : v f≠0) (i : Fin n) : HolGerm.eval (actualTargetCoordinateGerm A e f v i)=0 := by
  unfold actualTargetCoordinateGerm
  split_ifs <;> simp [map_mul,map_sub,map_add,coordinateGerm,eval_pivot,
    eval_transverse,eval_pivot_inverse e f v hf,div_eq_mul_inv]

private theorem taylor_transverse (e i : Fin n) :
    actualUnshiftedTaylorAlgHom n (actualTargetTransverseGerm e i)=actualNormalChartTransverse e i := by
  by_cases hi : i=e <;> simp [actualTargetTransverseGerm,actualNormalChartTransverse,hi,
    actualUnshiftedTaylor_coordinate]

private theorem taylor_pivot (e f : Fin n) (v : Fin n → ℂ) :
    actualUnshiftedTaylorAlgHom n (actualTargetPivotGerm e f v)=actualNormalChartPivotUnit e f v := by
  rw [actualTargetPivotGerm,map_add,taylor_transverse]
  exact congrArg (fun g=>g+actualNormalChartTransverse e f) ((actualUnshiftedTaylorAlgHom n).commutes (v f))

private theorem formal_pivot_constant (e f : Fin n) (v : Fin n → ℂ) :
    MvPowerSeries.constantCoeff (actualNormalChartPivotUnit e f v)=v f := by
  by_cases he : f=e <;> simp [actualNormalChartPivotUnit,actualNormalChartTransverse,he]

private theorem taylor_pivot_inverse (e f : Fin n) (v : Fin n → ℂ) (hf : v f≠0) :
    actualUnshiftedTaylorAlgHom n (Ring.inverse (actualTargetPivotGerm e f v))=
      (actualNormalChartPivotUnit e f v)⁻¹ := by
  apply (MvPowerSeries.eq_inv_iff_mul_eq_one (by simpa only [formal_pivot_constant] using hf)).mpr
  have h:=congrArg (actualUnshiftedTaylorAlgHom n)
    (Ring.inverse_mul_cancel _ (actualTargetPivotGerm_isUnit e f v hf))
  rwa [map_mul,map_one,taylor_pivot] at h

private theorem taylor_coordinate (A : Set (Fin n)) (e f : Fin n) (v : Fin n → ℂ)
    (hf : v f≠0) (i : Fin n) :
    actualUnshiftedTaylorAlgHom n (actualTargetCoordinateGerm A e f v i)=
      actualNormalChartTransitionCoordinates A e f v i := by
  have hc (c : ℂ) : actualUnshiftedTaylorAlgHom n (HolGerm.constHom c)=MvPowerSeries.C c :=
    (actualUnshiftedTaylorAlgHom n).commutes c
  unfold actualTargetCoordinateGerm actualNormalChartTransitionCoordinates
  split_ifs <;> simp only [map_mul,map_sub,map_add,actualUnshiftedTaylor_coordinate,
    taylor_pivot,taylor_transverse,taylor_pivot_inverse e f v hf,hc]

private theorem exists_actual_coordinate_pullback (c : Fin n → HolGerm (ComplexModel n))
    (hc : ∀i,HolGerm.eval (c i)=0) :
    ∃φ : HolGerm (ComplexModel n)→ₐ[ℂ]HolGerm (ComplexModel n),∀i,φ (coordinateGerm i)=c i := by
  choose H hH hG using fun i=>HolGerm.exists_eq_mk (c i)
  let η : ComplexModel n → ComplexModel n:=
    fun z=>(EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm (fun i=>H i z)
  have hη : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z := by
    filter_upwards [eventually_all.mpr hH] with z hz
    exact (EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm.differentiableAt.comp z
      (differentiableAt_pi.mpr hz)
  have hη0 : η 0=0 := by
    ext i
    change H i 0=0
    have h:=congrArg HolGerm.eval (hG i)
    simpa only [HolGerm.eval_mk,hc i] using h.symm
  let φ:=compAlgHom η hη hη0
  refine ⟨φ,?_⟩
  intro i
  have heq : φ (coordinateGerm i)=HolGerm.mk (H i) (hH i) := by
    unfold φ coordinateGerm
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z=>rfl
  exact heq.trans (hG i).symm

private theorem exists_actual_target_pullback (A : Set (Fin n)) (e f : Fin n)
    (v : Fin n → ℂ) (hf : v f≠0) :
    ∃φ : HolGerm (ComplexModel n)→ₐ[ℂ]HolGerm (ComplexModel n),
      (∀i,φ (coordinateGerm i)=actualTargetCoordinateGerm A e f v i) ∧
      ∀g,actualUnshiftedTaylorAlgHom n (φ g)=
        actualNormalChartTransitionHom A e f v (actualUnshiftedTaylorAlgHom n g) := by
  obtain ⟨φ,hφ⟩:=exists_actual_coordinate_pullback (actualTargetCoordinateGerm A e f v)
    (eval_coordinate A e f v hf)
  have hMap : (actualUnshiftedTaylorAlgHom n).comp φ=
      (actualNormalChartTransitionHom A e f v).comp (actualUnshiftedTaylorAlgHom n) := by
    apply actualGermAlgHom_eq_of_coordinate_images
    · intro i
      change actualUnshiftedTaylorAlgHom n (φ (coordinateGerm i))=
        actualNormalChartTransitionHom A e f v (actualUnshiftedTaylorAlgHom n (coordinateGerm i))
      rw [hφ,taylor_coordinate A e f v hf,actualUnshiftedTaylor_coordinate,actualNormalChartTransition_X]
    · intro i
      change actualUnshiftedTaylorAlgHom n (φ (coordinateGerm i))∈_
      rw [hφ]
      have hm : actualTargetCoordinateGerm A e f v i∈
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) :=
        (HolGerm.mem_maximalIdeal_iff _).mpr (eval_coordinate A e f v hf i)
      have h:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hm
      have hMax : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
          (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)))=actualFormalCoordinateIdeal n univ := by
        simpa only [pow_one,actualFormalCoordinateIdeal,Set.image_univ,genuineFormalVariables] using
          map_actualUnshifted_maximal_pow n 1
      rwa [hMax] at h
  exact ⟨φ,hφ,fun g=>DFunLike.congr_fun hMap g⟩

/-- The actual rational-coordinate germs construct a genuine analytic target
equivalence with the ENTIRE prescribed formal Taylor substitution. The only
overlap condition is the same actual nonzero direction coordinate. -/
theorem exists_actual_analytic_normal_target_equiv
    (A : Set (Fin n)) (e f : Fin n) (heA : e∈A) (hfA : f∈A)
    (v : Fin n → ℂ) (he : v e=1) (hf : v f≠0) :
    ∃E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n),
      (∀i,E (coordinateGerm i)=actualTargetCoordinateGerm A e f v i) ∧
      ∀g,actualUnshiftedTaylorAlgHom n (E g)=
        actualNormalChartTransitionHom A e f v (actualUnshiftedTaylorAlgHom n g) := by
  let w:=actualNormalChartNormalizedDirection f v
  have hwe : w e≠0 := by
    dsimp only [w,actualNormalChartNormalizedDirection]
    rw [he,one_div]
    exact inv_ne_zero hf
  obtain ⟨φ,hφ,hTφ⟩:=exists_actual_target_pullback A e f v hf
  obtain ⟨ψ,_hψ,hTψ⟩:=exists_actual_target_pullback A f e w hwe
  let EF:=actualNormalChartTransitionAlgEquiv A e f heA hfA v he hf
  have hLeft (g : HolGerm (ComplexModel n)) : ψ (φ g)=g := by
    apply actualUnshiftedTaylorAlgHom_injective n
    rw [hTψ,hTφ]
    exact EF.left_inv (actualUnshiftedTaylorAlgHom n g)
  have hRight (g : HolGerm (ComplexModel n)) : φ (ψ g)=g := by
    apply actualUnshiftedTaylorAlgHom_injective n
    rw [hTφ,hTψ]
    exact EF.right_inv (actualUnshiftedTaylorAlgHom n g)
  let E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n):=
    { toFun:=φ
      invFun:=ψ
      left_inv:=hLeft
      right_inv:=hRight
      map_mul':=φ.map_mul
      map_add':=φ.map_add
      commutes':=φ.commutes }
  exact ⟨E,hφ,hTφ⟩

private theorem taylor_of_actual_quotient
    (A : Set (Fin n)) (e : Fin n) (heA : e∈A) (b : Fin n → ℂ)
    (μ : ℕ) (g H : HolGerm (ComplexModel n))
    (hp : g∈actualAnalyticCoordinateIdeal A^μ)
    (hH : coordinateGerm e^μ*H=actualAnalyticBlowupPullback A e b g) :
    actualUnshiftedTaylorAlgHom n H=actualNormalizedFormalMember A e heA b μ
      (actualUnshiftedTaylorAlgHom n g) (actualTaylor_mem_coordinateCentre_pow A μ g hp) := by
  apply actualNormalizedFormalMember_unique
  have h:=congrArg (actualUnshiftedTaylorAlgHom n) hH
  rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate] at h
  exact h.trans (DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e b) g)

private theorem same_member_covariance
    (A : Set (Fin n)) (e f : Fin n) (heA : e∈A) (hfA : f∈A)
    (v : Fin n → ℂ) (he : v e=1) (hf : v f≠0)
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (hT : ∀g,actualUnshiftedTaylorAlgHom n (E g)=
      actualNormalChartTransitionHom A e f v (actualUnshiftedTaylorAlgHom n g))
    (μ : ℕ) (g : HolGerm (ComplexModel n)) (hp : g∈actualAnalyticCoordinateIdeal A^μ)
    (Hf He : HolGerm (ComplexModel n))
    (hHf : coordinateGerm f^μ*Hf=actualAnalyticBlowupPullback A f
      (actualNormalChartNormalizedDirection f v) g)
    (hHe : coordinateGerm e^μ*He=actualAnalyticBlowupPullback A e v g) :
    actualTargetPivotGerm e f v^μ*E Hf=He := by
  apply actualUnshiftedTaylorAlgHom_injective n
  rw [map_mul,map_pow,taylor_pivot,hT,
    taylor_of_actual_quotient A f hfA (actualNormalChartNormalizedDirection f v) μ g Hf hp hHf,
    taylor_of_actual_quotient A e heA v μ g He hp hHe]
  exact actualNormalChartTransition_normalized_member A e f heA hfA v he hf μ
    (actualUnshiftedTaylorAlgHom n g) (actualTaylor_mem_coordinateCentre_pow A μ g hp)

private theorem whole_normalized_ideal_transport
    (A : Set (Fin n)) (e f : Fin n) (heA : e∈A) (hfA : f∈A)
    (v : Fin n → ℂ) (hf : v f≠0)
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (hCov : ∀(μ : ℕ)(g : HolGerm (ComplexModel n)),g∈actualAnalyticCoordinateIdeal A^μ →
      ∀Hf He : HolGerm (ComplexModel n),
      coordinateGerm f^μ*Hf=actualAnalyticBlowupPullback A f
        (actualNormalChartNormalizedDirection f v) g →
      coordinateGerm e^μ*He=actualAnalyticBlowupPullback A e v g →
      actualTargetPivotGerm e f v^μ*E Hf=He)
    (I : Ideal (HolGerm (ComplexModel n))) :
    Ideal.map E.toRingEquiv.toRingHom
        (actualAnalyticNormalizedMemberIdeal I A f (actualNormalChartNormalizedDirection f v))=
      actualAnalyticNormalizedMemberIdeal I A e v := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro Hf ⟨μ,g,hg,hp,hHf⟩
    change E Hf∈actualAnalyticNormalizedMemberIdeal I A e v
    obtain ⟨He,hHe,_hTaylor⟩:=exists_actualAnalyticBlowup_quotient A e heA v μ g hp
    apply (Ideal.unit_mul_mem_iff_mem _ ((actualTargetPivotGerm_isUnit e f v hf).pow μ)).mp
    rw [hCov μ g hp Hf He hHf hHe]
    exact Ideal.subset_span ⟨μ,g,hg,hp,hHe⟩
  · apply Ideal.span_le.mpr
    rintro He ⟨μ,g,hg,hp,hHe⟩
    obtain ⟨Hf,hHf,_hTaylor⟩:=exists_actualAnalyticBlowup_quotient A f hfA
      (actualNormalChartNormalizedDirection f v) μ g hp
    rw [←hCov μ g hp Hf He hHf hHe]
    exact (Ideal.map E.toRingEquiv.toRingHom
      (actualAnalyticNormalizedMemberIdeal I A f (actualNormalChartNormalizedDirection f v))).mul_mem_left _
      (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨μ,g,hg,hp,hHf⟩))

/-- One genuinely constructed analytic target equivalence transports EVERY
literal source member at its SAME weight by a genuine pivot unit, and transports
the ENTIRE independently named normalized-member ideal for every source ideal.
No target equality, analytic inverse or chart-compatibility certificate is input. -/
theorem exists_actual_analytic_normal_target_transport
    (A : Set (Fin n)) (e f : Fin n) (heA : e∈A) (hfA : f∈A)
    (v : Fin n → ℂ) (he : v e=1) (hf : v f≠0) :
    ∃E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n),
      (∀i,E (coordinateGerm i)=actualTargetCoordinateGerm A e f v i) ∧
      (∀g,actualUnshiftedTaylorAlgHom n (E g)=
        actualNormalChartTransitionHom A e f v (actualUnshiftedTaylorAlgHom n g)) ∧
      IsUnit (actualTargetPivotGerm e f v) ∧
      (∀(μ : ℕ)(g : HolGerm (ComplexModel n)),g∈actualAnalyticCoordinateIdeal A^μ →
        ∀Hf He : HolGerm (ComplexModel n),
        coordinateGerm f^μ*Hf=actualAnalyticBlowupPullback A f
          (actualNormalChartNormalizedDirection f v) g →
        coordinateGerm e^μ*He=actualAnalyticBlowupPullback A e v g →
        actualTargetPivotGerm e f v^μ*E Hf=He) ∧
      ∀I : Ideal (HolGerm (ComplexModel n)),
        Ideal.map E.toRingEquiv.toRingHom
          (actualAnalyticNormalizedMemberIdeal I A f (actualNormalChartNormalizedDirection f v))=
          actualAnalyticNormalizedMemberIdeal I A e v := by
  obtain ⟨E,hCoord,hT⟩:=exists_actual_analytic_normal_target_equiv A e f heA hfA v he hf
  have hCov:=same_member_covariance A e f heA hfA v he hf E hT
  exact ⟨E,hCoord,hT,actualTargetPivotGerm_isUnit e f v hf,hCov,
    whole_normalized_ideal_transport A e f heA hfA v hf E hCov⟩

end
end Hironaka.HironakaActualAnalyticNormalTargetTransition
