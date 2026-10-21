/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentreJetFrameCocycle
import Hironaka.Resolution.HironakaRelativeNormalTaylorCoefficients
import Hironaka.Invariant.OrderMultiplicativity

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentreJointJets
noncomputable section
open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HolGerm HolomorphicTaylorTail HironakaRelativeNormalIdeal HironakaRelativeNormalTaylorCoefficients
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaActualHSConstantCentreJetFrames
  HironakaActualCentreJetFrameTruncation HironakaActualCentreJetFrameCocycle

/-- Genuine last-coordinate projection of the original joint model. -/
def actualJointNormalProjection (d n : ℕ) : ComplexModel (d+n) →L[ℂ] ComplexModel n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin n => EuclideanSpace.proj (i.natAdd d))

@[simp] theorem actualJointNormalProjection_apply (d n : ℕ) (z : ComplexModel (d+n)) (i : Fin n) :
    actualJointNormalProjection d n z i=z (i.natAdd d) := rfl

/-- The genuine linear joint tangent translation L(c,z)=z+T(c), with no formal nonzero evaluation. -/
def actualCentreJointMap (d t : ℕ) : ComplexModel (d+(d+t)) →L[ℂ] ComplexModel (d+t) :=
  actualJointNormalProjection d (d+t)+(tangentInclusion d t).comp (tangentProjection d (d+t))

/-- Whole ORIGINAL holomorphic germ pullback by the true origin-preserving joint map. -/
def actualCentreJointPullback (d t : ℕ) :
    HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel (d+(d+t))) :=
  compAlgHom (actualCentreJointMap d t)
    (Eventually.of_forall fun _ => (actualCentreJointMap d t).differentiableAt) (map_zero _)

/-- True entire normal-word jets with factorials restored, over the original whole tangent germ ring. -/
def actualJointScalarJet (d n q : ℕ) :
    letI := tangentAlgebra d n
    HolGerm (ComplexModel (d+n)) →ₗ[HolGerm (ComplexModel d)]
      (monomialIndex n q → HolGerm (ComplexModel d)) :=
  letI := tangentAlgebra d n
  { toFun := fun g w => (w.1.val.factorial : HolGerm (ComplexModel d))*normalTaylorCoefficients d n q g w
    map_add' := fun g h => by
      funext w
      simp only [map_add,Pi.add_apply,mul_add]
    map_smul' := fun c g => by
      funext w
      simp only [map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      ring }

/-- Factorial units preserve the COMPLETE original normal-power kernel, including all repeated words. -/
theorem ker_actualJointScalarJet (d n q : ℕ) :
    letI := tangentAlgebra d n
    LinearMap.ker (actualJointScalarJet d n q)=
      (normalIdeal d n ^ q).restrictScalars (HolGerm (ComplexModel d)) := by
  let := tangentAlgebra d n
  ext g
  constructor
  · intro hg
    have hz := LinearMap.mem_ker.mp hg
    apply mem_normalIdeal_pow_of_normalTaylorCoefficients_eq_zero d n q g
    funext w
    have hu : IsUnit (w.1.val.factorial : HolGerm (ComplexModel d)) :=
      (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by
        simpa only [map_natCast] using (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero w.1.val) :
          (w.1.val.factorial : ℂ) ≠ 0))
    apply hu.mul_right_eq_zero.mp
    exact congrFun hz w
  · intro hg
    apply LinearMap.mem_ker.mpr
    have hz := normalTaylorCoefficients_eq_zero_of_mem d n q g hg
    funext w
    change (w.1.val.factorial : HolGerm (ComplexModel d))*normalTaylorCoefficients d n q g w=0
    rw [show normalTaylorCoefficients d n q g w=0 from congrFun hz w,mul_zero]


/-- Every ENTIRE original joint ideal image is the span of the SAME genuine normal-word-times-generator columns. -/
theorem actualJointScalarJet_ideal_image (d n q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel (d+n))) :
    let := tangentAlgebra d n
    ((Ideal.span (range G)).restrictScalars (HolGerm (ComplexModel d))).map (actualJointScalarJet d n q)=
      Submodule.span (HolGerm (ComplexModel d))
        (range fun b : monomialIndex n q × ι => actualJointScalarJet d n q (normalWord d n b.1*G b.2)) := by
  let := tangentAlgebra d n
  let S : (monomialIndex n q → HolGerm (ComplexModel d)) →ₗ[HolGerm (ComplexModel d)]
      (monomialIndex n q → HolGerm (ComplexModel d)) :=
    { toFun := fun v w => (w.1.val.factorial : HolGerm (ComplexModel d))*v w
      map_add' := fun v w => by ext a;exact mul_add _ _ _
      map_smul' := fun c v => by
        funext w
        change (w.1.val.factorial : HolGerm (ComplexModel d))*(c*v w)=
          c*((w.1.val.factorial : HolGerm (ComplexModel d))*v w)
        exact mul_left_comm _ _ _ }
  calc
    _ = (((Ideal.span (range G)).restrictScalars (HolGerm (ComplexModel d))).map
        (normalTaylorCoefficients d n q)).map S := by
      rw [← Submodule.map_comp]
      rfl
    _ = (Submodule.span (HolGerm (ComplexModel d))
        (range fun b : monomialIndex n q × ι => normalTaylorCoefficients d n q (normalWord d n b.1*G b.2))).map S := by
      rw [map_span_ideal_normalTaylorCoefficients_eq_word_columns]
    _ = _ := by
      rw [Submodule.map_span,← Set.range_comp]
      rfl


/-- True affine chain rule for original iterated directional derivatives between the genuine models. -/
private theorem iterDeriv_comp_actual_affine {m n : ℕ}
    (F : ComplexModel m →L[ℂ] ComplexModel n) (b : ComplexModel n)
    {U : Set (ComplexModel n)} (hU : IsOpen U) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f U) :
    ∀ V : List (ComplexModel m),∀ z : ComplexModel m,F z+b ∈ U →
      iterDeriv V (fun y => f (F y+b)) z=iterDeriv (V.map F) f (F z+b)
  | [],_,_ => rfl
  | v :: V,z,hz => by
    have he : iterDeriv V (fun y => f (F y+b)) =ᶠ[𝓝 z]
        (fun y => iterDeriv (V.map F) f (F y+b)) := by
      filter_upwards [(hU.preimage (F.continuous.add continuous_const)).mem_nhds hz] with y hy
      exact iterDeriv_comp_actual_affine F b hU hf V y hy
    have hd := (differentiableOn_iterDeriv hf hU (V.map F) _ hz).differentiableAt (hU.mem_nhds hz)
    simp only [List.map_cons,iterDeriv_cons,dirDeriv]
    rw [he.fderiv_eq]
    change (fderiv ℂ ((iterDeriv (V.map F) f) ∘ (fun y => F y+b)) z) v=_
    rw [fderiv_comp z hd (F.differentiableAt.add_const b)]
    simp only [ContinuousLinearMap.comp_apply,fderiv_add_const,F.fderiv]

/-- The restored actual word jet of any true joint representative is its ORIGINAL normal directional derivative germ. -/
theorem actualJointScalarJet_mk (d n q : ℕ) (f : ComplexModel (d+n) → ℂ) (hf : HolAt f 0)
    (w : monomialIndex n q) :
    actualJointScalarJet d n q (HolGerm.mk f hf) w=
      HolGerm.mk (iterDeriv ((List.ofFn w.2).map (normalVector d n)) f ∘ tangentInclusion d n)
        (eventually_differentiableAt_comp_clm (tangentInclusion d n)
          (eventually_holomorphic_iterDeriv hf _)) := by
  change (w.1.val.factorial : HolGerm (ComplexModel d))*
    relativeTaylorCoefficient d n (List.ofFn w.2) (HolGerm.mk f hf)=_
  rw [relativeTaylorCoefficient,iteratedDerivativeGerm_mk]
  simp only [List.length_ofFn,planeTrace,compAlgHom_mk,Algebra.smul_def]
  have hc : (w.1.val.factorial : HolGerm (ComplexModel d))*
      algebraMap ℂ (HolGerm (ComplexModel d)) ((w.1.val.factorial : ℂ)⁻¹)=1 := by
    have h := congrArg (algebraMap ℂ (HolGerm (ComplexModel d)))
      (mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero w.1.val) :
        (w.1.val.factorial : ℂ) ≠ 0))
    simpa only [map_mul,map_natCast,map_one] using h
  rw [← mul_assoc,hc,one_mul]


/-- Genuine last-coordinate inclusion, used only as an actual linear fibre slice. -/
def actualJointNormalInclusion (d n : ℕ) : ComplexModel n →L[ℂ] ComplexModel (d+n) :=
  ∑ i : Fin n,(EuclideanSpace.proj i).smulRight (normalVector d n i)

@[simp] theorem actualJointNormalInclusion_normal (d n : ℕ) (z : ComplexModel n) (i : Fin n) :
    actualJointNormalInclusion d n z (i.natAdd d)=z i := by
  simp [actualJointNormalInclusion,sum_apply,ContinuousLinearMap.smulRight_apply,
    normalVector,Pi.single_apply,Fin.natAdd_inj]

@[simp] theorem actualJointNormalInclusion_tangent (d n : ℕ) (z : ComplexModel n) (i : Fin d) :
    actualJointNormalInclusion d n z (i.castAdd n)=0 := by
  have hne : ∀ j : Fin n,i.castAdd n ≠ j.natAdd d := by
    intro j he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  simp [actualJointNormalInclusion,sum_apply,ContinuousLinearMap.smulRight_apply,
    normalVector,hne]

@[simp] theorem actualJointNormalProjection_inclusion (d n : ℕ) (z : ComplexModel n) :
    actualJointNormalProjection d n (actualJointNormalInclusion d n z)=z := by
  ext i
  simp

@[simp] theorem actualJointNormalProjection_tangent (d n : ℕ) (c : ComplexModel d) :
    actualJointNormalProjection d n (tangentInclusion d n c)=0 := by
  ext i
  simp

@[simp] theorem tangentProjection_actualJointNormalInclusion (d n : ℕ) (z : ComplexModel n) :
    tangentProjection d n (actualJointNormalInclusion d n z)=0 := by
  ext i
  simp

@[simp] theorem actualJointNormalInclusion_basis (d n : ℕ) (i : Fin n) :
    actualJointNormalInclusion d n (EuclideanSpace.basisFun (Fin n) ℂ i)=normalVector d n i := by
  simp [actualJointNormalInclusion,EuclideanSpace.basisFun_apply,ContinuousLinearMap.smulRight_apply]

/-- The actual joint map has the exact original fibre z+T(c), on ALL points. -/
theorem actualCentreJointMap_fibre (d t : ℕ) (c : ComplexModel d) (z : ComplexModel (d+t)) :
    actualCentreJointMap d t
      (actualJointNormalInclusion d (d+t) z+tangentInclusion d (d+t) c)=z+tangentInclusion d t c := by
  simp [actualCentreJointMap,ContinuousLinearMap.comp_apply,
    map_add,tangentProjection_tangentInclusion]

/-- The unchanged original normal word is the true polynomial on the last-coordinate projection. -/
theorem normalWord_joint_mk (d n q : ℕ) (w : monomialIndex n q) :
    normalWord d n w=HolGerm.mk (wordFunction w ∘ actualJointNormalProjection d n)
      (Eventually.of_forall fun z => (differentiable_wordFunction w).differentiableAt.comp z
        (actualJointNormalProjection d n).differentiableAt) := by
  exact (show normalWord d n w=
      wordMonomial (⟨w.1,fun i => (w.2 i).natAdd d⟩ : monomialIndex (d+n) q) from rfl).trans
    (wordMonomial_eq_mk (⟨w.1,fun i => (w.2 i).natAdd d⟩ : monomialIndex (d+n) q))

/-- Original holomorphic entries give their genuine tangent coefficient germs, on the SAME real domain. -/
theorem actualCentreMacaulayEntry_holAt (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (h0 : (0 : ComplexModel (d+t)) ∈ U)
    (a : monomialIndex (d+t) q) (b : monomialIndex (d+t) q × ι) :
    HolAt (fun c => originalMacaulayMatrix q H (tangentInclusion d t c) a b) 0 := by
  have hh : HolAt (fun p => originalMacaulayMatrix q H p a b) 0 := by
    filter_upwards [hU.mem_nhds h0] with p hp
    exact ((differentiableOn_originalMacaulayMatrix_entry q H hU hH a b) p hp).differentiableAt
      (hU.mem_nhds hp)
  exact eventually_differentiableAt_comp_clm (tangentInclusion d t) hh

/-- Entrywise germs of the SAME original Macaulay matrix on the actual tangent plane. -/
def actualCentreMacaulayGerm (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (h0 : (0 : ComplexModel (d+t)) ∈ U) :
    Matrix (monomialIndex (d+t) q) (monomialIndex (d+t) q × ι) (HolGerm (ComplexModel d)) :=
  fun a b => HolGerm.mk (fun c => originalMacaulayMatrix q H (tangentInclusion d t c) a b)
    (actualCentreMacaulayEntry_holAt d t q H hU hH h0 a b)


/-- Every SAME actual joint normal-word column is exactly the original moving Macaulay column as an ENTIRE tangent germ. -/
theorem actualJointScalarJet_column_dictionary (d t q : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) {U : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (h0 : (0 : ComplexModel (d+t)) ∈ U)
    (hH0 : ∀ i,HolAt (H i) 0) (b : monomialIndex (d+t) q × ι) :
    actualJointScalarJet d (d+t) q
      (normalWord d (d+t) b.1*actualCentreJointPullback d t (HolGerm.mk (H b.2) (hH0 b.2)))=
      fun a => actualCentreMacaulayGerm d t q H hU hH h0 a b := by
  let V : Set (ComplexModel (d+(d+t))) := (actualCentreJointMap d t) ⁻¹' U
  have hV : IsOpen V := hU.preimage (actualCentreJointMap d t).continuous
  have h0V : (0 : ComplexModel (d+(d+t))) ∈ V := by
    change actualCentreJointMap d t 0 ∈ U
    simpa only [map_zero] using h0
  let F : ComplexModel (d+(d+t)) → ℂ := fun u =>
    wordFunction b.1 (actualJointNormalProjection d (d+t) u)*H b.2 (actualCentreJointMap d t u)
  have hF : DifferentiableOn ℂ F V := by
    intro u hu
    exact (((differentiable_wordFunction b.1).differentiableAt.comp u
      (actualJointNormalProjection d (d+t)).differentiableAt).mul
        (((hH b.2) _ hu).differentiableAt (hU.mem_nhds hu) |>.comp u
          (actualCentreJointMap d t).differentiableAt)).differentiableWithinAt
  have hF0 : HolAt F 0 := by
    filter_upwards [hV.mem_nhds h0V] with u hu
    exact (hF u hu).differentiableAt (hV.mem_nhds hu)
  have hge : normalWord d (d+t) b.1*actualCentreJointPullback d t (HolGerm.mk (H b.2) (hH0 b.2))=
      HolGerm.mk F hF0 := by
    rw [normalWord_joint_mk,actualCentreJointPullback,compAlgHom_mk,← HolGerm.mk_mul]
    rfl
  rw [hge]
  funext a
  rw [actualJointScalarJet_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  have hT : Tendsto (tangentInclusion d t) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)
  filter_upwards [hT.eventually (hU.mem_nhds h0)] with c hc
  change iterDeriv ((List.ofFn a.2).map (normalVector d (d+t))) F (tangentInclusion d (d+t) c)=
    originalMacaulayMatrix q H (tangentInclusion d t c) a b
  have hb : tangentInclusion d (d+t) c ∈ V := by
    change actualCentreJointMap d t (tangentInclusion d (d+t) c) ∈ U
    have he : actualCentreJointMap d t (tangentInclusion d (d+t) c)=tangentInclusion d t c := by
      simpa only [map_zero,zero_add] using actualCentreJointMap_fibre d t c 0
    rwa [he]
  have hdirs : (List.ofFn (fun k : Fin a.1.val => EuclideanSpace.basisFun (Fin (d+t)) ℂ (a.2 k))).map
      (actualJointNormalInclusion d (d+t))=(List.ofFn a.2).map (normalVector d (d+t)) := by
    simp only [List.map_ofFn,Function.comp_def,actualJointNormalInclusion_basis]
  have hchain := iterDeriv_comp_actual_affine (actualJointNormalInclusion d (d+t))
    (tangentInclusion d (d+t) c) hV hF
    (List.ofFn (fun k : Fin a.1.val => EuclideanSpace.basisFun (Fin (d+t)) ℂ (a.2 k))) 0
    (by simpa only [map_zero,zero_add] using hb)
  rw [hdirs,map_zero,zero_add] at hchain
  rw [← hchain]
  have hfun : (fun z => F (actualJointNormalInclusion d (d+t) z+tangentInclusion d (d+t) c))=
      (fun z => wordFunction b.1 z*H b.2 (z+tangentInclusion d t c)) := by
    funext z
    dsimp only [F]
    rw [actualCentreJointMap_fibre]
    simp only [map_add,actualJointNormalProjection_inclusion,actualJointNormalProjection_tangent,add_zero]
  rw [hfun]
  let W : Set (ComplexModel (d+t)) := (fun z => z+tangentInclusion d t c) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_id.add continuous_const)
  have h0W : (0 : ComplexModel (d+t)) ∈ W := by
    change U ((0 : ComplexModel (d+t))+tangentInclusion d t c)
    rw [zero_add]
    exact hc
  have hcol : DifferentiableOn ℂ (fun z => wordFunction b.1 z*H b.2 (z+tangentInclusion d t c)) W := by
    intro z hz
    exact ((differentiable_wordFunction b.1).differentiableAt.mul
      (((hH b.2) _ hz).differentiableAt (hU.mem_nhds hz) |>.comp z
        (differentiableAt_id.add_const (tangentInclusion d t c)))).differentiableWithinAt
  exact OrderMultiplicativity.iterDeriv_ofFn_eq_iteratedFDeriv hW hcol a.1.val
    (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (a.2 k)) h0W

end
end Hironaka.HironakaActualCentreJointJets
