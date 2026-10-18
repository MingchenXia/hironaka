/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHolomorphicFibreHS
import Hironaka.Resolution.HironakaRelativeNormalIdeal
import Mathlib.Analysis.Analytic.IteratedFDeriv

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTangentJetConnection
noncomputable section
open HironakaRelativeNormalIdeal HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetMonomialSpan

/-- One original function/domain gives the actual translated jets at EVERY order on the SAME tangent parameter domain. -/
theorem actual_tangent_translated_jet_analytic (d t : ℕ)
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    {g : ComplexModel (d+t) → ℂ} (hg : DifferentiableOn ℂ g U)
    (j : ℕ) (v : Fin j → ComplexModel (d+t)) :
    AnalyticOnNhd ℂ (fun c : ComplexModel d =>
      iteratedFDeriv ℂ j (fun z => g (z+tangentInclusion d t c)) 0 v)
      ((tangentInclusion d t) ⁻¹' U) := by
  have hAn : AnalyticOnNhd ℂ g U := fun x hx =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn hU hg hx
  intro c hc
  have hjet := ((hAn.iteratedFDeriv j) _ hc).comp ((tangentInclusion d t).analyticAt c)
  have hev := ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin j => ComplexModel (d+t)) ℂ v).analyticAt _).comp hjet
  convert hev using 1
  funext b
  rw [iteratedFDeriv_comp_add_right,zero_add]
  rfl

/-- ONLY genuine original holomorphicity on its real open supplies the all-order true tangent connection. -/
theorem actual_tangent_translated_jet_fderiv (d t : ℕ)
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    {g : ComplexModel (d+t) → ℂ} (hg : DifferentiableOn ℂ g U)
    (j : ℕ) (v : Fin j → ComplexModel (d+t)) (c a : ComplexModel d)
    (hc : tangentInclusion d t c ∈ U) :
    fderiv ℂ (fun b : ComplexModel d =>
      iteratedFDeriv ℂ j (fun z => g (z+tangentInclusion d t b)) 0 v) c a=
      iteratedFDeriv ℂ (j+1) g (tangentInclusion d t c) (Fin.cons (tangentInclusion d t a) v) := by
  have hAn : AnalyticOnNhd ℂ g U := fun x hx =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn hU hg hx
  have hjet : DifferentiableAt ℂ (iteratedFDeriv ℂ j g) (tangentInclusion d t c) :=
    ((hAn.iteratedFDeriv j) _ hc).differentiableAt
  have he : (fun b : ComplexModel d =>
      iteratedFDeriv ℂ j (fun z => g (z+tangentInclusion d t b)) 0 v)=
      (fun b : ComplexModel d => iteratedFDeriv ℂ j g (tangentInclusion d t b) v) := by
    funext b
    rw [iteratedFDeriv_comp_add_right,zero_add]
  rw [he]
  change fderiv ℂ ((fun x => iteratedFDeriv ℂ j g x v) ∘ tangentInclusion d t) c a=_
  rw [fderiv_comp c (hjet.continuousMultilinear_apply_const v) (tangentInclusion d t).differentiableAt]
  rw [(tangentInclusion d t).fderiv]
  change fderiv ℂ (fun x => iteratedFDeriv ℂ j g x v) (tangentInclusion d t c) (tangentInclusion d t a)=_
  simpa only [Fin.tail_cons,Fin.cons_zero] using
    (hjet.iteratedFDeriv_succ_apply_left' (m := Fin.cons (tangentInclusion d t a) v)).symm


/-- The genuine analytic mixed-direction identity retains the original tuple and its actual first direction. -/
theorem actual_analytic_directional_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) (j : ℕ) (v : Fin j → E) (w : E) :
    iteratedFDeriv ℂ j (fun y => fderiv ℂ f y w) x v=
      iteratedFDeriv ℂ (j+1) f x (Fin.cons w v) := by
  let ev : (E →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ w
  have hdir : AnalyticAt ℂ (fun y => fderiv ℂ f y w) x :=
    (ev.analyticAt _).comp hf.fderiv
  have hleft := hdir.contDiffAt.iteratedFDeriv_comp_perm v (Fin.revPerm : Equiv.Perm (Fin j))
  have hright := hf.contDiffAt.iteratedFDeriv_comp_perm (Fin.cons w v)
    (Fin.revPerm : Equiv.Perm (Fin (j+1)))
  change iteratedFDeriv ℂ j (fun y => fderiv ℂ f y w) x (v ∘ Fin.rev)=
    iteratedFDeriv ℂ j (fun y => fderiv ℂ f y w) x v at hleft
  change iteratedFDeriv ℂ (j+1) f x (Fin.cons w v ∘ Fin.rev)=
    iteratedFDeriv ℂ (j+1) f x (Fin.cons w v) at hright
  rw [Fin.cons_comp_rev,iteratedFDeriv_succ_apply_right] at hright
  simp only [Fin.init_snoc,Fin.snoc_last] at hright
  have hd : ContDiffAt ℂ j (fderiv ℂ f) x := hf.fderiv.contDiffAt.of_le le_top
  have he := ev.iteratedFDeriv_comp_left hd (i := j) le_rfl
  have heval : iteratedFDeriv ℂ j (fun y => fderiv ℂ f y w) x (v ∘ Fin.rev)=
      iteratedFDeriv ℂ j (fderiv ℂ f) x (v ∘ Fin.rev) w := by
    change iteratedFDeriv ℂ j (ev ∘ fderiv ℂ f) x (v ∘ Fin.rev)=_
    rw [he]
    rfl
  exact hleft.symm.trans (heval.trans hright)


/-- A true parameter derivative is the SAME joint successor jet on a genuine neighborhood, with no mixed-partial certificate. -/
theorem actual_joint_fibre_jet_parameter_fderiv {r n : ℕ}
    {D : Set (ComplexModel r × ComplexModel n)} (hD : IsOpen D)
    {F : ComplexModel r × ComplexModel n → ℂ} (hF : DifferentiableOn ℂ F D)
    (p a : ComplexModel r) (hp : (p,0) ∈ D) (j : ℕ) (v : Fin j → ComplexModel n) :
    fderiv ℂ (fun b : ComplexModel r => iteratedFDeriv ℂ j (fun z => F (b,z)) 0 v) p a=
      iteratedFDeriv ℂ (j+1) F (p,0) (Fin.cons (a,0) (fun i => (0,v i))) := by
  let S := ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel n)
  let w : Fin j → (ComplexModel r × ComplexModel n) := fun i => (0,v i)
  have hAn : AnalyticOnNhd ℂ F D := fun x hx =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn hD hF hx
  have hjet : DifferentiableAt ℂ (iteratedFDeriv ℂ j F) (p,0) :=
    ((hAn.iteratedFDeriv j) _ hp).differentiableAt
  have hnear : (fun b : ComplexModel r => iteratedFDeriv ℂ j (fun z => F (b,z)) 0 v) =ᶠ[𝓝 p]
      (fun b : ComplexModel r => iteratedFDeriv ℂ j F (b,0) w) := by
    filter_upwards [S.continuous.continuousAt.tendsto.eventually (hD.mem_nhds hp)] with b hb
    exact congrArg (fun L : ContinuousMultilinearMap ℂ (fun _ : Fin j => ComplexModel n) ℂ => L v)
      (HironakaActualHolomorphicFibreHS.actualIndependentParameter_iteratedFDeriv_slice hD hF hb j)
  rw [hnear.fderiv_eq]
  change fderiv ℂ ((fun x => iteratedFDeriv ℂ j F x w) ∘ S) p a=_
  rw [fderiv_comp p (hjet.continuousMultilinear_apply_const w) S.differentiableAt,S.fderiv]
  change fderiv ℂ (fun x => iteratedFDeriv ℂ j F x w) (p,0) (a,0)=_
  simpa only [Fin.tail_cons,Fin.cons_zero] using
    (hjet.iteratedFDeriv_succ_apply_left' (m := Fin.cons (a,0) w)).symm


private theorem weighted_tangent_jet_fderiv (d t : ℕ)
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    {g φ : ComplexModel (d+t) → ℂ} (hg : DifferentiableOn ℂ g U)
    (hφ : Differentiable ℂ φ) (j : ℕ) (v : Fin j → ComplexModel (d+t))
    (c a : ComplexModel d) (hc : tangentInclusion d t c ∈ U) :
    fderiv ℂ (fun b : ComplexModel d =>
      iteratedFDeriv ℂ j (fun z => φ z*g (z+tangentInclusion d t b)) 0 v) c a=
      iteratedFDeriv ℂ (j+1) (fun z => φ z*g (z+tangentInclusion d t c)) 0
        (Fin.cons (tangentInclusion d t a) v)-
      iteratedFDeriv ℂ j (fun z => fderiv ℂ φ z (tangentInclusion d t a)*
        g (z+tangentInclusion d t c)) 0 v := by
  let T := tangentInclusion d t
  let L : (ComplexModel d × ComplexModel (d+t)) →L[ℂ] ComplexModel (d+t) :=
    ContinuousLinearMap.snd ℂ _ _+T.comp (ContinuousLinearMap.fst ℂ _ _)
  let D : Set (ComplexModel d × ComplexModel (d+t)) := L ⁻¹' U
  have hD : IsOpen D := hU.preimage L.continuous
  let F (y : ComplexModel d × ComplexModel (d+t)) := φ y.2*g (L y)
  have hF : DifferentiableOn ℂ F D := by
    intro y hy
    exact (((hφ y.2).comp y differentiableAt_snd).mul
      ((hg.differentiableAt (hU.mem_nhds hy)).comp y L.differentiableAt)).differentiableWithinAt
  have hAn : AnalyticOnNhd ℂ F D := fun y hy =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn hD hF hy
  have hp : (c,0) ∈ D := by simpa [D,L,T] using hc
  let w : ComplexModel d × ComplexModel (d+t) := (-a,T a)
  have hLw : L w=0 := by simp [L,w]
  let K (y : ComplexModel d × ComplexModel (d+t)) := fderiv ℂ φ y.2 (T a)*g (L y)
  have hdir (y : ComplexModel d × ComplexModel (d+t)) (hy : y ∈ D) : fderiv ℂ F y w=K y := by
    have hφ' := (hφ y.2).hasFDerivAt.comp y (ContinuousLinearMap.snd ℂ (ComplexModel d) (ComplexModel (d+t))).hasFDerivAt
    have hg' := (hg.differentiableAt (hU.mem_nhds hy)).hasFDerivAt.comp y L.hasFDerivAt
    have hprod := hφ'.mul hg'
    have he := congrArg (fun B : (ComplexModel d × ComplexModel (d+t)) →L[ℂ] ℂ => B w) hprod.fderiv
    change fderiv ℂ F y w=_ at he
    have hWsnd : (ContinuousLinearMap.snd ℂ (ComplexModel d) (ComplexModel (d+t))) w=T a := rfl
    simpa only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,hWsnd,hLw,map_zero,
      smul_eq_mul,mul_zero,zero_mul,add_zero,zero_add,Function.comp_apply,K,mul_comm] using he
  have hnear (y : ComplexModel d × ComplexModel (d+t)) (hy : y ∈ D) :
      (fun x => fderiv ℂ F x w) =ᶠ[𝓝 y] K :=
    eventually_of_mem (hD.mem_nhds hy) fun x hx => hdir x hx
  have hK : DifferentiableOn ℂ K D := by
    intro y hy
    let ev : ((ComplexModel d × ComplexModel (d+t)) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ w
    have hka : AnalyticAt ℂ (fun x => fderiv ℂ F x w) y :=
      (ev.analyticAt _).comp (hAn y hy).fderiv
    exact (hka.congr (hnear y hy)).differentiableAt.differentiableWithinAt
  let vv : Fin j → (ComplexModel d × ComplexModel (d+t)) := fun i => (0,v i)
  have hparam := actual_joint_fibre_jet_parameter_fderiv hD hF c a hp j v
  have hnext := HironakaActualHolomorphicFibreHS.actualIndependentParameter_iteratedFDeriv_slice hD hF hp (j+1)
  have hnextval : iteratedFDeriv ℂ (j+1) (fun z => F (c,z)) 0
      (Fin.cons (T a) v)=iteratedFDeriv ℂ (j+1) F (c,0) (Fin.cons (0,T a) vv) := by
    rw [hnext]
    change iteratedFDeriv ℂ (j+1) F (c,0) (fun i => (0,(Fin.cons (T a) v : Fin (j+1) → ComplexModel (d+t)) i))=_
    apply congrArg (iteratedFDeriv ℂ (j+1) F (c,0))
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  have hcorrection := HironakaActualHolomorphicFibreHS.actualIndependentParameter_iteratedFDeriv_slice hD hK hp j
  have hcorrectionval : iteratedFDeriv ℂ j (fun z => K (c,z)) 0 v=
      iteratedFDeriv ℂ (j+1) F (c,0) (Fin.cons w vv) := by
    rw [hcorrection]
    change iteratedFDeriv ℂ j K (c,0) vv=_
    rw [← ((hnear (c,0) hp).iteratedFDeriv ℂ j).eq_of_nhds]
    exact actual_analytic_directional_jet (hAn (c,0) hp) j vv w
  have hsum : iteratedFDeriv ℂ (j+1) F (c,0) (Fin.cons (0,T a) vv)=
      iteratedFDeriv ℂ (j+1) F (c,0) (Fin.cons (a,0) vv)+
        iteratedFDeriv ℂ (j+1) F (c,0) (Fin.cons w vv) := by
    let M := iteratedFDeriv ℂ (j+1) F (c,0)
    have hw : (0,T a)=(a,0)+w := by ext <;> simp [w]
    change M.curryLeft (0,T a) vv=M.curryLeft (a,0) vv+M.curryLeft w vv
    rw [hw,map_add]
    rfl
  have hall : fderiv ℂ (fun b : ComplexModel d =>
      iteratedFDeriv ℂ j (fun z => F (b,z)) 0 v) c a=
      iteratedFDeriv ℂ (j+1) (fun z => F (c,z)) 0 (Fin.cons (T a) v)-
        iteratedFDeriv ℂ j (fun z => K (c,z)) 0 v := by
    rw [hparam,hnextval,hcorrectionval,hsum,add_sub_cancel_right]
  exact hall


/-- The unchanged original word-multiplied Macaulay entry has its TRUE multiplier derivative correction. -/
theorem actual_original_macaulay_tangent_fderiv (d t : ℕ) {ι : Type*}
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    (G : ι → ComplexModel (d+t) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U) (q : ℕ)
    (row : monomialIndex (d+t) q) (col : monomialIndex (d+t) q × ι)
    (c a : ComplexModel d) (hc : tangentInclusion d t c ∈ U) :
    fderiv ℂ (fun b : ComplexModel d => originalMacaulayMatrix q G (tangentInclusion d t b) row col) c a=
      iteratedFDeriv ℂ (row.1.val+1)
        (fun z => wordFunction col.1 z*G col.2 (z+tangentInclusion d t c)) 0
        (Fin.cons (tangentInclusion d t a) (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k)))-
      iteratedFDeriv ℂ row.1.val
        (fun z => fderiv ℂ (wordFunction col.1) z (tangentInclusion d t a)*
          G col.2 (z+tangentInclusion d t c)) 0
        (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k)) := by
  exact weighted_tangent_jet_fderiv d t hU (hG col.2) (differentiable_wordFunction col.1)
    row.1.val (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k)) c a hc

/-- The correction is the explicit actual finite lower-word polynomial, with genuine multiplicities from repeated letters. -/
theorem actual_wordFunction_fderiv {n q : ℕ} (w : monomialIndex n q)
    (z b : ComplexModel n) :
    fderiv ℂ (wordFunction w) z b=∑ k : Fin w.1.val,
      b (w.2 k)*(∏ l ∈ (Finset.univ : Finset (Fin w.1.val)).erase k, z (w.2 l)) := by
  have hd := HasFDerivAt.finsetProd (u := (Finset.univ : Finset (Fin w.1.val)))
    (g := fun k (x : ComplexModel n) => x (w.2 k))
    (g' := fun k => (EuclideanSpace.proj (w.2 k) : ComplexModel n →L[ℂ] ℂ))
    (fun k _ => (EuclideanSpace.proj (w.2 k) : ComplexModel n →L[ℂ] ℂ).hasFDerivAt (x := z))
  have he := congrArg (fun A : ComplexModel n →L[ℂ] ℂ => A b) hd.fderiv
  change fderiv ℂ (fun x : ComplexModel n => ∏ k : Fin w.1.val, x (w.2 k)) z b=_
  simpa [smul_eq_mul,mul_comm] using he

end
end Hironaka.HironakaActualTangentJetConnection
