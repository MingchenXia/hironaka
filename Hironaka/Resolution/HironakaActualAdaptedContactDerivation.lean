import Hironaka.Resolution.HironakaActualNormalizedOriginDerivation
import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon
import Hironaka.Blowup.BlowupDerivativeIdeal

/-! Genuine adapted differentiation on the ACTUAL source manifold, with no
coordinate-model extension. Blueprint:
hironaka-actual-adapted-contact-derivation-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualAdaptedContactDerivation
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaSmoothSubmersionGermIdealColon HironakaRelativeNormalIdeal
  HironakaActualPrincipalPartsCompatibility HironakaRelativeNormalTaylorCoefficients
  DerivativeIdeal IdealOrderArithmetic RelativePrincipalizationSpan
  HironakaActualEulerContactPowerRecovery HironakaActualHomogenizedTangentStability MaximalContact

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem adapted_mono {I J : GermIdeal n X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (hIJ : ∀f,I.mem x f→J.mem x f) :
    adaptedIdeal I x Φ h0≤adaptedIdeal J x Φ h0:=by
  apply Ideal.span_le.mpr
  rintro _ ⟨f,hf,hIf,rfl⟩
  exact Ideal.subset_span ⟨f,hf,hIJ f hIf,rfl⟩

/-- ENTIRE actual adapted members retain the genuine functional product. -/
theorem adapted_product_member (I J : GermIdeal n X) (x : X)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    {a b : HolGerm (ComplexModel n)} (ha : a∈adaptedIdeal I x Φ h0)
    (hb : b∈adaptedIdeal J x Φ h0) : a*b∈adaptedIdeal (I.mul J) x Φ h0:=by
  have hMul : (adaptedIdeal I x Φ h0)*(adaptedIdeal J x Φ h0)≤
      adaptedIdeal (I.mul J) x Φ h0:=by
    rw [adaptedIdeal,adaptedIdeal,Ideal.span_mul_span']
    apply Ideal.span_le.mpr
    rintro _ ⟨a,⟨f,hf,hIf,rfl⟩,b,⟨g,hg,hJg,rfl⟩,rfl⟩
    exact Ideal.subset_span ⟨f*g,hf.mul hg,
      IdealOrderArithmetic.mul_mem_mul hIf hJg (hf.mul hg),
      (adaptedGerm_mul x Φ h0 g f hg hf).symm⟩
  exact hMul (Ideal.mul_mem_mul ha hb)

private theorem directional_adapted_generator (I : GermIdeal n X) (hI : I.IsCoherent)
    (x : X) (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (v : ComplexModel n) (f : X→ℂ) (hf : HolomorphicAt n f x) (hIf : I.mem x f) :
    actualDirectionalDerivation v (adaptedGerm x Φ h0 f hf)∈adaptedIdeal (derivIdeal I) x Φ h0:=by
  let e:=complexChartAt (n:=n) x
  have hxs : x∈e.val.source:=mem_complexChartAt_source x
  have htar : (0 : ComplexModel n)∈Φ.target:=by
    simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hInv0 : Φ.invFun 0=e.val x:=by
    rw [←h0,Φ.left_inv _ Φ.center_mem_source]
    rfl
  have hInvT : Tendsto Φ.invFun (𝓝 (0 : ComplexModel n)) (𝓝 (e.val x)):=by
    have ht:=(Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds htar)).continuousAt.tendsto
    simpa only [hInv0] using ht
  let c (j : Fin n) (z : ComplexModel n):=fderiv ℂ Φ.invFun z v j
  have hc (j : Fin n) : HolAt (c j) 0:=by
    have hd:=Hironaka.differentiableOn_fderiv_apply_of_isOpen Φ.invFun_holomorphic Φ.isOpen_target v
    filter_upwards [Φ.isOpen_target.mem_nhds htar] with z hz
    exact (EuclideanSpace.proj (𝕜:=ℂ) j).differentiableAt.comp z
      ((hd z hz).differentiableAt (Φ.isOpen_target.mem_nhds hz))
  let g (j : Fin n):=chartDeriv e (EuclideanSpace.single j 1) f
  have hg (j : Fin n) : HolomorphicAt n (g j) x:=holomorphicAt_chartDeriv hxs hf
  have hIg (j : Fin n) : (derivIdeal I).mem x (g j):=
    chartDeriv_mem_derivIdeal (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hI h) hxs hIf
  have hgj (j : Fin n) : HolAt (fun z=>(g j) (e.val.symm (Φ.invFun z))) 0:=
    (holomorphic_adapted_iff x Φ h0 (g j)).mpr (hg j)
  have hflat : HolAt (f ∘ e.val.symm ∘ Φ.invFun) 0:=
    (holomorphic_adapted_iff x Φ h0 f).mpr hf
  have hEq : actualDirectionalDerivation v (adaptedGerm x Φ h0 f hf)=
      ∑j,HolGerm.mk (c j) (hc j)*adaptedGerm x Φ h0 (g j) (hg j):=by
    change HolGerm.mk (fun z=>fderiv ℂ (f ∘ e.val.symm ∘ Φ.invFun) z v)
      (eventually_holomorphic_iterDeriv hflat [v])=_
    have hsum : HolAt (fun z=>∑j,c j z*(g j) (e.val.symm (Φ.invFun z))) 0:=
      HolAt.fintype_sum fun j=>(hc j).mul (hgj j)
    calc
      _=HolGerm.mk _ hsum:=HolGerm.mk_eq_mk_iff.mpr (by
        filter_upwards [Φ.isOpen_target.mem_nhds htar,
          hInvT.eventually (e.val.open_target.mem_nhds (e.val.map_source hxs)),
          hInvT.eventually (eventually_differentiableAt_comp_symm e hxs hf)] with z hz hze hfe
        have hi:=(Φ.invFun_holomorphic z hz).differentiableAt (Φ.isOpen_target.mem_nhds hz)
        change fderiv ℂ ((f ∘ e.val.symm) ∘ Φ.invFun) z v=_
        rw [fderiv_comp z hfe hi,ContinuousLinearMap.comp_apply]
        conv_lhs=>rw [←sum_smul_single (fderiv ℂ Φ.invFun z v)]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul,smul_eq_mul]
        simp only [c,g,chartDeriv,e.val.right_inv hze])
      _=_:=by
        rw [HolGerm.mk_sum Finset.univ _
          (fun j=>(hc j).mul (hgj j))]
        exact Finset.sum_congr rfl fun j _=>HolGerm.mk_mul _ _ _ _
  rw [hEq]
  exact (adaptedIdeal (derivIdeal I) x Φ h0).sum_mem fun j _=>
    (adaptedIdeal (derivIdeal I) x Φ h0).mul_mem_left _ (Ideal.subset_span ⟨g j,hg j,hIg j,rfl⟩)

/-- Every actual whole adapted member differentiates into the actual ORIGINAL
derivative stalk, on the genuine source manifold of arbitrary universe. -/
theorem directional_derivative_adapted_member (I : GermIdeal n X) (hI : I.IsCoherent)
    (x : X) (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) (v : ComplexModel n)
    {g : HolGerm (ComplexModel n)} (hg : g∈adaptedIdeal I x Φ h0) :
    actualDirectionalDerivation v g∈adaptedIdeal (derivIdeal I) x Φ h0:=by
  have hOrigin:=adapted_mono Φ h0
    (fun f h=>le_derivIdeal (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hI h) x f h)
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨f,hf,hIf,rfl⟩
    exact directional_adapted_generator I hI x Φ h0 v f hf hIf
  · simpa only [map_zero] using (adaptedIdeal (derivIdeal I) x Φ h0).zero_mem
  · intro a b _ha _hb hDa hDb
    rw [map_add]
    exact (adaptedIdeal (derivIdeal I) x Φ h0).add_mem hDa hDb
  · intro a b hb hDb
    change actualDirectionalDerivation v (a*b)∈adaptedIdeal (derivIdeal I) x Φ h0
    rw [(actualDirectionalDerivation v).leibniz]
    simp only [smul_eq_mul]
    exact (adaptedIdeal (derivIdeal I) x Φ h0).add_mem
      ((adaptedIdeal (derivIdeal I) x Φ h0).mul_mem_left a hDb)
      ((adaptedIdeal (derivIdeal I) x Φ h0).mul_mem_right (actualDirectionalDerivation v a)
        (hOrigin hb))

/-- Genuine ORIGINAL contact internally selects a nonzero adapted derivative
and produces the SAME normalized whole derivation with every actual original
derivative-stalk iterate and source Euler stability. -/
theorem exists_actual_contact_adapted_derivation (I : GermIdeal n X) (hI : I.IsCoherent)
    (d : ℕ) (hd : 1≤d) (U : Set X) (u : X→ℂ) (hu : IsTangentDirection I d U u)
    (x : X) (hx : x∈U) (hxCos : x∈GermIdealOrder.cosupport n univ I d)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    ∃hUh : HolomorphicAt n u x,
      u x=0 ∧ adaptedGerm x Φ h0 u hUh∈adaptedIdeal (iterDerivIdeal I (d-1)) x Φ h0 ∧
      ∃v : ComplexModel n,
        HolGerm.eval (actualDirectionalDerivation v (adaptedGerm x Φ h0 u hUh))≠0 ∧
        ∃δ : Derivation ℂ (HolGerm (ComplexModel n)) (HolGerm (ComplexModel n)),
          δ (adaptedGerm x Φ h0 u hUh)=1 ∧
          (∀ (A : GermIdeal n X) (_hA : A.IsCoherent) k g,
            g∈adaptedIdeal A x Φ h0→
              iteratedDerivation δ k g∈adaptedIdeal (iterDerivIdeal A k) x Φ h0) ∧
          (∀ (A T : GermIdeal n X) (_hA : A.IsCoherent)
            (_hStable : ∀f,((derivIdeal A).mul T).mem x f→A.mem x f),
            adaptedGerm x Φ h0 u hUh∈adaptedIdeal T x Φ h0→
              ∀g∈adaptedIdeal A x Φ h0,(adaptedGerm x Φ h0 u hUh)*δ g∈adaptedIdeal A x Φ h0):=by
  have hHolI : ∀y f,I.mem y f→HolomorphicAt n f y:=
    fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hI h
  have hUh : HolomorphicAt n u x:=
    holomorphicAt_of_mem_iterDerivIdeal hHolI (d-1) x u (hu.mem x hx)
  have hu0 : u x=0:=apply_eq_zero_of_mem_cosupport hHolI hd hxCos (hu.mem x hx)
  obtain ⟨e',v',hxe',hNonzero⟩:=hu.multiplicity_one x hx hu0
  obtain ⟨α,_hα,hFlat⟩:=BlowupDerivativeIdeal.chartDeriv_eventuallyEq_sum_flat
    (complexChartAt (n:=n) x) (mem_complexChartAt_source x) Φ hUh e' hxe' v'
  have hSome : ∃j : Fin n,
      fderiv ℂ (u ∘ (chartAt (ComplexModel n) x).symm ∘ Φ.invFun) 0
        (EuclideanSpace.single j 1)≠0:=by
    by_contra! hAll
    have hEq:=hFlat.self_of_nhds
    change chartDeriv e' v' u x=∑j,α j x*
      fderiv ℂ (u ∘ (chartAt (ComplexModel n) x).symm ∘ Φ.invFun)
        (Φ.toFun (chartAt (ComplexModel n) x x)) (EuclideanSpace.single j 1) at hEq
    rw [h0] at hEq
    exact hNonzero (by simpa only [hAll,mul_zero,Finset.sum_const_zero] using hEq)
  obtain ⟨j,hj⟩:=hSome
  let v:=EuclideanSpace.single j (1 : ℂ)
  let t:=adaptedGerm x Φ h0 u hUh
  have hEval : HolGerm.eval (actualDirectionalDerivation v t)≠0:=by
    change fderiv ℂ (u ∘ (chartAt (ComplexModel n) x).symm ∘ Φ.invFun) 0 v≠0
    exact hj
  obtain ⟨w,hw⟩:=(HolGerm.isUnit_iff_eval_ne_zero _).mpr hEval
  let δ : Derivation ℂ (HolGerm (ComplexModel n)) (HolGerm (ComplexModel n)):=
    (↑(w⁻¹) : HolGerm (ComplexModel n)) • actualDirectionalDerivation v
  have hOne : δ t=1:=by
    change (↑(w⁻¹) : HolGerm (ComplexModel n))*actualDirectionalDerivation v t=1
    rw [←hw]
    simp
  have hFirst (A : GermIdeal n X) (hA : A.IsCoherent)
      (g : HolGerm (ComplexModel n)) (hg : g∈adaptedIdeal A x Φ h0) :
      δ g∈adaptedIdeal (derivIdeal A) x Φ h0:=by
    exact (adaptedIdeal (derivIdeal A) x Φ h0).mul_mem_left _
      (directional_derivative_adapted_member A hA x Φ h0 v hg)
  refine ⟨hUh,hu0,Ideal.subset_span ⟨u,hUh,hu.mem x hx,rfl⟩,v,hEval,δ,hOne,?_,?_⟩
  · intro A hA k g hg
    induction k with
    | zero=>exact hg
    | succ k ih=>
      exact hFirst (iterDerivIdeal A k) (isCoherent_iterDerivIdeal hA k)
        (iteratedDerivation δ k g) ih
  · intro A T hA hStable huT g hg
    have hMul:=adapted_product_member (derivIdeal A) T x Φ h0 (hFirst A hA g hg) huT
    have hResult:=adapted_mono Φ h0 hStable hMul
    simpa only [mul_comm] using hResult

/-- Actual native contact and source tangent stability recover EVERY finite
contact power into the TRUE original derivative stalk; no coordinate extension
or supplied target derivation/Euler/cancellation certificate. -/
theorem actual_contact_adapted_power_recovery (I : GermIdeal n X) (hI : I.IsCoherent)
    (d : ℕ) (hd : 1≤d) (U : Set X) (u : X→ℂ) (hu : IsTangentDirection I d U u)
    (x : X) (hx : x∈U) (hxCos : x∈GermIdealOrder.cosupport n univ I d)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    ∃hUh : HolomorphicAt n u x,
      ∀ (A T : GermIdeal n X) (_hA : A.IsCoherent) (_hT : T.IsCoherent)
        (_hStable : ((derivIdeal A).mul T).Le A) (_huT : T.mem x u)
        (D : ℕ) (_hUPow : A.mem x (fun y=>u y^D)) j (f : HolGerm (ComplexModel n)),
        (adaptedGerm x Φ h0 u hUh)^j*f∈adaptedIdeal A x Φ h0→
          f∈adaptedIdeal (iterDerivIdeal A j) x Φ h0:=by
  obtain ⟨hUh,_hu0,_huMember,v,_hEval,δ,hOne,hIter,hEuler⟩:=
    exists_actual_contact_adapted_derivation I hI d hd U u hu x hx hxCos Φ h0
  refine ⟨hUh,?_⟩
  intro A T hA hT hStable huT D hUPow j f hGiven
  let t:=adaptedGerm x Φ h0 u hUh
  let B:=adaptedIdeal (iterDerivIdeal A j) x Φ h0
  have huAdapt : t∈adaptedIdeal T x Φ h0:=Ideal.subset_span ⟨u,hUh,huT,rfl⟩
  have hEB : ∀g∈B,t*δ g∈B:=hEuler (iterDerivIdeal A j) T
    (isCoherent_iterDerivIdeal hA j) (iterDeriv_tangent_stability hA hT hStable j x) huAdapt
  have hPow : t^D∈adaptedIdeal A x Φ h0:=by
    have hPowHol:=GermIdeal.IsCoherent.holomorphicAt_mem hA hUPow
    have hMem : adaptedGerm x Φ h0 (fun y=>u y^D) hPowHol∈adaptedIdeal A x Φ h0:=
      Ideal.subset_span ⟨(fun y=>u y^D),hPowHol,hUPow,rfl⟩
    have hEq : adaptedGerm x Φ h0 (fun y=>u y^D) hPowHol=t^D:=by
      exact HolGerm.mk_pow _ ((holomorphic_adapted_iff x Φ h0 u).mpr hUh) D
    rwa [hEq] at hMem
  have hBD : t^D∈B:=adapted_mono Φ h0
    (le_iterDerivIdeal (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hA h) j x) hPow
  exact euler_contact_power_recovery δ hOne B hEB hBD j f (hIter A hA j _ hGiven)

end
end Hironaka.HironakaActualAdaptedContactDerivation
