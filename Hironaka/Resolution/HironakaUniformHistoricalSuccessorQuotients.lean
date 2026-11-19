import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor
import Hironaka.Resolution.HironakaHolomorphicJetRankLoci
import Hironaka.Analytic.HolomorphicGermReducednessBridge
import Hironaka.MarkedIdeal.InvertibleIdealQuotient

/-! One literal analytic controlled-quotient family on the ENTIRE actual
normal-chart domain. All local divisibility is derived from source centre
powers before the quotients are uniquely glued; target historical laws and
HS values are not assumptions. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaUniformHistoricalSuccessorQuotients
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualAnalyticBlowupTaylor HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  InvertibleIdealQuotient

variable {n : ℕ}

/-- Locally divisible holomorphic functions have one unique analytic quotient
on the whole open domain when the divisor has no open zero set. -/
theorem exists_unique_holomorphic_quotient_on_open
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {U : Set M} (hU : IsOpen U) (H h : M → ℂ)
    (hnon : ∀W : Set M,IsOpen W → W⊆U → W.Nonempty → ∃y∈W,h y≠0)
    (hlocal : ∀x∈U,∃q : M → ℂ,HolomorphicAt n q x ∧
      H=ᶠ[𝓝 x] fun y=>h y*q y) :
    ∃Q : M → ℂ,(∀x∈U,HolomorphicAt n Q x) ∧
      (∀x∈U,H x=h x*Q x) ∧
      ∀Q' : M → ℂ,(∀x∈U,HolomorphicAt n Q' x) →
        (∀x∈U,H x=h x*Q' x) → EqOn Q' Q U := by
  choose q hq hEq using fun x : U=>hlocal x.val x.property
  let Q : M → ℂ:=fun y=>if hy : y∈U then q ⟨y,hy⟩ y else 0
  have hQlocal (x : M) (hx : x∈U) : Q=ᶠ[𝓝 x] q ⟨x,hx⟩ := by
    filter_upwards [hU.mem_nhds hx,(hq ⟨x,hx⟩).eventually,
      (hEq ⟨x,hx⟩).eventually_nhds] with y hy hqy hEqy
    have hEqy' : H=ᶠ[𝓝 y] fun z=>h z*q ⟨x,hx⟩ z:=hEqy
    have hMul : ∀ᶠz in 𝓝 y,h z*q ⟨x,hx⟩ z=h z*q ⟨y,hy⟩ z:=
      hEqy'.symm.trans (hEq ⟨y,hy⟩)
    have he:=eventuallyEq_of_mul_eventuallyEq hU hnon hy hqy (hq ⟨y,hy⟩) hMul
    simpa only [Q,dif_pos hy] using he.eq_of_nhds.symm
  have hQ (x : M) (hx : x∈U) : HolomorphicAt n Q x:=
    (hq ⟨x,hx⟩).congr (hQlocal x hx).symm
  have hProduct (x : M) (hx : x∈U) : H x=h x*Q x:=by
    rw [(hQlocal x hx).eq_of_nhds]
    exact (hEq ⟨x,hx⟩).eq_of_nhds
  refine ⟨Q,hQ,hProduct,?_⟩
  intro Q' hQ' hProduct' x hx
  have hMul : ∀ᶠy in 𝓝 x,h y*Q' y=h y*Q y:=by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hProduct' y hy).symm.trans (hProduct y hy)
  exact (eventuallyEq_of_mul_eventuallyEq hU hnon hx (hQ' x hx) (hQ x hx) hMul).eq_of_nhds

/-- The actual chart has the literal translated normal form at EVERY point
of its exceptional hyperplane, with the original pivot and normal set. -/
theorem actualBlowupMap_translate_at_zero_pivot
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (hz : z e=0) (w : ComplexModel n) :
    actualAnalyticBlowupMap A e b (w+z)=
      actualAnalyticBlowupMap A e (fun i=>b i+z i) w+
        actualAnalyticBlowupMap A e b z := by
  ext i
  simp only [PiLp.add_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate]
  by_cases hi : i∈A
  · by_cases hie : i=e
    · subst i
      simp [hi,hz]
    · simp only [if_pos hi,if_neg hie,hz,zero_mul,add_zero]
      ring
  · simp [hi]

private theorem coordinate_power_no_open_zero (e : Fin n) (mu : ℕ) (U : Set (ComplexModel n)) :
    ∀W : Set (ComplexModel n),IsOpen W → W⊆U → W.Nonempty →
      ∃y∈W,(y e)^mu≠0 := by
  intro W hW _hne hWne
  by_contra! hzero
  obtain ⟨x,hx⟩:=hWne
  have hx0 : x e=0:=eq_zero_of_pow_eq_zero (hzero x hx)
  have ht : Tendsto (fun z : ComplexModel n=>z+x) (𝓝 0) (𝓝 x):=by
    have hc : ContinuousAt (fun z : ComplexModel n=>z+x) 0:=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hc.tendsto
  have heq : (fun z : ComplexModel n=>z e)=ᶠ[𝓝 0] fun _=>0:=by
    filter_upwards [ht.eventually (hW.mem_nhds hx)] with z hz
    have h:=eq_zero_of_pow_eq_zero (hzero (z+x) hz)
    simpa only [PiLp.add_apply,hx0,add_zero] using h
  apply HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e
  exact (HolGerm.mk_eq_mk_iff.mpr heq).trans HolGerm.mk_zero

private theorem differentiable_near_open {U : Set (ComplexModel n)} (hU : IsOpen U)
    {f : ComplexModel n → ℂ} (hf : DifferentiableOn ℂ f U)
    {x : ComplexModel n} (hx : x∈U) : ∀ᶠy in 𝓝 x,DifferentiableAt ℂ f y := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hf.differentiableAt (hU.mem_nhds hy)

/-- Source centre powers at EVERY actual centre point derive local genuine
analytic divisibility at EVERY target point on the whole chart domain. -/
theorem actual_chart_local_quotient_of_source_powers
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (f : ComplexModel n → ℂ) (hf : DifferentiableOn ℂ f U) (mu : ℕ)
    (hCentre : ∀(x : ComplexModel n)(hx : x∈U),(∀i∈A,x i=0) →
      translatedGerm x f (differentiable_near_open hU hf hx)∈actualAnalyticCoordinateIdeal A^mu)
    (z : ComplexModel n) (hzU : actualAnalyticBlowupMap A e b z∈U) :
    ∃q : ComplexModel n → ℂ,HolomorphicAt n q z ∧
      (fun y=>f (actualAnalyticBlowupMap A e b y))=ᶠ[𝓝 z] fun y=>(y e)^mu*q y := by
  let sigma:=actualAnalyticBlowupMap A e b
  have hsigma : Differentiable ℂ sigma:=differentiable_actualAnalyticBlowupMap A e b
  have hH : ∀ᶠy in 𝓝 z,DifferentiableAt ℂ (fun y=>f (sigma y)) y:=by
    filter_upwards [hsigma.continuous.continuousAt.tendsto.eventually (hU.mem_nhds hzU)] with y hy
    exact (hf.differentiableAt (hU.mem_nhds hy)).comp y (hsigma y)
  have hproj : Differentiable ℂ (fun y : ComplexModel n=>y e):=
    (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiable
  by_cases hz : z e=0
  · let x:=sigma z
    have hx : ∀i∈A,x i=0:=by
      intro i hi
      simp [x,sigma,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi,hz]
    have hp:=hCentre x hzU hx
    obtain ⟨G,hG,_hTaylor⟩:=exists_actualAnalyticBlowup_quotient A e he (fun i=>b i+z i)
      mu (translatedGerm x f (differentiable_near_open hU hf hzU)) hp
    obtain ⟨g,hg,rfl⟩:=HolGerm.exists_eq_mk G
    unfold coordinateGerm at hG
    rw [←HolGerm.mk_pow,←HolGerm.mk_mul] at hG
    unfold actualAnalyticBlowupPullback translatedGerm at hG
    rw [compAlgHom_mk] at hG
    have hEq:=HolGerm.mk_eq_mk_iff.mp hG
    change (fun w=>(w e)^mu*g w)=ᶠ[𝓝 0]
      fun w=>f (actualAnalyticBlowupMap A e (fun i=>b i+z i) w+x) at hEq
    have ht : Tendsto (fun y : ComplexModel n=>y-z) (𝓝 z) (𝓝 0):=by
      have hc : ContinuousAt (fun y : ComplexModel n=>y-z) z:=
        continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hc.tendsto
    refine ⟨fun y=>g (y-z),?_,?_⟩
    · filter_upwards [ht.eventually hg] with y hy
      exact (hy.comp y (differentiableAt_id.sub_const z)).mdifferentiableAt
    · filter_upwards [ht.eventually hEq] with y hy
      have hSquare:=actualBlowupMap_translate_at_zero_pivot A e b z hz (y-z)
      rw [sub_add_cancel] at hSquare
      have hye : (y-z) e=y e:=by simp [hz]
      change f (sigma y)=(y e)^mu*g (y-z)
      rw [hye] at hy
      exact (hy.trans (congrArg f hSquare.symm)).symm
  · have hne : ∀ᶠy in 𝓝 z,y e≠0:=hproj.continuous.continuousAt.eventually_ne hz
    refine ⟨fun y=>f (sigma y)/(y e)^mu,?_,?_⟩
    · filter_upwards [hH,hne] with y hy hny
      have hNum : DifferentiableAt ℂ (fun w=>f (sigma w)) y:=hy
      have hDen : DifferentiableAt ℂ (fun w : ComplexModel n=>(w e)^mu) y:=(hproj y).pow mu
      have hDiv : DifferentiableAt ℂ (fun w : ComplexModel n=>f (sigma w)/(w e)^mu) y:=
        by simpa only [div_eq_mul_inv] using hNum.fun_mul (hDen.fun_inv (pow_ne_zero mu hny))
      exact hDiv.mdifferentiableAt
    · filter_upwards [hne] with y hy
      exact (mul_div_cancel₀ _ (pow_ne_zero mu hy)).symm

/-- ONE analytic family on the ENTIRE actual normal chart is produced BEFORE
all target points from point-free source centre powers. All labels and
individual marks remain literal, and uniqueness prevents per-point resets. -/
theorem exists_unique_actual_chart_quotient_family
    {L : Type*} (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (f : L → ComplexModel n → ℂ) (hf : ∀v,DifferentiableOn ℂ (f v) U) (mu : L → ℕ)
    (hCentre : ∀v (x : ComplexModel n)(hx : x∈U),(∀i∈A,x i=0) →
      translatedGerm x (f v) (differentiable_near_open hU (hf v) hx)∈
        actualAnalyticCoordinateIdeal A^(mu v)) :
    ∃F : L → ComplexModel n → ℂ,
      (∀v,DifferentiableOn ℂ (F v) (actualAnalyticBlowupMap A e b ⁻¹' U)) ∧
      (∀v z,actualAnalyticBlowupMap A e b z∈U →
        (z e)^(mu v)*F v z=f v (actualAnalyticBlowupMap A e b z)) ∧
      ∀F' : L → ComplexModel n → ℂ,
        (∀v,DifferentiableOn ℂ (F' v) (actualAnalyticBlowupMap A e b ⁻¹' U)) →
        (∀v z,actualAnalyticBlowupMap A e b z∈U →
          (z e)^(mu v)*F' v z=f v (actualAnalyticBlowupMap A e b z)) →
        ∀v,EqOn (F' v) (F v) (actualAnalyticBlowupMap A e b ⁻¹' U) := by
  let V:=actualAnalyticBlowupMap A e b ⁻¹' U
  have hV : IsOpen V:=hU.preimage (differentiable_actualAnalyticBlowupMap A e b).continuous
  choose F hF hProduct hUnique using fun v=>exists_unique_holomorphic_quotient_on_open
    hV (fun z=>f v (actualAnalyticBlowupMap A e b z)) (fun z=>(z e)^(mu v))
      (coordinate_power_no_open_zero e (mu v) V)
      (fun z hz=>actual_chart_local_quotient_of_source_powers A e he b hU (f v) (hf v) (mu v)
        (hCentre v) z hz)
  refine ⟨F,?_,fun v z hz=>(hProduct v z hz).symm,?_⟩
  · intro v z hz
    exact (hF v z hz).self_of_nhds.differentiableAt.differentiableWithinAt
  · intro F' hF' hProduct' v
    apply hUnique v (F' v) ?_ (fun z hz=>(hProduct' v z hz).symm)
    intro z hz
    exact holomorphicAt_of_mdifferentiableOn hV
      (mdifferentiableOn_iff_differentiableOn.mpr (hF' v)) hz

/-- At EVERY exceptional point the SAME prechosen analytic quotient has the
literal normalized whole-germ equation in the actual recentered chart. -/
theorem actual_chart_quotient_translated_product
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (f F : ComplexModel n → ℂ) (hf : DifferentiableOn ℂ f U)
    (hF : DifferentiableOn ℂ F (actualAnalyticBlowupMap A e b ⁻¹' U)) (mu : ℕ)
    (hProduct : ∀y,actualAnalyticBlowupMap A e b y∈U →
      (y e)^mu*F y=f (actualAnalyticBlowupMap A e b y))
    (z : ComplexModel n) (hzU : actualAnalyticBlowupMap A e b z∈U) (hz : z e=0) :
    (coordinateGerm e)^mu*translatedGerm z F
      (differentiable_near_open
        (hU.preimage (differentiable_actualAnalyticBlowupMap A e b).continuous) hF hzU)=
      actualAnalyticBlowupPullback A e (fun i=>b i+z i)
        (translatedGerm (actualAnalyticBlowupMap A e b z) f (differentiable_near_open hU hf hzU)) := by
  unfold coordinateGerm translatedGerm actualAnalyticBlowupPullback
  rw [←HolGerm.mk_pow,←HolGerm.mk_mul,compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  have hV : IsOpen (actualAnalyticBlowupMap A e b ⁻¹' U):=
    hU.preimage (differentiable_actualAnalyticBlowupMap A e b).continuous
  have ht : Tendsto (fun w : ComplexModel n=>w+z) (𝓝 0) (𝓝 z):=by
    have hc : ContinuousAt (fun w : ComplexModel n=>w+z) 0:=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hc.tendsto
  filter_upwards [ht.eventually (hV.mem_nhds hzU)] with w hw
  have hp:=hProduct (w+z) hw
  change (w e)^mu*F (w+z)=
    f (actualAnalyticBlowupMap A e (fun i=>b i+z i) w+actualAnalyticBlowupMap A e b z)
  simpa only [PiLp.add_apply,hz,add_zero,actualBlowupMap_translate_at_zero_pivot A e b z hz w] using hp

end
end Hironaka.HironakaUniformHistoricalSuccessorQuotients
