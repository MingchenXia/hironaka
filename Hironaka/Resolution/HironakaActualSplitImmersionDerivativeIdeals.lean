import Hironaka.Resolution.HironakaActualSplitImmersionFields

/-! Whole actual derivative ideals along a supported carrier under an
actual holomorphic split immersion, in possibly different dimensions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSplitImmersionDerivativeIdeals
noncomputable section
open Hironaka.HolomorphicIdealSheaves DerivativeIdeal DerivativeIdealAlong
  DerivativeIdealAlongEtale DerivativeIdealAlongCoherent HadamardBridge RelativePrincipalizationSpan InvertibleIdealQuotient
variable {n m : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel m) M'] [IsComplexManifold m M']
  {φ : M'→M} {ψ : M→M'}

private theorem fieldDeriv_sub {e : ComplexChart n M} {ξ : Fin n→M→ℂ} {x : M}
    (hx : x∈e.val.source) {f g : M→ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    fieldDeriv e ξ (fun q=>f q-g q)=ᶠ[𝓝 x] fun q=>fieldDeriv e ξ f q-fieldDeriv e ξ g q := by
  filter_upwards [e.val.open_source.mem_nhds hx,hf.eventually_nhds,hg.eventually_nhds] with q hq hfq hgq
  have hf' :=(eventually_differentiableAt_comp_symm e hq hfq).self_of_nhds
  have hg' :=(eventually_differentiableAt_comp_symm e hq hgq).self_of_nhds
  have hpart (v : ComplexModel n) : chartDeriv e v (fun z=>f z-g z) q=
      chartDeriv e v f q-chartDeriv e v g q:=by
    change fderiv ℂ ((f ∘ e.val.symm)-(g ∘ e.val.symm)) (e.val q) v=_
    rw [fderiv_sub hf' hg']
    rfl
  simp only [fieldDeriv,hpart,mul_sub,Finset.sum_sub_distrib]

section Retraction
variable
    (hφ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ φ)
    (hψ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ ψ)
    (hLeft : ∀y,ψ (φ y)=y) (N : Set M) (hN : ∀q∈N,φ (ψ q)=q)

include hφ hψ hLeft in
omit [IsComplexManifold n M] [IsComplexManifold m M'] in
private theorem splitAt (y : M') : HironakaActualSplitImmersionFields.SplitAt (n:=n) (m:=m) φ ψ y:=
  ⟨Eventually.of_forall fun p=>(hφ p).mdifferentiableAt (by simp),
    Eventually.of_forall fun q=>(hψ q).mdifferentiableAt (by simp),Eventually.of_forall hLeft⟩

include hψ hLeft in
omit [IsComplexManifold n M] [IsComplexManifold m M'] in
private theorem ψ_tendsto (y : M') : Tendsto ψ (𝓝 (φ y)) (𝓝 y):=by
  simpa only [hLeft] using (hψ (φ y)).continuousAt.tendsto

include hψ hLeft hN in
omit [IsComplexManifold n M] in
private theorem comp_vanishing {y : M'} {g : M'→ℂ}
    (hg : (vanishingIdeal (n:=m) (φ ⁻¹' N)).mem y g) :
    (vanishingIdeal (n:=n) N).mem (φ y) (g ∘ ψ) := by
  refine ⟨holomorphicAt_comp_map
    (Eventually.of_forall fun q=>(hψ q).mdifferentiableAt (by simp)) (by rw [hLeft];exact hg.1),?_⟩
  filter_upwards [(ψ_tendsto hψ hLeft y).eventually hg.2] with q hq hqN
  exact hq (by change φ (ψ q)∈N;rw [hN q hqN];exact hqN)

include hφ in
omit [IsComplexManifold m M'] in
private theorem comp_vanishing_preimage {y : M'} {g : M→ℂ}
    (hg : (vanishingIdeal (n:=n) N).mem (φ y) g) :
    (vanishingIdeal (n:=m) (φ ⁻¹' N)).mem y (g ∘ φ) := by
  refine ⟨holomorphicAt_comp_map
    (Eventually.of_forall fun p=>(hφ p).mdifferentiableAt (by simp)) hg.1,?_⟩
  filter_upwards [(hφ y).continuousAt.eventually hg.2] with p hp hpN
  exact hp hpN

include hφ hψ hLeft hN in
private theorem tangent_transfer {y : M'} {e : ComplexChart n M} {e' : ComplexChart m M'}
    {ξ : Fin n→M→ℂ} (hy' : y∈e'.val.source) (hξ : IsTangentField N e ξ (φ y)) :
    IsTangentField (φ ⁻¹' N) e'
      (HironakaActualSplitImmersionFields.transferField φ ψ e e' ξ) y := by
  let hS:=splitAt hφ hψ hLeft y
  have hHol :=HironakaActualSplitImmersionFields.holomorphicAt_transferField hS hy'
    hξ.mem_source hξ.holomorphicAt
  refine ⟨hy',hHol,?_⟩
  intro g hg
  have hv:=comp_vanishing hψ hLeft N hN hg
  have hd:=comp_vanishing_preimage hφ N (hξ.preserves (g ∘ ψ) hv)
  have ht:=HironakaActualSplitImmersionFields.fieldDeriv_transfer hS hy' hξ.mem_source ξ hg.1
  refine ⟨holomorphicAt_fieldDeriv hy' hHol hg.1,?_⟩
  filter_upwards [hd.2,ht] with p hp hpt hpN
  rw [hpt]
  exact hp hpN

include hφ hψ hLeft in
private theorem push_field_deriv {y : M'} {e : ComplexChart n M} {e' : ComplexChart m M'}
    (hy : φ y∈e.val.source) (hy' : y∈e'.val.source) (η : Fin m→M'→ℂ)
    {g : M→ℂ} (hg : HolomorphicAt n g (φ y)) :
    ∀ᶠq in 𝓝 (φ y),φ (ψ q)=q →
      fieldDeriv e (HironakaActualSplitImmersionFields.transferField ψ φ e' e η) g q=
        fieldDeriv e' η (g ∘ φ) (ψ q) := by
  have hchain : ∀j,chartDeriv e' (EuclideanSpace.single j 1) (g ∘ φ)=ᶠ[𝓝 y]
      fun p=>∑i,HironakaActualSplitImmersionFields.chainCoeff e e' φ
        (EuclideanSpace.single j 1) i p * chartDeriv e (EuclideanSpace.single i 1) g (φ p):=
    fun j=>HironakaActualSplitImmersionFields.chartDeriv_comp_eventuallyEq_sum e e'
      (Eventually.of_forall fun p=>(hφ p).mdifferentiableAt (by simp)) hy' hy hg _
  filter_upwards [(ψ_tendsto hψ hLeft y).eventually (eventually_all.2 hchain)] with q hq hfix
  simp only [fieldDeriv,HironakaActualSplitImmersionFields.transferField,hq,hfix,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>by ring

include hφ hψ hLeft in
private theorem push_field_holomorphic {y : M'} {e : ComplexChart n M} {e' : ComplexChart m M'}
    (hy : φ y∈e.val.source) (hy' : y∈e'.val.source)
    {η : Fin m→M'→ℂ} (hη : ∀j,HolomorphicAt m (η j) y) (i : Fin n) :
    HolomorphicAt n (HironakaActualSplitImmersionFields.transferField ψ φ e' e η i) (φ y) := by
  apply HolomorphicAt.sum
  intro j _
  apply HolomorphicAt.mul
  · exact holomorphicAt_comp_map (Eventually.of_forall fun q=>(hψ q).mdifferentiableAt (by simp))
      (by rw [hLeft];exact hη j)
  · exact holomorphicAt_comp_map
      (f:=HironakaActualSplitImmersionFields.chainCoeff e e' φ (EuclideanSpace.single j 1) i)
      (Eventually.of_forall fun q=>(hψ q).mdifferentiableAt (by simp)) (by
        rw [hLeft]
        exact HironakaActualSplitImmersionFields.holomorphicAt_chainCoeff e e'
          (Eventually.of_forall fun p=>(hφ p).mdifferentiableAt (by simp)) hy' hy _ i)

include hφ hψ hLeft hN in
private theorem tangent_push {y : M'} {e : ComplexChart n M} {e' : ComplexChart m M'}
    {η : Fin m→M'→ℂ} (hy : φ y∈e.val.source) (hη : IsTangentField (φ ⁻¹' N) e' η y) :
    IsTangentField N e (HironakaActualSplitImmersionFields.transferField ψ φ e' e η) (φ y) := by
  have hHol:=push_field_holomorphic hφ hψ hLeft hy hη.mem_source hη.holomorphicAt
  refine ⟨hy,hHol,?_⟩
  intro g hg
  have hv:=comp_vanishing_preimage hφ N hg
  have hd:=hη.preserves (g ∘ φ) hv
  have ht:=push_field_deriv hφ hψ hLeft hy hη.mem_source η hg.1
  refine ⟨holomorphicAt_fieldDeriv hy hHol hg.1,?_⟩
  filter_upwards [(ψ_tendsto hψ hLeft y).eventually hd.2,ht] with q hq hqt hqN
  rw [hqt (hN q hqN)]
  exact hq (by change φ (ψ q)∈N;rw [hN q hqN];exact hqN)

include hφ hψ hLeft hN in
private theorem pullback_derivIdealAlong_le (I : GermIdeal n M)
    (hI : ∀x g,I.mem x g → HolomorphicAt n g x) :
    (GermIdeal.pullback (m:=m) φ (derivIdealAlong N I)).Le
      (derivIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m:=m) φ I)) := by
  intro y g hg
  let hS:=splitAt hφ hψ hLeft y
  have hφev:=hS.mdiff
  have hcompmem {J : GermIdeal n M} {b : M→ℂ} (hb : J.mem (φ y) b)
      (hbhol : HolomorphicAt n b (φ y)) :
      (GermIdeal.pullback (m:=m) φ J).mem y (b ∘ φ):=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨b,hb,rfl⟩ (holomorphicAt_comp_map hφev hbhol))
  refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
  rintro s ⟨b,hb,rfl⟩
  obtain ⟨_hbhol,K,t,c,ht,hc,hsum⟩:=hb
  have hcomp : b ∘ φ=ᶠ[𝓝 y] fun p=>∑k,(c k ∘ φ) p*(t k ∘ φ) p:=
    (hφ y).continuousAt.eventually hsum
  refine DerivativeIdeal.isInSpanAt_congr ?_ hcomp.symm
  refine IsInSpanAt.sum Finset.univ fun k _=>IsInSpanAt.mul_left (holomorphicAt_comp_map hφev (hc k)) ?_
  have hgen1 {u : M'→ℂ}
      (hu : DerivGenAlong (φ ⁻¹' N) (GermIdeal.pullback (m:=m) φ I) y u)
      (hhu : HolomorphicAt m u y) :
      IsInSpanAt (n:=m) (DerivGenAlong (φ ⁻¹' N) (GermIdeal.pullback (m:=m) φ I) y) y u:=
    isInSpanAt_self hu hhu
  rcases ht k with htk|htk|⟨e,ξ,f,hξ,hf,htk⟩
  · exact hgen1 (Or.inl (hcompmem htk (hI _ _ htk))) (holomorphicAt_comp_map hφev (hI _ _ htk))
  · have hv:=comp_vanishing_preimage hφ N htk
    exact hgen1 (Or.inr (Or.inl hv)) hv.1
  · rw [htk]
    let e':=complexChartAt (n:=m) y
    have hy' : y∈e'.val.source:=mem_complexChartAt_source y
    have hfhol:=hI _ _ hf
    have hfφ : HolomorphicAt m (f ∘ φ) y:=holomorphicAt_comp_map hφev hfhol
    have hTan:=tangent_transfer hφ hψ hLeft N hN hy' hξ
    have htField:=HironakaActualSplitImmersionFields.fieldDeriv_transfer hS hy' hξ.mem_source ξ hfφ
    have hfψ : HolomorphicAt n ((f ∘ φ) ∘ ψ) (φ y):=
      holomorphicAt_comp_map (Eventually.of_forall fun q=>(hψ q).mdifferentiableAt (by simp))
        (by rw [hLeft];exact hfφ)
    let δ : M→ℂ:=fun q=>f q-((f ∘ φ) ∘ ψ) q
    have hδ : (vanishingIdeal (n:=n) N).mem (φ y) δ:=by
      refine ⟨?_,Eventually.of_forall fun q hqN=>?_⟩
      · filter_upwards [hfhol,hfψ] with q hq hq'
        exact hq.sub hq'
      · simp only [δ,Function.comp_apply,hN q hqN,sub_self]
    have hDδ:=comp_vanishing_preimage hφ N (hξ.preserves δ hδ)
    have hSub:=(hφ y).continuousAt.eventually (fieldDeriv_sub (ξ:=ξ) hξ.mem_source hfhol hfψ)
    have hNative :=hgen1 (Or.inr (Or.inr ⟨e',_,f ∘ φ,hTan,hcompmem hf hfhol,rfl⟩))
      (holomorphicAt_fieldDeriv hy' hTan.holomorphicAt hfφ)
    have hVanish :=(vanishingIdeal_le_derivIdealAlong (N:=φ ⁻¹' N)
      (𝔞:=GermIdeal.pullback (m:=m) φ I) y _ hDδ)
    refine DerivativeIdeal.isInSpanAt_congr (IsInSpanAt.add hNative hVanish) ?_
    filter_upwards [htField,hSub] with p hp hpSub
    simp only [Function.comp_apply]
    rw [hp,hpSub]
    ring

include hφ hψ hLeft hN in
private theorem derivIdealAlong_pullback_le (I : GermIdeal n M)
    (hI : ∀x g,I.mem x g → HolomorphicAt n g x) :
    (derivIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m:=m) φ I)).Le
      (GermIdeal.pullback (m:=m) φ (derivIdealAlong N I)) := by
  intro y g hg
  have hφev:= (splitAt hφ hψ hLeft y).mdiff
  have hpb {b : M→ℂ} (hb : (derivIdealAlong N I).mem (φ y) b) :
      IsInSpanAt (n:=m) (fun s=>∃a,(derivIdealAlong N I).mem (φ y) a ∧ s=a ∘ φ) y (b ∘ φ):=
    isInSpanAt_self ⟨b,hb,rfl⟩ (holomorphicAt_comp_map hφev hb.1)
  refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ hg)
  rintro t (ht|ht|⟨e',η,f',hη,hf',rfl⟩)
  · exact (GermIdeal.mem_pullback_iff.mp ht).mono fun s ⟨a,ha,hs⟩=>
      ⟨a,le_derivIdealAlong hI _ _ ha,hs⟩
  · have hv:=comp_vanishing hψ hLeft N hN ht
    have heq : (t ∘ ψ) ∘ φ=ᶠ[𝓝 y] t:=Eventually.of_forall fun p=>by simp [hLeft]
    exact DerivativeIdeal.isInSpanAt_congr (hpb (vanishingIdeal_le_derivIdealAlong _ _ hv)) heq
  · obtain ⟨-,K,s,c,hs,hc,hsum⟩:=GermIdeal.mem_pullback_iff.mp hf'
    choose b hb hsb using hs
    have hbhol : ∀k,HolomorphicAt n (b k) (φ y):=fun k=>hI _ _ (hb k)
    have hsφ : ∀k,HolomorphicAt m (s k) y:=fun k=>hsb k ▸ holomorphicAt_comp_map hφev (hbhol k)
    have hprod:=fieldDeriv_eventuallyEq_sum_mul (ξ:=η) hη.mem_source hc hsφ hsum
    refine DerivativeIdeal.isInSpanAt_congr ?_ hprod.symm
    refine IsInSpanAt.sum Finset.univ fun k _=>IsInSpanAt.add ?_ ?_
    · refine IsInSpanAt.mul_left (holomorphicAt_fieldDeriv hη.mem_source hη.holomorphicAt (hc k)) ?_
      rw [hsb k]
      exact hpb (le_derivIdealAlong hI _ _ (hb k))
    · refine IsInSpanAt.mul_left (hc k) ?_
      let e:=complexChartAt (n:=n) (φ y)
      have hey : φ y∈e.val.source:=mem_complexChartAt_source (φ y)
      let ξ:=HironakaActualSplitImmersionFields.transferField ψ φ e' e η
      have hTan : IsTangentField N e ξ (φ y):=tangent_push hφ hψ hLeft N hN hey hη
      have htr:=(hφ y).continuousAt.eventually
        (push_field_deriv hφ hψ hLeft hey hη.mem_source η (hbhol k))
      have heq : (fieldDeriv e ξ (b k)) ∘ φ=ᶠ[𝓝 y] fieldDeriv e' η (s k):=by
        filter_upwards [htr] with p hp
        change fieldDeriv e ξ (b k) (φ p)=fieldDeriv e' η (s k) p
        rw [hp (congrArg φ (hLeft p)),hLeft p,hsb k]
      refine DerivativeIdeal.isInSpanAt_congr (hpb ?_) heq
      exact isInSpanAt_self (Or.inr (Or.inr ⟨e,ξ,b k,hTan,hb k,rfl⟩))
        (holomorphicAt_fieldDeriv hey hTan.holomorphicAt (hbhol k))

include hφ hψ hLeft hN in
theorem pullback_derivIdealAlong (I : GermIdeal n M)
    (hI : ∀x g,I.mem x g → HolomorphicAt n g x) :
    GermIdeal.pullback (m:=m) φ (derivIdealAlong N I)=
      derivIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m:=m) φ I) :=
  GermIdeal.ext (funext fun y=>funext fun g=>propext
    ⟨pullback_derivIdealAlong_le hφ hψ hLeft N hN I hI y g,
      derivIdealAlong_pullback_le hφ hψ hLeft N hN I hI y g⟩)

include hφ hψ hLeft hN in
theorem pullback_iterDerivIdealAlong (I : GermIdeal n M)
    (hI : ∀x g,I.mem x g → HolomorphicAt n g x) :
    ∀q,GermIdeal.pullback (m:=m) φ (iterDerivIdealAlong N I q)=
      iterDerivIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m:=m) φ I) q
  | 0=>rfl
  | q+1=>by
    rw [iterDerivIdealAlong,pullback_derivIdealAlong hφ hψ hLeft N hN _
      (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong hI q),
      pullback_iterDerivIdealAlong I hI q,iterDerivIdealAlong]

end Retraction
end
end Hironaka.HironakaActualSplitImmersionDerivativeIdeals
