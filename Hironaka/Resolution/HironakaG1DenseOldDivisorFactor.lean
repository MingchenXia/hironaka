import Hironaka.Resolution.HironakaNormalCrossingsFiniteMarkedCompletion
import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon
import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked
import Hironaka.Analytic.HolomorphicGermNoetherian
import Mathlib.RingTheory.Nakayama

/-! Actual boundary density excludes old factors of the ORIGINAL weighted record.
Blueprint FIRST: hironaka-g1-dense-old-divisor-factor.tex.
Whole vanishing/colon/stalk ideals and actual generator powers are retained. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1DenseOldDivisorFactor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus
  IdealWeightPowers IdealOrderArithmetic GermIdealOrder DivisorExponent DivisorExponentAlong
  NormalCrossings HironakaNormalCrossingsFiniteMarkedCompletion
  HironakaSmoothSubmersionGermIdealColon HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedCoefficientCompression MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers ResolutionInvariantSpec

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- Original density restricts to the SAME genuine local holomorphic neighbourhood. -/
theorem eventually_zero_of_dense_diff {W H : Set X} (hDense : W⊆closure (W\H))
    {x : X} {f : X→ℂ} (hf : HolomorphicAt n f x)
    (hz : ∀ᶠy in 𝓝 x,y∈W\H→f y=0) : ∀ᶠy in 𝓝 x,y∈W→f y=0 := by
  have hLocal : ∀ᶠy in 𝓝 x,ContinuousAt f y∧(y∈W\H→f y=0) := by
    filter_upwards [hf,hz] with y hy hyz
    exact ⟨hy.continuousAt,hyz⟩
  obtain ⟨V,hV,hVo,hxV⟩:=mem_nhds_iff.mp hLocal
  let U : Opens X:=⟨V,hVo⟩
  have hfc : Continuous (fun y : U=>f y.val) := continuous_iff_continuousAt.mpr fun y=>
    (hV y.property).1.comp continuous_subtype_val.continuousAt
  have hClosed : IsClosed {y : U|f y.val=0}:=isClosed_eq hfc continuous_const
  have hZero : (Subtype.val : U→X) ⁻¹' (W\H)⊆{y : U|f y.val=0}:=
    fun y hy=>(hV y.property).2 hy
  filter_upwards [hVo.mem_nhds hxV] with y hy hyW
  let yU : U:=⟨y,hy⟩
  have hd : yU∈closure ((Subtype.val : U→X) ⁻¹' (W\H)) :=
    (Set.ext_iff.mp (U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (W\H)) yU).mp (hDense hyW)
  have hmem:=closure_mono hZero hd
  rw [hClosed.closure_eq] at hmem
  exact hmem

/-- Density INTERNALLY gives the entire original colon equality. -/
theorem colon_vanishingIdeal_eq_of_dense (W H : Set X) (hH : IsClosed H)
    (hHC : (vanishingIdeal (n:=n) H).IsCoherent) (hDense : W⊆closure (W\H)) :
    colon (vanishingIdeal (n:=n) W) (vanishingIdeal (n:=n) H)=vanishingIdeal (n:=n) W := by
  apply GermIdeal.ext
  funext x f
  apply propext
  constructor
  · intro hf
    obtain ⟨U,hU,hxU,r,G,hG,hgen⟩:=hHC x
    have hGh (i : Fin r) : HolomorphicAt n (G i) x:=
      DivisorExponent.holomorphicAt_of_mdifferentiableOn_open hU (hG i) hxU
    have hGm (i : Fin r) : (vanishingIdeal (n:=n) H).mem x (G i):=
      (hgen x hxU (G i)).mpr (isInSpanAt_self ⟨i,rfl⟩ (hGh i))
    have hProducts : ∀i : Fin r,∀ᶠy in 𝓝 x,y∈W→G i y*f y=0:=
      fun i=>(hf.2 (G i) (hGm i)).2
    have hOff : ∀ᶠy in 𝓝 x,y∈W\H→f y=0 := by
      filter_upwards [hU.mem_nhds hxU,eventually_all.mpr hProducts] with y hyU hy hyW
      by_contra hfy
      have hGs : ∀i : Fin r,G i y=0:=fun i=>(mul_eq_zero.mp (hy i hyW.1)).resolve_right hfy
      have hUnit : (vanishingIdeal (n:=n) H).mem y (fun _=>1) := by
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [hH.isOpen_compl.mem_nhds hyW.2] with z hz hzH
        exact (hz hzH).elim
      obtain ⟨_hh,K,s,a,hs,_ha,he⟩:=(hgen y hyU (fun _=>1)).mp hUnit
      have hEval:=he.self_of_nhds
      have hSum : (∑i : Fin K,a i y*s i y)=0 := Finset.sum_eq_zero fun i _=>by
        obtain ⟨j,hj⟩:=hs i
        rw [←hj,hGs j,mul_zero]
      exact one_ne_zero (hEval.trans hSum)
    exact ⟨hf.1,eventually_zero_of_dense_diff hDense hf.1 hOff⟩
  · intro hf
    refine ⟨hf.1,fun g hg=>⟨hg.1.mul hf.1,?_⟩⟩
    filter_upwards [hf.2] with y hy hyW
    rw [hy hyW,mul_zero]

private theorem adaptedIdeal_eq_singleton (I : GermIdeal n X) (hI : I.IsCoherent)
    (x : X) (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) (h : X→ℂ)
    (hh : HolomorphicAt n h x)
    (hgen : ∀F,I.mem x F↔IsInSpanAt (n:=n) (·=h) x F) :
    adaptedIdeal I x Φ h0=Ideal.span {adaptedGerm x Φ h0 h hh} := by
  let G : Fin 1→X→ℂ:=fun _=>h
  have hg : ∀i,HolomorphicAt n (G i) x:=fun _=>hh
  have hr : range G={h}:=by ext F; simp [G]
  ext g
  obtain ⟨F,hF,rfl⟩:=exists_original_adapted_representative x Φ h0 g
  rw [mem_adaptedIdeal_iff I hI x Φ h0 F hF]
  have hb := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff x Φ h0 G F).trans
    (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span _
      (fun i=>(holomorphic_adapted_iff x Φ h0 (G i)).mpr (hg i))
      ((holomorphic_adapted_iff x Φ h0 F).mpr hF))
  rw [hr] at hb
  change IsInSpanAt (n:=n) (·∈({h} : Set (X→ℂ))) x F↔adaptedGerm x Φ h0 F hF∈
    Ideal.span (range (fun _ : Fin 1=>adaptedGerm x Φ h0 h hh)) at hb
  simpa only [mem_singleton_iff,range_const] using (hgen F).trans hb

private theorem eventually_zero_of_adaptedGerm_eq_zero (x : X)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (F : X→ℂ) (hF : HolomorphicAt n F x)
    (hz : adaptedGerm x Φ h0 F hF=0) : ∀ᶠy in 𝓝 x,F y=0 := by
  have he : (fun w=>F (GiraudAlong.flatInv Φ w))=ᶠ[𝓝 (0 : ComplexModel n)] (fun _=>0) := by
    have hz' : adaptedGerm x Φ h0 F hF=HolGerm.mk (fun _=>0)
        (Eventually.of_forall fun _=>differentiableAt_const (0 : ℂ)) := hz.trans (by rfl)
    exact HolGerm.mk_eq_mk_iff.mp hz'
  have ht : Tendsto (GiraudAlong.flatMap Φ) (𝓝 x) (𝓝 (0 : ComplexModel n)) := by
    have ht := (HomogenizedGlueingAlong.continuousAt_flatMap
      (BlowupFlatCoordinates.mem_flatDomain_self Φ)).tendsto
    simpa only [GiraudAlong.flatMap,h0] using ht
  filter_upwards [ht.eventually he,(BlowupFlatCoordinates.isOpen_flatDomain Φ).mem_nhds
    (BlowupFlatCoordinates.mem_flatDomain_self Φ)] with y hy hyD
  rwa [GiraudAlong.flatInv_flatMap hyD] at hy

private theorem ideal_eq_bot_of_colon_eq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R) (a : R) (ha : a∈IsLocalRing.maximalIdeal R)
    (hle : J≤Ideal.span {a}) (hc : J.colon (Ideal.span {a})=J) : J=⊥ := by
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {a}) J
    (Ideal.fg_of_isNoetherianRing J) ?_ ?_
  · rw [Ideal.smul_eq_mul]
    intro b hb
    obtain ⟨c,hcb⟩:=Ideal.mem_span_singleton.mp (hle hb)
    have hcJ : c∈J := by
      rw [←hc,Ideal.mem_colon_span_singleton,mul_comm,←hcb]
      exact hb
    rw [hcb]
    exact Ideal.mul_mem_mul (Ideal.subset_span (mem_singleton a)) hcJ
  · apply Ideal.span_le.mpr
    intro b hb
    rcases mem_singleton_iff.mp hb with rfl
    exact IsLocalRing.maximalIdeal_le_jacobson ⊥ ha

/-- Actual density, actual SNC and the ORIGINAL nonzero ideal exclude an entire old factor. -/
theorem not_stalk_vanishing_le_of_dense (W : Set X)
    (hW : (vanishingIdeal (n:=n) W).IsCoherent) (E : List (Set X))
    (hE : IsSNCDivisor n E) (i : Fin E.length) (hDense : W⊆closure (W\E.get i))
    (x : X) (hx : x∈E.get i) (hne : IsNonzeroAt (vanishingIdeal (n:=n) W) x) :
    ¬∀F,(vanishingIdeal (n:=n) W).mem x F→(vanishingIdeal (n:=n) (E.get i)).mem x F := by
  intro hle
  let I:=vanishingIdeal (n:=n) W
  let H:=vanishingIdeal (n:=n) (E.get i)
  have hHI:=isInvertible_vanishingIdeal_snc_member hE i
  have hHC:=DivisorMetric.isCoherent_of_isInvertible hHI
  obtain ⟨U,hU,hxU,h,hh,_hnon,hgen⟩:=hHI x
  have hhol : HolomorphicAt n h x:=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hh hxU
  have hmem : H.mem x h:=(hgen x hxU h).mpr (isInSpanAt_self rfl hhol)
  obtain ⟨_hClosed,_hInt,hreg⟩:=snc_member_codimOne_geometry hE i
  obtain ⟨k,hk,_hkn⟩:=hreg x hx
  obtain ⟨_hk,_hx,Φ,_hsrc,h0,_hflat⟩:=hk
  let J:=adaptedIdeal I x Φ h0
  let L:=adaptedIdeal H x Φ h0
  let a:=adaptedGerm x Φ h0 h hhol
  have hLa : L=Ideal.span {a}:=adaptedIdeal_eq_singleton H hHC x Φ h0 h hhol (hgen x hxU)
  have hJL : J≤L := by
    apply Ideal.span_le.mpr
    rintro g ⟨F,hF,hIF,rfl⟩
    exact Ideal.subset_span ⟨F,hF,hle F hIF,rfl⟩
  have hc : J.colon L=J := by
    rw [←adaptedIdeal_colon_eq I H hW hHC x Φ h0]
    rw [colon_vanishingIdeal_eq_of_dense W (E.get i) (hE.1 _ (List.get_mem _ _)) hHC hDense]
  have ha : a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
    rw [HolGerm.mem_maximalIdeal_iff]
    change HolGerm.eval (adaptedGerm x Φ h0 h hhol)=0
    unfold adaptedGerm
    rw [HolGerm.eval_mk]
    change h (GiraudAlong.flatInv Φ 0)=0
    rw [GiraudAlong.flatInv_zero h0]
    exact hmem.2.self_of_nhds hx
  let : IsNoetherianRing (HolGerm (ComplexModel n)):=isNoetherianRing_holGerm_euclidean n
  have hJ0 : J=⊥:=ideal_eq_bot_of_colon_eq J a ha (hLa ▸ hJL) (hLa ▸ hc)
  obtain ⟨F,hF,hfreq⟩:=hne
  have hFhol:=GermIdeal.IsCoherent.holomorphicAt_mem hW hF
  have hFg : adaptedGerm x Φ h0 F hFhol∈J:=
    (mem_adaptedIdeal_iff I hW x Φ h0 F hFhol).mpr hF
  rw [hJ0,Ideal.mem_bot] at hFg
  have hz:=eventually_zero_of_adaptedGerm_eq_zero x Φ h0 F hFhol hFg
  exact hfreq (hz.mono fun _ hy hne=>hne hy)

/-- The original coherent divisibility predicate, not merely the support, is excluded. -/
theorem not_isDivNear_vanishingIdeal_of_dense (W : Set X)
    (hW : (vanishingIdeal (n:=n) W).IsCoherent) (E : List (Set X))
    (hE : IsSNCDivisor n E) (i : Fin E.length) (hDense : W⊆closure (W\E.get i))
    (x : X) (hx : x∈E.get i) (hne : IsNonzeroAt (vanishingIdeal (n:=n) W) x) :
    ¬IsDivNear n (vanishingIdeal (n:=n) W) (E.get i) 1 x := by
  intro hdiv
  obtain ⟨k,hk,_hkn⟩:=(snc_member_codimOne_geometry hE i).2.2 x hx
  apply not_stalk_vanishing_le_of_dense W hW E hE i hDense x hx hne
  intro F hF
  have hf:=(isDivNear_iff hW hk).mp hdiv F hF
  have hHC:=DivisorMetric.isCoherent_of_isInvertible (isInvertible_vanishingIdeal_snc_member hE i)
  rwa [FactorizationFromResolution.idealPow_one_of_isCoherent hHC] at hf

/-- Positive generator powers still belong to the ENTIRE original reduced ideal. -/
theorem weightedFunctionIdeal_le_vanishingIdeal {ι : Type*} [Fintype ι]
    (W : Set X) (w : ι→ℕ) (hw : ∀i,0<w i) (c : ι→X→ℂ)
    (hc : ∀i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    (hgen : ∀x F,(vanishingIdeal (n:=n) W).mem x F↔IsInSpanAt (n:=n) (·∈range c) x F) :
    (weightedFunctionIdeal (n:=n) w c).Le (vanishingIdeal (n:=n) W) := by
  intro x F hF
  apply BlowupStrictIdeal.mem_vanishingIdeal_of_isInSpanAt' ?_ hF
  rintro G ⟨i,rfl⟩
  have hci : (vanishingIdeal (n:=n) W).mem x (c i):=
    (hgen x (c i)).mpr (isInSpanAt_self ⟨i,rfl⟩ (Eventually.of_forall (hc i)))
  refine ⟨Eventually.of_forall ((hc i).pow _),?_⟩
  filter_upwards [hci.2] with y hy hyW
  rw [hy hyW,zero_pow (Nat.ne_of_gt (compressionExponent_pos w hw i))]

/-- The ACTUAL ordinary weighted domain supplies nonzero original germs internally. -/
theorem vanishing_nonzero_of_weighted_domain {ι : Type*} [Fintype ι] {k : ℕ}
    (W : Set X) (E : List (Set X)) (w : ι→ℕ) (hw : ∀i,0<w i) (c : ι→X→ℂ)
    (hc : ∀i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    (hgen : ∀x F,(vanishingIdeal (n:=n) W).mem x F↔IsInSpanAt (n:=n) (·∈range c) x F)
    (hQ : IsInvDomain k (⟨univ,E,weightedFunctionIdeal w c,weightedCommonMark w⟩ : MarkedIdeal n X))
    (x : X) : IsNonzeroAt (vanishingIdeal (n:=n) W) x := by
  obtain ⟨F,hF,hfreq⟩:=hQ.isNonzeroAlongAt x (mem_univ x)
  exact ⟨F,weightedFunctionIdeal_le_vanishingIdeal W w hw c hc hgen x F hF,
    hfreq.mono fun _ hy=>hy.2⟩

/-- Whole positive-power membership and actual density exclude an old factor of J.
The hypotheses are genuine generator memberships; no desired divisibility conclusion is supplied. -/
theorem not_isDivNear_of_generator_powers_dense {ι : Type*} [Fintype ι]
    (W : Set X) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (c : ι→X→ℂ) (hc : ∀i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    (hgen : ∀x F,(vanishingIdeal (n:=n) W).mem x F↔IsInSpanAt (n:=n) (·∈range c) x F)
    (J : GermIdeal n X) (hJ : J.IsCoherent) (r : ι→ℕ)
    (_hr : ∀i,0<r i) (hPow : ∀i x,J.mem x (fun y=>c i y^r i))
    (i : Fin E.length) (hDense : W⊆closure (W\E.get i))
    (x : X) (hx : x∈E.get i) (hne : IsNonzeroAt (vanishingIdeal (n:=n) W) x) :
    ¬IsDivNear n J (E.get i) 1 x := by
  intro hDiv
  have hI : finiteFunctionIdeal (n:=n) c=vanishingIdeal (n:=n) W := by
    apply GermIdeal.ext
    funext y F
    exact propext (hgen y F).symm
  have hW : (vanishingIdeal (n:=n) W).IsCoherent:=hI ▸isCoherent_finiteFunctionIdeal c hc
  obtain ⟨k,hk,_hkn⟩:=(snc_member_codimOne_geometry hE i).2.2 x hx
  have hHC:=DivisorMetric.isCoherent_of_isInvertible (isInvertible_vanishingIdeal_snc_member hE i)
  have hci (j : ι) : (vanishingIdeal (n:=n) (E.get i)).mem x (c j) := by
    have hPowH:=(isDivNear_iff hJ hk).mp hDiv _ (hPow j x)
    rw [FactorizationFromResolution.idealPow_one_of_isCoherent hHC] at hPowH
    refine ⟨Eventually.of_forall (hc j),?_⟩
    filter_upwards [hPowH.2] with y hy hyH
    exact eq_zero_of_pow_eq_zero (hy hyH)
  apply not_stalk_vanishing_le_of_dense W hW E hE i hDense x hx hne
  intro F hF
  apply BlowupStrictIdeal.mem_vanishingIdeal_of_isInSpanAt' ?_ ((hgen x F).mp hF)
  rintro G ⟨j,rfl⟩
  exact hci j

/-- Every literal old slot of the original weighted record has native exponent zero. -/
theorem weighted_divExpAlong_eq_zero_of_dense {ι : Type*} [Fintype ι] {k : ℕ}
    (W : Set X) (E : List (Set X)) (w : ι→ℕ) (hw : ∀i,0<w i) (c : ι→X→ℂ)
    (hc : ∀i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    (hgen : ∀x F,(vanishingIdeal (n:=n) W).mem x F↔IsInSpanAt (n:=n) (·∈range c) x F)
    (hDense : W⊆closure (W\⋃H∈E,H))
    (hQ : IsInvDomain k (⟨univ,E,weightedFunctionIdeal w c,weightedCommonMark w⟩ : MarkedIdeal n X))
    (H : Set X) (hH : H∈E) (x : X) :
    divExpAlong n univ (weightedFunctionIdeal w c) H x=0 := by
  rw [divExpAlong_univ]
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp hH
  subst H
  have hE:=hQ.isWellFormed.isSNCDivisor
  have hD : W⊆closure (W\E.get i) := by
    apply hDense.trans (closure_mono ?_)
    rintro y ⟨hyW,hyE⟩
    refine ⟨hyW,fun hyH=>hyE ?_⟩
    exact mem_iUnion.mpr ⟨E.get i,mem_iUnion.mpr ⟨List.get_mem _ _,hyH⟩⟩
  by_cases hx : x∈E.get i
  · have hnot:=not_isDivNear_of_generator_powers_dense W E hE c hc hgen
      (weightedFunctionIdeal w c) hQ.isWellFormed.isCoherent
      (fun j=>weightedCommonMark w/w j) (compressionExponent_pos w hw)
      (fun j y=>isInSpanAt_self ⟨j,rfl⟩ (Eventually.of_forall ((hc j).pow _)))
      i hD x hx (vanishing_nonzero_of_weighted_domain W E w hw c hc hgen hQ x)
    by_contra hne
    exact hnot ((isDivNear_divExp (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem
      hQ.isWellFormed.isCoherent hg) x).mono (Nat.one_le_iff_ne_zero.mpr hne))
  · have hnone : ¬∃e,¬IsDivNear n (weightedFunctionIdeal w c) (E.get i) (e+1) x := by
      rintro ⟨e,he⟩
      exact he (isDivNear_of_notMem (hE.1 _ (List.get_mem _ _)) hx (e+1))
    simp only [divExp,dif_neg hnone]

end
end Hironaka.HironakaG1DenseOldDivisorFactor
