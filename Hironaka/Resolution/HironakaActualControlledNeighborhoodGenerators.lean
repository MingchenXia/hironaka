import Hironaka.Resolution.HironakaActualCurrentMarkedFunctionSquares
import Hironaka.Resolution.HironakaActualGlobalInheritedCut
import Hironaka.Resolution.HironakaActualAnalyticNearbyVertexGenerators

/-! The actual coherent geometric ideal, in its genuine chart, is generated
on one neighborhood by the SAME given representatives of its entire origin
generators. No neighborhood equality is supplied. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualControlledNeighborhoodGenerators
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations OkaCoherence
 HironakaSmoothCentreCoherentDomain HironakaSmoothSubmersionGermIdealColon
 HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalAnalyticGraphQuotient
 HironakaActualLocalStrictSaturation HironakaRelativeNormalCoherentSaturation
 HironakaActualAnalyticNearbyVertexGenerators RelativePrincipalizationSpan
 InvertibleIdealQuotient
variable {n : ℕ}

/-- The literal flattened sheaf has exactly the entire adapted ideal at zero. -/
theorem actual_flattened_origin_eq_adapted
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (A : GermIdeal n X) (hA : A.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    originalCoherentOriginIdeal (actualFlattenedOriginalSheaf A x Φ)=adaptedIdeal A x Φ h0 := by
  have hz:=actualFlatteningInverseMap_zero x Φ h0
  let ψ:=actualFlatteningInverseMap x Φ
  have hψ0 : ψ 0=x:=hz
  have hS : ∀f,(∃F,A.mem (ψ 0) F ∧ f=F ∘ ψ) → HolAt f 0 := by
    rintro f ⟨F,hF,rfl⟩
    have hFx:A.mem x F:=by simpa only [hψ0] using hF
    exact (holomorphic_adapted_iff x Φ h0 F).mpr (holomorphicAt_of_mem_coherent A hA hFx)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hAf,rfl⟩
    apply whole_origin_span_mem _ _ hS ?_ hf (GermIdeal.mem_pullback_iff.mp hAf)
    rintro s ⟨F,hF,rfl⟩
    have hFx:A.mem x F:=by simpa only [hψ0] using hF
    apply Ideal.subset_span
    exact ⟨F,holomorphicAt_of_mem_coherent A hA hFx,hFx,rfl⟩
  · apply Ideal.span_le.mpr
    rintro g ⟨F,hF,hAF,rfl⟩
    have hp : HolAt (F ∘ ψ) 0:=(holomorphic_adapted_iff x Φ h0 F).mpr hF
    apply Ideal.subset_span
    refine ⟨F ∘ ψ,hp,?_,rfl⟩
    apply GermIdeal.mem_pullback_iff.mpr
    exact isInSpanAt_self ⟨F,by change A.mem (ψ 0) F; rw [hψ0]; exact hAF,rfl⟩
      (hp.mono fun _ hy=>hy.mdifferentiableAt)

/-- Original coherence gives local finite generation only on the actual
target of the genuine chart. -/
theorem actual_flattened_local_fg
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (A : GermIdeal n X) (hA : A.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    IdealFGAt (actualFlattenedOriginalSheaf A x Φ).mem (0 : ComplexModel n) := by
  have hcoh:=coherentOn_actualFlattenedOriginalSheaf A hA x Φ hsrc
  obtain ⟨U,hU,h0U,_hUT,N,S,hS,hgen⟩:=hcoh 0 (actualFlattening_target_zero_mem x Φ h0)
  refine ⟨U,hU,h0U,Fin N,inferInstance,S,
    fun i=>mdifferentiableOn_iff_differentiableOn.mp (hS i),?_⟩
  intro y hy g
  rw [hgen y hy g,CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h=>h.differentiableAt),a,fun i=>(ha i).mono (fun _ h=>h.differentiableAt),he⟩
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h=>h.mdifferentiableAt),a,fun i=>(ha i).mono (fun _ h=>h.mdifferentiableAt),he⟩

/-- Entire generation of the origin ideal spreads to one actual neighborhood
using the SAME supplied holomorphic representatives, with no replacement. -/
theorem exists_actual_neighborhood_of_same_origin_generators
    {ι : Type} [Fintype ι] (A : GermIdeal n (ComplexModel n))
    (hA : IdealFGAt A.mem (0 : ComplexModel n))
    (f : ι → ComplexModel n → ℂ) (hf : ∀i,HolAt (f i) 0)
    (hspan : Ideal.span (range fun i=>HolGerm.mk (f i) (hf i))=originalCoherentOriginIdeal A) :
    ∃U : Set (ComplexModel n),IsOpen U ∧ (0 : ComplexModel n)∈U ∧
      (∀i,DifferentiableOn ℂ (f i) U) ∧ ∀y∈U,∀g,A.mem y g ↔ InSpanAt f y g := by
  obtain ⟨V,hVsub,hV,h0V⟩:=mem_nhds_iff.mp (eventually_all.mpr fun i=>(hf i).eventually)
  have hreg (i : ι) : DifferentiableOn ℂ (f i) V:=
    fun y hy=>(hVsub hy i).self_of_nhds.differentiableWithinAt
  have hJ : IdealFGAt (fun y g=>InSpanAt f y g) (0 : ComplexModel n):=
    ⟨V,hV,h0V,ι,inferInstance,f,hreg,fun _ _ _=>Iff.rfl⟩
  have hAhol (g : ComplexModel n → ℂ) (hg : A.mem 0 g) : HolAt g 0 := by
    obtain ⟨O,_hO,h0O,κ,hκ,s,_hs,hgen⟩:=hA
    let :=hκ
    exact ((hgen 0 h0O g).mp hg).1
  have hEq (g : ComplexModel n → ℂ) : A.mem 0 g ↔ InSpanAt f 0 g := by
    by_cases hg : HolAt g 0
    · rw [←mk_mem_origin_iff_of_local_fg A hA hg,←hspan]
      exact (inSpanAt_zero_iff_mem_origin_span f hf hg).symm
    · exact ⟨fun h=>(hg (hAhol g h)).elim,fun h=>(hg h.1).elim⟩
  obtain ⟨U,hU,h0U,he⟩:=exists_open_coherent_equality hA hJ hEq
  exact ⟨U∩V,hU.inter hV,⟨h0U,h0V⟩,fun i=>(hreg i).mono inter_subset_right,
    fun y hy=>he y hy.1⟩


private theorem pullback_local_comp
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (A : GermIdeal n X) (hA : A.IsCoherent) (ψ : ComplexModel n → X)
    (V : TopologicalSpace.Opens (ComplexModel n))
    (hψ : ∀z∈V,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ψ z) :
    GermIdeal.pullback (m:=n) (fun z : V=>ψ z) A=
      GermIdeal.pullback (m:=n) (Subtype.val : V → ComplexModel n) (GermIdeal.pullback (m:=n) ψ A) := by
  refine GermIdeal.ext (funext fun z=>funext fun g=>propext ⟨?_,?_⟩)
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg))
    rintro _ ⟨F,hF,rfl⟩
    have hV : ∀ᶠw in 𝓝 (z : ComplexModel n),w∈V:=V.isOpen.mem_nhds z.property
    have hp : ∀ᶠw in 𝓝 (z : ComplexModel n),
        MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ψ w :=
      hV.mono fun w hw=>hψ w hw
    have hh : HolomorphicAt n (F ∘ ψ) (z : ComplexModel n):=
      HadamardBridge.holomorphicAt_comp_map hp (holomorphicAt_of_mem_coherent A hA hF)
    exact ⟨F ∘ ψ,GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨F,hF,rfl⟩ hh),rfl⟩
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg))
    rintro _ ⟨F,hF,rfl⟩
    refine IsInSpanAt.mono ?_ (GermIdealPullbackCalculus.isInSpanAt_comp
      (contMDiff_subtype_val (U:=V)) (GermIdeal.mem_pullback_iff.mp hF))
    rintro _ ⟨a,⟨F,hF,rfl⟩,rfl⟩
    exact ⟨F,hF,rfl⟩

private theorem pullback_eq_native_finite_span
    {ι : Type} [Fintype ι] (A : GermIdeal n (ComplexModel n))
    (V : TopologicalSpace.Opens (ComplexModel n)) (f : ι → ComplexModel n → ℂ)
    (hf : ∀i,DifferentiableOn ℂ (f i) V)
    (hgen : ∀y∈V,∀g,A.mem y g ↔ InSpanAt f y g) :
    GermIdeal.pullback (m:=n) (Subtype.val : V → ComplexModel n) A=
      HironakaActualCoherentWeightedCoefficientMarked.finiteFunctionIdeal
        (fun i (z : V)=>f i z) := by
  have hs (i : ι) (z : V) : HolomorphicAt n (f i) (z : ComplexModel n) :=
    (holAt_of_differentiableOn V.isOpen (hf i) z.property).mono fun _ h=>h.mdifferentiableAt
  have hd (z : V) (g : ComplexModel n → ℂ) :
      A.mem z g ↔ IsInSpanAt (n:=n) (·∈range f) (z : ComplexModel n) g := by
    let E:=Fintype.equivFin ι
    have hr : range (fun i=>f (E.symm i))=range f:=by
      ext g
      constructor
      · rintro ⟨i,rfl⟩;exact ⟨E.symm i,rfl⟩
      · rintro ⟨i,rfl⟩;exact ⟨E i,by simp⟩
    rw [hgen z z.property g,←CoherentIdealColon.inSpanAt_comp_equiv E.symm f z g,
      ←hr,CoherentIdealColon.isInSpanAt_range_iff]
    constructor
    · rintro ⟨hg,a,ha,he⟩
      exact ⟨hg.mono (fun _ h=>h.mdifferentiableAt),a,fun i=>(ha i).mono (fun _ h=>h.mdifferentiableAt),he⟩
    · rintro ⟨hg,a,ha,he⟩
      exact ⟨hg.mono (fun _ h=>h.differentiableAt),a,fun i=>(ha i).mono (fun _ h=>h.differentiableAt),he⟩
  refine GermIdeal.ext (funext fun z=>funext fun g=>propext ⟨?_,?_⟩)
  · intro hg
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    refine IsInSpanAt.mono ?_ (GermIdealPullbackCalculus.isInSpanAt_comp
      (contMDiff_subtype_val (U:=V)) ((hd z a).mp ha))
    rintro _ ⟨a,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
    rintro _ ⟨i,rfl⟩
    exact ⟨f i,(hd z (f i)).mpr (isInSpanAt_self ⟨i,rfl⟩ (hs i z)),rfl⟩

open HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
 MarkedIdeals MarkedIdealBiholomorphism

/-- A coherent actual record whose entire adapted ideal is the weighted
quotient span becomes the literal native weighted record on one genuine
chart neighborhood, using ANY fixed same-germ quotient representatives. -/
theorem exists_actual_native_weighted_record_of_adapted_span
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (Q : MarkedIdeal n X) (hQ : Q.ideal.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    {ι : Type} [Fintype ι] (w : ι → ℕ) (H : ι → HolGerm (ComplexModel n))
    (hIdeal : adaptedIdeal Q.ideal x Φ h0=weightedCompression w H)
    (hd : Q.d=weightedCommonMark w)
    (f : ι → ComplexModel n → ℂ) (hf : ∀i,HolAt (f i) 0)
    (hF : ∀i,H i=HolGerm.mk (f i) (hf i)) :
    ∃V : TopologicalSpace.Opens (ComplexModel n),(0 : ComplexModel n)∈V ∧
      (V : Set (ComplexModel n))⊆Φ.target ∧
      (∀i,DifferentiableOn ℂ (f i) V) ∧
      MarkedIdeal.pullback (fun z : V=>actualFlatteningInverseMap x Φ z) Q=
        ⟨(fun z : V=>actualFlatteningInverseMap x Φ z) ⁻¹' Q.N,
          Q.E.map ((fun z : V=>actualFlatteningInverseMap x Φ z) ⁻¹' ·),
          weightedFunctionIdeal w (fun i (z : V)=>f i z),weightedCommonMark w⟩ := by
  let A:=actualFlattenedOriginalSheaf Q.ideal x Φ
  have hA : IdealFGAt A.mem (0 : ComplexModel n):=actual_flattened_local_fg Q.ideal hQ x Φ hsrc h0
  let powered:=fun i z=>f i z^(weightedCommonMark w/w i)
  have hp : ∀i,HolAt (powered i) 0:=fun i=>(hf i).mono fun _ h=>h.pow _
  have hspan : Ideal.span (range fun i=>HolGerm.mk (powered i) (hp i))=originalCoherentOriginIdeal A := by
    rw [actual_flattened_origin_eq_adapted Q.ideal hQ x Φ h0,hIdeal]
    unfold weightedCompression
    congr 1
    apply congrArg range
    funext i
    rw [hF i,←HolGerm.mk_pow]
  obtain ⟨O,hO,h0O,hpow,hgen⟩:=exists_actual_neighborhood_of_same_origin_generators A hA powered hp hspan
  obtain ⟨W,hWsub,hW,h0W⟩:=mem_nhds_iff.mp (eventually_all.mpr hf)
  let V : TopologicalSpace.Opens (ComplexModel n):=⟨(O∩Φ.target)∩W,(hO.inter Φ.isOpen_target).inter hW⟩
  have h0V : (0 : ComplexModel n)∈V:=⟨⟨h0O,actualFlattening_target_zero_mem x Φ h0⟩,h0W⟩
  have hVT : (V : Set (ComplexModel n))⊆Φ.target:=fun _ h=>h.1.2
  have hVpow : ∀i,DifferentiableOn ℂ (powered i) V:=fun i=>(hpow i).mono fun _ h=>h.1.1
  have hVgen : ∀y∈V,∀g,A.mem y g ↔ InSpanAt powered y g:=fun y hy=>hgen y hy.1.1
  have hideal : GermIdeal.pullback (m:=n) (fun z : V=>actualFlatteningInverseMap x Φ z) Q.ideal=
      weightedFunctionIdeal w (fun i (z : V)=>f i z) := by
    rw [pullback_local_comp Q.ideal hQ (actualFlatteningInverseMap x Φ) V
      (fun z hz=>actualFlatteningInverseMap_mdifferentiable x Φ hsrc z (hVT hz))]
    exact pullback_eq_native_finite_span A V powered hVpow hVgen
  refine ⟨V,h0V,hVT,fun i z hz=>(hWsub hz.2 i).differentiableWithinAt,?_⟩
  cases Q with
  | mk N E ideal d =>
    cases hd
    change MarkedIdeals.MarkedIdeal.mk _ _ _ _=_
    rw [hideal]
    rfl


open Hironaka.BlowupSequences GermIdealOrder HironakaActualGlobalInheritedCut HironakaActualAnalyticBlowupTaylor
 HironakaActualCoefficientPresentationCentrePower HironakaActualFiniteCoefficientIdeals
 HironakaActualCoefficientAnalyticBlowup HironakaHolomorphicJetMonomialSpan
 HironakaRelativeNormalIdeal MarkedIdeals.MarkedIdeal BlowupControlledTransform

/-- A genuine global blowup and actual source weighted functions internally
produce one quotient chart and its native realization of the ENTIRE geometric
controlled record, retaining the full given old boundary list and the born
member. The same chart and quotient germs work for ANY chosen same-germ
representatives. No post-transform ideal or neighborhood identity is input. -/
theorem exists_actual_global_controlled_native_weighted_record
    {d t : ℕ} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (d+t)) Z] [IsComplexManifold (d+t) Z]
    (U : TopologicalSpace.Opens (ComplexModel (d+t))) (h0U : (0 : ComplexModel (d+t))∈U)
    {ι : Type} [Fintype ι] (w : ι → ℕ) (hw : ∀i,0<w i)
    (c : ι → ComplexModel (d+t) → ℂ)
    (hc : ∀i,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (c i) U)
    (hCos : ∀i,(U : Set (ComplexModel (d+t)))∩complexCoordinatePlane (d+t) d⊆
      cosupport (d+t) univ (actualPrincipalCoefficientIdeal (d+t) (c i)) (w i))
    (E : List (Set U)) (π : Z → U)
    (hπ : IsBlowupAlong (d+t) ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+t))=0) :
    let cg:=fun i=>HolGerm.mk (c i)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) h0U).mono fun _ hz=>hz.differentiableAt)
    let M : MarkedIdeal (d+t) U:=⟨univ,E,weightedFunctionIdeal w (fun i (z : U)=>c i z),weightedCommonMark w⟩
    let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π
    ∃(e : Fin (d+t))(b : Fin (d+t) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0),
      d≤e.val ∧ (∀i : Fin (d+t),i.val<d → b i=0) ∧ b e=0 ∧
      Θ.source⊆(chartAt (ComplexModel (d+t)) y).target ∧
      (∀z : Z,z∈(chartAt (ComplexModel (d+t)) y).source →
        chartAt (ComplexModel (d+t)) y z∈Θ.source →
        (π z : ComplexModel (d+t))=actualAnalyticBlowupMap (actualTangentCentreVariables d t) e b
          (Θ.toFun (chartAt (ComplexModel (d+t)) y z))) ∧
      ∃H : ι → HolGerm (ComplexModel (d+t)),
        (∀i,coordinateGerm e^w i*H i=actualAnalyticBlowupPullback (actualTangentCentreVariables d t) e b (cg i)) ∧
        adaptedIdeal Q.ideal y Θ hΘ0=weightedCompression w H ∧ Q.ideal.IsCoherent ∧
        ∀(f : ι → ComplexModel (d+t) → ℂ)(hf : ∀i,HolAt (f i) 0),
          (∀i,H i=HolGerm.mk (f i) (hf i)) →
          ∃V : TopologicalSpace.Opens (ComplexModel (d+t)),(0 : ComplexModel (d+t))∈V ∧
            (V : Set (ComplexModel (d+t)))⊆Θ.target ∧
            (∀i,DifferentiableOn ℂ (f i) V) ∧
            MarkedIdeal.pullback (fun z : V=>actualFlatteningInverseMap y Θ z) Q=
              ⟨(fun z : V=>actualFlatteningInverseMap y Θ z) ⁻¹' Q.N,
                Q.E.map ((fun z : V=>actualFlatteningInverseMap y Θ z) ⁻¹' ·),
                weightedFunctionIdeal w (fun i (z : V)=>f i z),weightedCommonMark w⟩ := by
  let cg:=fun i=>HolGerm.mk (c i)
    ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) h0U).mono fun _ hz=>hz.differentiableAt)
  let M0 : MarkedIdeal (d+t) U:=⟨univ,[],weightedFunctionIdeal w (fun i (z : U)=>c i z),weightedCommonMark w⟩
  let M : MarkedIdeal (d+t) U:=⟨univ,E,weightedFunctionIdeal w (fun i (z : U)=>c i z),weightedCommonMark w⟩
  let C:=((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d)
  let Q:=M.geoTransform C π
  obtain ⟨e,b,Θ,hΘ0,he,hbt,hbe,hΘsrc,hSquare,H,hH,_hTaylor,hIdeal0,_hCosupp⟩:=
    exists_actual_global_controlled_weighted_cut U h0U w hw c hc hCos π hπ y hy
  have hcu (i : ι) : MDifferentiable 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (fun z : U=>c i z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) z.property).comp_contMDiff
      (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=U)).contMDiffAt)).mdifferentiableAt
  have hI:=isCoherent_weightedFunctionIdeal w (fun i (z : U)=>c i z) hcu
  have hQ : Q.ideal.IsCoherent := by
    rw [geoTransform_ideal_eq_controlledTransform (𝔪:=M) rfl hI hπ]
    exact CoherentIdealColon.isCoherent_colon_of_isCoherent
      (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hI)
      (DivisorMetric.isCoherent_of_isInvertible (isInvertible_idealPow_exceptionalDivisor hπ (weightedCommonMark w)))
  have hIdeal : adaptedIdeal Q.ideal y Θ hΘ0=weightedCompression w H := by
    rw [geoTransform_ideal_eq_controlledTransform (𝔪:=M) rfl hI hπ]
    rw [geoTransform_ideal_eq_controlledTransform (𝔪:=M0) rfl hI hπ] at hIdeal0
    exact hIdeal0
  refine ⟨e,b,Θ,hΘ0,he,hbt,hbe,hΘsrc,hSquare,H,hH,hIdeal,hQ,?_⟩
  intro f hf hF
  exact exists_actual_native_weighted_record_of_adapted_span Q hQ y Θ hΘsrc hΘ0 w H hIdeal
    (geoTransform_d (𝔪:=M) C π) f hf hF

end
end Hironaka.HironakaActualControlledNeighborhoodGenerators

