import Hironaka.Resolution.HironakaActualOriginalInitialHSPhase
import Hironaka.Resolution.HironakaActualDiagonalTaylor
import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon

/-! Literal genuine affine coordinates for the SAME original PHS functions
and full InitialHSPhase weighted record. Entire ideals are derived from
actual source finite generation; no global coordinate-model coherence,
numerical HS replacement or desired target history is an input. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalInitialAffineDictionary
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaActualDiagonalTaylor HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaSmoothSubmersionGermIdealColon
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalHSMarkedDomain
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualRelativeNormalJetDivision
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  ManifoldFiniteSpanChartTransport EuclideanHolomorphicGermSpan
  RelativePrincipalizationSpan InvertibleIdealQuotient

variable {n : ℕ}

private theorem diagonal_inverse (c : Fin n → ℂ) (hc : ∀i,c i≠0) (z : ComplexModel n) :
    actualDiagonalMap c (actualDiagonalMap (fun i=>(c i)⁻¹) z)=z := by
  ext i
  rw [actualDiagonalMap_apply,actualDiagonalMap_apply,←mul_assoc,mul_inv_cancel₀ (hc i),one_mul]

private theorem subtype_chart_apply (U : Opens (ComplexModel n)) (x z : U) :
    chartAt (ComplexModel n) x z=(z : ComplexModel n) := by
  rw [Opens.chartAt_eq,chartAt_self_eq]
  rfl

/-- Actual affine coordinates in the ORIGINAL true open, with a fixed
nonzero diagonal. The inverse is literally x + diagonal(c) z. -/
def actualInitialAffineChart (U : Opens (ComplexModel n)) (x : U)
    (c : Fin n → ℂ) (hc : ∀i,c i≠0) :
    LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x) where
  source:=U
  target:=(fun z=>(x : ComplexModel n)+actualDiagonalMap c z) ⁻¹' U
  isOpen_source:=U.isOpen
  isOpen_target:=U.isOpen.preimage (continuous_const.add (actualDiagonalMap c).continuous)
  center_mem_source:=by rw [subtype_chart_apply];exact x.property
  toFun:=fun z=>actualDiagonalMap (fun i=>(c i)⁻¹) (z-x.val)
  invFun:=fun z=>x.val+actualDiagonalMap c z
  toFun_holomorphic:=((actualDiagonalMap (fun i=>(c i)⁻¹)).differentiable.comp
    (differentiable_id.sub_const x.val)).differentiableOn
  invFun_holomorphic:=((actualDiagonalMap c).differentiable.const_add x.val).differentiableOn
  mapsTo_toFun:=by
    intro z hz
    change x.val+actualDiagonalMap c (actualDiagonalMap (fun i=>(c i)⁻¹) (z-x.val))∈U
    rw [diagonal_inverse c hc,add_sub_cancel]
    exact hz
  mapsTo_invFun:=fun _ hz=>hz
  left_inv:=by
    intro z _hz
    rw [diagonal_inverse c hc,add_sub_cancel]
  right_inv:=by
    intro z _hz
    rw [add_sub_cancel_left]
    have h:=diagonal_inverse (fun i=>(c i)⁻¹) (fun i=>inv_ne_zero (hc i)) z
    simpa only [inv_inv] using h

/-- The actual affine chart has the genuine native source target and is
centred at zero; no source-domain certificate is supplied. -/
theorem actual_initial_affine_chart_geometry (U : Opens (ComplexModel n)) (x : U)
    (c : Fin n → ℂ) (hc : ∀i,c i≠0) :
    (actualInitialAffineChart U x c hc).source⊆(chartAt (ComplexModel n) x).target ∧
      (actualInitialAffineChart U x c hc).toFun (chartAt (ComplexModel n) x x)=0 := by
  constructor
  · intro v hv
    rw [Opens.chartAt_eq,chartAt_self_eq]
    exact (OpenPartialHomeomorph.refl (ComplexModel n)).map_subtype_source ⟨x⟩ (x:=⟨v,hv⟩) (mem_univ v)
  · change actualDiagonalMap (fun i=>(c i)⁻¹) (chartAt (ComplexModel n) x x-x.val)=0
    rw [subtype_chart_apply,sub_self,map_zero]

private theorem affine_inverse_native (U : Opens (ComplexModel n)) (x : U)
    (c : Fin n → ℂ) (hc : ∀i,c i≠0) (z : ComplexModel n)
    (hz : z∈(actualInitialAffineChart U x c hc).target) :
    (((chartAt (ComplexModel n) x).symm ((actualInitialAffineChart U x c hc).invFun z) : U) :
      ComplexModel n)=x.val+actualDiagonalMap c z := by
  have h:=(chartAt (ComplexModel n) x).right_inv
    ((actual_initial_affine_chart_geometry U x c hc).1 ((actualInitialAffineChart U x c hc).mapsTo_invFun hz))
  rw [subtype_chart_apply] at h
  exact h

/-- An entire ORIGINAL restricted function germ is the literal diagonal
pullback of its translated original germ in these genuine coordinates. -/
theorem actual_initial_affine_adapted_germ (U : Opens (ComplexModel n)) (x : U)
    (c : Fin n → ℂ) (hc : ∀i,c i≠0) (f : ComplexModel n → ℂ) (hf : HolAt f x.val)
    (hfU : HolomorphicAt n (fun z : U=>f z.val) x) :
    adaptedGerm x (actualInitialAffineChart U x c hc)
      (actual_initial_affine_chart_geometry U x c hc).2 (fun z : U=>f z.val) hfU=
      actualDiagonalPullback c (translatedGerm x.val f hf) := by
  rw [actualDiagonalPullback,translatedGerm,compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  have h0 : (0 : ComplexModel n)∈(actualInitialAffineChart U x c hc).target := by
    change x.val+actualDiagonalMap c 0∈U
    simpa only [map_zero,add_zero] using x.property
  filter_upwards [(actualInitialAffineChart U x c hc).isOpen_target.mem_nhds h0] with z hz
  change f (((chartAt (ComplexModel n) x).symm ((actualInitialAffineChart U x c hc).invFun z) : U).val)=
    f (actualDiagonalMap c z+x.val)
  rw [affine_inverse_native U x c hc z hz,add_comm x.val]

section NativeGeneration
variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {ι : Type*} [Fintype ι]

/-- SOURCE whole finite generation proves the ENTIRE native adapted
ideal. Only generation at the actual point is needed, no global model FG. -/
theorem actual_native_adapted_ideal_of_whole_generation
    (J : GermIdeal n X) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (f : ι → X → ℂ) (hf : ∀i,HolomorphicAt n (f i) x)
    (hgen : ∀F,J.mem x F ↔ IsInSpanAt (n:=n) (·∈range f) x F) :
    adaptedIdeal J x Φ h0=Ideal.span (range fun i=>adaptedGerm x Φ h0 (f i) (hf i)) := by
  let e:=Fintype.equivFin ι
  let g:=fun j : Fin (Fintype.card ι)=>f (e.symm j)
  have hr : range g=range f:=e.symm.surjective.range_comp f
  have hrg : range (fun j=>adaptedGerm x Φ h0 (g j) (hf (e.symm j)))=
      range (fun i=>adaptedGerm x Φ h0 (f i) (hf i)):=
    e.symm.surjective.range_comp (fun i=>adaptedGerm x Φ h0 (f i) (hf i))
  rw [←hrg]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨F,hF,hJF,rfl⟩
    have hSpan : IsInSpanAt (n:=n) (·∈range g) x F:=by rw [hr];exact (hgen F).mp hJF
    exact (isInSpanAt_iff_holGerm_mem_span _
      (fun j=>(holomorphic_adapted_iff x Φ h0 (g j)).mpr (hf (e.symm j)))
      ((holomorphic_adapted_iff x Φ h0 F).mpr hF)).mp
        ((isInSpanAt_comp_adapted_iff x Φ h0 g F).mp hSpan)
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Ideal.subset_span ⟨g j,hf (e.symm j),
      (hgen (g j)).mpr (isInSpanAt_self ⟨e.symm j,rfl⟩ (hf (e.symm j))),rfl⟩

/-- Literal powered source functions have their exact ENTIRE compression
in ANY genuine chart, before any cut or HS comparison is considered. -/
theorem actual_native_weighted_function_adapted_ideal
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (w : ι → ℕ) (f : ι → X → ℂ) (hf : ∀i,HolomorphicAt n (f i) x) :
    adaptedIdeal (weightedFunctionIdeal w f) x Φ h0=
      weightedCompression w (fun i=>adaptedGerm x Φ h0 (f i) (hf i)) := by
  rw [actual_native_adapted_ideal_of_whole_generation (weightedFunctionIdeal w f) x Φ h0
    (fun i z=>f i z^(weightedCommonMark w/w i))
      (fun i=>BlowupDerivativeIdeal.holomorphicAt_pow (hf i) _) (fun _=>Iff.rfl)]
  unfold weightedCompression
  apply congrArg Ideal.span
  congr 1

end NativeGeneration

/-- Fixed nonzero original row constants preserve the WHOLE source span. -/
theorem actual_span_const_units {ι : Type*} (r : ι → ℂ) (hr : ∀i,r i≠0)
    (F : ι → HolGerm (ComplexModel n)) :
    Ideal.span (range fun i=>HolGerm.constHom (r i)*F i)=Ideal.span (range F) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (Ideal.unit_mul_mem_iff_mem _ ((isUnit_iff_ne_zero.mpr (hr i)).map HolGerm.constHom)).mp
      (Ideal.subset_span ⟨i,rfl⟩)

/-- Fixed nonzero original row constants preserve the ENTIRE actual
compression with precisely the original unchanged marks. -/
theorem actual_weighted_compression_const_units {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (r : ι → ℂ) (hr : ∀i,r i≠0) (F : ι → HolGerm (ComplexModel n)) :
    weightedCompression w (fun i=>HolGerm.constHom (r i)*F i)=weightedCompression w F := by
  unfold weightedCompression
  have h : (fun i=>(HolGerm.constHom (r i)*F i)^(weightedCommonMark w/w i))=
      fun i=>HolGerm.constHom ((r i)^(weightedCommonMark w/w i))*F i^(weightedCommonMark w/w i) := by
    funext i
    rw [mul_pow,map_pow]
  rw [h]
  exact actual_span_const_units (fun i=>(r i)^(weightedCommonMark w/w i))
    (fun i=>pow_ne_zero _ (hr i)) _

section ActualPresentation
variable {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ → ℕ}

private theorem presentation_restricted_holomorphic
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) (x : presentationOpen PHS) (i) :
    HolomorphicAt n (fun z : presentationOpen PHS=>PHS.representatives i z.val) x := by
  have h : HolomorphicAt n (PHS.representatives i) x.val:=
    (PHS.holomorphicAt x.val x.property i).mono (fun _ h=>h.mdifferentiableAt)
  exact h.comp_contMDiff
    (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=presentationOpen PHS)).contMDiffAt)

private theorem presentation_pullback_generation
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) (x : presentationOpen PHS)
    (F : presentationOpen PHS → ℂ) :
    (GermIdeal.pullback (m:=n) (Subtype.val : presentationOpen PHS → ComplexModel n) A).mem x F ↔
      IsInSpanAt (n:=n) (·∈range fun i (z : presentationOpen PHS)=>PHS.representatives i z.val) x F := by
  let V:=actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)
  let e:=Fintype.equivFin V
  let f:=fun j : Fin (Fintype.card V)=>PHS.representatives (e.symm j)
  have hgen (H : ComplexModel n → ℂ) : A.mem x.val H ↔
      IsInSpanAt (n:=n) (·∈range f) x.val H := by
    have hoka : A.mem x.val H ↔ InSpanAt f x.val H:=
      (PHS.wholeGeneration x.val x.property H).trans
        (CoherentIdealColon.inSpanAt_comp_equiv e.symm PHS.representatives x.val H).symm
    rw [CoherentIdealColon.isInSpanAt_range_iff]
    constructor
    · intro h
      obtain ⟨hh,a,ha,he⟩:=hoka.mp h
      exact ⟨hh.mono (fun _ hz=>hz.mdifferentiableAt),a,
        fun i=>(ha i).mono (fun _ hz=>hz.mdifferentiableAt),he⟩
    · rintro ⟨hh,a,ha,he⟩
      exact hoka.mpr ⟨hh.mono (fun _ hz=>hz.differentiableAt),a,
        fun i=>(ha i).mono (fun _ hz=>hz.differentiableAt),he⟩
  have h:=FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
    (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=presentationOpen PHS)).contMDiffAt)
    A f (fun j=>(PHS.holomorphicAt x.val x.property (e.symm j)).mono
      (fun _ hz=>hz.mdifferentiableAt)) hgen F
  have hr : range (fun j=>f j ∘ (Subtype.val : presentationOpen PHS → ComplexModel n))=
      range (fun i (z : presentationOpen PHS)=>PHS.representatives i z.val) :=
    e.symm.surjective.range_comp (fun i (z : presentationOpen PHS)=>PHS.representatives i z.val)
  rwa [hr] at h

/-- The actual true native source ideal is coherent on the PHS open,
derived from its SAME finite source functions. This makes no assertion of
global coherence of the possibly extended ambient coordinate model. -/
theorem actual_initial_presentation_native_coherent
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) :
    (GermIdeal.pullback (m:=n) (Subtype.val : presentationOpen PHS → ComplexModel n) A).IsCoherent := by
  have heq : GermIdeal.pullback (m:=n) (Subtype.val : presentationOpen PHS → ComplexModel n) A=
      finiteFunctionIdeal (fun i (z : presentationOpen PHS)=>PHS.representatives i z.val) :=
    GermIdeal.ext (funext fun x=>funext fun F=>propext (presentation_pullback_generation PHS x F))
  rw [heq]
  exact isCoherent_finiteFunctionIdeal _
    (fun i x=>(presentation_restricted_holomorphic PHS x i).self_of_nhds)

/-- The SAME true original PHS functions span the ENTIRE actual native
source ideal in these affine coordinates, with fixed nonzero row factors.
Only original whole generation is used; model-global coherence is absent. -/
theorem actual_initial_affine_presentation_span
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) (x : presentationOpen PHS)
    (c : Fin n → ℂ) (hc : ∀i,c i≠0)
    (r : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ℂ)
    (hr : ∀i,r i≠0) :
    Ideal.span (range fun i=>HolGerm.constHom (r i)*actualDiagonalPullback c
      (translatedGerm x.val (PHS.representatives i) (PHS.holomorphicAt _ x.property i)))=
      adaptedIdeal (GermIdeal.pullback (m:=n)
        (Subtype.val : presentationOpen PHS → ComplexModel n) A) x
        (actualInitialAffineChart (presentationOpen PHS) x c hc)
        (actual_initial_affine_chart_geometry (presentationOpen PHS) x c hc).2 := by
  rw [actual_span_const_units r hr,
    actual_native_adapted_ideal_of_whole_generation _ x _ _
      (fun i (z : presentationOpen PHS)=>PHS.representatives i z.val)
      (presentation_restricted_holomorphic PHS x) (presentation_pullback_generation PHS x)]
  apply congrArg Ideal.span
  congr 1
  funext i
  exact (actual_initial_affine_adapted_germ (presentationOpen PHS) x c hc _
    (PHS.holomorphicAt _ x.property i) (presentation_restricted_holomorphic PHS x i)).symm

/-- ENTIRE actual initial weighted-Q compression in a genuine affine
chart. The literal original N, ALL ordered boundary positions and common
mark are retained; no new marked record or CAN is selected. -/
theorem actual_initial_affine_weighted_record
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    {M : Type*} (η : presentationOpen PHS → M) (E : List (Set M))
    (x : presentationOpen PHS) (c : Fin n → ℂ) (hc : ∀i,c i≠0)
    (r : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ℂ)
    (hr : ∀i,r i≠0) :
    let Q:=initialWeightedRecord PHS η E
    adaptedIdeal Q.ideal x (actualInitialAffineChart (presentationOpen PHS) x c hc)
        (actual_initial_affine_chart_geometry (presentationOpen PHS) x c hc).2=
      weightedCompression (fun i : actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val)
        (fun i=>HolGerm.constHom (r i)*actualDiagonalPullback c
          (translatedGerm x.val (PHS.representatives i) (PHS.holomorphicAt _ x.property i))) ∧
    Q.N=univ ∧ Q.E=E.map (η ⁻¹' ·) ∧
      Q.d=weightedCommonMark (fun i : actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val) := by
  refine ⟨?_,rfl,rfl,rfl⟩
  rw [actual_weighted_compression_const_units _ r hr]
  change adaptedIdeal (weightedFunctionIdeal (fun i : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val)
    (fun i (z : presentationOpen PHS)=>PHS.representatives i z.val)) x _ _=_
  rw [actual_native_weighted_function_adapted_ideal x _ _ _ _ (presentation_restricted_holomorphic PHS x)]
  apply congrArg (weightedCompression (fun i : actualInitialVertices MonomialOrder.degLex
    (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val))
  funext i
  exact actual_initial_affine_adapted_germ (presentationOpen PHS) x c hc _
    (PHS.holomorphicAt _ x.property i) (presentation_restricted_holomorphic PHS x i)

end ActualPresentation

end
end Hironaka.HironakaActualHistoricalInitialAffineDictionary
