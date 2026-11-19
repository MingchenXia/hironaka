import Hironaka.Resolution.HironakaG8ActualOccupiedQuotientChartCover
import Hironaka.Resolution.HironakaG8NativeHSFullBoundaryTerminalWindow
import Hironaka.Resolution.HironakaActualControlledNeighborhoodGenerators
import Hironaka.Resolution.HironakaActualOriginalGeometricCentreBennett

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8FreshPostCutNativeFamily
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers HolGerm
  OkaRelationSheaf OkaIdealOperations OkaCoherence
  HironakaSmoothCentreCoherentDomain HironakaSmoothSubmersionGermIdealColon
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalAnalyticGraphQuotient
  HironakaActualLocalStrictSaturation HironakaRelativeNormalCoherentSaturation
  HironakaActualAnalyticNearbyVertexGenerators RelativePrincipalizationSpan InvertibleIdealQuotient
  HironakaActualControlledNeighborhoodGenerators HironakaRelativeNormalCoherentTranslatedJets
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualFixedInheritedSelector HironakaActualHistoricalNativeStageStep
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualWeightedCoefficientCompression
  HironakaActualCoherentWeightedCoefficientMarked MarkedIdeals
  MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec HironakaG11PresLineState
  HironakaG8NativeCommonDenominatorReduction HironakaG8LocalHistory
  HironakaActualOriginalGeometricCentreBennett HironakaG8NativeHSFullBoundaryTerminalWindow
  HironakaEmbeddedAnalytic BlowupTowerTransforms HironakaBaseChange MaxLocusLocal

variable {n : ℕ}

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

private theorem zero_translated_adapted_vanishing {X : CMfd.{0} n} (W : Set X)
    (hW : (vanishingIdeal (n:=n) W).IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Φ) 0)=
      adaptedIdeal (vanishingIdeal (n:=n) W) x Φ h0 := by
  rw [← actual_flattened_origin_eq_adapted _ hW x Φ h0]
  unfold originalCoherentOriginIdeal
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨F,hF,hMem,rfl⟩
    exact ⟨F,hF,(actual_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 F).mpr
      ((actual_zero_translated_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 F).mp hMem),rfl⟩
  · rintro ⟨F,hF,hMem,rfl⟩
    exact ⟨F,hF,(actual_zero_translated_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 F).mpr
      ((actual_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 F).mp hMem),rfl⟩

/-- Literal representatives of one new selected family in actual native coordinates. -/
def FreshNativeGeneratedAt {X : CMfd.{0} n} (Q : MarkedIdeal n X) (W : Set X) (x : X) : Prop :=
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℕ), (∀ i, 0 < w i) ∧
      Q.d = weightedCommonMark w ∧
      ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)),
        Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
        Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      ∃ (V : Opens (ComplexModel n)) (hV : (0 : ComplexModel n) ∈ V)
        (ψ : V → X) (f : ι → V → ℂ),
        (V : Set (ComplexModel n)) ⊆ Φ.target ∧
        ψ = (fun z : V => actualFlatteningInverseMap x Φ z.val) ∧
        ψ ⟨0,hV⟩ = x ∧ MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ψ ∧
        (∀ i, MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (f i)) ∧
        GermIdeal.pullback (m := n) ψ (vanishingIdeal (n := n) W) = finiteFunctionIdeal f ∧
        MarkedIdeal.pullback ψ Q = ⟨univ,Q.E.map (ψ ⁻¹' ·),weightedFunctionIdeal w f,weightedCommonMark w⟩

/-- The freshly selected actual point family generates the reduced strict
ideal and the weighted native ideal on one common coordinate window. -/
theorem exists_fresh_native_pair_of_active_point
    {X : CMfd.{0} n} {Q : MarkedIdeal n X} {W : Set X} {H : ℕ → ℕ}
    (hState : NativeHSState Q W H) (x : X) (hx : x ∈ Q.cosupp)  :
    FreshNativeGeneratedAt Q W x := by
  classical
  obtain ⟨_,hW,hQN,hQI,Sv,S,k,a,words,_,hPos,_,hMark,_,_,hAt⟩ := hState
  obtain ⟨Φ,hSrc,h0,Γ,_,hReduced,hWeighted⟩ := hAt x hx
  let w := fun v : Sv => normalExponentDegree v.val
  have hIW := CartanIrreducible.cartanCoherence W hW
  have hReduced' : Ideal.span (range Γ) = adaptedIdeal (vanishingIdeal (n := n) W) x Φ h0 := by
    have hRange : range (fun i => Γ (a i)) = range Γ := by
      ext g
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨a i,rfl⟩
      · rintro ⟨v,rfl⟩
        exact ⟨a.symm v,by simp⟩
    rw [hRange, zero_translated_adapted_vanishing W hIW x Φ hSrc h0] at hReduced
    exact hReduced
  have hRep (i : Sv) : ∃ f : ComplexModel n → ℂ, ∃ hf : HolAt f 0, Γ i = HolGerm.mk f hf := by
    induction Γ i using HolGerm.induction_on with
    | h f hf => exact ⟨f,hf,rfl⟩
  choose f hf hΓ using hRep
  let G := actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ
  let T := actualFlattenedOriginalSheaf Q.ideal x Φ
  let g := fun i z => f i z ^ (weightedCommonMark w / w i)
  have hg (i : Sv) : HolAt (g i) 0 := (hf i).mono fun _ h => h.pow _
  have hRG : Ideal.span (range fun i => HolGerm.mk (f i) (hf i)) = originalCoherentOriginIdeal G := by
    rw [actual_flattened_origin_eq_adapted _ hIW x Φ h0,←hReduced']
    simp only [← hΓ]
  have hTG : Ideal.span (range fun i => HolGerm.mk (g i) (hg i)) = originalCoherentOriginIdeal T := by
    rw [actual_flattened_origin_eq_adapted _ hQI x Φ h0,hWeighted]
    unfold weightedCompression
    apply congrArg Ideal.span
    apply congrArg range
    funext i
    rw [hΓ i,← HolGerm.mk_pow]
  obtain ⟨U,hU,hU0,hfU,hgenU⟩ := exists_actual_neighborhood_of_same_origin_generators
    G (actual_flattened_local_fg _ hIW x Φ hSrc h0) f hf hRG
  obtain ⟨D,hD,hD0,hgD,hgenD⟩ := exists_actual_neighborhood_of_same_origin_generators
    T (actual_flattened_local_fg _ hQI x Φ hSrc h0) g hg hTG
  let V : Opens (ComplexModel n) := ⟨(U∩D)∩Φ.target,(hU.inter hD).inter Φ.isOpen_target⟩
  have hV0 : (0 : ComplexModel n) ∈ V := ⟨⟨hU0,hD0⟩,actualFlattening_target_zero_mem x Φ h0⟩
  let ψ : V → X := fun z => actualFlatteningInverseMap x Φ z.val
  have hMD := actualFlatteningInverseMap_mdifferentiable x Φ hSrc
  have hF (i : Sv) (z : V) : MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (f i) z.val :=
    ((hfU i).differentiableAt (hU.mem_nhds z.property.1.1)).mdifferentiableAt
  have hVal (z : V) : MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
      (Subtype.val : V → ComplexModel n) z :=
    (contMDiff_subtype_val (n := ∞) z).mdifferentiableAt (by simp)
  have hLow : GermIdeal.pullback (m := n) ψ (vanishingIdeal (n := n) W) =
      finiteFunctionIdeal (n := n) (fun i (z : V) => f i z.val) := by
    rw [pullback_local_comp _ hIW _ V (fun z hz => hMD z hz.2)]
    exact pullback_eq_native_finite_span G V f
      (fun i => (hfU i).mono fun _ hz => hz.1.1)
      (fun z hz => hgenU z hz.1.1)
  have hHigh : GermIdeal.pullback (m := n) ψ Q.ideal =
      weightedFunctionIdeal (n := n) w (fun i (z : V) => f i z.val) := by
    rw [pullback_local_comp _ hQI _ V (fun z hz => hMD z hz.2)]
    exact pullback_eq_native_finite_span T V g
      (fun i => (hgD i).mono fun _ hz => hz.1.2)
      (fun z hz => hgenD z hz.1.2)
  refine ⟨Sv,inferInstance,w,hPos,hMark,Φ,hSrc,h0,V,hV0,ψ,fun i z => f i z.val,fun _ hz => hz.2,rfl,
    actualFlatteningInverseMap_zero x Φ h0,fun z => (hMD z.val z.property.2).comp z (hVal z),
    fun i z => (hF i z).comp z (hVal z),hLow,?_⟩
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (by change ψ ⁻¹' Q.N = univ; rw [hQN,preimage_univ]) rfl hHigh hMark

/-- A point of the actual occupied target with strictly smaller singular profile
has a newly selected native record in any prescribed quotient window. Its
boundary is the whole ordered controlled boundary. -/
theorem exists_fresh_native_after_occupied_cut
    {X Y : CMfd.{0} (n+1)} (Q : MarkedIdeal (n+1) X)
    (hQ : IsInvDomain (n+1) Q) {W : Set X} {H : ℕ → ℕ}
    (hState : NativeHSState Q W H) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong (n+1) C π) (hC : Q.IsAdmissibleCentre C)
    (y : Y) (D : Opens Y) (hyD : y ∈ D)
    (hy : y ∈ singularSet (n := n+1) (strictTransform (n+1) π W))
    (hDrop : toLex (HironakaHolomorphicJetChartInvariance.hilbertSamuelAt
      (vanishingIdeal (n := n+1) (strictTransform (n+1) π W)) y) < toLex H) :
    let W' := strictTransform (n+1) π W
    let H' := HironakaHolomorphicJetChartInvariance.hilbertSamuelAt
      (vanishingIdeal (n := n+1) W') y
    ∃ (U : Opens Y) (hyU : y ∈ U), U ≤ D ∧
      ∃ R : MarkedIdeal (n+1) (CMfd.of (n := n+1) U),
        IsInvDomain (n+1) R ∧
        R.E = (Q.geoTransform C π).E.map ((Subtype.val : U → Y) ⁻¹' ·) ∧
        NativeHSState R ((Subtype.val : U → Y) ⁻¹' W') H' ∧
        toLex H' < toLex H ∧ FreshNativeGeneratedAt R ((Subtype.val : U → Y) ⁻¹' W') ⟨y,hyU⟩ := by
  intro W' H'
  let T : BlowupTower X Y := .step .refl C π hπ
  have hW' : IsComplexAnalyticSubset (n := n+1) W' := by
    have h := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hState.2.1 T
    simpa [T,W',BlowupTower.proj_step,BlowupTower.proj_refl] using h
  have hQE := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ T ⟨trivial,hC⟩).isWellFormed.isSNCDivisor
  obtain ⟨U,hyU,hUD,R,_,_,hR,hE,hSR,_,_,_,_,_,hyR⟩ :=
    HironakaG8NativeHSFullBoundaryTerminalWindow.exists_native_hs_ambient_full_boundary_terminal_window
      (Nat.succ_pos n) W' hW' (Q.geoTransform C π).E hQE y hy D hyD
  exact ⟨U,hyU,hUD,R,hR,hE,hSR,hDrop,exists_fresh_native_pair_of_active_point hSR _ hyR⟩

/-- The two reselected records give the same local marked class on each
common chart carrying the same strict profile and ordered boundary. -/
theorem fresh_native_overlap_class
    {X Y O : CMfd.{0} n}
    (p : O ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (q : O ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    {P : MarkedIdeal n X} {Q : MarkedIdeal n Y} {W : Set X} {V : Set Y} {H : ℕ → ℕ}
    (hP : NativeHSState P W H) (hQ : NativeHSState Q V H)
    (hW : p ⁻¹' W = q ⁻¹' V)
    (hE : (MarkedIdeal.pullback p P).E = (MarkedIdeal.pullback q Q).E) :
    LocWPEquiv (MarkedIdeal.pullback p P) (MarkedIdeal.pullback q Q) := by
  have hA : NativeHSState (MarkedIdeal.pullback p P) (p ⁻¹' W) H := hP.pullback p
  have hB : NativeHSState (MarkedIdeal.pullback q Q) (p ⁻¹' W) H := hW ▸ hQ.pullback q
  exact HironakaG11PresLineStable.locWPEquiv_native hA hB hE.symm

/-- On the literal intersection of two post-cut windows, equality of the
intrinsic profile suffices for agreement of their restricted marked classes. -/
theorem fresh_native_open_overlap_class
    {X : CMfd.{0} n} (U V : Opens X) (W : Set X) (E : List (Set X)) {H : ℕ → ℕ}
    (P : MarkedIdeal n (CMfd.of (n := n) U))
    (Q : MarkedIdeal n (CMfd.of (n := n) V))
    (hP : NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H)
    (hQ : NativeHSState Q ((Subtype.val : V → X) ⁻¹' W) H)
    (hEP : P.E = E.map ((Subtype.val : U → X) ⁻¹' ·))
    (hEQ : Q.E = E.map ((Subtype.val : V → X) ⁻¹' ·)) :
    let O := U ⊓ V
    let UP := nestedOpens U O
    let VQ := nestedOpens V O
    let p := (nestedOpensDiffeo (n := n) (show O ≤ U from inf_le_left)).symm
    let q := (nestedOpensDiffeo (n := n) (show O ≤ V from inf_le_right)).symm
    LocWPEquiv (MarkedIdeal.pullback p (MarkedIdeal.pullback (Subtype.val : UP → U) P))
      (MarkedIdeal.pullback q (MarkedIdeal.pullback (Subtype.val : VQ → V) Q)) := by
  intro O UP VQ p q
  apply fresh_native_overlap_class p q (hP.restrict UP) (hQ.restrict VQ) rfl
  change (P.E.map ((Subtype.val : UP → U) ⁻¹' ·)).map (p ⁻¹' ·) =
    (Q.E.map ((Subtype.val : VQ → V) ⁻¹' ·)).map (q ⁻¹' ·)
  simp only [hEP,hEQ,List.map_map,Function.comp_def]
  rfl

end
end Hironaka.HironakaG8FreshPostCutNativeFamily
