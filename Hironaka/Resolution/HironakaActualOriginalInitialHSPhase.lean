import Hironaka.Resolution.HironakaActualHistoricalHSMarkedDomain
import Hironaka.Resolution.HironakaActualPrescribedCentreRebasing

/-! Original analytic geometry internally initializes the SAME whole-HS
family, selector, true geometric presentation, full boundary and marked phase.
No chosen initial family or desired presentation is an input. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalInitialHSPhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaIdealOperations OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeNormalJetDivision HironakaActualNormalZeroAnalyticSaturation
  HironakaActualFormalInitialDiagram HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualCoefficientPresentationCentrePower
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaActualWholeHSSingularity HironakaActualHistoricalHSMarkedDomain
  HironakaActualInheritedNestedContactFlag HironakaActualInheritedCurrentSourceRelabel
  HironakaActualFixedInheritedSelector HironakaActualPrescribedCentreRebasing
  HironakaActualLocalHolomorphicOriginPullback HironakaActualLocalStrictSaturation
  HironakaActualFixedFlatteningHSComparison HironakaActualFlatCoordinateIntrinsicHS
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaActualStrictPullbackSaturation
  HironakaActualPointGeometricBennett HironakaActualSameCurrentGeometricStage
  HironakaActualSingularChartTransport
  HironakaActualVanishingIntrinsicHSTransport
  HironakaActualInheritedNeighborhoodMarkedHS HironakaActualCauchyCoefficientLimits
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsInvariance SimultaneousNormalCrossings ResolutionInvariantSpec
  RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient HadamardBridge
  BlowupTowers BlowupFlatCoordinates HironakaEmbeddedAnalytic RegularAtDimTransport
  GermIdealOrder IdealWeightPowers OrderTaylor MarkedIdealRestrictOpen

variable {n : ℕ}

private theorem origin_eq_of_zero_mem_iff (A B : GermIdeal n (ComplexModel n))
    (h : ∀ f,A.mem 0 f ↔ B.mem 0 f) :
    originalCoherentOriginIdeal A=originalCoherentOriginIdeal B := by
  unfold originalCoherentOriginIdeal
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨f,hf,ha,rfl⟩
    exact ⟨f,hf,(h f).mp ha,rfl⟩
  · rintro ⟨f,hf,hb,rfl⟩
    exact ⟨f,hf,(h f).mpr hb,rfl⟩

private theorem positive_marks_of_true_origin
    (B : Set (ComplexModel n)) (h0B : (0 : ComplexModel n)∈B)
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n
      (originalCoherentOriginIdeal (vanishingIdeal (n := n) B))))
    (hmem : ∀ i,G.germs i∈originalCoherentOriginIdeal (vanishingIdeal (n := n) B)) :
    ∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n
      (originalCoherentOriginIdeal (vanishingIdeal (n := n) B))),0<normalExponentDegree i.val := by
  have hvan : originalCoherentOriginIdeal (vanishingIdeal (n := n) B)≤
      RingHom.ker (HolGerm.eval : HolGerm (ComplexModel n) →+* ℂ) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hB,rfl⟩
    change HolGerm.eval (HolGerm.mk f hf)=0
    rw [HolGerm.eval_mk]
    exact hB.2.self_of_nhds h0B
  intro i
  by_contra hi
  have hd : normalExponentDegree i.val=0:=Nat.eq_zero_of_not_pos hi
  have hi0 : i.val=0 := by
    ext j
    exact (Finset.sum_eq_zero_iff.mp hd) j (Finset.mem_univ j)
  have hOne:=G.monic i
  change MvPowerSeries.coeff i.val (actualUnshiftedTaylorAlgHom n (G.germs i))=1 at hOne
  rw [hi0,actualTaylor_coeff_zero] at hOne
  have hz : HolGerm.eval (G.germs i)=0:=hvan (hmem i)
  exact zero_ne_one (hz.symm.trans hOne)

section OriginalChart
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

private theorem local_pullback_comp_at
    (A : GermIdeal n M) (hA : ∀ x f,A.mem x f → HolomorphicAt n f x)
    (f : ComplexModel n → M) (g : ComplexModel n → ComplexModel n) (p : ComplexModel n)
    (hf : ∀ᶠ z in 𝓝 (g p),MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) f z)
    (hg : ∀ᶠ z in 𝓝 p,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) g z)
    (v : ComplexModel n → ℂ) :
    (GermIdeal.pullback (m := n) g (GermIdeal.pullback (m := n) f A)).mem p v ↔
      (GermIdeal.pullback (m := n) (f ∘ g) A).mem p v := by
  constructor
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro _ ⟨s,hs,rfl⟩
    refine IsInSpanAt.mono ?_
      (CoefficientRestrictionTower.isInSpanAt_comp_map hg (GermIdeal.mem_pullback_iff.mp hs))
    rintro _ ⟨b,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,rfl⟩
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨a ∘ f,GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨a,ha,rfl⟩ (holomorphicAt_comp_map hf (hA _ _ ha))),rfl⟩

private theorem current_chart_source (a : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) a).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a a)=0)
    (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0=0) :
    (currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0).source⊆(chartAt (ComplexModel n) a).target :=
  fun _ hz=>hsrc hz.1

private theorem current_chart_zero (a : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a a)=0)
    (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0=0) :
    (currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0).toFun (chartAt (ComplexModel n) a a)=0 := by
  change Ψ.invFun (Φ.toFun (chartAt (ComplexModel n) a a))=0
  rw [hΦ0]
  exact local_invFun_zero Ψ hΨ0

private theorem current_vanishing_stalk (a : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) a).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a a)=0)
    (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0=0)
    (W : Set M) (z : ComplexModel n)
    (hz : z∈(currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0).target) (v : ComplexModel n → ℂ) :
    (GermIdeal.pullback (m := n) Ψ.toFun
      (vanishingIdeal (n := n) (actualFixedFlatteningSet a Φ W))).mem z v ↔
    (vanishingIdeal (n := n) (actualFixedFlatteningSet a
      (currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0) W)).mem z v := by
  have hg : ∀ᶠ y in 𝓝 z,MDifferentiableAt 𝓘(ℂ,ComplexModel n)
      𝓘(ℂ,ComplexModel n) Ψ.toFun y :=
    eventually_of_mem (Ψ.isOpen_source.mem_nhds hz.1) fun y hy=>
      (Ψ.toFun_holomorphic.differentiableAt (Ψ.isOpen_source.mem_nhds hy)).mdifferentiableAt
  have hf : ∀ᶠ y in 𝓝 (Ψ.toFun z),MDifferentiableAt 𝓘(ℂ,ComplexModel n)
      𝓘(ℂ,ComplexModel n) (actualFlatteningInverseMap a Φ) y :=
    eventually_of_mem (Φ.isOpen_target.mem_nhds hz.2) fun y hy=>
      actualFlatteningInverseMap_mdifferentiable a Φ hsrc y hy
  have hReplace : (GermIdeal.pullback (m := n) Ψ.toFun
      (vanishingIdeal (n := n) (actualFixedFlatteningSet a Φ W))).mem z v ↔
      (GermIdeal.pullback (m := n) Ψ.toFun
        (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) a Φ)).mem z v := by
    constructor
    · intro hv
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
      rintro _ ⟨f,hf,rfl⟩
      exact ⟨f,(flattened_vanishing_mem_iff a Φ hsrc W (Ψ.toFun z) hz.2 f).mpr hf,rfl⟩
    · intro hv
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
      rintro _ ⟨f,hf,rfl⟩
      exact ⟨f,(flattened_vanishing_mem_iff a Φ hsrc W (Ψ.toFun z) hz.2 f).mp hf,rfl⟩
  exact hReplace.trans ((local_pullback_comp_at (vanishingIdeal (n := n) W)
    (fun _ _ hf=>hf.1) (actualFlatteningInverseMap a Φ) Ψ.toFun z hf hg v).trans
      (flattened_vanishing_mem_iff a _ (current_chart_source a Φ hsrc hΦ0 Ψ hΨ0) W z hz v))

private theorem current_true_origin (W : Set M)
    (hW : IsComplexAnalyticSubset (n := n) W) (a : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) a).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a a)=0)
    (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0=0) :
    Ideal.map (localGermAlgEquiv Ψ hΨ0).toRingEquiv.toRingHom
      (originalCoherentOriginIdeal (vanishingIdeal (n := n) (actualFixedFlatteningSet a Φ W)))=
    originalCoherentOriginIdeal (vanishingIdeal (n := n) (actualFixedFlatteningSet a
      (currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0) W)) := by
  have hcoh := CartanIrreducible.cartanCoherence W hW
  have hfg := fixedFlattening_vanishing_local_fg W hcoh a Φ hsrc hΦ0
  have ho := origin_pullback_eq_of_holomorphic_germ Ψ.toFun
    (local_toFun_holomorphic Ψ) hΨ0 _ hfg
  have h0 := actualFlattening_target_zero_mem a _ (current_chart_zero a Φ hΦ0 Ψ hΨ0)
  exact ho.symm.trans (origin_eq_of_zero_mem_iff _ _
    (current_vanishing_stalk a Φ hsrc hΦ0 Ψ hΨ0 W 0 h0))

private theorem original_initial_presentation (W : Set M)
    (hW : IsComplexAnalyticSubset (n := n) W) (a : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) a).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a a)=0) :
    ∃ (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0=0),
      let Ξ:=currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0
      let B:=vanishingIdeal (n := n) (actualFixedFlatteningSet a Ξ W)
      let I:=originalCoherentOriginIdeal B
      ∃ (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
        (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
        (PHS : ActualGeometricInheritedNeighborhoodHS B I G
          (fun ℓ=>hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ)),
        Ideal.span (range G.germs)=I ∧
        (∀ k,ActualInheritedPrefixReducedAt G k) ∧
        (∀ k,actualFixedSelectorContactAt S G.germs k) ∧ PHS.neighborhood⊆Ξ.target := by
  let I0:=originalCoherentOriginIdeal (vanishingIdeal (n := n) (actualFixedFlatteningSet a Φ W))
  obtain ⟨Ψ,hΨ0,G0,hspan0,hDiagram,hContact0,hPrefix0,_hJac0⟩:=
    exists_original_initial_whole_nested_contact_flag n I0
  let Ξ:=currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0
  let B:=vanishingIdeal (n := n) (actualFixedFlatteningSet a Ξ W)
  let I:=originalCoherentOriginIdeal B
  have hspan : Ideal.span (range G0.germs)=I:=
    hspan0.trans (current_true_origin W hW a Φ hsrc hΦ0 Ψ hΨ0)
  have hD : actualInitialDiagram MonomialOrder.degLex (actualInheritedCurrentSourceIdeal I)=
      actualInitialDiagram MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I0) := by
    simpa only [hspan,actualInheritedCurrentSourceIdeal] using hDiagram
  let hV:=actualInitialVertices_eq_of_diagram_eq hD.symm
  let G:=actualCurrentSourceInheritedFamily G0 I hD
  let S:=actualInitialFixedInheritedSelector (analyticZeroTaylorIdeal n I)
  have hSpan : Ideal.span (range G.germs)=I:=
    actualCurrentSourceInheritedFamily_span G0 I hspan hD
  have hPrefix : ∀ k,ActualInheritedPrefixReducedAt G k:=
    fun k=>actualInheritedRelabelFamily_prefix_reduced G0 hV k (hPrefix0 k)
  have hContact : ∀ k,actualFixedSelectorContactAt S G.germs k := by
    intro k
    apply (actualInitialFixedInheritedSelector_contact _ G k).mpr
    exact actualInheritedRelabelFamily_contact G0 hV k (hContact0 k)
  have hΞsrc:=current_chart_source a Φ hsrc hΦ0 Ψ hΨ0
  have hΞ0:=current_chart_zero a Φ hΦ0 Ψ hΨ0
  have hfg:=fixedFlattening_vanishing_local_fg W (CartanIrreducible.cartanCoherence W hW)
    a Ξ hΞsrc hΞ0
  have hReference (ℓ) : hilbertSamuelAt B 0 ℓ=hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ:=
    (hilbertSamuelAt_eq_fixedFlattening_model a Ξ hΞsrc hΞ0 W ℓ).symm
  choose H hH hG using fun i=>HolGerm.exists_eq_mk (G.germs i)
  obtain ⟨PHS,_hSame,hU⟩:=exists_actual_same_representatives_neighborhood_hs B hfg I G
    hSpan hPrefix rfl _ hReference H hH (fun i=>(hG i).symm)
    Ξ.target Ξ.isOpen_target (actualFlattening_target_zero_mem a Ξ hΞ0)
  exact ⟨Ψ,hΨ0,G,S,PHS,hSpan,hPrefix,hContact,hU⟩

private theorem actual_original_window (W : Set M) (a : M)
    (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hsrc : Ξ.source⊆(chartAt (ComplexModel n) a).target)
    (hΞ0 : Ξ.toFun (chartAt (ComplexModel n) a a)=0)
    (U : Opens (ComplexModel n)) (h0U : (0 : ComplexModel n)∈U)
    (hU : (U : Set (ComplexModel n))⊆Ξ.target) :
    ∃ (V : Opens M) (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V),
      a∈V ∧ (∀ z,(η z : M)=actualFlatteningInverseMap a Ξ z.val) ∧
      ∀ z ℓ,hilbertSamuelAt (vanishingIdeal (n := n) (actualFixedFlatteningSet a Ξ W)) z.val ℓ=
        hilbertSamuelAt (vanishingIdeal (n := n) W) (η z : M) ℓ := by
  let Θ:=coordinateTargetRestriction Ξ hΞ0 U h0U hU
  have hΘsrc : Θ.source⊆(chartAt (ComplexModel n) a).target:=fun _ hz=>hsrc hz.1
  let V : Opens M:=⟨flatDomain Θ,isOpen_flatDomain Θ⟩
  let η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V:=
    (actualFlatCoordinateDiffeomorph Θ hΘsrc).symm
  have haV : a∈V:=⟨mem_chart_source _ a,Θ.center_mem_source⟩
  have hSet : (Subtype.val : U → ComplexModel n) ⁻¹' actualFixedFlatteningSet a Ξ W=
      (fun z : U=>actualFlatteningInverseMap a Θ z.val) ⁻¹' W := by
    ext z
    exact and_iff_right (hU z.property)
  refine ⟨V,η,haV,fun _=>rfl,?_⟩
  intro z ℓ
  have hModel:=hilbertSamuelAt_vanishing_actual_open_any (n := n) U (actualFixedFlatteningSet a Ξ W) z ℓ
  rw [hSet] at hModel
  exact hModel.symm.trans (hilbertSamuelAt_vanishing_actual_flat_inverse (n := n) Θ hΘsrc W z ℓ)

/- The old coordinate-pullback API fixes both manifolds in the SAME universe.
Here the original manifold and its actual model open have independent
universes; the genuine coordinate argument, with the actual inverse, applies. -/
private theorem coordinate_family_diffeomorph
    {Y Z : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] (g : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    {ι : Type*} {A : ι → Set Y} {S : ι → Finset (Fin n)} {z : Z}
    (hA : IsCoordinateFamilyAt n A S (g z)) :
    IsCoordinateFamilyAt n (fun i=>g ⁻¹' A i) S z := by
  obtain ⟨Φ,hΦt,hΦ0,hΦA⟩:=hA
  let I:=𝓘(ℂ,ComplexModel n)
  have hrange : range I=univ:=by simp [I]
  let e:=chartAt (ComplexModel n) z
  let e':=chartAt (ComplexModel n) (g z)
  let F : ComplexModel n → ComplexModel n:=fun u=>e' (g (e.symm u))
  let N : Set (ComplexModel n):=e.target∩e.symm ⁻¹' (univ∩g ⁻¹' e'.source)
  have hNo : IsOpen N:=e.continuousOn_symm.isOpen_inter_preimage e.open_target
    (isOpen_univ.inter (g.contMDiff.continuous.isOpen_preimage _ e'.open_source))
  have hzN : e z∈N:=⟨e.map_source (mem_chart_source _ z),by
    rw [mem_preimage,e.left_inv (mem_chart_source _ z)]
    exact ⟨mem_univ _,mem_chart_source _ (g z)⟩⟩
  have hFN : DifferentiableOn ℂ F N := by
    have h:=(contMDiffOn_iff.mp (g.contMDiff.contMDiffOn (s := univ))).2 z (g z)
    refine (h.differentiableOn (by simp)).mono ?_
    intro u hu
    exact ⟨⟨mem_univ _,hu.1⟩,mem_univ _,hu.2.2,mem_univ _⟩
  have hmd : MDifferentiableAt I I g z:=(g.contMDiff z).mdifferentiableAt (by simp)
  have hderiv : mfderiv I I g z=fderiv ℂ F (e z) := by
    rw [hmd.mfderiv,hrange,fderivWithin_univ]
    rfl
  have hleft : (mfderiv I I g.symm (g z)).comp (mfderiv I I g z)=ContinuousLinearMap.id ℂ _ := by
    rw [←mfderiv_comp z ((g.symm.contMDiff (g z)).mdifferentiableAt (by simp)) hmd,
      show g.symm ∘ g=id from funext g.symm_apply_apply]
    exact mfderiv_id
  have hInjective : Function.Injective (mfderiv I I g z):=
    Function.LeftInverse.injective (g := mfderiv I I g.symm (g z))
      (fun v=>DFunLike.congr_fun hleft v)
  have hinj : Function.Injective (fderiv ℂ F (e z)):=hderiv ▸ hInjective
  obtain ⟨Ψ,hΨN,hΨF,_⟩:=exists_localHolomorphicEquivAt hNo hzN hFN hinj
  have hFz : F (e z)=e' (g z):=by simp only [F,e.left_inv (mem_chart_source _ z)]
  refine ⟨LocalHolomorphicEquivAt.comp Ψ Φ (hΨF ▸ hFz),?_,?_,?_⟩
  · intro u hu
    exact (hΨN hu.1).1
  · change Φ.toFun (Ψ.toFun (e z))=0
    rw [hΨF,hFz]
    exact hΦ0
  · intro i hzi y hy hyΘ
    change e y∈Ψ.source∩Ψ.toFun ⁻¹' Φ.source at hyΘ
    change g y∈A i ↔ Φ.toFun (Ψ.toFun (e y))∈coordSubspace (S i)
    have hyN:=(hΨN hyΘ.1).2
    rw [mem_preimage,e.left_inv hy] at hyN
    have hFy : F (e y)=e' (g y):=by simp only [F,e.left_inv hy]
    have hyΦ : e' (g y)∈Φ.source := by
      have h:=hyΘ.2
      rwa [mem_preimage,hΨF,hFy] at h
    rw [hΨF,hFy]
    exact hΦA i hzi hyN.2 hyΦ

private theorem entire_boundary_snc {U : Opens (ComplexModel n)}
    (E : List (Set M)) (hE : IsSNCDivisor n E) (V : Opens M)
    (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V) :
    IsSNCDivisor n (E.map ((fun z : U=>(η z : M)) ⁻¹' ·)) := by
  have hV : IsSNCDivisor n (E.map ((Subtype.val : V → M) ⁻¹' ·)):=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage (n := n)
    (NormalCrossingsInvariance.pullsBackCoordinates_val V) continuous_subtype_val hE
  let F:=E.map ((Subtype.val : V → M) ⁻¹' ·)
  have hPulled : IsSNCDivisor n (F.map (η ⁻¹' ·)) := by
    refine ⟨?_,?_⟩
    · intro H hH
      obtain ⟨H0,hH0,rfl⟩:=List.mem_map.mp hH
      exact (hV.1 H0 hH0).preimage η.contMDiff.continuous
    · intro z
      obtain ⟨S,hS,hCard,hInj⟩:=hV.2 (η z)
      let c : Fin (F.map (η ⁻¹' ·)).length → Fin F.length:=Fin.cast (List.length_map _)
      have hGet (i) : (F.map (η ⁻¹' ·)).get i=η ⁻¹' F.get (c i) := by
        simp [List.get_eq_getElem,c]
      refine ⟨fun i=>S (c i),IsCoordinateFamilyAt.reindex
        (coordinate_family_diffeomorph η hS) c hGet (fun _=>rfl),?_,?_⟩
      · intro i hi
        exact hCard (c i) (by rwa [hGet] at hi)
      · intro i hi j hj hij
        have hi' : η z∈F.get (c i) := by
          change z∈(F.map (η ⁻¹' ·)).get i at hi
          rwa [hGet] at hi
        have hj' : η z∈F.get (c j) := by
          change z∈(F.map (η ⁻¹' ·)).get j at hj
          rwa [hGet] at hj
        exact Fin.cast_injective _ (hInj hi' hj' hij)
  simpa only [F,List.map_map,Set.preimage_preimage,Function.comp_def] using hPulled

end OriginalChart

/-- The literal finite powered-function record, with EVERY original boundary
position pulled through the actual map supplied by the original-only producer. -/
def initialWeightedRecord
    {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    {M : Type u} (η : presentationOpen PHS → M) (E : List (Set M)) :
    MarkedIdeal n (presentationOpen PHS) :=
  ⟨univ,E.map (η ⁻¹' ·),weightedFunctionIdeal (fun i=>normalExponentDegree i.val)
    (fun i (z : presentationOpen PHS)=>PHS.representatives i z.val),
    weightedCommonMark (fun i : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val)⟩

section Presentation
variable {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ → ℕ}

private theorem presentation_functions_mdifferentiable
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) (i) :
    MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (fun z : presentationOpen PHS=>PHS.representatives i z.val) := by
  intro z
  have hh:=holomorphicAt_of_mdifferentiableOn PHS.isOpen_neighborhood
    (mdifferentiableOn_iff_differentiableOn.mpr (PHS.holomorphicOn i)) z.property
  exact (hh.comp_contMDiff (Eventually.of_forall fun _=>
    (contMDiff_subtype_val (U := presentationOpen PHS)).contMDiffAt)).mdifferentiableAt

private theorem translated_order_of_native_order
    (U : Opens (ComplexModel n)) (z : U) (f : ComplexModel n → ℂ)
    (hf : HolAt f z.val) (q : ℕ)
    (hv : VanishesToOrderOn n univ z q (fun w : U=>f w.val)) :
    translatedGerm z.val f hf∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  apply (translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal z.val f hf q).mpr
  have hPow:=mem_idealPow_of_vanishesToOrderOn_univ hv
  have hExt:=mem_idealPow_pointIdeal_extendOpens U q hPow
  apply mem_idealPow_congr hExt
  filter_upwards [U.isOpen.mem_nhds z.property] with w hw
  change extendOpens U (fun a : U=>f a.val) (⟨w,hw⟩ : U).val=f w
  rw [extendOpens_val]

private theorem initial_record_cosupp_iff
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS → M) (E : List (Set M))
    (z : presentationOpen PHS) :
    z∈(initialWeightedRecord PHS η E).cosupp ↔ ∀ ℓ,hilbertSamuelAt A z.val ℓ=R ℓ := by
  let U:=presentationOpen PHS
  let μ:=fun i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>
    normalExponentDegree i.val
  let f:=fun i (y : U)=>PHS.representatives i y.val
  have hf (i) := presentation_functions_mdifferentiable PHS i
  have hhol (i) : HolomorphicAt n (f i) z:=
    holomorphicAt_of_mdifferentiableOn isOpen_univ (hf i).mdifferentiableOn (mem_univ z)
  change z∈cosupport n univ (weightedFunctionIdeal μ f) (weightedCommonMark μ) ↔ _
  rw [cosupport_weightedFunctionIdeal μ hw f hf]
  simp only [mem_iInter]
  constructor
  · intro hz
    apply (PHS.wholeHS z.val z.property).mp
    intro i
    have hv:=((mem_cosupport_finiteFunctionIdeal_iff (fun _ : Unit=>f i) z (μ i)
      (fun _=>hhol i)).mp (hz i)) ()
    exact translated_order_of_native_order U z _ (PHS.holomorphicAt _ z.property i) _ hv
  · intro hHS i
    apply (mem_cosupport_finiteFunctionIdeal_iff (fun _ : Unit=>f i) z (μ i) (fun _=>hhol i)).mpr
    intro _
    have hGerm:=((PHS.wholeHS z.val z.property).mpr hHS) i
    have hPoint:=(translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal z.val _
      (PHS.holomorphicAt _ z.property i) (μ i)).mp hGerm
    have hPulled:=comp_mem_idealPow_pointIdeal
      (φ := (Subtype.val : U → ComplexModel n)) (u := z)
      (Eventually.of_forall fun y=>(contMDiff_subtype_val (U := U) (n := ∞) y).mdifferentiableAt (by simp))
      (μ i) hPoint
    exact ⟨f i,hPulled,Eventually.of_forall fun _ _=>rfl⟩

end Presentation

/-- The original analytic geometry supplies the weighted Hilbert–Samuel
record and its full initial data directly. -/
theorem exists_original_initial_hs_data
    {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    (a : M) (ha : a∈singularSet (n := n) W)
    (E : List (Set M)) (hE : IsSNCDivisor n E)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) a).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a a)=0) :
    ∃ (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0=0),
      let Ξ:=currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0
      ∃ (_hΞsrc : Ξ.source⊆(chartAt (ComplexModel n) a).target)
        (_hΞ0 : Ξ.toFun (chartAt (ComplexModel n) a a)=0),
      let B:=vanishingIdeal (n := n) (actualFixedFlatteningSet a Ξ W)
      let I:=originalCoherentOriginIdeal B
      ∃ (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
        (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
        (PHS : ActualGeometricInheritedNeighborhoodHS B I G
          (fun ℓ=>hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ)),
        Ideal.span (range G.germs)=I ∧ (∀ i,G.germs i∈I) ∧
        (∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
          0<normalExponentDegree i.val) ∧
        (∀ k,ActualInheritedPrefixReducedAt G k) ∧
        (∀ k,actualFixedSelectorContactAt S G.germs k) ∧
        (∀ k,(actualFixedSelectorJacobian S G.germs k).det≠0) ∧
        PHS.neighborhood⊆Ξ.target ∧
        (∀ ℓ,hilbertSamuelValue I ℓ=hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) ∧
      ∃ (V : Opens M)
        (η : presentationOpen PHS ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V),
        a∈V ∧ (∀ z,(η z : M)=actualFlatteningInverseMap a Ξ z.val) ∧
        (∀ z ℓ,hilbertSamuelAt B z.val ℓ=hilbertSamuelAt (vanishingIdeal (n := n) W) (η z : M) ℓ) ∧
        let Q:=initialWeightedRecord PHS (fun z=>(η z : M)) E
        IsInvDomain n Q ∧
        Q.cosupp={z | ∀ ℓ,hilbertSamuelAt (vanishingIdeal (n := n) W) (η z : M) ℓ=
          hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ} ∧
        Q.cosupp⊆(fun z=>(η z : M)) ⁻¹' singularSet (n := n) W ∧
        (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈Q.cosupp := by
  obtain ⟨Ψ,hΨ0,G,S,PHS,hSpan,hPrefix,hContact,hU⟩:=original_initial_presentation W hW a Φ hsrc hΦ0
  let Ξ:=currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0
  let B:=vanishingIdeal (n := n) (actualFixedFlatteningSet a Ξ W)
  let I:=originalCoherentOriginIdeal B
  have hΞsrc:=current_chart_source a Φ hsrc hΦ0 Ψ hΨ0
  have hΞ0:=current_chart_zero a Φ hΦ0 Ψ hΨ0
  have hMem (i) : G.germs i∈I:=hSpan.le (Ideal.subset_span ⟨i,rfl⟩)
  have h0B : (0 : ComplexModel n)∈actualFixedFlatteningSet a Ξ W := by
    refine ⟨actualFlattening_target_zero_mem a Ξ hΞ0,?_⟩
    change actualFlatteningInverseMap a Ξ 0∈W
    rw [actualFlatteningInverseMap_zero a Ξ hΞ0]
    exact (mem_singularSet_iff.mp ha).1
  have hw:=positive_marks_of_true_origin _ h0B G hMem
  obtain ⟨V,η,haV,hη,hCov⟩:=actual_original_window W a Ξ hΞsrc hΞ0
    (presentationOpen PHS) PHS.zero_mem hU
  let Q:=initialWeightedRecord PHS (fun z=>(η z : M)) E
  have hBoundary:=entire_boundary_snc E hE V η
  have hNonzero:=presentation_weighted_nonzero hW ha PHS hw
  have hDom : IsInvDomain n Q := by
    refine ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
      isCoherent_weightedFunctionIdeal _ _ (presentation_functions_mdifferentiable PHS),
      hBoundary,isTransverse_univ_of_isSNCDivisor hBoundary⟩,?_,hNonzero.1,?_⟩
    · intro z _
      exact ⟨n,le_rfl,EmbeddedFromResolution.regularAtDim_of_mem_nhds (by
        change (univ : Set (presentationOpen PHS))∈𝓝 z
        exact Filter.univ_mem)⟩
    · intro z _
      exact hNonzero.2 z
  have hCos : Q.cosupp={z | ∀ ℓ,hilbertSamuelAt (vanishingIdeal (n := n) W) (η z : M) ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ} := by
    ext z
    rw [initial_record_cosupp_iff PHS hw]
    exact forall_congr' fun ℓ=>by rw [hCov z ℓ]
  have hSing : Q.cosupp⊆(fun z=>(η z : M)) ⁻¹' singularSet (n := n) W := by
    intro z hz
    apply entire_hs_equality_locus_subset_singularSet hW ha
    rw [hCos] at hz
    exact hz
  have hZero : (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈Q.cosupp := by
    rw [hCos]
    intro ℓ
    rw [hη,actualFlatteningInverseMap_zero a Ξ hΞ0]
  have hOriginHS (ℓ) : hilbertSamuelValue I ℓ=hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ:=
    (hilbertSamuelAt_model_zero B ℓ).symm.trans
      (hilbertSamuelAt_eq_fixedFlattening_model a Ξ hΞsrc hΞ0 W ℓ).symm
  refine ⟨Ψ,hΨ0,hΞsrc,hΞ0,G,S,PHS,hSpan,hMem,hw,hPrefix,hContact,
    fun k=>actualFixedSelectorJacobian_det_ne_zero S G.germs G.monic G.lower k,
    hU,hOriginHS,V,η,haV,hη,hCov,hDom,hCos,hSing,hZero⟩

/-- ORIGINAL analytic geometry initializes all historical witnesses, the SAME
true geometric presentation and ENTIRE boundary record, and chooses an actual
finite marked phase. No initial family, selector, PHS or domain is given. -/
theorem exists_original_initial_hs_phase
    {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    (a : M) (ha : a∈singularSet (n := n) W)
    (E : List (Set M)) (hE : IsSNCDivisor n E)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) a).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a a)=0) :
    ∃ (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0=0),
      let Ξ:=currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0
      ∃ (_hΞsrc : Ξ.source⊆(chartAt (ComplexModel n) a).target)
        (_hΞ0 : Ξ.toFun (chartAt (ComplexModel n) a a)=0),
      let B:=vanishingIdeal (n := n) (actualFixedFlatteningSet a Ξ W)
      let I:=originalCoherentOriginIdeal B
      ∃ (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
        (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
        (PHS : ActualGeometricInheritedNeighborhoodHS B I G
          (fun ℓ=>hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ)),
        Ideal.span (range G.germs)=I ∧ (∀ i,G.germs i∈I) ∧
        (∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
          0<normalExponentDegree i.val) ∧
        (∀ k,ActualInheritedPrefixReducedAt G k) ∧
        (∀ k,actualFixedSelectorContactAt S G.germs k) ∧
        (∀ k,(actualFixedSelectorJacobian S G.germs k).det≠0) ∧
        PHS.neighborhood⊆Ξ.target ∧
        (∀ ℓ,hilbertSamuelValue I ℓ=hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) ∧
      ∃ (V : Opens M)
        (η : presentationOpen PHS ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V),
        a∈V ∧ (∀ z,(η z : M)=actualFlatteningInverseMap a Ξ z.val) ∧
        (∀ z ℓ,hilbertSamuelAt B z.val ℓ=hilbertSamuelAt (vanishingIdeal (n := n) W) (η z : M) ℓ) ∧
        let Q:=initialWeightedRecord PHS (fun z=>(η z : M)) E
        IsInvDomain n Q ∧
        Q.cosupp={z | ∀ ℓ,hilbertSamuelAt (vanishingIdeal (n := n) W) (η z : M) ℓ=
          hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ} ∧
        Q.cosupp⊆(fun z=>(η z : M)) ⁻¹' singularSet (n := n) W ∧
        (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈Q.cosupp ∧
        ∀ (K : Set (presentationOpen PHS)),IsCompact K →
        ∀ (O : Opens (presentationOpen PHS)),(O : Set (presentationOpen PHS))⊆K →
        ∃ (Y : CMfd n) (T : BlowupTower (CMfd.of (n := n) O) Y),
          IsCanonical (MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS) Q)
            ((CanonicalCentres.canonicalInvariant n).inv
              (MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS) Q)) T ∧
          IsGeoResolution (MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS) Q) T := by
  obtain ⟨Ψ,hΨ0,hΞsrc,hΞ0,G,S,PHS,hSpan,hMem,hw,hPrefix,hContact,hJac,
    hU,hOriginHS,V,η,haV,hη,hCov,hDom,hCos,hSing,hZero⟩ :=
    exists_original_initial_hs_data W hW a ha E hE Φ hsrc hΦ0
  refine ⟨Ψ,hΨ0,hΞsrc,hΞ0,G,S,PHS,hSpan,hMem,hw,hPrefix,hContact,hJac,
    hU,hOriginHS,V,η,haV,hη,hCov,hDom,hCos,hSing,hZero,?_⟩
  intro K hK O hO
  exact HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (CanonicalCentres.canonicalInvariant n) (X := CMfd.of (n := n) (presentationOpen PHS)) hDom hK O hO

end
end Hironaka.HironakaActualOriginalInitialHSPhase
