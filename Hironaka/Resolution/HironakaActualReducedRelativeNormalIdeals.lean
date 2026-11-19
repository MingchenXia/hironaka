import Hironaka.Resolution.HironakaActualIteratedRelativeNormalHistory
import Hironaka.Resolution.HironakaActualIntrinsicStableIdealSquare

/-! ENTIRE reduced normal ideal dictionaries on the ACTUAL original opens.
No coherent ideal is extended outside its original local domain.
Blueprint: hironaka-actual-reduced-relative-normal-ideals-20261102.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualReducedRelativeNormalIdeals
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualRelativeNormalGeometry HironakaActualIteratedRelativeNormalHistory
  HironakaActualIntrinsicStableIdealSquare HironakaActualZeroCoordinateContactSeed
  RelativePrincipalizationSpan GermIdealPullbackCalculus RestrictedIdealExtension
  HomogenizedGlueing InvertibleIdealQuotient BlowupRestrictOpen

def normalCarrier {n : ℕ} {U : Opens (ComplexModel n)} (C : Set U) : Set (productOpen U):=
  zeroSection U '' C

private theorem projection_section {n : ℕ} (U : Opens (ComplexModel n)) (x : U) :
    projection U (zeroSection U x)=x:=by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

private theorem section_projection {n : ℕ} {U : Opens (ComplexModel n)} {z : productOpen U}
    (hz : actualJointNormalProjection n 1 z.val=0) : zeroSection U (projection U z)=z:=by
  apply Subtype.ext
  change tangentInclusion n 1 (tangentProjection n 1 z.val)=z.val
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz,map_zero,add_zero] using
    (join_projections (n:=n) (m:=1) z.val)

private theorem normalCarrier_eq {n : ℕ} {U : Opens (ComplexModel n)} (C : Set U) :
    normalCarrier C={z | projection U z∈C ∧ actualJointNormalProjection n 1 z.val=0}:=by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨by simpa only [projection_section] using hx,?_⟩
    change actualJointNormalProjection n 1 (tangentInclusion n 1 x.val)=0
    simp
  · rintro ⟨hx,hz⟩
    exact ⟨projection U z,hx,section_projection hz⟩

theorem normalCarrier_analytic {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (hC : IsComplexAnalyticSubset (n:=n) C) : IsComplexAnalyticSubset (n:=n+1) (normalCarrier C):=by
  have hp:=AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (projection_contMDiff U) hC
  have hq:=AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (g:=fun z : productOpen U=>actualJointNormalProjection n 1 z.val)
    ((actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val)
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))
  rw [normalCarrier_eq]
  exact hp.inter hq

private theorem normalCarrier_preimage_global {n : ℕ} {U : Opens (ComplexModel n)} (C : Set U) :
    normalCarrier C=(Subtype.val : productOpen U→ComplexModel (n+1)) ⁻¹'
      zeroCoordinateCarrier (m:=1) ((Subtype.val : U→ComplexModel n) '' C):=by
  rw [normalCarrier_eq]
  ext z
  change (projection U z∈C ∧ actualJointNormalProjection n 1 z.val=0) ↔
    (tangentProjection n 1 z.val∈(Subtype.val : U→ComplexModel n) '' C ∧ actualJointNormalProjection n 1 z.val=0)
  constructor
  · rintro ⟨hc,hq⟩
    exact ⟨⟨projection U z,hc,rfl⟩,hq⟩
  · rintro ⟨⟨x,hx,he⟩,hq⟩
    have hx' : x=projection U z:=Subtype.ext he
    exact ⟨hx' ▸ hx,hq⟩

private abbrev normalIdeal (n : ℕ) : GermIdeal (n+1) (ComplexModel (n+1)):=
  vanishingIdeal (n:=n+1) (HironakaActualZeroCoordinateContactSeed.zeroPlane n)

private abbrev normalPullback {n : ℕ} (U : Opens (ComplexModel n)) : GermIdeal (n+1) (productOpen U):=
  GermIdeal.pullback (m:=n+1) (Subtype.val : productOpen U→ComplexModel (n+1)) (normalIdeal n)

private theorem normal_coherent (n : ℕ) : (normalIdeal n).IsCoherent:=by
  apply CartanIrreducible.cartanCoherence
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (actualJointNormalProjection n 1).contMDiff
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))

private theorem normalPullback_coherent {n : ℕ} (U : Opens (ComplexModel n)) : (normalPullback U).IsCoherent:=
  isCoherent_pullback contMDiff_subtype_val (normal_coherent n)

private theorem pullback_mem_comp {a b : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X]
    [ChartedSpace (ComplexModel b) Y] [IsComplexManifold b Y]
    (f : Y→X) (hf : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ f)
    {A : GermIdeal a X} {x : Y} {g : X→ℂ} (hg : A.mem (f x) g) (hh : HolomorphicAt a g (f x)) :
    (GermIdeal.pullback (m:=b) f A).mem x (g∘f):=
  GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩
    (hh.comp_contMDiff (Eventually.of_forall fun _=>hf.contMDiffAt)))

private theorem pullback_vanishing_le {a b : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X]
    [ChartedSpace (ComplexModel b) Y] [IsComplexManifold b Y]
    (f : Y→X) (hf : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ f) (A : Set X) :
    (GermIdeal.pullback (m:=b) f (vanishingIdeal (n:=a) A)).Le
      (vanishingIdeal (n:=b) (f ⁻¹' A)):=by
  intro x g hg
  obtain ⟨hh,N,s,c,hs,_hc,he⟩:=GermIdeal.mem_pullback_iff.mp hg
  have hs0 : ∀i,∀ᶠ y in 𝓝 x,y∈f ⁻¹' A → s i y=0:=by
    intro i
    obtain ⟨v,hv,hsv⟩:=hs i
    filter_upwards [hf.continuous.continuousAt.eventually hv.2] with y hy hyA
    rw [hsv,Function.comp_apply]
    exact hy hyA
  refine ⟨hh,?_⟩
  filter_upwards [he,eventually_all.mpr hs0] with y hy hy0 hyA
  rw [hy]
  exact Finset.sum_eq_zero fun i _=>by rw [hy0 i hyA,mul_zero]

private theorem vanishing_le_of_subset {a : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X] {A B : Set X} (hAB : A⊆B) :
    (vanishingIdeal (n:=a) B).Le (vanishingIdeal (n:=a) A):=by
  intro x g hg
  exact ⟨hg.1,hg.2.mono fun y hy hyA=>hy (hAB hyA)⟩

private theorem normal_sum_le_vanishing {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (hC : IsComplexAnalyticSubset (n:=n) C) :
    (relativeNormalIdeal (vanishingIdeal (n:=n) C)).Le (vanishingIdeal (n:=n+1) (normalCarrier C)):=by
  have hTarget:=(CartanIrreducible.cartanCoherence _ (normalCarrier_analytic hC))
  have hP : normalCarrier C⊆(projection U) ⁻¹' C:=fun z hz=>(Set.ext_iff.mp (normalCarrier_eq C) z).mp hz |>.1
  have hN : normalCarrier C⊆(Subtype.val : productOpen U→ComplexModel (n+1)) ⁻¹'
      HironakaActualZeroCoordinateContactSeed.zeroPlane n:=
    fun z hz=>(Set.ext_iff.mp (normalCarrier_eq C) z).mp hz |>.2
  intro z f hf
  change IsInSpanAt (n:=n+1)
    (fun g=>(GermIdeal.pullback (m:=n+1) (projection U) (vanishingIdeal (n:=n) C)).mem z g ∨
      (normalPullback U).mem z g) z f at hf
  apply HomogenizedIdeal.mem_of_isInSpanAt hTarget
  refine IsInSpanAt.mono (fun g hg=>?_) hf
  rcases hg with hp | hn
  · exact vanishing_le_of_subset hP z g (pullback_vanishing_le (projection U) (projection_contMDiff U) C z g hp)
  · exact vanishing_le_of_subset hN z g
      (pullback_vanishing_le (Subtype.val : productOpen U→ComplexModel (n+1)) contMDiff_subtype_val
        (HironakaActualZeroCoordinateContactSeed.zeroPlane n) z g hn)

private theorem normal_sum_mem_off_plane {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (hC : IsComplexAnalyticSubset (n:=n) C) {z : productOpen U}
    (hz : actualJointNormalProjection n 1 z.val≠0) {f : productOpen U→ℂ} (hf : HolomorphicAt (n+1) f z) :
    (relativeNormalIdeal (vanishingIdeal (n:=n) C)).mem z f:=by
  have h1 : (normalIdeal n).mem z.val (fun _=>1):=by
    refine ⟨holomorphicAt_const 1,?_⟩
    filter_upwards [(isClosed_eq (actualJointNormalProjection n 1).continuous continuous_const).isOpen_compl.mem_nhds hz]
      with y hy hyH
    exact False.elim (hy hyH)
  have hp1:=pullback_mem_comp (Subtype.val : productOpen U→ComplexModel (n+1)) contMDiff_subtype_val h1 h1.1
  have hJ1 : (relativeNormalIdeal (vanishingIdeal (n:=n) C)).mem z (fun _=>1):=
    le_sumIdeal_right (normalPullback_coherent U) z _ hp1
  have hJ:=relativeNormalIdeal_isCoherent (CartanIrreducible.cartanCoherence _ hC)
  exact HomogenizedIdeal.mem_of_isInSpanAt hJ
    (isInSpanAt_of_eq_mul hJ1 hf hf (Eventually.of_forall fun y=>(mul_one (f y)).symm))

private theorem normal_sum_mem_section {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (hC : IsComplexAnalyticSubset (n:=n) C) (x : U) (f : productOpen U→ℂ)
    (hR : (vanishingIdeal (n:=n+1) (normalCarrier C)).mem (zeroSection U x) f) :
    (relativeNormalIdeal (vanishingIdeal (n:=n) C)).mem (zeroSection U x) f:=by
  let W : Set (ComplexModel n):=(Subtype.val : U→ComplexModel n) '' C
  have hR' : (vanishingIdeal (n:=n+1)
      ((Subtype.val : productOpen U→ComplexModel (n+1)) ⁻¹' zeroCoordinateCarrier (m:=1) W)).mem (zeroSection U x) f:=by
    simpa only [normalCarrier_preimage_global,W] using hR
  have hGlobal : (vanishingIdeal (n:=n+1) (zeroCoordinateCarrier (m:=1) W)).mem (tangentInclusion n 1 x.val)
      (extendOpens (productOpen U) f):=vanishingIdeal_opens_mem_iff (productOpen U) |>.mp hR'
  obtain ⟨_hF,N,s,a,hs,ha,he⟩:=(zero_coordinate_functional_mem_iff (m:=1) W x.val (extendOpens (productOpen U) f)).mp hGlobal
  have hI : (vanishingIdeal (n:=n) C).IsCoherent:=CartanIrreducible.cartanCoherence _ hC
  have hJ:=relativeNormalIdeal_isCoherent hI
  apply HomogenizedIdeal.mem_of_isInSpanAt hJ
  refine ⟨hR.1,N,(fun i=>s i∘Subtype.val),(fun i=>a i∘Subtype.val),?_,?_,?_⟩
  · intro i
    change (relativeNormalIdeal (vanishingIdeal (n:=n) C)).mem (zeroSection U x) (s i∘Subtype.val)
    rcases hs i with ⟨b,hb,hsb⟩ | ⟨j,hsj⟩
    · have hLocal : (vanishingIdeal (n:=n) C).mem x (b∘Subtype.val):=by
        have h:=vanishingIdeal_opens_mem_comp_val U hb
        simpa only [W,Subtype.val_injective.preimage_image] using h
      have hBase : (vanishingIdeal (n:=n) C).mem (projection U (zeroSection U x)) (b∘Subtype.val):=by
        simpa only [projection_section] using hLocal
      have hp:=pullback_mem_comp (projection U) (projection_contMDiff U) hBase hBase.1
      rw [hsb]
      exact le_sumIdeal_left (isCoherent_pullback (projection_contMDiff U) hI) (zeroSection U x) _ hp
    · have hCoord : (normalIdeal n).mem (tangentInclusion n 1 x.val) (fun y=>y (j.natAdd n)):=by
        refine ⟨Eventually.of_forall (fun _=>(EuclideanSpace.proj (j.natAdd n) : ComplexModel (n+1)→L[ℂ] ℂ).differentiableAt.mdifferentiableAt),?_⟩
        exact Eventually.of_forall fun y hy=>congrArg (fun v : ComplexModel 1=>v j) hy
      have hp:=pullback_mem_comp (x:=zeroSection U x)
        (Subtype.val : productOpen U→ComplexModel (n+1)) contMDiff_subtype_val hCoord hCoord.1
      rw [hsj]
      exact le_sumIdeal_right (normalPullback_coherent U) (zeroSection U x) _ hp
  · intro i
    exact (ha i).comp_contMDiff (f:=(Subtype.val : productOpen U→ComplexModel (n+1))) (y:=zeroSection U x)
      (Eventually.of_forall fun _=>(contMDiff_subtype_val :
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞
        (Subtype.val : productOpen U→ComplexModel (n+1))).contMDiffAt)
  · filter_upwards [(continuous_subtype_val : Continuous (Subtype.val : productOpen U→ComplexModel (n+1))).continuousAt.eventually he] with y hy
    simpa only [Function.comp_apply,extendOpens_val] using hy

/-- ENTIRE actual reduced relative normal ideals, not merely their cosupport
or their section pullback. The ORIGINAL local ideal remains on its actual U. -/
theorem relative_reduced_normal_ideal {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (hC : IsComplexAnalyticSubset (n:=n) C) :
    relativeNormalIdeal (vanishingIdeal (n:=n) C)=vanishingIdeal (n:=n+1) (normalCarrier C):=by
  apply GermIdeal.ext
  funext z f
  apply propext
  constructor
  · exact normal_sum_le_vanishing hC z f
  · intro hR
    by_cases hz : actualJointNormalProjection n 1 z.val=0
    · have he:=section_projection hz
      have hR' : (vanishingIdeal (n:=n+1) (normalCarrier C)).mem (zeroSection U (projection U z)) f:=he.symm ▸ hR
      exact he ▸ normal_sum_mem_section hC (projection U z) f hR'
    · exact normal_sum_mem_off_plane hC hz hR.1

theorem iterated_normal_carrier_analytic {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (hC : IsComplexAnalyticSubset (n:=n) C) (r : ℕ) :
    IsComplexAnalyticSubset (n:=n+r) (iteratedZeroSection U r '' C):=by
  induction r with
  | zero=>
    change IsComplexAnalyticSubset (n:=n) (id '' C)
    rw [image_id]
    exact hC
  | succ r ih=>
    have he : iteratedZeroSection U (r+1) '' C=
        zeroSection (iteratedOpen U r) '' (iteratedZeroSection U r '' C):=by
      rw [image_image]
      rfl
    rw [he]
    exact normalCarrier_analytic ih

theorem iterated_reduced_normal_ideal {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (hC : IsComplexAnalyticSubset (n:=n) C) (r : ℕ) :
    iteratedIdeal (vanishingIdeal (n:=n) C) r=
      vanishingIdeal (n:=n+r) (iteratedZeroSection U r '' C):=by
  induction r with
  | zero=>change vanishingIdeal (n:=n) C=vanishingIdeal (n:=n) (id '' C);rw [image_id]
  | succ r ih=>
    have he : iteratedZeroSection U (r+1) '' C=
        zeroSection (iteratedOpen U r) '' (iteratedZeroSection U r '' C):=by
      rw [image_image]
      rfl
    change relativeNormalIdeal (iteratedIdeal (vanishingIdeal (n:=n) C) r)=_
    rw [ih,he]
    exact relative_reduced_normal_ideal (iterated_normal_carrier_analytic hC r)

end
end Hironaka.HironakaActualReducedRelativeNormalIdeals
