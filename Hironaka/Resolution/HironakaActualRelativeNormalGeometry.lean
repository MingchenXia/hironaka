import Hironaka.Resolution.HironakaActualMarkOneFixedContactHistory
import Hironaka.Resolution.HironakaActualNativeSectionInitialBar

/-! Entire original relative normal geometry on the actual product over an
arbitrary original open. The coherent ideal is never extended to all coordinate
space. Blueprint: hironaka-actual-relative-normal-geometry-20261102.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualRelativeNormalGeometry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualZeroCoordinateContactSeed RelativePrincipalizationSpan
  GermIdealPullbackCalculus GermIdealOrder TangentDirectionAlong GiraudAlong
  HomogenizedGlueing DerivativeIdeal IdealWeightPowers InvertibleIdealQuotient
  BlowupTowers BlowupTowerTransforms HomogenizedIdealAlong StepOneValue
  CodimOneSupportAlong HironakaSmoothSubmersionOrderedChoiceImageTrace
  RestrictedIdealExtension HironakaSmoothSubmersionRelativeRestriction
open ResolutionInvariantSpec (IsInvDomain)

private abbrev baseModel {n : ℕ} (U : Opens (ComplexModel n)) : CMfd n:=CMfd.of (n:=n) U
private abbrev ambientModel {n : ℕ} (U : Opens (ComplexModel n)) : CMfd (n+1):=
  CMfd.of (n:=n+1) (productOpen U)

def relativeBaseMarked {n : ℕ} {U : Opens (ComplexModel n)} (I : GermIdeal n U) : MarkedIdeal n (baseModel U):=
  ⟨univ,[],I,1⟩

private def normalPlaneIdeal (n : ℕ) : GermIdeal (n+1) (ComplexModel (n+1)):=
  vanishingIdeal (n:=n+1) (HironakaActualZeroCoordinateContactSeed.zeroPlane n)

def relativeNormalIdeal {n : ℕ} {U : Opens (ComplexModel n)} (I : GermIdeal n U) :
    GermIdeal (n+1) (productOpen U):=
  sumIdeal (GermIdeal.pullback (m:=n+1) (projection U) I)
    (GermIdeal.pullback (m:=n+1) (Subtype.val : productOpen U→ComplexModel (n+1)) (normalPlaneIdeal n))

def relativeNormalMarked {n : ℕ} {U : Opens (ComplexModel n)} (I : GermIdeal n U) :
    MarkedIdeal (n+1) (ambientModel U):=⟨univ,[],relativeNormalIdeal I,1⟩

def relativeNormalCoordinate {n : ℕ} (U : Opens (ComplexModel n)) : productOpen U→ℂ:=
  addedCoordinate n ∘ Subtype.val

private theorem normalPlaneIdeal_coherent (n : ℕ) : (normalPlaneIdeal n).IsCoherent:=by
  apply CartanIrreducible.cartanCoherence
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (actualJointNormalProjection n 1).contMDiff
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))

private theorem normalPullback_coherent {n : ℕ} (U : Opens (ComplexModel n)) :
    (GermIdeal.pullback (m:=n+1) (Subtype.val : productOpen U→ComplexModel (n+1)) (normalPlaneIdeal n)).IsCoherent:=
  isCoherent_pullback contMDiff_subtype_val (normalPlaneIdeal_coherent n)

theorem relativeNormalIdeal_isCoherent {n : ℕ} {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) : (relativeNormalIdeal I).IsCoherent:=
  isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hI) (normalPullback_coherent U)

private theorem pullback_mem_comp {a b : ℕ} {X : CMfd a} {Y : CMfd b}
    (f : Y→X) (hf : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ f)
    {I : GermIdeal a X} (hI : I.IsCoherent) {x : Y} {g : X→ℂ} (hg : I.mem (f x) g) :
    (GermIdeal.pullback (m:=b) f I).mem x (g∘f):=
  GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩
    ((GermIdeal.IsCoherent.holomorphicAt_mem hI hg).comp_contMDiff
      (Eventually.of_forall fun _=>hf.contMDiffAt)))

private theorem projection_section {n : ℕ} (U : Opens (ComplexModel n)) (x : U) :
    projection U (zeroSection U x)=x:=by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

private theorem normal_trace_le {n : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) :
    (GermIdeal.pullback (m:=n) (zeroSection U)
      (GermIdeal.pullback (m:=n+1) (Subtype.val : productOpen U→ComplexModel (n+1)) (normalPlaneIdeal n))).Le I:=by
  rw [←coherent_pullback_comp contMDiff_subtype_val (zeroSection_contMDiff U)
    (normalPlaneIdeal n) (normalPlaneIdeal_coherent n)]
  intro x g hg
  obtain ⟨hgh,K,s,a,hs,_,he⟩:=GermIdeal.mem_pullback_iff.mp hg
  have hz : ∀i,s i=ᶠ[𝓝 x] 0:=by
    intro i
    obtain ⟨b,hb,hsb⟩:=hs i
    filter_upwards [((contMDiff_subtype_val.comp (zeroSection_contMDiff U)).continuous.continuousAt.eventually hb.2)] with y hy
    rw [hsb]
    exact hy (by change actualJointNormalProjection n 1 (tangentInclusion n 1 y.val)=0;simp)
  apply HomogenizedIdeal.mem_of_isInSpanAt hI
  refine ⟨hgh,0,(fun i=>i.elim0),(fun i=>i.elim0),(fun i=>i.elim0),(fun i=>i.elim0),?_⟩
  filter_upwards [he,eventually_all.mpr hz] with y hy hy0
  rw [hy]
  simp only [Fin.sum_univ_zero]
  exact Finset.sum_eq_zero fun i _=>by simp only [hy0 i,Pi.zero_apply,mul_zero]

theorem section_pullback_relativeNormalIdeal {n : ℕ} {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) :
    GermIdeal.pullback (m:=n) (zeroSection U) (relativeNormalIdeal I)=I:=by
  unfold relativeNormalIdeal
  rw [pullback_sumIdeal_dimensions (zeroSection_contMDiff U)
    (isCoherent_pullback (projection_contMDiff U) hI) (normalPullback_coherent U)]
  have hp : GermIdeal.pullback (m:=n) (zeroSection U)
      (GermIdeal.pullback (m:=n+1) (projection U) I)=I:=by
    rw [←coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U) I hI,
      show (projection U)∘(zeroSection U)=id from funext (projection_section U),
      BlowupControlledTransform.pullback_id hI]
  rw [hp]
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    apply HomogenizedIdeal.mem_of_isInSpanAt hI
    exact IsInSpanAt.mono (fun b hb=>hb.elim id (normal_trace_le hI x b))
      (IdealOrderArithmetic.mem_sumIdeal_iff.mp hg)
  · exact le_sumIdeal_left hI x g

private theorem base_comp_mem {n : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) {z : productOpen U} {g : U→ℂ} (hg : I.mem (projection U z) g) :
    (relativeNormalIdeal I).mem z (g∘projection U):=
  le_sumIdeal_left (isCoherent_pullback (projection_contMDiff U) hI) z _
    (pullback_mem_comp (X:=baseModel U) (Y:=ambientModel U) (projection U) (projection_contMDiff U) hI hg)

private def fibreSection {n : ℕ} (U : Opens (ComplexModel n)) (c : ComplexModel 1) (x : U) : productOpen U:=
  ⟨join x.val c,by change tangentProjection n 1 (join x.val c)∈U;rw [first_join];exact x.property⟩

private theorem fibreSection_continuous {n : ℕ} (U : Opens (ComplexModel n)) (c : ComplexModel 1) :
    Continuous (fibreSection U c):=by
  apply Continuous.subtype_mk
  exact ((tangentInclusion n 1).continuous.comp continuous_subtype_val).add continuous_const

private theorem projection_frequently {n : ℕ} {U : Opens (ComplexModel n)}
    {z : productOpen U} {g : U→ℂ} (h : ∃ᶠ y in 𝓝 (projection U z),g y≠0) :
    ∃ᶠ y in 𝓝 z,g (projection U y)≠0:=by
  by_contra hn
  have hn':=not_frequently.mp hn
  let f:=fibreSection U (actualJointNormalProjection n 1 z.val)
  have hfx : f (projection U z)=z:=by
    apply Subtype.ext
    exact join_projections z.val
  have hf : Continuous f:=fibreSection_continuous U (actualJointNormalProjection n 1 z.val)
  have ht : Tendsto f (𝓝 (projection U z)) (𝓝 z):=by
    simpa only [hfx] using hf.tendsto (projection U z)
  apply h
  filter_upwards [ht.eventually hn'] with y hy
  have hp : projection U (f y)=y:=by apply Subtype.ext;exact first_join y.val _
  simpa only [hp] using hy

private theorem relative_domain {n q : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hM : IsInvDomain q (relativeBaseMarked I)) : IsInvDomain (q+1) (relativeNormalMarked I):=by
  have hI : I.IsCoherent:=hM.isWellFormed.isCoherent
  have hN : IsClosedSubmanifold (n+1) (univ : Set (productOpen U)):=
    ⟨isClosed_univ,fun z _=>⟨n+1,AnalyticIrreducibleComponents.regularAtDim_univ z⟩⟩
  refine ⟨⟨hN,relativeNormalIdeal_isCoherent hI,NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hN⟩,?_,le_rfl,?_⟩
  · intro z _
    obtain ⟨j,hj,hreg⟩:=hM.dimLE (projection U z) (mem_univ _)
    have he:=RegularPointDimension.eq_of_regularAtDim hreg
      (AnalyticIrreducibleComponents.regularAtDim_univ (projection U z))
    refine ⟨n+1,Nat.add_le_add_right (he ▸ hj) 1,AnalyticIrreducibleComponents.regularAtDim_univ z⟩
  · intro z _
    obtain ⟨g,hg,hf⟩:=hM.isNonzeroAlongAt (projection U z) (mem_univ _)
    refine ⟨g∘projection U,base_comp_mem hI hg,?_⟩
    have hf' : ∃ᶠ y in 𝓝 (projection U z),g y≠0:=hf.mono fun _ hy=>hy.2
    exact (projection_frequently hf').mono fun _ hy=>⟨mem_univ _,hy⟩

private theorem normal_tangent {n : ℕ} :
    IsTangentDirectionAlong (univ : Set (ComplexModel (n+1))) (normalPlaneIdeal n) 1 univ (addedCoordinate n):=by
  have he : zeroCarrier (univ : Set (ComplexModel n))=HironakaActualZeroCoordinateContactSeed.zeroPlane n:=by
    ext z
    change (tangentProjection n 1 z∈univ ∧ actualJointNormalProjection n 1 z=0) ↔ actualJointNormalProjection n 1 z=0
    simp only [mem_univ,true_and]
  simpa only [zeroIdeal,he,normalPlaneIdeal] using zero_coordinate_tangent (univ : Set (ComplexModel n))

private theorem relative_tangent {n : ℕ} {U : Opens (ComplexModel n)} (I : GermIdeal n U) :
    IsTangentDirectionAlong (univ : Set (productOpen U)) (relativeNormalIdeal I) 1 univ (relativeNormalCoordinate U):=by
  have hU : IsTangentDirectionAlong (univ : Set (ComplexModel (n+1))) (normalPlaneIdeal n) 1 (productOpen U) (addedCoordinate n):=
    ⟨(productOpen U).isOpen,fun z _=>normal_tangent.mem z (mem_univ _),
      fun z _ hz=>normal_tangent.multiplicity_one z (mem_univ _) hz⟩
  have hp:=ContactEquivalenceAlong.isTangentDirectionAlong_pullback_val (productOpen U)
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem (normalPlaneIdeal_coherent n) hg) hU
  have hp' : IsTangentDirectionAlong (univ : Set (productOpen U))
      (GermIdeal.pullback (m:=n+1) (Subtype.val : productOpen U→ComplexModel (n+1)) (normalPlaneIdeal n)) 1 univ
      (relativeNormalCoordinate U):=by simpa only [preimage_univ,relativeNormalCoordinate] using hp
  refine ⟨isOpen_univ,?_,hp'.multiplicity_one⟩
  intro z _
  exact le_sumIdeal_right (normalPullback_coherent U) z _ (hp'.mem z (mem_univ _))

private theorem relative_maximal {n : ℕ} {U : Opens (ComplexModel n)} (I : GermIdeal n U) :
    IsMaximalOrderAlong (univ : Set (productOpen U)) (relativeNormalIdeal I) 1:=by
  have he : zeroCarrier (univ : Set (ComplexModel n))=HironakaActualZeroCoordinateContactSeed.zeroPlane n:=by
    ext z
    change (tangentProjection n 1 z∈univ ∧ actualJointNormalProjection n 1 z=0) ↔ actualJointNormalProjection n 1 z=0
    simp only [mem_univ,true_and]
  have hG : IsMaximalOrderAlong (univ : Set (ComplexModel (n+1))) (normalPlaneIdeal n) 1:=by
    simpa only [zeroIdeal,he,normalPlaneIdeal] using
      (zero_coordinate_maximal_order (W:=univ) (isComplexAnalyticSubset_univ (n:=n) (M:=ComplexModel n)))
  let A : MarkedIdeal (n+1) (ComplexModel (n+1)):=⟨univ,[],normalPlaneIdeal n,2⟩
  have hr:=MarkedIdealRestrictOpen.cosupp_pullback_val A
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem (normalPlaneIdeal_coherent n) hg) (productOpen U)
  intro z hz
  have hz' : z∈(MarkedIdeal.pullback (Subtype.val : productOpen U→ComplexModel (n+1)) A).cosupp:=
    ⟨mem_univ _,fun f hf=>hz.2 f (le_sumIdeal_right (normalPullback_coherent U) z f hf)⟩
  exact hG z.val ((Set.ext_iff.mp hr z).mp hz')

private theorem coordinate_zero_iff {n : ℕ} {U : Opens (ComplexModel n)} (z : productOpen U) :
    relativeNormalCoordinate U z=0 ↔ actualJointNormalProjection n 1 z.val=0:=by
  constructor
  · intro hz
    ext i
    have hi : i=0:=Fin.eq_zero i
    subst i
    simpa [relativeNormalCoordinate,addedCoordinate,HironakaActualGraphFunctionalIdeal.graphFunction,zeroFunction] using hz
  · intro hz
    simpa [relativeNormalCoordinate,addedCoordinate,HironakaActualGraphFunctionalIdeal.graphFunction,zeroFunction] using
      congrArg (fun v : ComplexModel 1=>v 0) hz

private theorem section_projection {n : ℕ} {U : Opens (ComplexModel n)} {z : productOpen U}
    (hz : relativeNormalCoordinate U z=0) : zeroSection U (projection U z)=z:=by
  apply Subtype.ext
  change tangentInclusion n 1 (tangentProjection n 1 z.val)=z.val
  have hq:=(coordinate_zero_iff z).mp hz
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hq,map_zero,add_zero] using
    (join_projections (n:=n) (m:=1) z.val)

private theorem section_coordinate_zero {n : ℕ} (U : Opens (ComplexModel n)) (x : U) :
    relativeNormalCoordinate U (zeroSection U x)=0:=by
  apply (coordinate_zero_iff _).mpr
  change actualJointNormalProjection n 1 (tangentInclusion n 1 x.val)=0
  simp

private theorem relative_codimOne_empty {n q : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hM : IsInvDomain q (relativeBaseMarked I)) :
    codimOnePartAlong (univ : Set (productOpen U)) (relativeNormalIdeal I) 1=∅:=by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hI : I.IsCoherent:=hM.isWellFormed.isCoherent
  have hc:=relativeNormalIdeal_isCoherent hI
  have hd:=relative_domain hM
  have ht:=relative_tangent I
  have hz0:=ht.cosupport_inter_subset
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hc hg) (by rfl)
    ⟨codimOnePartAlong_subset hz,mem_univ _⟩
  have he:=eventually_mem_codimOnePartAlong_iff_eq_zero hc hd.isWellFormed.isClosedSubmanifold_N
    (by rfl) ht (mem_univ z) hz
  obtain ⟨g,hg,hf⟩:=hM.isNonzeroAlongAt (projection U z) (mem_univ _)
  have hcomp:=base_comp_mem hI hg
  have hs : Tendsto (zeroSection U) (𝓝 (projection U z)) (𝓝 z):=by
    simpa only [section_projection hz0] using (zeroSection_contMDiff U).continuous.tendsto (projection U z)
  have heg : ∀ᶠ y in 𝓝 z,(relativeNormalIdeal I).mem y (g∘projection U):=eventually_mem hc hcomp
  apply hf
  filter_upwards [hs.eventually he,hs.eventually heg] with y hy hgy
  have hyR:=hy.mpr ⟨mem_univ _,section_coordinate_zero U y⟩
  have hyCos:=codimOnePartAlong_subset hyR
  have hval:=(vanishesToOrderOn_one_iff (mem_univ _)
    (GermIdeal.IsCoherent.holomorphicAt_mem hc hgy)).mp (hyCos.2 (g∘projection U) hgy)
  intro hneq
  exact hneq.2 (by simpa only [Function.comp_apply,projection_section] using hval)

/-- ONLY the original base domain internally produces the full relative normal
domain and all original geometric hypotheses of the fixed-contact history. -/
theorem relative_normal_original_geometry {n q : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hM : IsInvDomain q (relativeBaseMarked I)) :
    IsInvDomain (q+1) (relativeNormalMarked I) ∧
    IsMaximalOrderAlong (relativeNormalMarked I).N (relativeNormalMarked I).ideal (relativeNormalMarked I).d ∧
    codimOnePartAlong (relativeNormalMarked I).N (relativeNormalMarked I).ideal (relativeNormalMarked I).d=∅ ∧
    IsTangentDirectionAlong (relativeNormalMarked I).N (relativeNormalMarked I).ideal (relativeNormalMarked I).d
      univ (relativeNormalCoordinate U):=
  ⟨relative_domain hM,relative_maximal I,relative_codimOne_empty hM,relative_tangent I⟩

end
end Hironaka.HironakaActualRelativeNormalGeometry
