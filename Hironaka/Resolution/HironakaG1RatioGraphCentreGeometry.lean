import Hironaka.Resolution.HironakaG1RatioSectionBlowup
import Hironaka.Resolution.HironakaActualSectionBoundaryGeometry

/-! Transversality and cosupport for arbitrary finite literal graph padding. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioGraphCentreGeometry
noncomputable section
open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HironakaG11PresLineState NormalCrossings NormalCrossingsInvariance
  HironakaActualSectionBoundaryGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaG1ProperCarrierNormalContact HironakaG1FiniteSourceWeakClassGraphLift
  HironakaG1IteratedProperNormalNativeState HironakaG1IteratedNormalBlockIdeal
  HironakaG1NormalGraphFlags HironakaBaseChange HironakaActualOpenEmbeddingCanonicalExtension
  HironakaSmoothSubmersionCoefficientIdeals HironakaG1RatioSectionBlowup
  MarkedIdealBiholomorphism InvDomainTowerAlong HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem iteratedNormalCarrier_transverse (A : Set U) (E : List (Set U))
    (hA : IsTransverse n A E) (t : ℕ) :
    IsTransverse (n+t) (iteratedNormalCarrier A t) (E.map (iteratedNormalProjection U t ⁻¹' ·)) := by
  induction t with
  | zero =>
    change IsTransverse n A (E.map (id ⁻¹' ·))
    rw [show (id ⁻¹' · : Set U → Set U) = id from funext (fun _ => preimage_id), List.map_id_fun]
    exact hA
  | succ t ih =>
    have h := isTransverse_liftedCarrier _ _ ih
    rw [List.map_map] at h
    exact h

private theorem iteratedNormalMarked_cosupp (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q)
    (t : ℕ) :
    IsInvDomain (n+t) (iteratedNormalMarked Q t) ∧
      (iteratedNormalMarked Q t).cosupp = iteratedNormalCarrier Q.cosupp t := by
  induction t with
  | zero => exact ⟨hQ,rfl⟩
  | succ t ih =>
    refine ⟨properNormalMarked_isInvDomain _ ih.1,?_⟩
    change (properNormalMarked (iteratedNormalMarked Q t)).cosupp =
      liftedCarrier (iteratedNormalCarrier Q.cosupp t)
    rw [properNormalMarked_cosupp _ ih.1,ih.2]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨by simpa [projection,zeroSection,tangentProjection_tangentInclusion] using hy,
        actualJointNormalProjection_tangent _ _ _⟩
    · intro hx
      refine ⟨projection _ x,hx.1,Subtype.ext ?_⟩
      change tangentInclusion _ 1 (tangentProjection _ 1 x.val) = x.val
      have hz : actualJointNormalProjection _ 1 x.val = 0 := hx.2
      simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz,map_zero,add_zero] using join_projections (n := n+t) (m := 1) x.val

/-- Finite holomorphic graph padding retains transversality with every
inherited boundary slot. The same statement applies to the full graph
and to the graph over the source carrier. -/
theorem blockGraph_isTransverse {t : ℕ} {A : Set U} {E : List (Set U)}
    (hA : IsTransverse n A E) {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f) :
    IsTransverse (n+t) (blockGraph f A) (E.map (blockProjection ⁻¹' ·)) := by
  let e := iteratedNormalBlockEquiv U t
  have h := isTransverse_preimage (MarkedIdealTowerTransport.pullsBackCoordinates e)
    (iteratedNormalCarrier_transverse A E hA t)
  rw [iteratedNormalCarrier_preimage_blockEquiv,List.map_map] at h
  have hp : iteratedNormalProjection U t ∘ e = blockProjection :=
    funext (iteratedNormalProjection_blockEquiv (U := U) (t := t))
  change IsTransverse (n+t) (blockGraph 0 A) (E.map ((iteratedNormalProjection U t ∘ e) ⁻¹' ·)) at h
  rw [hp] at h
  let b := blockChartEquiv (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (↥U) ∞)
    hf (contMDiff_const (c := (0 : ComplexModel t)))
  have hb := isTransverse_preimage (MarkedIdealTowerTransport.pullsBackCoordinates b) h
  change IsTransverse (n+t) (blockChartMap id f 0 ⁻¹' _) _ at hb
  rw [blockChartMap_preimage_graph, preimage_id,List.map_map] at hb
  have hπ : (blockProjection : blockOpen U t → U) ∘ b = blockProjection :=
    funext (blockProjection_chartMap id f 0)
  change IsTransverse (n+t) (blockGraph f A) (E.map (((blockProjection : blockOpen U t → U) ∘ b) ⁻¹' ·)) at hb
  rwa [hπ] at hb

/-- The cosupport of the whole cylindrical graph record is exactly the
graph over the source cosupport. -/
theorem blockAmbientMarked_cosupp {t : ℕ} {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) :
    (blockAmbientMarked f Q).cosupp = blockGraph f Q.cosupp := by
  obtain ⟨hD,hC⟩ := iteratedNormalMarked_cosupp Q hQ t
  let e := iteratedNormalBlockEquiv U t
  let b := blockChartEquiv (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (↥U) ∞)
    hf (contMDiff_const (c := (0 : ComplexModel t)))
  have hE := iteratedNormalMarked_pullback_blockEquiv Q hQ.isWellFormed.isCoherent t
  have hCos := MarkedIdealTowerTransport.cosupp_pullback_eq
    (Φ := e) hD.isWellFormed.isCoherent
  rw [hE,hC,iteratedNormalCarrier_preimage_blockEquiv] at hCos
  have hshift := blockAmbientMarked_pullback_shift f hf Q hQ.isWellFormed.isCoherent
  have hDom := isInvDomain_pullback e hD
  rw [hE] at hDom
  have hc := MarkedIdealTowerTransport.cosupp_pullback_eq (Φ := b) hDom.isWellFormed.isCoherent
  rw [hshift,hCos] at hc
  change _ = blockChartMap id f 0 ⁻¹' _ at hc
  rwa [blockChartMap_preimage_graph,preimage_id] at hc


open HironakaG1ProperNormalNativeChart BlowupFlatCoordinates

private theorem chart_opens_apply {d : ℕ} (O : Opens (ComplexModel d)) (x y : O) :
    chartAt (ComplexModel d) x y = y.val := by
  rw [Opens.chartAt_eq,chartAt_self_eq]
  rfl

private theorem zeroSection_projection (z : productOpen U)
    (hz : actualJointNormalProjection n 1 z.val = 0) : zeroSection U (projection U z) = z := by
  apply Subtype.ext
  change tangentInclusion n 1 (tangentProjection n 1 z.val) = z.val
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz,map_zero,add_zero]
    using join_projections (n := n) (m := 1) z.val

private theorem projection_zeroSection (x : U) : projection U (zeroSection U x) = x :=
  Subtype.ext (tangentProjection_tangentInclusion n 1 x.val)

private def liftAxes (S : Finset (Fin n)) : Finset (Fin (n+1)) := S.map (Fin.castAddEmb 1)

private theorem join_mem_liftAxes (v : ComplexModel n) (w : ComplexModel 1) (S : Finset (Fin n)) :
    HironakaActualIntrinsicStableAmbientIso.join v w ∈ coordSubspace (liftAxes S) ↔ v ∈ coordSubspace S := by
  constructor
  · intro h i hi
    have h' := h ((Fin.castAddEmb 1) i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    simpa [HironakaActualIntrinsicStableAmbientIso.join] using h'
  · intro h j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    simpa [HironakaActualIntrinsicStableAmbientIso.join] using h i hi

private theorem join_mem_normalAxes (v : ComplexModel n) (w : ComplexModel 1) (S : Finset (Fin n)) :
    HironakaActualIntrinsicStableAmbientIso.join v w ∈ coordSubspace (liftAxes S ∪ {Fin.last n}) ↔
      v ∈ coordSubspace S ∧ w = 0 := by
  have hlast : Fin.last n = (0 : Fin 1).natAdd n := by ext; simp
  constructor
  · intro h
    refine ⟨(join_mem_liftAxes v w S).mp (fun i hi => h i (Finset.mem_union_left _ hi)),?_⟩
    ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simpa [HironakaActualIntrinsicStableAmbientIso.join,hlast] using h (Fin.last n) (by simp)
  · rintro ⟨hv,rfl⟩ i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (join_mem_liftAxes _ _ _).mpr hv i hi
    · obtain rfl := Finset.mem_singleton.mp hi
      simp [HironakaActualIntrinsicStableAmbientIso.join,hlast]

/-- A centre that shares active boundary equations with a source divisor
retains its normal crossings after adjoining one genuine normal coordinate. -/
theorem liftedCarrier_hasNormalCrossings {A : Set U} {E : List (Set U)}
    (hA : HasNormalCrossings n A E) :
    HasNormalCrossings (n+1) (liftedCarrier A) (E.map (projection U ⁻¹' ·)) := by
  intro z hz
  let x := projection U z
  have hx : x ∈ A := hz.1
  have hzEq : zeroSection U x = z := zeroSection_projection z hz.2
  rw [← hzEq]
  obtain ⟨S₀,S,⟨Φ,hsrc,h0,hflat⟩,hS⟩ := hA x hx
  let e : Fin (E.map (projection U ⁻¹' ·)).length ≃ Fin E.length :=
    finCongr (List.length_map _)
  have hGet (i : Fin (E.map (projection U ⁻¹' ·)).length) :
      (E.map (projection U ⁻¹' ·)).get i = projection U ⁻¹' E.get (e i) := by
    simp only [e,List.get_eq_getElem,List.getElem_map,finCongr_apply,Fin.val_cast]
  have hAt (i : Fin (E.map (projection U ⁻¹' ·)).length)
      (hi : zeroSection U x ∈ (E.map (projection U ⁻¹' ·)).get i) : x ∈ E.get (e i) := by
    rw [hGet] at hi
    simpa only [mem_preimage,projection_zeroSection] using hi
  refine ⟨liftAxes S₀ ∪ {Fin.last n},fun i => liftAxes (S (e i)), ?_,
    fun i hi => by simpa only [liftAxes,Finset.card_map] using hS (e i) (hAt i hi)⟩
  refine ⟨productFlat U x Φ,productFlat_source_subset x Φ hsrc,productFlat_center x Φ h0,?_⟩
  rintro (_ | i) hi y _ hy
  all_goals
    have hSrc : projection U y ∈ (chartAt (ComplexModel n) x).source :=
      AnalyticSubsetOpens.mem_chartAt_opens_source.mpr (by rw [chartAt_self_eq]; trivial)
    have hφ : chartAt (ComplexModel n) x (projection U y) ∈ Φ.source := by
      rw [chart_opens_apply]
      change tangentProjection n 1 y.val ∈ Φ.source
      change chartAt (ComplexModel (n+1)) (zeroSection U x) y ∈ _ at hy
      rwa [chart_opens_apply] at hy
  · have h := hflat none hx hSrc hφ
    simp only [Option.elim_none,complexChartAt,chart_opens_apply] at h ⊢
    change (projection U y ∈ A ∧ actualJointNormalProjection n 1 y.val = 0) ↔
      HironakaActualIntrinsicStableAmbientIso.join (Φ.toFun (tangentProjection n 1 y.val))
        (actualJointNormalProjection n 1 y.val) ∈ coordSubspace _
    rw [join_mem_normalAxes]
    exact and_congr_left fun _ => h
  · have h := hflat (some (e i)) (hAt i hi) hSrc hφ
    simp only [Option.elim_some,complexChartAt,chart_opens_apply] at h ⊢
    rw [hGet]
    change projection U y ∈ E.get (e i) ↔
      HironakaActualIntrinsicStableAmbientIso.join (Φ.toFun (tangentProjection n 1 y.val))
        (actualJointNormalProjection n 1 y.val) ∈ coordSubspace _
    rw [join_mem_liftAxes]
    exact h


private theorem iteratedNormalCarrier_NC (A : Set U) (E : List (Set U))
    (hA : HasNormalCrossings n A E) (t : ℕ) :
    HasNormalCrossings (n+t) (iteratedNormalCarrier A t) (E.map (iteratedNormalProjection U t ⁻¹' ·)) := by
  induction t with
  | zero =>
    change HasNormalCrossings n A (E.map (id ⁻¹' ·))
    rw [show (id ⁻¹' · : Set U → Set U) = id from funext (fun _ => preimage_id), List.map_id_fun]
    exact hA
  | succ t ih =>
    have h := liftedCarrier_hasNormalCrossings ih
    rw [List.map_map] at h
    exact h

/-- The literal graph of an arbitrary source centre retains normal
crossings with the entire inherited boundary, including when the centre
is contained in an inherited divisor. -/
theorem blockGraph_hasNormalCrossings {t : ℕ} {A : Set U} {E : List (Set U)}
    (hA : HasNormalCrossings n A E) {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f) :
    HasNormalCrossings (n+t) (blockGraph f A) (E.map (blockProjection ⁻¹' ·)) := by
  let e := iteratedNormalBlockEquiv U t
  have h := hasNormalCrossings_preimage (MarkedIdealTowerTransport.pullsBackCoordinates e)
    (iteratedNormalCarrier_NC A E hA t)
  rw [iteratedNormalCarrier_preimage_blockEquiv,List.map_map] at h
  have hp : iteratedNormalProjection U t ∘ e = blockProjection :=
    funext (iteratedNormalProjection_blockEquiv (U := U) (t := t))
  change HasNormalCrossings (n+t) (blockGraph 0 A) (E.map ((iteratedNormalProjection U t ∘ e) ⁻¹' ·)) at h
  rw [hp] at h
  let b := blockChartEquiv (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (↥U) ∞)
    hf (contMDiff_const (c := (0 : ComplexModel t)))
  have hb := hasNormalCrossings_preimage (MarkedIdealTowerTransport.pullsBackCoordinates b) h
  change HasNormalCrossings (n+t) (blockChartMap id f 0 ⁻¹' _) _ at hb
  rw [blockChartMap_preimage_graph, preimage_id,List.map_map] at hb
  have hπ : (blockProjection : blockOpen U t → U) ∘ b = blockProjection :=
    funext (blockProjection_chartMap id f 0)
  change HasNormalCrossings (n+t) (blockGraph f A) (E.map (((blockProjection : blockOpen U t → U) ∘ b) ⁻¹' ·)) at hb
  rwa [hπ] at hb

/-- Every actual source-admissible centre gives the literal admissible graph
centre, with the original mark and all inherited slots. -/
theorem blockGraph_admissibleCentre {t : ℕ} {D : Set U}
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q)
    (hD : Q.IsAdmissibleCentre D) :
    (blockAmbientMarked f Q).IsAdmissibleCentre (blockGraph f D) := by
  refine ⟨blockGraph_closed_submanifold hf hD.1,?_,blockGraph_hasNormalCrossings hD.2.2 hf⟩
  rw [blockAmbientMarked_cosupp hf Q hQ]
  exact fun _ hz => ⟨hD.2.1 hz.1,hz.2⟩

/-- Transversality to the full graph and the graph over the original
carrier, and admissibility of the embedded centre, on an actual ratio
cylinder open image. All three statements use its literal ordered boundary. -/
theorem ratioSection_centreGeometry {t : ℕ} {X : CMfd.{0} (n+t)}
    {e : X → blockOpen U t} (he : IsOpenHoloEmbedding (n+t) e)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) {A D : Set U} {H : ℕ → ℕ}
    (hState : NativeHSState (X := CMfd.of (n := n) U) Q A H)
    (hD : Q.IsAdmissibleCentre D) :
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    let W := sectionSupport e f
    IsTransverse (n+t) W P.E ∧ IsTransverse (n+t) (P.N ∩ W) P.E ∧
      P.IsAdmissibleCentre (e ⁻¹' blockGraph f D) := by
  intro P W
  have hFull := blockGraph_isTransverse
    (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor) hf
  have hRes := blockGraph_isTransverse hQ.isWellFormed.isTransverse hf
  have hSup : P.N ∩ W = e ⁻¹' blockGraph f Q.N := by
    ext x
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,mem_univ _,h.2⟩⟩
  obtain ⟨hClosed,hCut,hNC⟩ := blockGraph_admissibleCentre hf Q hQ hD
  have hCo : (blockAmbientMarked f Q).IsWellFormed := by
    exact (blockAmbientMarked_nativeHSState f hf Q H hState hQ).1.isWellFormed
  refine ⟨isTransverse_preimage he.pullsBackCoordinates hFull,?_,?_,?_,he.hasNormalCrossings_preimage hNC⟩
  · rw [hSup]
    exact isTransverse_preimage he.pullsBackCoordinates hRes
  · refine ⟨hClosed.1.preimage he.continuous,fun x hx => ?_⟩
    obtain ⟨k,hk⟩ := hClosed.2 (e x) hx
    exact ⟨k,he.regularAtDim_preimage hk⟩
  · change e ⁻¹' blockGraph f D ⊆ (MarkedIdeal.pullback e (blockAmbientMarked f Q)).cosupp
    rw [cosupp_pullback_of_isOpenHoloEmbedding (X := CMfd.of (n := n+t) (blockOpen U t)) (Y := X) e he _ hCo]
    exact preimage_mono hCut

end
end Hironaka.HironakaG1RatioGraphCentreGeometry
