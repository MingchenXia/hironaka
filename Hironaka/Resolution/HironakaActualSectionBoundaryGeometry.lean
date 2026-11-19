import Hironaka.Resolution.HironakaActualSectionContactKept
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCharts

/-! Actual simultaneous boundary coordinates lift to the zero-section carrier, including the last normal coordinate and every original ordered boundary position. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionBoundaryGeometry
noncomputable section
open Hironaka.BlowupSequences NormalCrossings
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
variable {n : ℕ}

private def liftAxes (S : Finset (Fin n)) : Finset (Fin (n+1)) :=
  S.map (Fin.castAddEmb 1)

private theorem join_mem_liftAxes (a : ComplexModel n) (b : ComplexModel 1) (S : Finset (Fin n)) :
    HironakaActualIntrinsicStableAmbientIso.join a b∈coordSubspace (liftAxes S) ↔ a∈coordSubspace S := by
  constructor
  · intro h i hi
    have hh := h ((Fin.castAddEmb 1) i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    simpa [HironakaActualIntrinsicStableAmbientIso.join] using hh
  · intro h j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    simpa [HironakaActualIntrinsicStableAmbientIso.join] using h i hi

private theorem join_mem_normal (a : ComplexModel n) (b : ComplexModel 1) :
    HironakaActualIntrinsicStableAmbientIso.join a b∈coordSubspace {Fin.last n} ↔ b=0 := by
  have hlast : Fin.last n=(0 : Fin 1).natAdd n := by
    ext
    simp
  constructor
  · intro h
    ext i
    obtain rfl : i=0 := Subsingleton.elim _ _
    simpa [HironakaActualIntrinsicStableAmbientIso.join,hlast] using h (Fin.last n) (by simp)
  · intro hb j hj
    obtain rfl := Finset.mem_singleton.mp hj
    simp [HironakaActualIntrinsicStableAmbientIso.join,hb,hlast]

private theorem join_mem_liftAxes_normal (a : ComplexModel n) (b : ComplexModel 1) (S : Finset (Fin n)) :
    HironakaActualIntrinsicStableAmbientIso.join a b∈coordSubspace (liftAxes S ∪ {Fin.last n}) ↔
      a∈coordSubspace S ∧ b=0 := by
  have hunion : coordSubspace (liftAxes S ∪ {Fin.last n}) =
      coordSubspace (liftAxes S) ∩ coordSubspace {Fin.last n} := by
    ext v
    change (∀ i∈liftAxes S ∪ {Fin.last n},v i=0) ↔
      (∀ i∈liftAxes S,v i=0) ∧ ∀ i∈({Fin.last n} : Finset (Fin (n+1))),v i=0
    constructor
    · intro h
      exact ⟨fun i hi => h i (Finset.mem_union_left _ hi),
        fun i hi => h i (Finset.mem_union_right _ hi)⟩
    · rintro ⟨h1,h2⟩ i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact h1 i hi
      · exact h2 i hi
  rw [hunion,Set.mem_inter_iff,join_mem_liftAxes,join_mem_normal]

private theorem disjoint_liftAxes_normal {S T : Finset (Fin n)} (h : Disjoint S T) :
    Disjoint (liftAxes S) (liftAxes T ∪ {Fin.last n}) := by
  apply Finset.disjoint_left.mpr
  intro j hjS hjN
  obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hjS
  rcases Finset.mem_union.mp hjN with hjT | hjLast
  · obtain ⟨k,hk,hki⟩ := Finset.mem_map.mp hjT
    have hki' : k=i := (Fin.castAddEmb 1).injective hki
    subst k
    exact Finset.disjoint_left.mp h hi hk
  · have hval := congrArg Fin.val (Finset.mem_singleton.mp hjLast)
    change i.val=n at hval
    exact (Nat.ne_of_lt i.isLt) hval

private theorem chart_apply {r : ℕ} (V : TopologicalSpace.Opens (ComplexModel r)) (x y : V) :
    chartAt (ComplexModel r) x y=y.val := by
  rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
  rfl

private theorem chart_source {r : ℕ} (V : TopologicalSpace.Opens (ComplexModel r)) (x y : V) :
    y∈(chartAt (ComplexModel r) x).source :=
  AnalyticSubsetOpens.mem_chartAt_opens_source.mpr (by simp)

private theorem mem_chart_target {r : ℕ} (V : TopologicalSpace.Opens (ComplexModel r))
    (x : V) (v : ComplexModel r) :
    v∈(chartAt (ComplexModel r) x).target ↔ v∈V := by
  constructor
  · intro hv
    have h := (chartAt (ComplexModel r) x).right_inv hv
    rw [chart_apply] at h
    exact h ▸ ((chartAt (ComplexModel r) x).symm v).property
  · intro hv
    have h := AnalyticSubsetOpens.chart_mem_opens_target (n := r) (x := x) (y := ⟨v,hv⟩) (by simp)
    simpa using h

variable {U : TopologicalSpace.Opens (ComplexModel n)}

private theorem projection_section (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

private theorem section_projection (A : Set U) (z : productOpen U) (hz : z∈liftedCarrier A) :
    zeroSection U (projection U z)=z := by
  apply Subtype.ext
  change tangentInclusion n 1 (tangentProjection n 1 z.val)=z.val
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz.2,map_zero,add_zero]
    using join_projections (n := n) (m := 1) z.val

private theorem productFlat_source (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target) :
    (productFlat U x Φ).source⊆(chartAt (ComplexModel (n+1)) (zeroSection U x)).target := by
  intro z hz
  apply (mem_chart_target (productOpen U) (zeroSection U x) z).mpr
  exact (mem_chart_target U x (tangentProjection n 1 z)).mp (hsrc hz)

private theorem productFlat_section (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (v : ComplexModel n) :
    (productFlat U x Φ).toFun (tangentInclusion n 1 v)=tangentInclusion n 1 (Φ.toFun v) := by
  simp [productFlat,HironakaActualIntrinsicStableAmbientIso.join,tangentProjection_tangentInclusion]

theorem isTransverse_liftedCarrier (A : Set U) (E : List (Set U))
    (hT : IsTransverse n A E) :
    IsTransverse (n+1) (liftedCarrier A) (E.map (projection U ⁻¹' ·)) := by
  classical
  intro z hz
  let x:=projection U z
  have hx : x∈A:=hz.1
  have hsec : zeroSection U x=z:=section_projection A z hz
  rw [←hsec]
  obtain ⟨S₀,S,⟨Φ,hsrc,h0,hflat⟩,hS⟩ := hT x hx
  let e : Fin (E.map (projection U ⁻¹' ·)).length ≃ Fin E.length :=
    finCongr (List.length_map _)
  have hget (i : Fin (E.map (projection U ⁻¹' ·)).length) :
      (E.map (projection U ⁻¹' ·)).get i = projection U ⁻¹' E.get (e i) := by
    simp only [e,List.get_eq_getElem,List.getElem_map,finCongr_apply,Fin.val_cast]
  refine ⟨liftAxes S₀ ∪ {Fin.last n},fun i => liftAxes (S (e i)),?_,?_⟩
  · refine ⟨productFlat U x Φ,productFlat_source x Φ hsrc,?_,?_⟩
    · change (productFlat U x Φ).toFun (tangentInclusion n 1 x.val)=0
      rw [productFlat_section]
      have hΦ0 : Φ.toFun x.val=0 := by simpa only [complexChartAt,chart_apply] using h0
      rw [hΦ0,map_zero]
    · rintro (_ | i) hxi y _hy hyΦ
      · have hyBase : chartAt (ComplexModel n) x (projection U y)∈Φ.source := by
          change tangentProjection n 1 y.val∈Φ.source
          change tangentProjection n 1 y.val∈Φ.source at hyΦ
          exact hyΦ
        have hBase := hflat none hx (chart_source U x (projection U y)) hyBase
        simp only [Option.elim_none,complexChartAt,chart_apply] at hBase ⊢
        change (projection U y∈A ∧ actualJointNormalProjection n 1 y.val=0) ↔
          HironakaActualIntrinsicStableAmbientIso.join (Φ.toFun (tangentProjection n 1 y.val))
            (actualJointNormalProjection n 1 y.val) ∈ coordSubspace (liftAxes S₀ ∪ {Fin.last n})
        rw [join_mem_liftAxes_normal]
        exact and_congr_left fun _ => hBase
      · have hxiBase : x∈E.get (e i) := by
          change zeroSection U x∈(E.map (projection U ⁻¹' ·)).get i at hxi
          rw [hget] at hxi
          simpa only [Set.mem_preimage,projection_section] using hxi
        have hyBase : chartAt (ComplexModel n) x (projection U y)∈Φ.source := by
          change tangentProjection n 1 y.val∈Φ.source
          change tangentProjection n 1 y.val∈Φ.source at hyΦ
          exact hyΦ
        have hBase := hflat (some (e i)) hxiBase (chart_source U x (projection U y)) hyBase
        simp only [Option.elim_some,complexChartAt,chart_apply] at hBase ⊢
        rw [hget]
        change projection U y∈E.get (e i) ↔
          HironakaActualIntrinsicStableAmbientIso.join (Φ.toFun (tangentProjection n 1 y.val))
            (actualJointNormalProjection n 1 y.val) ∈ coordSubspace (liftAxes (S (e i)))
        rw [join_mem_liftAxes]
        exact hBase
  · intro i hxi
    have hxiBase : x∈E.get (e i) := by
      rw [hget] at hxi
      simpa only [Set.mem_preimage,projection_section] using hxi
    obtain ⟨hcard,hdisj⟩ := hS (e i) hxiBase
    exact ⟨by simpa only [liftAxes,Finset.card_map] using hcard,disjoint_liftAxes_normal hdisj⟩


open HironakaSmoothSubmersionMonomialChartPullback HironakaSmoothSubmersionContactParameterCharts
  HironakaSmoothSubmersionNormalCrossings BlowupTowers

private theorem model_projection_isSubmersionOfComplement :
    Manifold.IsSubmersionOfComplement (ComplexModel 1)
      𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ (tangentProjection n 1) := by
  intro w
  let e:=splitCoordinates n 1
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts e
    (OpenPartialHomeomorph.refl (ComplexModel (n+1))) (OpenPartialHomeomorph.refl (ComplexModel n))
  · exact mem_univ _
  · exact mem_univ _
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn <;> exact contMDiffOn_id
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn <;> exact contMDiffOn_id
  · intro z hz
    exact mem_univ _
  · intro z hz
    change tangentProjection n 1 z=(e z).1
    have hfirst (v : ComplexModel (n+1)) : (e v).1=tangentProjection n 1 v := by
      ext i
      change fibreProjection n 1 v i=tangentProjection n 1 v i
      rw [fibreProjection_apply,tangentProjection_apply]
    exact (hfirst z).symm

theorem projection_isSubmersion :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ (projection U) := by
  have h:=restrictedOpenMap_isSubmersionOfComplement
    (X := CMfd.of (n := n) (ComplexModel n))
    (Y := CMfd.of (n := n+1) (ComplexModel (n+1)))
    (model_projection_isSubmersionOfComplement (n := n)) (productOpen U) U (fun _ hz => hz)
  exact h.isSubmersion

theorem isSNCDivisor_preimage_projection (E : List (Set U)) (hE : IsSNCDivisor n E) :
    IsSNCDivisor (n+1) (E.map (projection U ⁻¹' ·)) :=
  isSNCDivisor_preimage_submersion (projection_isSubmersion (U := U)) E hE

open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan GermIdealPullbackCalculus
  GermIdealOrder HironakaActualSectionInitialValues InvertibleIdealQuotient
open ResolutionInvariantSpec (IsInvDomain)

theorem section_projected_domain (q : ℕ) (A : Set U) (E : List (Set U)) (I : GermIdeal n U) (d : ℕ)
    (h : IsInvDomain q (⟨A,E,I,d⟩ : MarkedIdeals.MarkedIdeal n U)) :
    IsInvDomain q
      (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),GermIdeal.pullback (m := n+1) (projection U) I,d⟩ :
        MarkedIdeals.MarkedIdeal (n+1) (productOpen U)) := by
  have hN:=liftedCarrier_closed_submanifold h.isWellFormed.isClosedSubmanifold_N
  have hc:=isCoherent_pullback (projection_contMDiff U) h.isWellFormed.isCoherent
  refine ⟨⟨hN,hc,isSNCDivisor_preimage_projection E h.isWellFormed.isSNCDivisor,
    isTransverse_liftedCarrier A E h.isWellFormed.isTransverse⟩,?_,h.one_le_d,?_⟩
  · intro z hz
    let x:=projection U z
    have hx : x∈A:=hz.1
    obtain ⟨k,hk,hreg⟩:=h.dimLE x hx
    refine ⟨k,hk,?_⟩
    have hr:=(regularAtDim_actual_section_iff A x hx k).mpr hreg
    change RegularAtDim (n := n+1) (liftedCarrier A) (zeroSection U (projection U z)) k at hr
    rwa [section_projection A z hz] at hr
  · intro z hz
    let x:=projection U z
    have hx : x∈A:=hz.1
    have hsec : zeroSection U x=z:=section_projection A z hz
    rw [←hsec]
    obtain ⟨g,hg,hfreq⟩:=h.isNonzeroAlongAt x hx
    have hg' : I.mem (projection U (zeroSection U x)) g := by
      simpa only [projection_section] using hg
    have hp : (GermIdeal.pullback (m := n+1) (projection U) I).mem (zeroSection U x) (g ∘ projection U) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg',rfl⟩
        ((GermIdeal.IsCoherent.holomorphicAt_mem h.isWellFormed.isCoherent hg').comp_contMDiff
          (Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt)))
    refine ⟨g ∘ projection U,hp,?_⟩
    by_contra hn
    have hn' := not_frequently.mp hn
    apply hfreq
    filter_upwards [(zeroSection_contMDiff U).continuous.continuousAt.eventually hn'] with y hy
    rintro ⟨hyA,hyg⟩
    apply hy
    refine ⟨?_,?_⟩
    · exact ⟨by simpa only [projection_section] using hyA,by simp [zeroSection]⟩
    · simpa only [Function.comp_apply,projection_section] using hyg

end
end Hironaka.HironakaActualSectionBoundaryGeometry

