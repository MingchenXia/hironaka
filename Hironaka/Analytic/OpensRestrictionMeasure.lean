import Hironaka.Analytic.OpensRestriction
import Hironaka.Analytic.ModificationMassInvariance
import Hironaka.Analytic.DiagonalMass
import Hironaka.Analytic.PotentialTheory.ManifoldPluripolar
import Hironaka.Analytic.RooftopEnvelope
import Hironaka.Analytic.UscRegularizationContinuous
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Analytic.PotentialTheory.PshRegularDistribution

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Measures, pluripolar sets and envelopes on a clopen open submanifold

Let `M` be a compact complex manifold and `U` a nonempty clopen subset, for instance a connected
component.  `U` is a compact complex manifold (`Hironaka.OpensRestriction`), and the objects of
global pluripotential theory on `M` restrict to `U` without change:

* `exceptionalLocus_val`, `isIsomorphismOver_val` — the inclusion is an isomorphism over `U`;
* `globalMixedMeasure_restrict_apply` — **the global mixed non-pluripolar measure is local**:
  `⟨⋀ (θᵢ|_U)_{uᵢ|_U}⟩(val⁻¹ S) = ⟨⋀ (θᵢ)_{uᵢ}⟩(S ∩ U)` for measurable `S`
  (from `ModificationMassInvariance.globalMixedMeasure_restrict_preimage_eq_map` with
  `π = Subtype.val`), and `diagonalPotentialMeasure_restrict_apply`;
* `manifoldLocallyPluripolar_preimage_val`, `manifoldLocallyPluripolar_image_val` — pluripolar
  sets restrict to `U` and extend from `U` (chart change by `locallyPluripolarAt_chartTransition`);
* `uscRegularization_comp_val` and `rooftopEnvelope_restrict` — usc regularization and the
  rooftop envelope commute with the restriction (competitors restrict, and a competitor on `U`
  glues with a competitor on `M` across the clopen `U`);
* `measure_eq_zero_of_forall_connectedComponent` — a set is null as soon as its trace on every
  connected component is null.

This is the general mechanism by which a statement about compact Kähler manifolds proved under
`[ConnectedSpace M]` extends to every compact Kähler manifold.  Sorry-free.
-/

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace Hironaka.OpensRestrictionMeasure

open Hironaka.HolomorphicMaps Hironaka.PositiveClasses Hironaka.BlowupSequences
  OpensRestriction

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {U : Opens M}

/-! ### The inclusion is an isomorphism over `U` -/

/-- The derivative of the inclusion is the identity in the preferred charts. -/
theorem mfderiv_val_bijective (y : U) :
    Function.Bijective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (Subtype.val : U → M) y) := by
  have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (Subtype.val : U → M) y := ((contMDiff_val U) y).mdifferentiableAt (by simp)
  rw [hd.mfderiv]
  have heq : writtenInExtChartAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) y
      (Subtype.val : U → M) =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ComplexModel n) y) y)] id := by
    have ht : (complexChartAt (n := n) y).val.target ∈
        𝓝 ((extChartAt 𝓘(ℂ, ComplexModel n) y) y) :=
      (complexChartAt (n := n) y).val.open_target.mem_nhds
        ((complexChartAt (n := n) y).val.map_source (mem_complexChartAt_source y))
    filter_upwards [ht] with z hz
    exact coordinateMap_val_complexChartAt y hz
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  rw [heq.fderiv_eq, fderiv_id]
  exact Function.bijective_id

theorem exceptionalLocus_val : exceptionalLocus n (Subtype.val : U → M) = ∅ :=
  eq_empty_of_forall_notMem fun y hy => hy (mfderiv_val_bijective y)

/-- The inclusion of an open submanifold is an isomorphism over it. -/
theorem isIsomorphismOver_val :
    IsIsomorphismOver n (Subtype.val : U → M) (U : Set M) := by
  refine ⟨⟨fun y _ => y.2, Subtype.val_injective.injOn, fun x hx => ⟨⟨x, hx⟩, hx, rfl⟩⟩, ?_⟩
  rw [exceptionalLocus_val]
  exact disjoint_empty _

/-- A clopen subset of a compact space is a compact space. -/
theorem compactSpace_of_isClopen [CompactSpace M] (hU : IsClopen (U : Set M)) :
    CompactSpace U :=
  isCompact_iff_compactSpace.mp hU.1.isCompact

/-! ### The global mixed measure is local -/

section Measure

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Locality of the global mixed non-pluripolar measure.**  For an open submanifold `U` of a
compact complex manifold which is itself compact (e.g. `U` clopen), the global mixed measure of
the restricted backgrounds and potentials is the trace on `U` of the global mixed measure:
`⟨⋀ (θᵢ|_U)_{uᵢ|_U}⟩(val⁻¹ S) = ⟨⋀ (θᵢ)_{uᵢ}⟩(S ∩ U)`. -/
theorem globalMixedMeasure_restrict_apply [CompactSpace U] [Nonempty U]
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hu' : ∀ i, ThetaPlurisubharmonic (restrictForm U (θ i)).val (fun y : U => u i y))
    {S : Set M} (hS : MeasurableSet S) :
    GlobalNonPluripolar.globalMixedMeasure (fun i => restrictForm U (θ i))
        (fun i (y : U) => u i y) hu' (Subtype.val ⁻¹' S) =
      GlobalNonPluripolar.globalMixedMeasure θ u hu (S ∩ U) := by
  have h := ModificationMassInvariance.globalMixedMeasure_restrict_preimage_eq_map
    (X := M) (Y := U) (π := Subtype.val) (N := (U : Set M)) (contMDiff_val U) U.isOpen
    (isIsomorphismOver_val (n := n)) hu hu'
  have hpre : (Subtype.val : U → M) ⁻¹' (U : Set M) = univ := by
    ext y; simp
  rw [hpre, Measure.restrict_univ] at h
  change GlobalNonPluripolar.globalMixedMeasure
      (ModificationMassInvariance.pullbackTuple (contMDiff_val U) θ)
      (fun i (y : U) => u i y) hu' (Subtype.val ⁻¹' S) = _
  rw [h]
  have hg : AEMeasurable (ModificationMassInvariance.invOver (Subtype.val : U → M) (U : Set M))
      ((GlobalNonPluripolar.globalMixedMeasure θ u hu).restrict (U : Set M)) :=
    (ModificationMassInvariance.continuousOn_invOver (contMDiff_val U) U.isOpen
      (isIsomorphismOver_val (n := n))).aemeasurable U.isOpen.measurableSet
  rw [Measure.map_apply_of_aemeasurable hg (measurable_subtype_coe hS),
    Measure.restrict_apply' U.isOpen.measurableSet]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, hxU⟩
    refine ⟨?_, hxU⟩
    have := (ModificationMassInvariance.invOver_mem (isIsomorphismOver_val (n := n)) hxU).2
    simp only [mem_preimage] at hx
    rwa [this] at hx
  · rintro ⟨hx, hxU⟩
    refine ⟨?_, hxU⟩
    simp only [mem_preimage]
    rwa [(ModificationMassInvariance.invOver_mem (isIsomorphismOver_val (n := n)) hxU).2]

/-- The diagonal case: `⟨(θ|_U)^n_{u|_U}⟩(val⁻¹ S) = ⟨θ^n_u⟩(S ∩ U)`. -/
theorem diagonalPotentialMeasure_restrict_apply [CompactSpace U] [Nonempty U]
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {S : Set M} (hS : MeasurableSet S) :
    DiagonalMass.diagonalPotentialMeasure (restrictForm U θ) (fun y : U => u y)
        (isThetaPshPotential_restrict hu) (Subtype.val ⁻¹' S) =
      DiagonalMass.diagonalPotentialMeasure θ u hu (S ∩ U) :=
  globalMixedMeasure_restrict_apply (θ := fun _ => θ) (u := fun _ => u) (fun _ => hu.1)
    (fun _ => (isThetaPshPotential_restrict hu).1) hS

end Measure

/-! ### Pluripolar sets -/

section Pluripolar

/-- A PSH function on a connected open set which is somewhere finite is somewhere finite on
every nonempty open subset (its pole set is Lebesgue null). -/
theorem exists_ne_bot_of_isOpen_subset {u : ComplexModel n → EReal} {V W : Set (ComplexModel n)}
    (hu : PlurisubharmonicOn u V) (hV : IsPreconnected V) (hne : ∃ a ∈ V, u a ≠ ⊥)
    (hW : IsOpen W) (hWne : W.Nonempty) (hWV : W ⊆ V) : ∃ b ∈ W, u b ≠ ⊥ := by
  by_contra h
  push Not at h
  have hae := hu.ae_finite volume hV hne
  have h0 : (volume.restrict V) W = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx hxW
    exact hx.2 (h x hxW)
  rw [Measure.restrict_apply hW.measurableSet, inter_eq_left.mpr hWV] at h0
  exact (hW.measure_pos volume hWne).ne' h0

/-- **Pluripolarity at a point only sees a neighbourhood.**  If `s` is locally pluripolar at
`x` and `t` agrees with a subset of `s` near `x`, then `t` is locally pluripolar at `x`. -/
theorem locallyPluripolarAt_of_inter_subset {s t : Set (ComplexModel n)} {x : ComplexModel n}
    (hs : LocallyPluripolarAt s x) {W : Set (ComplexModel n)} (hW : W ∈ 𝓝 x)
    (hts : t ∩ W ⊆ s) : LocallyPluripolarAt t x := by
  obtain ⟨V, u, hVo, hxV, hVc, hu, hne, hp⟩ := hs
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hVo.mem_nhds hxV) hW)
  refine ⟨Metric.ball x r, u, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball x r).isPreconnected, fun y hy => hu y (hrsub hy).1,
    exists_ne_bot_of_isOpen_subset hu hVc hne Metric.isOpen_ball ⟨x, Metric.mem_ball_self hr⟩
      (fun y hy => (hrsub hy).1), fun y hy hyt => hp y (hrsub hy).1 (hts ⟨hyt, (hrsub hy).2⟩)⟩

/-- **Pluripolarity pulls back along a holomorphic open partial homeomorphism** (a chart
transition): if `s` is locally pluripolar at `τ z`, then `τ⁻¹ s` is locally pluripolar at `z`. -/
theorem locallyPluripolarAt_preimage {τ : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n)}
    (hτ : DifferentiableOn ℂ τ τ.source) {z : ComplexModel n} (hz : z ∈ τ.source)
    {s : Set (ComplexModel n)} (hs : LocallyPluripolarAt s (τ z)) :
    LocallyPluripolarAt (τ.source ∩ τ ⁻¹' s) z := by
  obtain ⟨V', u', hVo, hxV, hVc, hu, hne, hp⟩ := hs
  have hD : τ.source ∩ τ ⁻¹' V' ∈ 𝓝 z :=
    (τ.continuousOn.isOpen_inter_preimage τ.open_source hVo).mem_nhds ⟨hz, hxV⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hD
  have hBsrc : Metric.ball z r ⊆ τ.source := fun y hy => (hrsub hy).1
  have hBV : MapsTo τ (Metric.ball z r) V' := fun y hy => (hrsub hy).2
  have hpsh : PlurisubharmonicOn (fun y => u' (τ y)) (Metric.ball z r) :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic Metric.isOpen_ball
      (hτ.mono hBsrc) hBV hu
  have himg : IsOpen (τ '' Metric.ball z r) := τ.isOpen_image_of_subset_source Metric.isOpen_ball hBsrc
  obtain ⟨b', ⟨b, hb, rfl⟩, hb'⟩ := exists_ne_bot_of_isOpen_subset hu hVc hne himg
    ⟨τ z, z, Metric.mem_ball_self hr, rfl⟩ (fun _ ⟨y, hy, hyb⟩ => hyb ▸ hBV hy)
  exact ⟨Metric.ball z r, fun y => u' (τ y), Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball z r).isPreconnected, hpsh, ⟨b, hb, hb'⟩,
    fun y hy hys => hp (τ y) (hBV hy) hys.2⟩

/-- **Pluripolar sets restrict to an open submanifold.** -/
theorem manifoldLocallyPluripolar_preimage_val {S : Set M}
    (hS : ManifoldLocallyPluripolar (n := n) S) :
    ManifoldLocallyPluripolar (n := n) (Subtype.val ⁻¹' S : Set U) := by
  intro c z hz
  have hne : Nonempty U := ⟨c.val.symm z⟩
  obtain ⟨x, hx⟩ := TopologicalSpace.Opens.chart_eq hne c.property
  set d := complexChartAt (n := n) (x : M) with hd
  have hdval : d.val = chartAt (ComplexModel n) (x : M) := rfl
  have hct : c.val.target ⊆ d.val.target := by
    rw [hx, hdval]; exact (chartAt (ComplexModel n) (x : M)).subtypeRestr_target_subset hne
  have hsymm : ∀ w ∈ c.val.target, (c.val.symm w : M) = d.val.symm w := by
    intro w hw
    have hw' : w ∈ ((chartAt (ComplexModel n) (x : M)).subtypeRestr hne).target := by
      rw [← hx]; exact hw
    have := (chartAt (ComplexModel n) (x : M)).subtypeRestr_symm_apply hne hw'
    rw [hdval, ← this, hx]
    rfl
  refine (hS d z (hct hz)).mono ?_
  rintro w ⟨hw, hwS⟩
  refine ⟨hct hw, ?_⟩
  simp only [mem_preimage] at hwS ⊢
  rwa [← hsymm w hw]

/-- **Pluripolar sets of a clopen open submanifold are pluripolar in the manifold.** -/
theorem manifoldLocallyPluripolar_image_val (hU : IsClopen (U : Set M)) {T : Set U}
    (hT : ManifoldLocallyPluripolar (n := n) T) :
    ManifoldLocallyPluripolar (n := n) (Subtype.val '' T : Set M) := by
  intro e z hz
  set p := e.val.symm z with hp
  by_cases hpU : p ∈ (U : Set M)
  · -- the preferred chart of `U` at `p`, read in `M`
    set y : U := ⟨p, hpU⟩
    set c := complexChartAt (n := n) y with hc
    set d := complexChartAt (n := n) p with hd
    have hcy : c.val y = d.val p := rfl
    have hcz : c.val y ∈ c.val.target := c.val.map_source (mem_complexChartAt_source y)
    have hloc : LocallyPluripolarAt (pluripolarChartSet (Subtype.val '' T) d) (d.val p) := by
      have h1 := hT c (c.val y) hcz
      rw [hcy] at h1
      refine locallyPluripolarAt_of_inter_subset h1 (c.val.open_target.mem_nhds hcz) ?_
      rintro w ⟨⟨hwd, ⟨t, htT, htw⟩⟩, hwc⟩
      refine ⟨hwc, ?_⟩
      have h2 : (c.val.symm w : M) = d.val.symm w := val_complexChartAt_opens_symm y hwc
      simp only [mem_preimage]
      have h3 : c.val.symm w = t := Subtype.val_injective (h2.trans htw.symm)
      rw [h3]; exact htT
    -- change of chart from `d` to `e`
    set τ := chartTransition e d with hτ
    have hpd : e.val.symm z ∈ d.val.source := mem_complexChartAt_source p
    have hzτ : z ∈ τ.source := ⟨hz, hpd⟩
    have hτz : τ z = d.val p := rfl
    have h4 := locallyPluripolarAt_preimage
      (RegularPatchNeighborhood.differentiableOn_chartTransition e d) hzτ (by rw [hτz]; exact hloc)
    refine locallyPluripolarAt_of_inter_subset h4 (τ.open_source.mem_nhds hzτ) ?_
    rintro w ⟨⟨hwe, hwT⟩, hwτ⟩
    refine ⟨hwτ, ?_, ?_⟩
    · exact d.val.map_source (show e.val.symm w ∈ d.val.source from hwτ.2)
    · have hw2 : e.val.symm w ∈ d.val.source := hwτ.2
      show d.val.symm (d.val (e.val.symm w)) ∈ Subtype.val '' T
      rw [d.val.left_inv hw2]
      exact hwT
  · -- away from `U` the set is empty near `z`
    have hW : e.val.target ∩ e.val.symm ⁻¹' (U : Set M)ᶜ ∈ 𝓝 z :=
      (e.val.isOpen_inter_preimage_symm hU.1.isOpen_compl).mem_nhds ⟨hz, hpU⟩
    have hempty : LocallyPluripolarAt (∅ : Set (ComplexModel n)) z :=
      manifoldLocallyPluripolar_empty (n := n) (M := M) e z hz |>.mono (empty_subset _)
    refine locallyPluripolarAt_of_inter_subset hempty hW ?_
    rintro w ⟨⟨-, ⟨t, -, htw⟩⟩, -, hwU⟩
    exact absurd (htw ▸ t.2) hwU

end Pluripolar

/-! ### Envelopes -/

section Envelopes

/-- **Usc regularization commutes with the restriction to an open subset.** -/
theorem uscRegularization_comp_val (f : M → EReal) :
    (fun y : U => uscRegularization f y) = uscRegularization (fun y : U => f y) := by
  funext y
  have hne : Nonempty U := ⟨y⟩
  have h := uscRegularization_comp_openPartialHomeomorph_apply f
    (U.openPartialHomeomorphSubtypeCoe hne) (x := y) (by simp)
  simpa [Function.comp_def] using h.symm

/-- Quasi-everywhere statements restrict to an open submanifold. -/
theorem quasiEverywhere_restrict {P : M → Prop} (hP : QuasiEverywhere (n := n) P) :
    QuasiEverywhere (n := n) (fun y : U => P y) :=
  manifoldLocallyPluripolar_preimage_val (U := U) hP

/-- Theta-PSH potentials (for a smooth form) restrict to an open submanifold. -/
theorem isThetaPshPotential_restrict' {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) :
    IsThetaPshPotential (SmoothRealForm.pullback (contMDiff_val U) θ) (fun y : U => u y) :=
  ⟨thetaPlurisubharmonic_restrict hu.1, locallyNondegenerate_restrict hu.2⟩

open Classical in
/-- The extension of a function on `U` by `⊥`. -/
def extendBot (ψ : U → EReal) : M → EReal :=
  fun x => if h : x ∈ (U : Set M) then ψ ⟨x, h⟩ else ⊥

@[simp] theorem extendBot_val (ψ : U → EReal) (y : U) : extendBot ψ (y : M) = ψ y := by
  unfold extendBot
  rw [dif_pos (show (y : M) ∈ (U : Set M) from y.2)]

/-- **A competitor on a clopen `U` glues with a competitor on `M`.** -/
theorem piecewise_mem_rooftopCompetitors (hU : IsClopen (U : Set M))
    {θ : SmoothRealForm n M 2} {f : M → EReal} {φ : M → EReal}
    (hφ : φ ∈ rooftopCompetitors θ f) {ψ : U → EReal}
    (hψ : ψ ∈ rooftopCompetitors (SmoothRealForm.pullback (contMDiff_val U) θ)
      (fun y : U => f y)) [DecidablePred (· ∈ (U : Set M))] :
    (U : Set M).piecewise (extendBot ψ) φ ∈ rooftopCompetitors θ f := by
  have hψ' : (fun y : U => extendBot ψ (y : M)) = ψ := funext fun y => extendBot_val ψ y
  refine ⟨⟨thetaPlurisubharmonic_piecewise hU (by rw [hψ']; exact hψ.1.1) hφ.1.1,
    locallyNondegenerate_piecewise hU (by rw [hψ']; exact hψ.1.2) hφ.1.2⟩, ?_⟩
  -- the exceptional set lies in the image of that of `ψ` and that of `φ`
  have hunion := manifoldLocallyPluripolar_union
    (manifoldLocallyPluripolar_image_val hU hψ.2) hφ.2
  refine hunion.mono ?_
  intro x hx
  have hx' : ¬ (U : Set M).piecewise (extendBot ψ) φ x ≤ f x := hx
  by_cases hxU : x ∈ (U : Set M)
  · left
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    show ¬ ψ ⟨x, hxU⟩ ≤ f x
    rwa [Set.piecewise_eq_of_mem _ _ _ hxU, show extendBot ψ x = ψ ⟨x, hxU⟩ from
      extendBot_val ψ ⟨x, hxU⟩] at hx'
  · right
    show ¬ φ x ≤ f x
    rwa [Set.piecewise_eq_of_notMem _ _ _ hxU] at hx'

/-- **The rooftop supremum is local on a clopen set**, provided there is a competitor. -/
theorem rooftopSupremum_restrict (hU : IsClopen (U : Set M)) {θ : SmoothRealForm n M 2}
    {f : M → EReal} (hne : (rooftopCompetitors θ f).Nonempty) :
    (fun y : U => rooftopSupremum θ f y) =
      rooftopSupremum (SmoothRealForm.pullback (contMDiff_val U) θ) (fun y : U => f y) := by
  classical
  obtain ⟨φ, hφ⟩ := hne
  funext y
  rw [rooftopSupremum_apply, rooftopSupremum_apply]
  apply le_antisymm
  · refine iSup₂_le fun u hu => ?_
    exact le_iSup₂_of_le (fun z : U => u z)
      ⟨isThetaPshPotential_restrict' hu.1, quasiEverywhere_restrict hu.2⟩ le_rfl
  · refine iSup₂_le fun ψ hψ => ?_
    refine le_iSup₂_of_le ((U : Set M).piecewise (extendBot ψ) φ)
      (piecewise_mem_rooftopCompetitors hU hφ hψ) ?_
    rw [Set.piecewise_eq_of_mem _ _ _ y.2, extendBot_val]

/-- **The rooftop envelope is local on a clopen set**: `P_{θ|_U}(f|_U) = P_θ(f)|_U`, provided
the competitor set on `M` is nonempty. -/
theorem rooftopEnvelope_restrict (hU : IsClopen (U : Set M)) {θ : SmoothRealForm n M 2}
    {f : M → EReal} (hne : (rooftopCompetitors θ f).Nonempty) :
    rooftopEnvelope (SmoothRealForm.pullback (contMDiff_val U) θ) (fun y : U => f y) =
      fun y : U => rooftopEnvelope θ f y := by
  unfold rooftopEnvelope
  rw [← rooftopSupremum_restrict hU hne, ← uscRegularization_comp_val]

/-- A rooftop envelope which is a theta-PSH potential on a nonempty manifold has a competitor:
otherwise the supremum and its regularization would be identically `-∞`. -/
theorem rooftopCompetitors_nonempty_of_isThetaPshPotential [Nonempty M]
    {θ : SmoothRealForm n M 2} {f : M → EReal}
    (hw : IsThetaPshPotential θ (rooftopEnvelope θ f)) :
    (rooftopCompetitors θ f).Nonempty := by
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hbot : rooftopEnvelope θ f = fun _ => ⊥ := by
    have hs : rooftopSupremum θ f = fun _ => ⊥ := by
      funext x
      rw [rooftopSupremum_apply, hempty]
      simp
    unfold rooftopEnvelope
    rw [hs]
    funext x
    apply le_antisymm _ bot_le
    exact uscRegularization_le_of_eventually_le (upperSemicontinuous_const x)
      (Eventually.of_forall fun _ => le_rfl)
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨y, -, hy⟩ := hw.2 x univ isOpen_univ (mem_univ x)
  exact hy (congrFun hbot y)

end Envelopes

/-! ### Connected components -/

section Components

/-- A complex manifold is locally connected (charts are local homeomorphisms onto open subsets of
`ℂⁿ`). -/
theorem locallyConnectedSpace (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] : LocallyConnectedSpace X :=
  ChartedSpace.locallyConnectedSpace (ComplexModel n) X

/-- The connected component of a point of a locally connected space, as an open set. -/
def componentOpens {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] (x : X) : Opens X :=
  ⟨connectedComponent x, isOpen_connectedComponent⟩

section

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

theorem isClopen_componentOpens (x : X) : IsClopen (componentOpens x : Set X) :=
  isClopen_connectedComponent

theorem mem_componentOpens (x : X) : x ∈ componentOpens x := mem_connectedComponent

instance instNonemptyComponentOpens (x : X) : Nonempty (componentOpens x) := ⟨⟨x, mem_connectedComponent⟩⟩

instance instConnectedSpaceComponentOpens (x : X) : ConnectedSpace (componentOpens x) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

instance instCompactSpaceComponentOpens [CompactSpace X] (x : X) :
    CompactSpace (componentOpens x) :=
  isCompact_iff_compactSpace.mp (isClopen_componentOpens x).1.isCompact

/-- **Nullity is decided on connected components.**  A set is null for a measure on a
second-countable locally connected space as soon as its trace on the connected component of
each of its points is null. -/
theorem measure_eq_zero_of_forall_connectedComponent [SecondCountableTopology X]
    [MeasurableSpace X] {μ : Measure X} {S : Set X}
    (h : ∀ x ∈ S, μ (S ∩ connectedComponent x) = 0) : μ S = 0 := by
  refine measure_null_of_locally_null S fun x hx => ⟨S ∩ connectedComponent x, ?_, h x hx⟩
  rw [mem_nhdsWithin]
  exact ⟨connectedComponent x, isOpen_connectedComponent, mem_connectedComponent,
    fun y hy => ⟨hy.2, hy.1⟩⟩

end

end Components

end

end Hironaka.OpensRestrictionMeasure
