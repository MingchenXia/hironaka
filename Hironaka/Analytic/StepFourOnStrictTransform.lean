import Hironaka.Analytic.StepFourKahlerClassOnW
import Hironaka.Analytic.SubmanifoldChartedSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 4 on the strict transform itself

Source: Copy-4, `prop:principalization`, Steps 4 and 6
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1880-1906,
1968-1984`): `lem:residual-nef` is applied **on `W`**, and in Step 6 the potential `f` of
the Kähler form `A_W` on `W` is *extended to a smooth function `f̃` near `W`*.

`StepFourKahlerClassOnW.exists_positiveOnOneFlattening_of_logSingularities` takes `W` as
the image of an abstract holomorphic immersion `ι : V → Y` and the extension of smooth
functions along `ι` as hypotheses.  Here `V := ↥W` with the flattening atlas of
`Hironaka.SubmanifoldChartedSpace` and `ι := Subtype.val`, and both hypotheses are
**proved**:

* `fderiv_coordinateMap_val_injective` — the inclusion of a closed complex submanifold is
  an immersion: in charts it has the holomorphic left inverse
  `w ↦ pr_k (Φ (e (d⁻¹ w)))`, so its differential is injective.
* `exists_chartSmooth_extension` — the smooth extension lemma (Lee, *Introduction to
  Smooth Manifolds*, Lemma 5.34, in the chart-smooth setting): on a compact `Y`, every
  chart-smooth function on `↥W` is the restriction of a chart-smooth function on `Y`.
  Near a point of `W`, extend by `h ∘ (flattening chart)⁻¹ ∘ pr_k ∘ Φ ∘ e`, which is
  constant along the normal coordinates; off `W` use `0`; glue with the partition of unity
  `ChartPartition.exists_chartSmooth_partitionOfUnity`.

`exists_positiveOnOneFlattening_of_logSingularities_strictTransform` is then Step 4 with
only source-level inputs left: a Kähler-current potential `φ'` on `W` with log
singularities along a metered divisor `D_W`, and the form identity
`θ' - Θ_{D_W} = β|_W` (`eq:AW-class`).  In Copy-4 `φ'` is
`(π|_W)^*φ_{K,ℓ} + τ ψ_{E_rel}|_W`, built from Step 1 and `sec:positive-current` (which
waits on QEA), so it remains a hypothesis.

The two new lemmas are sorry-free; the Step-4 theorem rests on `lem:residual-nef`'s two
named inputs exactly as `StepFourKahlerClassOnW` does.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepFourOnStrictTransform

open Hironaka.HolomorphicMaps Hironaka.RegularLocusDense Hironaka.BlowupSequences
  Hironaka.PositiveClasses
  Hironaka.HolomorphicIdealSheaves Hironaka.AnalyticGluingData
  SubmanifoldChartedSpace ManifoldTubePositivity TubePositivityOneFlattening
  GlobalTubeFunction ChartPartition ResidualNefReduction StepFourKahlerClassOnW

noncomputable section

variable {n k : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X}

/-! ### The inclusion is an immersion -/

/-- **The inclusion `↥W → X` is an immersion.**  Read in a flattening chart `F` of `↥W`
and any ambient chart `d`, it has the left inverse
`w ↦ pr_k (Φ_F (e_F (d⁻¹ w)))`, holomorphic near the image point. -/
theorem fderiv_coordinateMap_val_injective (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀ (e : ComplexChart k W) (d : ComplexChart n X) (z : ComplexModel k),
      z ∈ coordinateDomain Subtype.val e d →
        Function.Injective (fderiv ℝ (coordinateMap Subtype.val e d) z) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro e d z hz
  obtain ⟨F, hF⟩ := e.property
  have hval := contMDiff_val hk hW
  have hzt : z ∈ F.coordTarget := by
    have h := hz.1
    rw [hF] at h
    exact h
  -- the coordinate representative of the inclusion
  have hc_eq : ∀ ζ ∈ F.coordTarget,
      coordinateMap Subtype.val e d ζ = d.val (F.ofCoord ζ) := by
    intro ζ hζ
    simp only [coordinateMap, Function.comp_apply]
    rw [hF, FlatData.chart_symm_apply, F.invPoint_val hζ]
  have hsymm : ∀ ζ ∈ F.coordTarget, ((e.val.symm ζ : W) : X) = F.ofCoord ζ := by
    intro ζ hζ
    rw [hF, FlatData.chart_symm_apply, F.invPoint_val hζ]
  -- its left inverse
  set G : ComplexModel n → ComplexModel k := fun w =>
    coordinateProjection n k (F.flat (F.amb.val (d.val.symm w))) with hG
  have hev : (G ∘ coordinateMap Subtype.val e d) =ᶠ[𝓝 z] id := by
    have hopen : IsOpen (F.coordTarget ∩ coordinateDomain Subtype.val e d) :=
      F.isOpen_coordTarget.inter (coordinateDomain_isOpen hval e d)
    filter_upwards [hopen.mem_nhds ⟨hzt, hz⟩] with ζ hζ
    have hd : F.ofCoord ζ ∈ d.val.source := by
      have h := hζ.2.2
      rw [mem_preimage, mem_preimage, hsymm ζ hζ.1] at h
      exact h
    simp only [Function.comp_apply, id, hG]
    rw [hc_eq ζ hζ.1, d.val.left_inv hd, F.flat_amb_ofCoord hζ.1,
      coordinateProjection_coordinateInclusion hk]
  -- differentiability of both
  have hcd : DifferentiableAt ℝ (coordinateMap Subtype.val e d) z :=
    (coordinateMap_contDiffAt_real hval e d hz).differentiableAt (by simp)
  have hamb : F.ofCoord z ∈ F.ambSource := F.ofCoord_mem_ambSource hzt
  have hw₀ : coordinateMap Subtype.val e d z ∈ (chartTransition d F.amb).source := by
    refine ⟨coordinateMap_mem_target hz, ?_⟩
    show d.val.symm (coordinateMap Subtype.val e d z) ∈ F.amb.val.source
    rw [hc_eq z hzt, d.val.left_inv]
    · exact hamb.1
    · have h := hz.2
      rw [mem_preimage, mem_preimage, hsymm z hzt] at h
      exact h
  have htrans : DifferentiableAt ℝ (chartTransition d F.amb) (coordinateMap Subtype.val e d z) :=
    (chartTransition_contDiffAt_real d F.amb hw₀).differentiableAt (by simp)
  have hflat_mem : chartTransition d F.amb (coordinateMap Subtype.val e d z) ∈ F.flat.source := by
    have h : chartTransition d F.amb (coordinateMap Subtype.val e d z)
        = F.amb.val (F.ofCoord z) := by
      show F.amb.val (d.val.symm (coordinateMap Subtype.val e d z)) = _
      rw [hc_eq z hzt, d.val.left_inv]
      have h := hz.2
      rw [mem_preimage, mem_preimage, hsymm z hzt] at h
      exact h
    rw [h]
    exact hamb.2
  have hflat : DifferentiableAt ℝ F.flat
      (chartTransition d F.amb (coordinateMap Subtype.val e d z)) :=
    (F.differentiableOn_flat.differentiableAt
      (F.flat.open_source.mem_nhds hflat_mem)).restrictScalars ℝ
  have hGd : DifferentiableAt ℝ G (coordinateMap Subtype.val e d z) := by
    have h := ((coordinateProjection n k).restrictScalars ℝ).differentiableAt.comp _
      (hflat.comp _ htrans)
    exact h
  have hcomp : (fderiv ℝ G (coordinateMap Subtype.val e d z)).comp
      (fderiv ℝ (coordinateMap Subtype.val e d) z) = ContinuousLinearMap.id ℝ _ := by
    rw [← fderiv_comp z hGd hcd, hev.fderiv_eq, fderiv_id]
  intro u v huv
  have h1 := congrArg (fun L : ComplexModel k →L[ℝ] ComplexModel k => L u) hcomp
  have h2 := congrArg (fun L : ComplexModel k →L[ℝ] ComplexModel k => L v) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
  rw [← h1, ← h2, huv]

/-! ### The smooth extension lemma -/

/-- **A local extension near a point of `W`.**  On the flattening domain `S` at `x`,
`g = h ∘ (flattening chart of ↥W)⁻¹ ∘ pr_k ∘ Φ ∘ e` is chart-smooth and agrees with `h`
on `W ∩ S`. -/
theorem exists_local_extension (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ (h : W → ℝ), ChartSmooth (n := k) h → ∀ x ∈ W,
      ∃ (S : Set X) (g : X → ℝ), IsOpen S ∧ x ∈ S ∧ ChartSmoothOn n g S ∧
        ∀ p : W, p.1 ∈ S → g p.1 = h p := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro h hh x hx
  set F := FlatData.ofRegularAtDim (hW x hx) with hFdef
  set P : X → ComplexModel n := fun y =>
    coordinateInclusion n k (coordinateProjection n k (F.flat (F.amb.val y))) with hP
  refine ⟨F.ambSource ∩ P ⁻¹' F.flat.target,
    fun y => h (F.invPoint (coordinateProjection n k (F.flat (F.amb.val y)))), ?_, ?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun y => F.flat (F.amb.val y)) F.ambSource :=
      F.flat.continuousOn.comp (F.amb.val.continuousOn.mono fun y hy => hy.1)
        fun y hy => hy.2
    have hcont : ContinuousOn P F.ambSource :=
      ((coordinateInclusion n k).continuous.comp
        (coordinateProjection n k).continuous).comp_continuousOn h1
    exact hcont.isOpen_inter_preimage F.isOpen_ambSource F.flat.open_target
  · have hxa : x ∈ F.ambSource := FlatData.mem_ambSource_ofRegularAtDim (hW x hx)
    refine ⟨hxa, ?_⟩
    show P x ∈ F.flat.target
    have heq : P x = F.flat (F.amb.val x) := F.coordinateInclusion_toCoord ⟨x, hx⟩ hxa
    rw [heq]
    exact F.flat.map_source hxa.2
  · intro e z hz
    have hhF := hh ⟨F.chart hk, chart_mem_atlas hk hW F⟩
    have hsrc : z ∈ (chartTransition e F.amb).source := ⟨hz.1, hz.2.1.1⟩
    have h1 : ContDiffAt ℂ ∞ (chartTransition e F.amb) z := chartTransition_contDiffAt e F.amb hsrc
    have h2 : ContDiffAt ℂ ∞ F.flat (chartTransition e F.amb z) :=
      (contDiffOn_of_differentiableOn_complex F.differentiableOn_flat
        F.flat.open_source).contDiffAt (F.flat.open_source.mem_nhds hz.2.1.2)
    have hinner : ContDiffAt ℝ ∞
        (fun w => coordinateProjection n k (F.flat (chartTransition e F.amb w))) z :=
      ((coordinateProjection n k).contDiff.contDiffAt.comp z (h2.comp z h1)).restrict_scalars ℝ
    have hmem : coordinateProjection n k (F.flat (chartTransition e F.amb z)) ∈
        (F.chart hk).target := hz.2.2
    have houter := hhF.contDiffAt ((F.chart hk).open_target.mem_nhds hmem)
    exact (houter.comp z hinner).contDiffWithinAt
  · intro p hp
    show h (F.invPoint (F.toCoord p)) = h p
    congr 1
    exact (F.chart hk).left_inv hp.1

/-- **The smooth extension lemma** (Lee, *Introduction to Smooth Manifolds*, Lemma 5.34, in
the chart-smooth setting).  On a compact complex manifold, every chart-smooth function on a
closed complex submanifold `↥W` (with its flattening atlas) is the restriction of a
chart-smooth function on the whole manifold. -/
theorem exists_chartSmooth_extension [CompactSpace X] (hk : k ≤ n) (hWc : IsClosed W)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ h : W → ℝ, ChartSmooth (n := k) h →
      ∃ f : X → ℝ, ChartSmooth (n := n) f ∧ ∀ p : W, f p.1 = h p := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro h hh
  have hloc : ∀ x : X, ∃ (S : Set X) (g : X → ℝ), IsOpen S ∧ x ∈ S ∧ ChartSmoothOn n g S ∧
      ∀ p : W, p.1 ∈ S → g p.1 = h p := by
    intro x
    by_cases hx : x ∈ W
    · exact exists_local_extension hk hW h hh x hx
    · exact ⟨Wᶜ, fun _ => 0, hWc.isOpen_compl, hx, fun e => contDiffOn_const,
        fun p hp => absurd p.2 hp⟩
  choose S g hSo hxS hg hgh using hloc
  obtain ⟨m, χ, idx, hχs, -, hχsupp, -, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) (fun x => (⟨S x, hSo x⟩ : Opens X))
      (fun x => ⟨x, hxS x⟩)
  refine ⟨fun y => ∑ a, bumpExtend (S (idx a)) (χ a) (g (idx a)) y, ?_, ?_⟩
  · intro e
    exact ContDiffOn.sum fun a _ =>
      chartSmooth_bumpExtend (hSo (idx a)) (hχs a) (hg (idx a)) (hχsupp a) e
  · intro p
    have hterm : ∀ a, bumpExtend (S (idx a)) (χ a) (g (idx a)) p.1 = χ a p.1 * h p := by
      intro a
      by_cases hpS : p.1 ∈ S (idx a)
      · rw [bumpExtend_of_mem hpS, hgh (idx a) p hpS]
      · rw [bumpExtend_of_notMem hpS,
          image_eq_zero_of_notMem_tsupport (fun hc => hpS (hχsupp a hc)), zero_mul]
    simp only [hterm]
    rw [← Finset.sum_mul, hχ1, one_mul]

/-! ### Step 4 on the strict transform -/

/-- **Copy-4 Step 4 on `W` itself.**  For a closed connected complex submanifold `W` of
dimension `k` of a compact complex manifold, with its flattening complex structure: if on
`W` there is a Kähler-current potential `φ'` of a form `θ'` with log singularities along a
metered divisor `D_W`, and `θ' - Θ_{D_W}` is the restriction `β|_W` (`eq:AW-class` at the
level of forms), then `β + ddᶜf̃` is strictly positive along the tangent directions of `W`
for a chart-smooth `f̃` on the ambient manifold.  The immersion and extension hypotheses
of `StepFourKahlerClassOnW` are discharged. -/
theorem exists_positiveOnOneFlattening_of_logSingularities_strictTransform [CompactSpace X]
    (hW : IsClosedConnectedSubmanifold n W k) (β : ClosedRealOneOneForm n X) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    ∀ {θ' : ClosedRealOneOneForm k W} {DW : MeteredEffectiveQDivisor k W} {φ' : W → EReal},
      IsKahlerCurrentPotential θ' φ' → HasLogSingularitiesAlong DW φ' →
      (∀ (e : ComplexChart k W) (z : ComplexModel k), z ∈ e.val.target →
        (θ' - DW.curvature).val.coeff e z =
          (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2) β).val.coeff e z) →
      ∃ (f : X → ℝ) (hf : ChartSmooth (n := n) f),
        PositiveOnOneFlattening W k (β + ddcClosedForm f hf) := by
  have hk := le_of_isClosedConnectedSubmanifold hW
  let := chartedSpace hk hW.2.2
  have := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have : Nonempty W := hW.2.1.nonempty.to_subtype
  intro θ' DW φ' hφ' hlog hclass
  exact exists_positiveOnOneFlattening_of_logSingularities hW.2.2 (contMDiff_val hk hW.2.2)
    (fderiv_coordinateMap_val_injective hk hW.2.2) (fun v => v.2)
    (fun w hw => ⟨⟨w, hw⟩, rfl⟩) β hφ' hlog hclass
    (exists_chartSmooth_extension hk hW.1 hW.2.2)

/-- **Copy-4 Steps 4 and 6 on `W` itself**: the local geometry `U ⊇ W`, `σ` with
`β + ddᶜσ` dominating a Kähler form on `U`, from the Step-4 current on `W`. -/
theorem exists_localGeometry_of_logSingularities_strictTransform [CompactSpace X]
    (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) (β : ClosedRealOneOneForm n X) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    ∀ {θ' : ClosedRealOneOneForm k W} {DW : MeteredEffectiveQDivisor k W} {φ' : W → EReal},
      IsKahlerCurrentPotential θ' φ' → HasLogSingularitiesAlong DW φ' →
      (∀ (e : ComplexChart k W) (z : ComplexModel k), z ∈ e.val.target →
        (θ' - DW.curvature).val.coeff e z =
          (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2) β).val.coeff e z) →
      ∃ (U : Set X) (σ : X → ℝ), IsOpen U ∧ W ⊆ U ∧ ChartSmooth (n := n) σ ∧
        DominatesKahlerFormOn β (fun x => (σ x : EReal)) U := by
  intro θ' DW φ' hφ' hlog hclass
  obtain ⟨f, hf, hpos⟩ :=
    exists_positiveOnOneFlattening_of_logSingularities_strictTransform hW β hφ' hlog hclass
  exact StepSixLocalGeometry.exists_localGeometry_of_positiveOnOneFlattening omega hW.1 hW.2.2
    β hf hpos

end

end Hironaka.StepFourOnStrictTransform
