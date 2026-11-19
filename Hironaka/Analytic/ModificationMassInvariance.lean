import Hironaka.Analytic.GlobalNonPluripolar
import Hironaka.Analytic.NonPluripolarHolomorphic
import Hironaka.Analytic.PatchOverlap
import Hironaka.Analytic.DiagonalMass
import Hironaka.Analytic.PotentialTheory.AnalyticSingularities
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.Analytic.HolomorphicLocalInverse
import Hironaka.Analytic.GlobalPotentialPullback
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Analytic.LocalPotentialPullback
import Hironaka.Analytic.FormPullbackFunctorial

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Invariance of non-pluripolar masses under blowups (Xia, Hironaka Prop. 2.4.2, diagonal case)

Source: Copy-4, `sec:npp`, item `it:invariance` (Xia, *Singularities in global pluripotential
theory*, Proposition 2.4.2), used in `lem:domination`, Step 2 (`eq:dom-Ak`):

> If `π : Y → X` is a modification and `T₁, …, Tₙ` are closed positive `(1,1)`-currents on `X`,
> then `∫_Y π^*T₁ ∧ ⋯ ∧ π^*Tₙ = ∫_X T₁ ∧ ⋯ ∧ Tₙ` (non-pluripolar products).

Part of the positive-current programme (`TN.2.3.PCI`).

## Main results

* `manifoldLocallyPluripolar_of_isComplexAnalyticSubset` — an analytic subset with empty
  interior is (locally) pluripolar: in every chart it lies in the pole set of
  `log ∑ |gᵢ ∘ T|²`, `T` the chart transition to the chart of a local presentation.
* `exists_isBiholomorphicPair_image` — an injective holomorphic map of an open set of `ℂⁿ` with
  invertible derivative everywhere is a biholomorphism onto its (open) image, with inverse
  `Function.invFunOn` (holomorphic inverse function theorem).
* `pullbackPatch` — a local-potential patch `Q` of `(θ, u)` on `X` and an atlas chart `e` of `Y`
  give a patch of `(π^*θ, u ∘ π)` on `Y` whose corrected potentials are those of `Q` composed with
  the coordinate expression `τ = Q.chart ∘ π ∘ e⁻¹` (no gauge term: the local potentials are
  pulled back as well).
* `globalMixedMeasure_restrict_preimage_eq_map` — **naturality**: if `π` is an isomorphism over
  an open `N ⊆ X`, the global mixed non-pluripolar measure of `(π^*θ, u ∘ π)` restricted to
  `π⁻¹ N` is the pushforward of that of `(θ, u)` restricted to `N` under the inverse of `π`.
* `diagonalPotentialMass_pullback_of_isBlowupAlong`,
  `diagonalPotentialMass_pullback_of_isBlowupSequence` — **mass invariance**:
  `∫_Y (π^*θ)_{u∘π}^n = ∫_X θ_u^n` for a blowup (the centre `C` and `π⁻¹ C` are analytic with
  empty interior, hence pluripolar and not charged) and, by induction, for a blowup sequence.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace Hironaka.ModificationMassInvariance

open Hironaka.HolomorphicMaps Hironaka.GlobalPotentialPatches Hironaka.BlowupSequences
  Hironaka.MixedNonPluripolar MixedNonPluripolar BedfordTaylor GlobalNonPluripolar

noncomputable section

/-! ### Analytic subsets with empty interior are pluripolar -/

section Pluripolar

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **An analytic subset with empty interior is locally pluripolar.**  At a chart point `z`,
transport the generators of a local presentation of `A` at `e⁻¹ z` through the chart transition:
`w = log ∑ |gᵢ ∘ T|²` is plurisubharmonic near `z`, `-∞` on `A`, and finite at a point off `A`
(which exists in every open set since `interior A = ∅`). -/
theorem manifoldLocallyPluripolar_of_isComplexAnalyticSubset {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hint : interior A = ∅) :
    ManifoldLocallyPluripolar (n := n) A := by
  intro e z hz
  set x : M := e.val.symm z with hxdef
  obtain ⟨P⟩ := hA x
  set c := complexChartAt (n := n) x with hcdef
  set T := chartTransition e c with hTdef
  have hxc : x ∈ c.val.source := mem_complexChartAt_source x
  set Ω : Set (ComplexModel n) := T.source ∩ T ⁻¹' P.coordinateNeighborhood with hΩdef
  have hΩ : IsOpen Ω := T.isOpen_inter_preimage P.isOpen_coordinateNeighborhood
  have hzT : z ∈ T.source := ⟨hz, hxc⟩
  have hTz : T z = c.val x := rfl
  have hzΩ : z ∈ Ω := ⟨hzT, by rw [mem_preimage, hTz]; exact P.center_mem_coordinateNeighborhood⟩
  set G : Fin P.generatorCount → ComplexModel n → ℂ := fun i w => P.generator i (T w) with hGdef
  have hG : ∀ i, DifferentiableOn ℂ (G i) Ω := fun i w hw =>
    ((P.generator_holomorphic i).differentiableAt
        (P.isOpen_coordinateNeighborhood.mem_nhds hw.2)).comp w
      ((chartTransition_contDiffAt e c hw.1).differentiableAt (by simp))
      |>.differentiableWithinAt
  -- points of `Ω`: membership in `A` is the vanishing of all `G i`
  have hzero : ∀ w ∈ Ω, (e.val.symm w ∈ A ↔ ∀ i, G i w = 0) := fun w hw =>
    P.zeroLocus hw.1.2 hw.2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ z hzΩ
  set V : Set (ComplexModel n) := Metric.ball z r with hVdef
  refine ⟨V, generatorLog G, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball z r).isPreconnected, fun w hw => ?_, ?_, fun w hw hwA => ?_⟩
  · have h := Hironaka.plurisubharmonicAt_scaled_generatorLog
      (f := G) ⟨Ω, hΩ, hball hw, hG⟩ one_pos
    simpa only [EReal.coe_one, one_mul] using h
  · -- a point of `V` off `A`
    have hzt : z ∈ e.val.target := hz
    set O : Set M := e.val.source ∩ e.val ⁻¹' V with hOdef
    have hO : IsOpen O := e.val.isOpen_inter_preimage Metric.isOpen_ball
    have hxO : x ∈ O := ⟨e.val.map_target hzt, by
      rw [mem_preimage, hxdef, e.val.right_inv hzt]; exact Metric.mem_ball_self hr⟩
    have hnot : ¬ O ⊆ A := fun hsub => by
      have := interior_maximal hsub hO
      rw [hint] at this
      exact this hxO
    obtain ⟨y, hyO, hyA⟩ := not_subset.mp hnot
    refine ⟨e.val y, hyO.2, fun hbot => hyA ?_⟩
    have hyΩ : e.val y ∈ Ω := hball hyO.2
    have h := (hzero (e.val y) hyΩ).mpr ((generatorLog_eq_bot_iff G _).mp hbot)
    rwa [e.val.left_inv hyO.1] at h
  · exact (generatorLog_eq_bot_iff G w).mpr ((hzero w (hball hw)).mp hwA.2)

end Pluripolar

/-! ### Holomorphic inverse function theorem on an injectivity domain -/

section InverseFunction

variable {n : ℕ}

/-- **An injective holomorphic map with invertible derivative is a biholomorphism onto its
image.**  The image `τ(A)` is open, and `Function.invFunOn τ A` is holomorphic on it: near
`τ w` it agrees with the local inverse of the inverse function theorem at `w`. -/
theorem exists_isBiholomorphicPair_image {A : Opens (ComplexModel n)}
    {τ : ComplexModel n → ComplexModel n} (hτ : ContDiffOn ℂ ∞ τ A) (hinj : InjOn τ A)
    (hder : ∀ w ∈ A, Function.Bijective (fderiv ℂ τ w)) :
    ∃ B : Opens (ComplexModel n), (B : Set (ComplexModel n)) = τ '' A ∧
      IsBiholomorphicPair A B τ (Function.invFunOn τ A) := by
  classical
  -- the local inverse at each point of `A`
  have hloc : ∀ w ∈ (A : Set (ComplexModel n)), ∃ Φ : OpenPartialHomeomorph (ComplexModel n)
      (ComplexModel n), w ∈ Φ.source ∧ ⇑Φ = τ ∧ ContDiffAt ℂ ∞ Φ.symm (τ w) := by
    intro w hw
    set Lw : ComplexModel n ≃L[ℂ] ComplexModel n :=
      (LinearEquiv.ofBijective (fderiv ℂ τ w).toLinearMap (hder w hw)).toContinuousLinearEquiv
    have hLw : (Lw : ComplexModel n →L[ℂ] ComplexModel n) = fderiv ℂ τ w :=
      ContinuousLinearMap.ext fun v => rfl
    have hcd : ContDiffAt ℂ ∞ τ w := hτ.contDiffAt (A.isOpen.mem_nhds hw)
    have hstrict : HasStrictFDerivAt τ (Lw : ComplexModel n →L[ℂ] ComplexModel n) w := by
      rw [hLw]; exact hcd.hasStrictFDerivAt (by simp)
    set Φ := hstrict.toOpenPartialHomeomorph τ
    have hwΦ : w ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
    have hΦcoe : ⇑Φ = τ := rfl
    have hτw : τ w ∈ Φ.target := by rw [← hΦcoe]; exact Φ.map_source hwΦ
    have hsymm : Φ.symm (τ w) = w := by rw [← hΦcoe]; exact Φ.left_inv hwΦ
    refine ⟨Φ, hwΦ, hΦcoe, Φ.contDiffAt_symm hτw (f₀' := Lw) ?_ ?_⟩
    · rw [hsymm, hΦcoe, hLw]
      exact (hcd.differentiableAt (by simp)).hasFDerivAt
    · rw [hsymm, hΦcoe]; exact hcd
  -- a neighbourhood of `τ w` inside the image, on which the inverse is the local inverse
  have hnhd : ∀ w ∈ (A : Set (ComplexModel n)), ∃ Φ : OpenPartialHomeomorph (ComplexModel n)
      (ComplexModel n), ⇑Φ = τ ∧ ContDiffAt ℂ ∞ Φ.symm (τ w) ∧
        Φ.target ∩ Φ.symm ⁻¹' A ∈ 𝓝 (τ w) ∧
        ∀ v ∈ Φ.target ∩ Φ.symm ⁻¹' A, Φ.symm v ∈ (A : Set (ComplexModel n)) ∧ τ (Φ.symm v) = v := by
    intro w hw
    obtain ⟨Φ, hwΦ, hΦcoe, hcd⟩ := hloc w hw
    have hτw : τ w ∈ Φ.target := by rw [← hΦcoe]; exact Φ.map_source hwΦ
    have hsymm : Φ.symm (τ w) = w := by rw [← hΦcoe]; exact Φ.left_inv hwΦ
    refine ⟨Φ, hΦcoe, hcd, ?_, fun v hv => ⟨hv.2, by rw [← hΦcoe]; exact Φ.right_inv hv.1⟩⟩
    exact (Φ.isOpen_inter_preimage_symm A.isOpen).mem_nhds ⟨hτw, by rw [mem_preimage, hsymm]; exact hw⟩
  have hopen : IsOpen (τ '' A) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨Φ, -, -, hmem, hinv⟩ := hnhd w hw
    exact Filter.mem_of_superset hmem fun v hv => ⟨Φ.symm v, (hinv v hv).1, (hinv v hv).2⟩
  have hleft : ∀ w ∈ (A : Set (ComplexModel n)), Function.invFunOn τ A (τ w) = w := by
    intro w hw
    have h := Function.invFunOn_pos (f := τ) (s := A) ⟨w, hw, rfl⟩
    exact hinj h.1 hw h.2
  refine ⟨⟨τ '' A, hopen⟩, rfl, ⟨hτ, ?_, fun w hw => ⟨w, hw, rfl⟩, ?_, hleft, ?_⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨Φ, -, hcd, hmem, hinv⟩ := hnhd w hw
    refine (hcd.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hmem] with v hv
    obtain ⟨h1, h2⟩ := hinv v hv
    rw [← h2, hleft _ h1, h2]
  · rintro _ ⟨w, hw, rfl⟩
    rw [hleft w hw]; exact hw
  · rintro _ ⟨w, hw, rfl⟩
    rw [hleft w hw]

end InverseFunction
/-! ### Coordinate expressions of holomorphic maps in arbitrary atlas charts -/

section Coordinates

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- A map holomorphic at one point has a holomorphic coordinate expression there, in any pair of
atlas charts containing the point and its image. -/
theorem contDiffAt_coordinateMap_of_contMDiffAt {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f x)
    (e : ComplexChart n X) (d : ComplexChart n Y) (hx : x ∈ e.val.source)
    (hfx : f x ∈ d.val.source) :
    ContDiffAt ℂ ∞ (coordinateMap f e d) (e.val x) := by
  have h := (contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas e.property)
    (IsManifold.subset_maximalAtlas d.property) hx hfx).mp hf
  simpa [coordinateMap, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, e.val.left_inv hx, contDiffWithinAt_univ] using h.2

/-- **Off the exceptional locus the coordinate expression has invertible derivative**, in any
pair of atlas charts: a local holomorphic section `s` of `π` (`exists_localInverse`) gives
`τ ∘ (e ∘ s ∘ d⁻¹) = id` near `τ w`, so `dτ_w` is onto, hence bijective. -/
theorem fderiv_coordinateMap_bijective {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (e : ComplexChart n Y) (d : ComplexChart n X) {w : ComplexModel n}
    (hw : w ∈ coordinateDomain π e d) (hexc : e.val.symm w ∉ exceptionalLocus n π) :
    Function.Bijective (fderiv ℂ (coordinateMap π e d) w) := by
  set y := e.val.symm w with hy
  set x := π y with hx
  obtain ⟨V, s, hV, hxV, hsx, hπs, hsmooth, -⟩ :=
    HolomorphicLocalInverse.exists_localInverse hπ hexc
  have hye : y ∈ e.val.source := e.val.map_target hw.1
  have hxd : x ∈ d.val.source := hw.2
  have hsxe : s x ∈ e.val.source := by rw [hsx]; exact hye
  set σ := coordinateMap s d e with hσ
  have hσd : ContDiffAt ℂ ∞ σ (d.val x) :=
    contDiffAt_coordinateMap_of_contMDiffAt (hsmooth x hxV) d e hxd hsxe
  have hσv : σ (d.val x) = w := by
    show e.val (s (d.val.symm (d.val x))) = w
    rw [d.val.left_inv hxd, hsx, hy, e.val.right_inv hw.1]
  have hτw : DifferentiableAt ℂ (coordinateMap π e d) w :=
    (coordinateMap_contDiffAt hπ e d hw).differentiableAt (by simp)
  -- `τ ∘ σ = id` near `d x`
  have hcont : ContinuousAt (fun v => s (d.val.symm v)) (d.val x) := by
    have h1 : ContinuousAt d.val.symm (d.val x) := d.val.continuousAt_symm (d.val.map_source hxd)
    have h2 : ContinuousAt s (d.val.symm (d.val x)) := by
      rw [d.val.left_inv hxd]; exact (hsmooth x hxV).continuousAt
    exact h2.comp h1
  have hinv : (coordinateMap π e d ∘ σ) =ᶠ[𝓝 (d.val x)] id := by
    have hsym : ContinuousAt d.val.symm (d.val x) := d.val.continuousAt_symm (d.val.map_source hxd)
    have hVn : ∀ᶠ v in 𝓝 (d.val x), d.val.symm v ∈ V := by
      apply hsym.eventually
      rw [d.val.left_inv hxd]; exact hV.mem_nhds hxV
    have hen : ∀ᶠ v in 𝓝 (d.val x), s (d.val.symm v) ∈ e.val.source := by
      have h3 : e.val.source ∈ 𝓝 (s (d.val.symm (d.val x))) := by
        rw [d.val.left_inv hxd]; exact e.val.open_source.mem_nhds hsxe
      exact hcont.eventually h3
    filter_upwards [hVn, hen, d.val.open_target.mem_nhds (d.val.map_source hxd)]
      with v hvV hve hvt
    show d.val (π (e.val.symm (e.val (s (d.val.symm v))))) = v
    rw [e.val.left_inv hve, hπs _ hvV, d.val.right_inv hvt]
  have hσdiff : DifferentiableAt ℂ σ (d.val x) := hσd.differentiableAt (by simp)
  have hcomp : (fderiv ℂ (coordinateMap π e d) w).comp (fderiv ℂ σ (d.val x)) =
      ContinuousLinearMap.id ℂ _ := by
    rw [← hσv] at hτw ⊢
    rw [← fderiv_comp (d.val x) hτw hσdiff, hinv.fderiv_eq, fderiv_id]
  have hsurj : Function.Surjective (fderiv ℂ (coordinateMap π e d) w) := fun v =>
    ⟨fderiv ℂ σ (d.val x) v, by
      simpa using congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L v) hcomp⟩
  set L : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (fderiv ℂ (coordinateMap π e d) w : ComplexModel n →L[ℂ] ComplexModel n).toLinearMap
  have hinj : Function.Injective L :=
    LinearMap.injective_iff_surjective (V := ComplexModel n) (f := L) |>.mpr hsurj
  exact ⟨hinj, hsurj⟩

end Coordinates

/-! ### The pulled-back patch -/

section PullbackPatch

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {π : Y → X}
  {θ : Fin n → ClosedRealOneOneForm n X} {u : Fin n → X → EReal}

/-- The pulled-back tuple of backgrounds `π^*θᵢ`. -/
abbrev pullbackTuple (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (θ : Fin n → ClosedRealOneOneForm n X) : Fin n → ClosedRealOneOneForm n Y :=
  fun i => ClosedRealOneOneForm.pullback hπ (θ i)

/-- **The pulled-back patch.**  For a patch `Q` of `(θ, u)` on `X` and an atlas chart `e` of `Y`:
the chart `e`, the coordinate domain `τ⁻¹(Q.domain)` (`τ = Q.chart ∘ π ∘ e⁻¹`), the potentials
`Q.potential ∘ τ`. -/
def pullbackPatch (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (Q : Patch θ u) (e : ComplexChart n Y) :
    Patch (pullbackTuple hπ θ) (fun i y => u i (π y)) where
  chart := e
  domain := ⟨LocalPotentialPullback.potentialDomain π e Q.chart Q.domain,
    LocalPotentialPullback.potentialDomain_isOpen hπ e Q.chart Q.domain.isOpen⟩
  domain_le_target := fun _ hw => hw.1.1
  potential i := Q.potential i ∘ coordinateMap π e Q.chart
  localPotential i :=
    LocalPotentialPullback.isSmoothLocalPotential_pullback hπ e (Q.localPotential i)
  plurisubharmonic i := by
    have hD := LocalPotentialPullback.potentialDomain_isOpen hπ e Q.chart Q.domain.isOpen
    have h := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hD
      (((coordinateMap_contDiffOn hπ e Q.chart).mono inter_subset_left).differentiableOn
        (by simp)) (fun _ hw => hw.2) (Q.plurisubharmonic i)
    intro w hw
    refine (h w hw).congr ?_
    filter_upwards [hD.mem_nhds hw] with w' hw'
    change u i (Q.chart.val.symm (Q.chart.val (π (e.val.symm w')))) + _ =
      u i (π (e.val.symm w')) + _
    rw [Q.chart.val.left_inv hw'.1.2]
    rfl

variable (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)

@[simp] theorem pullbackPatch_chart (Q : Patch θ u) (e : ComplexChart n Y) :
    (pullbackPatch hπ Q e).chart = e := rfl

theorem mem_pullbackPatch_domain {Q : Patch θ u} {e : ComplexChart n Y} {w : ComplexModel n} :
    w ∈ (pullbackPatch hπ Q e).domain ↔
      w ∈ LocalPotentialPullback.potentialDomain π e Q.chart Q.domain := Iff.rfl

/-- Points of the pulled-back domain lie over the source of `Q`. -/
theorem map_mem_source_of_mem_domain {Q : Patch θ u} {e : ComplexChart n Y} {w : ComplexModel n}
    (hw : w ∈ (pullbackPatch hπ Q e).domain) : π (e.val.symm w) ∈ Q.source :=
  ⟨hw.1.2, hw.2⟩

/-- The corrected potentials of the pulled-back patch are those of `Q` composed with `τ`. -/
theorem corrected_pullbackPatch {Q : Patch θ u} {e : ComplexChart n Y} (i : Fin n)
    {w : ComplexModel n} (hw : w ∈ (pullbackPatch hπ Q e).domain) :
    (pullbackPatch hπ Q e).corrected i w = Q.corrected i (coordinateMap π e Q.chart w) := by
  change u i (π (e.val.symm w)) + _ = u i (Q.chart.val.symm (Q.chart.val (π (e.val.symm w)))) + _
  rw [Q.chart.val.left_inv hw.1.2]
  rfl

/-- The source of the pulled-back patch is the part of `e.source` over `Q.source`. -/
theorem mem_pullbackPatch_source {Q : Patch θ u} {e : ComplexChart n Y} {y : Y} :
    y ∈ (pullbackPatch hπ Q e).source ↔ y ∈ e.val.source ∧ π y ∈ Q.source := by
  constructor
  · rintro ⟨hy, hw⟩
    have h : π (e.val.symm (e.val y)) ∈ Q.source := map_mem_source_of_mem_domain hπ hw
    rw [e.val.left_inv hy] at h
    exact ⟨hy, h⟩
  · rintro ⟨hy, hQ⟩
    refine ⟨hy, ⟨e.val.map_source hy, ?_⟩, ?_⟩
    · show π (e.val.symm (e.val y)) ∈ Q.chart.val.source
      rw [e.val.left_inv hy]; exact Q.source_subset hQ
    · show Q.chart.val (π (e.val.symm (e.val y))) ∈ Q.domain
      rw [e.val.left_inv hy]; exact hQ.2

end PullbackPatch
/-! ### Local-to-global equality of measures on an open set -/

section MeasureLocal

/-- Two measures that agree near every point of an open set `U` (on open neighbourhoods inside
`U`) agree on `U`: a countable subcover (second countability) and `restrict_iUnion_congr`. -/
theorem restrict_eq_of_locally_eq {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] {μ ν : Measure Y} {U : Set Y}
    (h : ∀ y ∈ U, ∃ S : Set Y, IsOpen S ∧ y ∈ S ∧ S ⊆ U ∧ μ.restrict S = ν.restrict S) :
    μ.restrict U = ν.restrict U := by
  classical
  choose S hS hyS hSU hμν using h
  set F : U → Set Y := fun y => S y.1 y.2 with hF
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable F (fun y => hS _ _)
  have : Countable T := hTc.to_subtype
  have hU : (⋃ i : T, F i) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => hSU _ _
    · intro y hy
      have hy' : y ∈ ⋃ i, F i := mem_iUnion.mpr ⟨⟨y, hy⟩, hyS y hy⟩
      rw [← hTU] at hy'
      obtain ⟨j, hjT, hj⟩ := mem_iUnion₂.mp hy'
      exact mem_iUnion.mpr ⟨⟨j, hjT⟩, hj⟩
  rw [← hU]
  exact Measure.restrict_iUnion_congr.mpr fun i => hμν _ _

end MeasureLocal

/-! ### The inverse of `π` over an isomorphism locus -/

section InverseOver

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [Nonempty Y] {π : Y → X} {N : Set X}

/-- The inverse of `π` over `N` (any value off `N`). -/
def invOver (π : Y → X) (N : Set X) : X → Y := Function.invFunOn π (π ⁻¹' N)

theorem invOver_mem (hiso : IsIsomorphismOver n π N) {x : X} (hx : x ∈ N) :
    invOver π N x ∈ π ⁻¹' N ∧ π (invOver π N x) = x :=
  Function.invFunOn_pos (hiso.1.surjOn hx)

theorem invOver_apply (hiso : IsIsomorphismOver n π N) {y : Y} (hy : y ∈ π ⁻¹' N) :
    invOver π N (π y) = y := by
  have h := invOver_mem hiso hy
  exact hiso.1.injOn h.1 hy h.2

/-- The inverse over `N` is continuous on `N`: near each point it is a local holomorphic section
of `π` (`exists_localInverse`, `π` is unramified over `N`). -/
theorem continuousOn_invOver (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hN : IsOpen N) (hiso : IsIsomorphismOver n π N) : ContinuousOn (invOver π N) N := by
  intro x hx
  obtain ⟨hyN, hyx⟩ := invOver_mem hiso hx
  have hexc : invOver π N x ∉ exceptionalLocus n π := fun h =>
    Set.disjoint_left.mp hiso.2 hyN h
  obtain ⟨V, s, hV, hxV, -, hπs, hsmooth, -⟩ :=
    HolomorphicLocalInverse.exists_localInverse hπ hexc
  rw [hyx] at hxV
  have heq : s =ᶠ[𝓝 x] invOver π N := by
    filter_upwards [hV.mem_nhds hxV, hN.mem_nhds hx] with x' hx'V hx'N
    have h1 : π (s x') = x' := hπs x' hx'V
    have h2 : s x' ∈ π ⁻¹' N := by rw [mem_preimage, h1]; exact hx'N
    calc s x' = invOver π N (π (s x')) := (invOver_apply hiso h2).symm
      _ = invOver π N x' := by rw [h1]
  exact ((hsmooth x hxV).continuousAt.congr heq).continuousWithinAt

end InverseOver

/-! ### Naturality of the global measure over an isomorphism locus -/

section Naturality

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [Nonempty Y] {π : Y → X}
  (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {N : Set X}
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {θ : Fin n → ClosedRealOneOneForm n X} {u : Fin n → X → EReal}

/-- **The coordinate measure of a pulled-back patch** is the pushforward, under the inverse of
`π`, of the coordinate measure of `Q` on the image of the source.  In coordinates this is the
holomorphic covariance of the truncation limit (`mixedTruncationLimitMeasure_comp_biholomorphic`)
for `τ = Q.chart ∘ π ∘ e⁻¹`, a biholomorphism of the pulled-back domain onto its image. -/
theorem patchMeasure_pullbackPatch (hN : IsOpen N) (hiso : IsIsomorphismOver n π N)
    (Q : Patch θ u) (hQN : (Q.source : Set X) ⊆ N) (e : ComplexChart n Y) :
    patchMeasure (pullbackPatch hπ Q e) =
      ((patchMeasure Q).restrict (π '' ((pullbackPatch hπ Q e).source : Set Y))).map
        (invOver π N) := by
  classical
  set P := pullbackPatch hπ Q e with hP
  set τ := coordinateMap π e Q.chart with hτdef
  have hAQ : ∀ w ∈ (P.domain : Set (ComplexModel n)), π (e.val.symm w) ∈ Q.source := fun w hw =>
    map_mem_source_of_mem_domain hπ hw
  have hAN : ∀ w ∈ (P.domain : Set (ComplexModel n)), e.val.symm w ∈ π ⁻¹' N := fun w hw =>
    hQN (hAQ w hw)
  have hτ : ContDiffOn ℂ ∞ τ P.domain :=
    (coordinateMap_contDiffOn hπ e Q.chart).mono fun w hw => hw.1
  have hinj : InjOn τ P.domain := by
    intro w₁ hw₁ w₂ hw₂ h
    have h1 : π (e.val.symm w₁) = π (e.val.symm w₂) :=
      Q.chart.val.injOn (Q.source_subset (hAQ w₁ hw₁)) (Q.source_subset (hAQ w₂ hw₂)) h
    have h2 : e.val.symm w₁ = e.val.symm w₂ := hiso.1.injOn (hAN w₁ hw₁) (hAN w₂ hw₂) h1
    exact e.val.symm.injOn hw₁.1.1 hw₂.1.1 h2
  have hder : ∀ w ∈ (P.domain : Set (ComplexModel n)), Function.Bijective (fderiv ℂ τ w) :=
    fun w hw => fderiv_coordinateMap_bijective hπ e Q.chart hw.1
      (fun h => Set.disjoint_left.mp hiso.2 (hAN w hw) h)
  obtain ⟨B, hB, hpair⟩ := exists_isBiholomorphicPair_image hτ hinj hder
  set σ := Function.invFunOn τ P.domain with hσ
  have hτA : ∀ w ∈ (P.domain : Set (ComplexModel n)), τ w ∈ B := fun w hw => by
    rw [← SetLike.mem_coe, hB]; exact ⟨w, hw, rfl⟩
  have hBQ : B ≤ Q.domain := by
    intro v hv
    rw [← SetLike.mem_coe, hB] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact hw.2
  -- `Q.chart⁻¹ v = π (e⁻¹ (σ v))` on `B`
  have hBsymm : ∀ v ∈ (B : Set (ComplexModel n)),
      Q.chart.val.symm v = π (e.val.symm (σ v)) := fun v hv => by
    have h1 : τ (σ v) = v := hpair.right_inv v hv
    have h2 : π (e.val.symm (σ v)) ∈ Q.chart.val.source :=
      Q.source_subset (hAQ _ (hpair.mapsTo_inv hv))
    calc Q.chart.val.symm v = Q.chart.val.symm (τ (σ v)) := by rw [h1]
      _ = π (e.val.symm (σ v)) := Q.chart.val.left_inv h2
  -- `π '' P.source` in coordinates
  have hchar : ∀ v ∈ (Q.domain : Set (ComplexModel n)),
      (Q.chart.val.symm v ∈ π '' (P.source : Set Y) ↔ v ∈ B) := by
    intro v hv
    constructor
    · rintro ⟨y, hyS, hyv⟩
      have hyS' := (mem_pullbackPatch_source hπ).mp hyS
      have hτe : τ (e.val y) = v := by
        show Q.chart.val (π (e.val.symm (e.val y))) = v
        rw [e.val.left_inv hyS'.1, hyv, Q.chart.val.right_inv (Q.domain_le_target hv)]
      rw [← hτe]
      exact hτA _ hyS.2
    · intro hvB
      refine ⟨e.val.symm (σ v), ?_, (hBsymm v hvB).symm⟩
      have hσA := hpair.mapsTo_inv hvB
      exact (mem_pullbackPatch_source hπ).mpr
        ⟨e.val.map_target hσA.1.1, by simpa using hAQ _ hσA⟩
  have hπS : π '' (P.source : Set Y) = Q.chart.val.source ∩ Q.chart.val ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyS, rfl⟩
      have hQ := ((mem_pullbackPatch_source hπ).mp hyS).2
      refine ⟨Q.source_subset hQ, ?_⟩
      have h := (hchar (Q.chart.val (π y)) hQ.2).mp
      rw [Q.chart.val.left_inv (Q.source_subset hQ)] at h
      exact h ⟨y, hyS, rfl⟩
    · rintro ⟨hxs, hxB⟩
      have h := (hchar (Q.chart.val x) (hBQ hxB)).mpr hxB
      rwa [Q.chart.val.left_inv hxs] at h
  have hπSm : MeasurableSet (π '' (P.source : Set Y)) := by
    rw [hπS]; exact (Q.chart.val.isOpen_inter_preimage B.isOpen).measurableSet
  have hπSQ : π '' (P.source : Set Y) ⊆ Q.source := by
    rintro _ ⟨y, hyS, rfl⟩; exact ((mem_pullbackPatch_source hπ).mp hyS).2
  -- the coordinate measure of `P`
  set μQ := mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic with hμQ
  have hvB : ∀ i, PlurisubharmonicOn (Q.corrected i) B := fun i =>
    (Q.plurisubharmonic i).mono hBQ
  have hvτ : ∀ i, PlurisubharmonicOn (fun w => Q.corrected i (τ w)) P.domain := fun i =>
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic P.domain.isOpen
      (hτ.differentiableOn (by simp)) (fun w hw => hBQ (hτA w hw)) (Q.plurisubharmonic i)
  have hμP : mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic =
      (μQ.restrict B).map σ := by
    refine (mixedTruncationLimitMeasure_congr P.plurisubharmonic hvτ
      (fun i w hw => corrected_pullbackPatch hπ i hw)).trans ?_
    rw [mixedTruncationLimitMeasure_comp_biholomorphic hpair hvB hvτ,
      Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (mixedTruncationLimitMeasure_compl hvB))]
    congr 1
    exact (mixedTruncationLimitMeasure_restrict_open hBQ Q.plurisubharmonic).symm
  ext T hT
  have hσm : AEMeasurable σ (μQ.restrict B) :=
    hpair.holo_inv.continuousOn.aemeasurable B.isOpen.measurableSet
  have hmeasA : MeasurableSet ((P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' T) :=
    PatchOverlap.measurableSet_inter_preimage
      (e.val.continuousOn_symm.mono P.domain_le_target) hT
  have hs'm : AEMeasurable (invOver π N) ((patchMeasure Q).restrict (π '' (P.source : Set Y))) :=
    ((continuousOn_invOver hπ hN hiso).mono fun x hx => hQN (hπSQ hx)).aemeasurable hπSm
  rw [show patchMeasure P = P.pushMeasure (mixedTruncationLimitMeasure P.domain P.corrected
      P.plurisubharmonic) from rfl, Patch.pushMeasure_apply, hμP,
    Measure.map_apply_of_aemeasurable hσm hmeasA, Measure.restrict_apply' B.isOpen.measurableSet,
    Measure.map_apply_of_aemeasurable hs'm hT, Measure.restrict_apply' hπSm,
    show patchMeasure Q = Q.pushMeasure μQ from rfl, Patch.pushMeasure_apply]
  congr 1
  ext v
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨⟨-, hσT⟩, hvB⟩
    refine ⟨hBQ hvB, ?_, (hchar v (hBQ hvB)).mpr hvB⟩
    rw [hBsymm v hvB, invOver_apply hiso (hAN _ (hpair.mapsTo_inv hvB))]
    exact hσT
  · rintro ⟨hvQ, hT', hvS⟩
    have hvB := (hchar v hvQ).mp hvS
    refine ⟨⟨hpair.mapsTo_inv hvB, ?_⟩, hvB⟩
    rw [hBsymm v hvB, invOver_apply hiso (hAN _ (hpair.mapsTo_inv hvB))] at hT'
    exact hT'

/-- **Naturality of the global non-pluripolar measure over an isomorphism locus.**  If `π` is an
isomorphism over the open set `N`, the global mixed measure of `(π^*θ, u ∘ π)` restricted to
`π⁻¹ N` is the pushforward of that of `(θ, u)` restricted to `N` under the inverse of `π` over
`N`.  Both sides are compared on the sources of pulled-back patches, which cover `π⁻¹ N`. -/
theorem globalMixedMeasure_restrict_preimage_eq_map [CompactSpace X] [CompactSpace Y]
    (hN : IsOpen N) (hiso : IsIsomorphismOver n π N)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hu' : ∀ i, ThetaPlurisubharmonic (pullbackTuple hπ θ i).val (fun y => u i (π y))) :
    (globalMixedMeasure (pullbackTuple hπ θ) (fun i y => u i (π y)) hu').restrict (π ⁻¹' N) =
      ((globalMixedMeasure θ u hu).restrict N).map (invOver π N) := by
  classical
  set μX := globalMixedMeasure θ u hu with hμX
  have hs'm : AEMeasurable (invOver π N) (μX.restrict N) :=
    (continuousOn_invOver hπ hN hiso).aemeasurable hN.measurableSet
  have hUm : MeasurableSet (π ⁻¹' N) := (hN.preimage hπ.continuous).measurableSet
  have hνU : ((μX.restrict N).map (invOver π N)).restrict (π ⁻¹' N) =
      (μX.restrict N).map (invOver π N) := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    change ((μX.restrict N).map (invOver π N)) ((π ⁻¹' N)ᶜ) = 0
    rw [Measure.map_apply_of_aemeasurable hs'm hUm.compl,
      Measure.restrict_apply' hN.measurableSet]
    have hempty : invOver π N ⁻¹' (π ⁻¹' N)ᶜ ∩ N = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro hx hxN
      exact hx (invOver_mem hiso hxN).1
    rw [hempty, measure_empty]
  rw [← hνU]
  apply restrict_eq_of_locally_eq
  intro y hy
  obtain ⟨Q₀, hQ₀⟩ := exists_patch_containing hu (π y)
  let D : Opens (ComplexModel n) := ⟨(Q₀.domain : Set (ComplexModel n)) ∩ Q₀.chart.val.symm ⁻¹' N,
    (Q₀.chart.val.continuousOn_symm.mono Q₀.domain_le_target).isOpen_inter_preimage
      Q₀.domain.isOpen hN⟩
  have hD : D ≤ Q₀.domain := fun _ hz => hz.1
  let Q := Q₀.restrict D hD
  have hQN : (Q.source : Set X) ⊆ N := by
    intro x hx
    have h := ((Patch.mem_source_restrict Q₀ D hD).mp hx)
    have h2 : Q₀.chart.val.symm (Q₀.chart.val x) ∈ N := h.2.2
    rwa [Q₀.chart.val.left_inv (Q₀.source_subset h.1)] at h2
  have hyQ : π y ∈ Q.source := (Patch.mem_source_restrict Q₀ D hD).mpr
    ⟨hQ₀, hQ₀.2, by
      show Q₀.chart.val.symm (Q₀.chart.val (π y)) ∈ N
      rw [Q₀.chart.val.left_inv (Q₀.source_subset hQ₀)]; exact hy⟩
  set e := complexChartAt (n := n) y
  set P := pullbackPatch hπ Q e with hP
  have hyP : y ∈ P.source :=
    (mem_pullbackPatch_source hπ).mpr ⟨mem_complexChartAt_source y, hyQ⟩
  have hPN : (P.source : Set Y) ⊆ π ⁻¹' N := fun y' hy' =>
    hQN ((mem_pullbackPatch_source hπ).mp hy').2
  refine ⟨P.source, P.source.isOpen, hyP, hPN, ?_⟩
  have hset : invOver π N ⁻¹' (P.source : Set Y) ∩ N = π '' (P.source : Set Y) := by
    ext x
    constructor
    · rintro ⟨hxP, hxN⟩
      exact ⟨_, hxP, (invOver_mem hiso hxN).2⟩
    · rintro ⟨y', hy'P, rfl⟩
      refine ⟨?_, hPN hy'P⟩
      rw [mem_preimage, invOver_apply hiso (hPN hy'P)]
      exact hy'P
  have hsub : π '' (P.source : Set Y) ⊆ Q.source := by
    rintro _ ⟨y', hy'P, rfl⟩
    exact ((mem_pullbackPatch_source hπ).mp hy'P).2
  rw [globalMixedMeasure_restrict_patch hu' P, patchMeasure_pullbackPatch hπ hN hiso Q hQN e,
    Measure.restrict_map_of_aemeasurable hs'm P.source.isOpen.measurableSet,
    Measure.restrict_restrict' hN.measurableSet, hset, ← globalMixedMeasure_restrict_patch hu Q,
    Measure.restrict_restrict_of_subset hsub]

end Naturality

/-! ### Mass invariance under one blowup -/

section Blowup

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- **Xia Hironaka Prop 2.4.2 for one blowup.**  The total global mixed non-pluripolar mass of
`(π^*θ, u ∘ π)` equals that of `(θ, u)`: the centre `C` and its preimage are analytic with empty
interior, hence pluripolar and not charged, and over `X \ C` the blowup is an isomorphism
(naturality). -/
theorem globalMixedMeasure_univ_pullback_of_isBlowupAlong [CompactSpace X] [CompactSpace Y]
    {C : Set X}
    {π : Y → X} (hπ : IsBlowupAlong n C π) {θ : Fin n → ClosedRealOneOneForm n X}
    {u : Fin n → X → EReal} (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hu' : ∀ i, ThetaPlurisubharmonic (pullbackTuple hπ.contMDiff θ i).val
      (fun y => u i (π y))) :
    globalMixedMeasure (pullbackTuple hπ.contMDiff θ) (fun i y => u i (π y)) hu' univ =
      globalMixedMeasure θ u hu univ := by
  classical
  have hseq : IsBlowupSequence n X Y (id ∘ π) :=
    IsBlowupSequence.step id C π IsBlowupSequence.refl hπ
  have hsurj : Function.Surjective π :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hseq).2
  rcases isEmpty_or_nonempty Y with hY | hY
  · have : IsEmpty X := ⟨fun x => by obtain ⟨y, -⟩ := hsurj x; exact hY.false y⟩
    rw [Set.univ_eq_empty_iff.mpr hY, Set.univ_eq_empty_iff.mpr ‹IsEmpty X›, measure_empty,
      measure_empty]
  set N : Set X := Cᶜ with hNdef
  have hN : IsOpen N := hπ.1.1.isOpen_compl
  have hiso : IsIsomorphismOver n π N :=
    BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  set μY := globalMixedMeasure (pullbackTuple hπ.contMDiff θ) (fun i y => u i (π y)) hu'
    with hμY
  set μX := globalMixedMeasure θ u hu with hμX
  have hCan : IsComplexAnalyticSubset (n := n) C :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
  have hCpol : ManifoldLocallyPluripolar (n := n) C :=
    manifoldLocallyPluripolar_of_isComplexAnalyticSubset hCan hπ.2.1
  have hEpol : ManifoldLocallyPluripolar (n := n) (π ⁻¹' C) :=
    manifoldLocallyPluripolar_of_isComplexAnalyticSubset
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hCan)
      (ExceptionalFibres.interior_preimage_eq_empty hπ)
  have hX0 : μX C = 0 := globalMixedMeasure_doesNotChargeManifoldPluripolar hu C hCpol
  have hY0 : μY (π ⁻¹' C) = 0 :=
    globalMixedMeasure_doesNotChargeManifoldPluripolar hu' _ hEpol
  have h1 : μY univ = μY (π ⁻¹' N) := by
    refine le_antisymm ?_ (measure_mono (subset_univ _))
    calc μY univ ≤ μY (π ⁻¹' N ∪ π ⁻¹' C) := measure_mono fun y _ => by
            by_cases h : π y ∈ C
            · exact Or.inr h
            · exact Or.inl h
      _ ≤ μY (π ⁻¹' N) + μY (π ⁻¹' C) := measure_union_le _ _
      _ = μY (π ⁻¹' N) := by rw [hY0, add_zero]
  have h2 : μX univ = μX N := by
    refine le_antisymm ?_ (measure_mono (subset_univ _))
    calc μX univ ≤ μX (N ∪ C) := measure_mono fun x _ => by
            by_cases h : x ∈ C
            · exact Or.inr h
            · exact Or.inl h
      _ ≤ μX N + μX C := measure_union_le _ _
      _ = μX N := by rw [hX0, add_zero]
  have hs'm : AEMeasurable (invOver π N) (μX.restrict N) :=
    (continuousOn_invOver hπ.contMDiff hN hiso).aemeasurable hN.measurableSet
  have h3 : μY (π ⁻¹' N) = μX N := by
    have h : (μY.restrict (π ⁻¹' N)) univ = ((μX.restrict N).map (invOver π N)) univ := by
      rw [globalMixedMeasure_restrict_preimage_eq_map hπ.contMDiff hN hiso hu hu']
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.map_apply_of_aemeasurable hs'm MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter] at h
    exact h
  rw [h1, h3, h2]

/-- **Diagonal form, one blowup**: `∫_Y (π^*θ)_{u∘π}^n = ∫_X θ_u^n`. -/
theorem diagonalPotentialMass_pullback_of_isBlowupAlong [CompactSpace X] [CompactSpace Y]
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (θ : ClosedRealOneOneForm n X)
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hu' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ).val
      (fun y => u (π y))) :
    DiagonalMass.diagonalPotentialMass (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
        (fun y => u (π y)) hu' = DiagonalMass.diagonalPotentialMass θ u hu :=
  globalMixedMeasure_univ_pullback_of_isBlowupAlong hπ (θ := fun _ => θ) (u := fun _ => u)
    (fun _ => hu.1) (fun _ => hu'.1)

end Blowup

/-! ### Geometric equality of backgrounds -/

section Geometric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The global mixed measure only sees the coefficients of the backgrounds on chart targets:
geometrically equal tuples give the same measure (every patch of one is a patch of the other). -/
theorem globalMixedMeasure_congr_geometricallyEq {θ θ' : Fin n → ClosedRealOneOneForm n M}
    (hθ : ∀ i, (θ i).val.GeometricallyEq (θ' i).val) {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hu' : ∀ i, ThetaPlurisubharmonic (θ' i).val (u i)) :
    globalMixedMeasure θ u hu = globalMixedMeasure θ' u hu' := by
  refine globalMixedMeasure_unique hu' _ fun P => ?_
  let P₀ : Patch θ u :=
    { P with
      localPotential := fun i =>
        ⟨(P.localPotential i).1, (P.localPotential i).2.1, (P.localPotential i).2.2.1,
          fun z hz => ((P.localPotential i).2.2.2 hz).trans
            (hθ i P.chart ((P.localPotential i).2.1 hz)).symm⟩ }
  exact globalMixedMeasure_restrict_patch hu P₀

/-- The diagonal mass only depends on the background up to geometric equality. -/
theorem diagonalPotentialMass_congr_geometricallyEq {θ θ' : ClosedRealOneOneForm n M}
    (h : θ.val.GeometricallyEq θ'.val) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hu' : IsThetaPshPotential θ'.val u) :
    DiagonalMass.diagonalPotentialMass θ u hu = DiagonalMass.diagonalPotentialMass θ' u hu' :=
  congrArg (fun μ : Measure M => μ univ)
    (globalMixedMeasure_congr_geometricallyEq (θ := fun _ => θ) (θ' := fun _ => θ')
      (fun _ => h) (u := fun _ => u) (fun _ => hu.1) (fun _ => hu'.1))

end Geometric

/-! ### Mass invariance under blowup sequences -/

section Sequence

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [mX : MeasurableSpace X] [bX : BorelSpace X] [CompactSpace X]

/-- **Xia Hironaka Prop 2.4.2 (diagonal case) for blowup sequences**:
`∫_Y (π^*θ)_{u∘π}^n = ∫_X θ_u^n`, for any Borel structure on `Y`.  Induction over the sequence,
with `(f ∘ g)^*θ = g^*(f^*θ)` up to geometric equality. -/
theorem diagonalPotentialMass_pullback_of_isBlowupSequence {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {π : Y → X}
    (hπ : IsBlowupSequence n X Y π) (θ : ClosedRealOneOneForm n X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    ∀ [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
      (hu' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ).val
        (fun y => u (π y))),
      DiagonalMass.diagonalPotentialMass (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
        (fun y => u (π y)) hu' = DiagonalMass.diagonalPotentialMass θ u hu := by
  induction hπ with
  | refl =>
      intro mY bY cY hu'
      have hm : mY = mX := bY.measurable_eq.trans bX.measurable_eq.symm
      subst hm
      exact diagonalPotentialMass_congr_geometricallyEq
        (SmoothRealForm.pullback_id_geometricallyEq θ.val) hu' hu
  | @step Y' Z' _ _ _ _ _ _ f C g hf hg ih =>
      intro mZ bZ cZ hu'
      let : MeasurableSpace Y' := borel Y'
      have : BorelSpace Y' := ⟨rfl⟩
      have hYc := StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hf
      have : CompactSpace Y' := hYc.1
      have hgseq := IsBlowupSequence.step id C g IsBlowupSequence.refl hg
      have hgsurj : Function.Surjective g :=
        (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hgseq).2
      have hv : IsThetaPshPotential (ClosedRealOneOneForm.pullback hf.contMDiff θ).val
          (fun y => u (f y)) := by
        refine ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hf.contMDiff hu.1, ?_⟩
        intro y U hU hyU
        obtain ⟨z, hz⟩ := hgsurj y
        obtain ⟨z', hz'U, hz'⟩ := hu'.2 z (g ⁻¹' U) (hU.preimage hg.contMDiff.continuous)
          (by rw [mem_preimage, hz]; exact hyU)
        exact ⟨g z', hz'U, hz'⟩
      have hv' : IsThetaPshPotential
          (ClosedRealOneOneForm.pullback hg.contMDiff
            (ClosedRealOneOneForm.pullback hf.contMDiff θ)).val (fun z => u (f (g z))) :=
        ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.contMDiff hv.1, hu'.2⟩
      calc DiagonalMass.diagonalPotentialMass _ _ hu'
          = DiagonalMass.diagonalPotentialMass
              (ClosedRealOneOneForm.pullback hg.contMDiff
                (ClosedRealOneOneForm.pullback hf.contMDiff θ)) (fun z => u (f (g z))) hv' :=
            diagonalPotentialMass_congr_geometricallyEq
              (SmoothRealForm.pullback_comp_geometricallyEq hf.contMDiff hg.contMDiff θ.val) hu' hv'
        _ = DiagonalMass.diagonalPotentialMass (ClosedRealOneOneForm.pullback hf.contMDiff θ)
              (fun y => u (f y)) hv :=
            diagonalPotentialMass_pullback_of_isBlowupAlong hg _ hv hv'
        _ = DiagonalMass.diagonalPotentialMass θ u hu := ih hv

end Sequence



end

end Hironaka.ModificationMassInvariance
