import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.ClosedFormPullback
import Hironaka.Analytic.LocalPotentialPullback
import Hironaka.Resolution.StrictTransformComposition

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Operations on metered effective `ℚ`-divisors

* `zero`: the zero divisor with the trivial metric; its support is empty.
* `add`: the sum `E + E'`, with weight `φ_E + φ_E'` and curvature `Θ_E + Θ_E'`; its support is
  contained in `supp E ∪ supp E'`.
* `pullback`: the pullback `g^* E` along a holomorphic map `g` whose exceptional locus has empty
  interior, with weight `φ_E ∘ g` and curvature `g^* Θ_E`; its support is `g⁻¹ (supp E)`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MeteredDivisorOperations

open Hironaka.HolomorphicIdealSheaves Hironaka.NumericalRestrictedVolumeScaffold
  Hironaka.BlowupSequences Hironaka.HolomorphicMaps Hironaka.LocalPotentialPullback

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable (n M) in
/-- The zero divisor with the trivial metric. -/
def zero : MeteredEffectiveQDivisor n M where
  weight := fun _ => 0
  curvature := 0
  local_presentation := fun x => by
    refine ⟨univ, isOpen_univ, mem_univ x, 0, Fin.elim0, Fin.elim0, fun _ => 0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun e => contDiffOn_const,
      fun y _ => by simp, fun e z _ _ => by simp⟩

theorem zero_support : (zero n M).support = ∅ := by
  ext x
  simp [MeteredEffectiveQDivisor.support, zero]

/-- The sum of two metered effective `ℚ`-divisors. -/
def add (E E' : MeteredEffectiveQDivisor n M) : MeteredEffectiveQDivisor n M where
  weight := fun y => E.weight y + E'.weight y
  curvature := E.curvature + E'.curvature
  local_presentation := fun x => by
    obtain ⟨U, hU, hxU, N, a, g, h, ha, hg, hne, hh, hw, hc⟩ := E.local_presentation x
    obtain ⟨U', hU', hxU', N', a', g', h', ha', hg', hne', hh', hw', hc'⟩ :=
      E'.local_presentation x
    refine ⟨U ∩ U', hU.inter hU', ⟨hxU, hxU'⟩, N + N', Fin.append a a', Fin.append g g',
      fun y => h y + h' y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [ha, ha']
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using (hg i).mono inter_subset_left
      · simpa using (hg' i).mono inter_subset_right
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · intro W hW hWU hWne
        simpa using hne i W hW (hWU.trans inter_subset_left) hWne
      · intro W hW hWU hWne
        simpa using hne' i W hW (hWU.trans inter_subset_right) hWne
    · intro e
      exact ((hh e).mono fun z hz => ⟨hz.1, hz.2.1⟩).add
        ((hh' e).mono fun z hz => ⟨hz.1, hz.2.2⟩)
    · intro y hy
      rw [hw y hy.1, hw' y hy.2, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, EReal.coe_add]
      abel
    · intro e z hz hzU
      have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (U ∩ U')) :=
        e.val.isOpen_inter_preimage_symm (hU.inter hU')
      rw [ClosedRealOneOneForm.coeff_add, hc e z hz hzU.1, hc' e z hz hzU.2,
        smoothDDC_add hS ((hh e).mono fun z hz => ⟨hz.1, hz.2.1⟩)
          ((hh' e).mono fun z hz => ⟨hz.1, hz.2.2⟩) ⟨hz, hzU⟩, neg_add]

theorem add_support_subset (E E' : MeteredEffectiveQDivisor n M) :
    (add E E').support ⊆ E.support ∪ E'.support := by
  intro y hy
  simpa [MeteredEffectiveQDivisor.support, add, EReal.add_eq_bot_iff] using hy

variable {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- A function chart-smooth on `U` composes with a holomorphic map to one chart-smooth on
`g⁻¹ U`. -/
theorem contDiffOn_comp_chart_symm {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {U : Set M} (hU : IsOpen U)
    {h : M → ℝ} (hh : ∀ d : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (d.val.symm z)) (d.val.target ∩ d.val.symm ⁻¹' U))
    (e : ComplexChart n Z) :
    ContDiffOn ℝ ∞ (fun z => h (g (e.val.symm z))) (e.val.target ∩ e.val.symm ⁻¹' (g ⁻¹' U)) := by
  intro u hu
  let d := complexChartAt (n := n) (g (e.val.symm u))
  have hud : u ∈ coordinateDomain g e d := ⟨hu.1, mem_complexChartAt_source _⟩
  have hW : IsOpen (potentialDomain g e d (d.val.target ∩ d.val.symm ⁻¹' U)) :=
    potentialDomain_isOpen hg e d (d.val.isOpen_inter_preimage_symm hU)
  have hmem : u ∈ potentialDomain g e d (d.val.target ∩ d.val.symm ⁻¹' U) := by
    refine ⟨hud, coordinateMap_mem_target hud, ?_⟩
    change d.val.symm (d.val (g (e.val.symm u))) ∈ U
    rw [d.val.left_inv hud.2]
    exact hu.2
  have hcomp := (hh d).comp_inter (coordinateMap_contDiffOn_real hg e d)
  refine ((hcomp.contDiffAt (hW.mem_nhds hmem)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(coordinateDomain_isOpen hg e d).mem_nhds hud] with w hw
  change h (g (e.val.symm w)) = h (d.val.symm (d.val (g (e.val.symm w))))
  rw [d.val.left_inv hw.2]

/-- The coefficients of `g^* θ` for a form with local potentials `-h` on `U`. -/
theorem coeff_pullback_eq_neg_smoothDDC {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {θ : ClosedRealOneOneForm n M} {U : Set M} (hU : IsOpen U) {h : M → ℝ}
    (hh : ∀ d : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (d.val.symm z)) (d.val.target ∩ d.val.symm ⁻¹' U))
    (hc : ∀ (d : ComplexChart n M) (z : ComplexModel n), z ∈ d.val.target →
      d.val.symm z ∈ U → θ.val.coeff d z = -smoothDDC (fun y => h (d.val.symm y)) z)
    (e : ComplexChart n Z) {u : ComplexModel n} (hu : u ∈ e.val.target)
    (huU : e.val.symm u ∈ g ⁻¹' U) :
    (ClosedRealOneOneForm.pullback hg θ).val.coeff e u =
      -smoothDDC (fun y => h (g (e.val.symm y))) u := by
  let d := complexChartAt (n := n) (g (e.val.symm u))
  have hud : u ∈ coordinateDomain g e d := ⟨hu, mem_complexChartAt_source _⟩
  have hWo : IsOpen (d.val.target ∩ d.val.symm ⁻¹' U) := d.val.isOpen_inter_preimage_symm hU
  have hρ : IsSmoothLocalPotential θ.val d (d.val.target ∩ d.val.symm ⁻¹' U)
      (fun z => -h (d.val.symm z)) := by
    refine ⟨hWo, inter_subset_left, (hh d).neg, fun z hz => ?_⟩
    rw [hc d z hz.1 hz.2, smoothDDC_neg hWo (hh d) hz]
  have hmem : u ∈ potentialDomain g e d (d.val.target ∩ d.val.symm ⁻¹' U) := by
    refine ⟨hud, coordinateMap_mem_target hud, ?_⟩
    change d.val.symm (d.val (g (e.val.symm u))) ∈ U
    rw [d.val.left_inv hud.2]
    exact huU
  have hpot := (isSmoothLocalPotential_pullback hg e hρ).2.2.2 hmem
  rw [ClosedRealOneOneForm.pullback_val, ← hpot]
  have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (g ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (hU.preimage hg.continuous)
  rw [← smoothDDC_neg hS (contDiffOn_comp_chart_symm hg hU hh e) ⟨hu, huU⟩]
  apply smoothDDC_congr
  filter_upwards [(coordinateDomain_isOpen hg e d).mem_nhds hud] with w hw
  change -h (d.val.symm (d.val (g (e.val.symm w)))) = -h (g (e.val.symm w))
  rw [d.val.left_inv hw.2]

/-- A function vanishing on no nonempty open subset of `U` composes with a holomorphic map whose
exceptional locus has empty interior to one vanishing on no nonempty open subset of `g⁻¹ U`. -/
theorem exists_ne_zero_comp {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅) {U : Set M} {f : M → ℂ}
    (hf : ∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, f y ≠ 0)
    {W : Set Z} (hW : IsOpen W) (hWU : W ⊆ g ⁻¹' U) (hne : W.Nonempty) :
    ∃ z ∈ W, f (g z) ≠ 0 := by
  have hnot : ¬ W ⊆ exceptionalLocus n g := fun hsub => by
    obtain ⟨z, hz⟩ := hne
    have := interior_maximal hsub hW hz
    rw [hint] at this
    exact this
  obtain ⟨z₀, hz₀W, hz₀E⟩ := not_subset.mp hnot
  have himg : g '' W ∈ 𝓝 (g z₀) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hg hz₀E]
    exact image_mem_map (hW.mem_nhds hz₀W)
  obtain ⟨y, hyi, hy⟩ := hf (interior (g '' W)) isOpen_interior
    (interior_subset.trans (image_subset_iff.mpr hWU)) ⟨_, mem_interior_iff_mem_nhds.mpr himg⟩
  obtain ⟨z, hzW, rfl⟩ := interior_subset hyi
  exact ⟨z, hzW, hy⟩

/-- **The pullback** `g^* E` along a holomorphic map whose exceptional locus has empty interior. -/
def pullback {g : Z → M} (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅) (E : MeteredEffectiveQDivisor n M) :
    MeteredEffectiveQDivisor n Z where
  weight := fun z => E.weight (g z)
  curvature := ClosedRealOneOneForm.pullback hg E.curvature
  local_presentation := fun z => by
    obtain ⟨U, hU, hzU, N, a, f, h, ha, hf, hne, hh, hw, hc⟩ := E.local_presentation (g z)
    refine ⟨g ⁻¹' U, hU.preimage hg.continuous, hzU, N, a, fun i => f i ∘ g, fun y => h (g y),
      ha, ?_, ?_, fun e => contDiffOn_comp_chart_symm hg hU hh e, fun y hy => hw (g y) hy,
      fun e u hu huU => coeff_pullback_eq_neg_smoothDDC hg hU hh hc e hu huU⟩
    · intro i y hy
      exact ((hf i (g y) hy).mdifferentiableAt (hU.mem_nhds hy)).comp_mdifferentiableWithinAt y
        ((hg y).mdifferentiableAt (by simp)).mdifferentiableWithinAt
    · intro i W hW hWU hWne
      exact exists_ne_zero_comp hg hint (hne i) hW hWU hWne

theorem pullback_support {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅) (E : MeteredEffectiveQDivisor n M) :
    (pullback hg hint E).support = g ⁻¹' E.support := rfl

end

end Hironaka.MeteredDivisorOperations
