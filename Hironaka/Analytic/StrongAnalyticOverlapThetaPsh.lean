import Hironaka.Analytic.StrongAnalyticOverlapGluing
import Hironaka.Analytic.PotentialTheory.AnalyticSingularities
import Hironaka.Analytic.NumericalRestrictedVolumeScaffold

set_option autoImplicit false

/-!
# Curvature bridge for overlap log sums

`StrongAnalyticOverlapGluing` replaces an ordinary maximum by a single
logarithmic weight with a smooth remainder, but bounded singularity
equivalence alone gives no plurisubharmonicity.  This module records the exact
additional structure under which the replacement *does* preserve the
theta-PSH condition: in every chart it must use one actual local potential
`ρ` of `θ`, and the potential being glued must be exactly
`c log(Σ |fᵢ|² + Σ |gⱼ|²) - ρ` near the chart point.

The conclusion is both global theta-plurisubharmonicity and CT22 strong
analytic singularities.  The hypothesis is an explicit finite holomorphic
log-sum presentation, not an assumed theta-PSH conclusion; it is the concrete
overlap datum that a global Bergman construction must provide.
-/

open Filter
open scoped Topology ContDiff

namespace Hironaka.StrongAnalyticOverlapThetaPsh


open Hironaka.NumericalRestrictedVolumeScaffold
open DemaillyAnalyticType
open StrongAnalyticOverlapGluing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A local finite-generator log-sum presentation relative to an actual local
potential of `θ`.  The shared `-ρ` remainder is the condition that makes the
concatenated logarithmic weight theta-PSH; arbitrary smooth remainders do not
have this consequence. -/
def HasLocalSmoothLogSumPresentations (θ : SmoothRealForm n M 2) (w : M → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ)
      (p q : ℕ) (c : ℝ) (f : Fin p → ComplexModel n → ℂ)
      (g : Fin q → ComplexModel n → ℂ),
      z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧ 0 < c ∧
        (∀ i, DifferentiableOn ℂ (f i) W) ∧
        (∀ j, DifferentiableOn ℂ (g j) W) ∧
        ∀ y ∈ W, chartFunction w e y =
          smoothLogSum c f g (fun t => -ρ t) y

/-- An exact local log-sum presentation relative to a common local potential
is theta-PSH.  The proof uses the established PSH theorem for a positive
multiple of `log Σ |fᵢ|²`, after the `-ρ + ρ` cancellation. -/
theorem thetaPlurisubharmonic_of_localSmoothLogSumPresentations
    {θ : SmoothRealForm n M 2} {w : M → EReal}
    (h : HasLocalSmoothLogSumPresentations θ w) :
    ThetaPlurisubharmonic θ w := by
  intro e z hz
  obtain ⟨W, ρ, p, q, c, f, g, hzW, hρ, hc, hf, hg, hrep⟩ := h e z hz
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  intro y hy
  have hfg : HolomorphicGeneratorsAt (Fin.append f g) y :=
    HolomorphicGeneratorsAt.append ⟨W, hρ.1, hy, hf⟩ ⟨W, hρ.1, hy, hg⟩
  have hpsh : PlurisubharmonicAt
      (fun t => (c : EReal) * generatorLog (Fin.append f g) t) y :=
    plurisubharmonicAt_scaled_generatorLog hfg hc
  apply hpsh.congr
  filter_upwards [hρ.1.mem_nhds hy] with t ht
  rw [hrep t ht]
  simp only [smoothLogSum, EReal.coe_neg]
  rw [← sub_eq_add_neg, EReal.sub_add_cancel]

/-- The same exact common-potential log-sum presentations supply CT22 strong
analytic singularities without any core-separation condition. -/
theorem hasManifoldSmoothAnalyticSingularities_of_localSmoothLogSumPresentations
    {θ : SmoothRealForm n M 2} {w : M → EReal}
    (h : HasLocalSmoothLogSumPresentations θ w) :
    HasManifoldSmoothAnalyticSingularities (n := n) w := by
  intro e z hz
  obtain ⟨W, ρ, p, q, c, f, g, hzW, hρ, hc, hf, hg, hrep⟩ := h e z hz
  refine ⟨c, p + q, Fin.append f g, ?_⟩
  refine ⟨hc, HolomorphicGeneratorsAt.append ⟨W, hρ.1, hzW, hf⟩
    ⟨W, hρ.1, hzW, hg⟩, fun t => -ρ t, ?_, ?_⟩
  · filter_upwards [hρ.1.mem_nhds hzW] with t ht
    exact (hρ.2.2.1 t ht).contDiffAt (hρ.1.mem_nhds ht) |>.neg
  · filter_upwards [hρ.1.mem_nhds hzW] with t ht
    simpa only [smoothLogSum, Pi.neg_apply] using hrep t ht

/-- The explicit common-local-potential data simultaneously gives the
curvature and strong-analytic-singularity clauses needed by a Demailly
regularization candidate. -/
theorem thetaPsh_and_strongAnalytic_of_localSmoothLogSumPresentations
    {θ : SmoothRealForm n M 2} {w : M → EReal}
    (h : HasLocalSmoothLogSumPresentations θ w) :
    ThetaPlurisubharmonic θ w ∧ HasManifoldSmoothAnalyticSingularities (n := n) w :=
  ⟨thetaPlurisubharmonic_of_localSmoothLogSumPresentations h,
    hasManifoldSmoothAnalyticSingularities_of_localSmoothLogSumPresentations h⟩

end

end Hironaka.StrongAnalyticOverlapThetaPsh
