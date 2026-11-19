import Hironaka.Analytic.StrongAnalyticOverlapThetaPsh
import Hironaka.Analytic.LocalBergmanThetaBranch
import Hironaka.Analytic.UniformLocalBergmanFiniteAtlas

set_option autoImplicit false

/-!
# Exact log-sum presentations carried by finite Bergman patches

The overlap bridge in `StrongAnalyticOverlapThetaPsh` needs an *exact*
presentation by a logarithmic sum minus one local potential.  A local Bergman
patch provides such a presentation on its source in every ambient chart: its
finite generator family is transported through the chart transition and the
second log-sum family is empty.  This is an equality of potentials, so it also
records the curvature datum needed by the theta-PSH bridge.

The final theorem gives a usable finite-atlas subclass.  If a global function
agrees, on every source in a finite Bergman atlas, with that source's actual
Bergman branch, then it has the common-potential local log-sum presentations.
The branch-agreement hypothesis is deliberately exact; bounded equivalence or
an ordinary maximum is insufficient for the theta-PSH conclusion.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.LocalBergmanSmoothLogSum


open Hironaka.AnalyticGluingData
open Hironaka.HolomorphicMaps
open Hironaka.LocalPotentialPullback
open Hironaka.NumericalRestrictedVolumeScaffold
open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open StrongAnalyticOverlapGluing
open StrongAnalyticOverlapThetaPsh

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- One actual Bergman branch has an exact common-local-potential log-sum
presentation in every ambient chart meeting its source.  The second finite
family has no generators; `smoothLogSum_append_empty` identifies the result
with the transported Bergman generator logarithm. -/
theorem exists_localSmoothLogSumPresentation_bergmanBranch
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (hm : 0 < m)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzsource : e.val.symm z ∈ D.source) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ)
      (p q : ℕ) (c : ℝ) (f : Fin p → ComplexModel n → ℂ)
      (g : Fin q → ComplexModel n → ℂ),
      z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧ 0 < c ∧
        (∀ i, DifferentiableOn ℂ (f i) W) ∧
        (∀ j, DifferentiableOn ℂ (g j) W) ∧
        (∀ y ∈ W, e.val.symm y ∈ D.source) ∧
        ∀ y ∈ W, chartFunction (bergmanBranch D) e y =
          smoothLogSum c f g (fun t => -ρ t) y := by
  let hid : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (id : M → M) := contMDiff_id
  let F : ComplexModel n → ComplexModel n := coordinateMap (id : M → M) e D.chart
  let W : Set (ComplexModel n) := potentialDomain (id : M → M) e D.chart D.domain
  let ρ : ComplexModel n → ℝ := D.potential ∘ F
  let f : Fin D.N → ComplexModel n → ℂ := fun i y => D.generator i (F y)
  let g : Fin 0 → ComplexModel n → ℂ := fun i => i.elim0
  have hW : IsOpen W := potentialDomain_isOpen hid e D.chart D.domain.isOpen
  have hzW : z ∈ W := by
    constructor
    · change z ∈ e.val.target ∧ e.val.symm z ∈ D.chart.val.source
      exact ⟨hz, hzsource.1⟩
    · change D.chart.val (e.val.symm z) ∈ D.domain
      exact hzsource.2
  have hρpull : IsSmoothLocalPotential (SmoothRealForm.pullback hid θ) e W ρ :=
    isSmoothLocalPotential_pullback hid e D.localPotential
  have hρ : IsSmoothLocalPotential θ e W ρ :=
    (SmoothRealForm.pullback_id_geometricallyEq θ).localPotential_iff e W ρ |>.mp hρpull
  have hdiff : DifferentiableOn ℂ F W :=
    ((coordinateMap_contDiffOn hid e D.chart).differentiableOn (by simp)).mono inter_subset_left
  have hf : ∀ i, DifferentiableOn ℂ (f i) W := by
    intro i
    exact (D.generator_analytic i).differentiableOn.comp hdiff (fun y hy => hy.2)
  have hg : ∀ j, DifferentiableOn ℂ (g j) W := by
    intro j
    exact j.elim0
  refine ⟨W, ρ, D.N, 0, (m : ℝ)⁻¹, f, g, hzW, hρ,
    inv_pos.mpr (Nat.cast_pos.mpr hm), hf, hg, ?_, ?_⟩
  · intro y hy
    exact ⟨hy.1.2, hy.2⟩
  intro y hy
  have hysource : e.val.symm y ∈ D.source := by
    constructor
    · exact hy.1.2
    · exact hy.2
  change bergmanBranch D (e.val.symm y) =
    smoothLogSum ((m : ℝ)⁻¹) f g (fun t => -ρ t) y
  rw [bergmanBranch, dif_pos hysource]
  change (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator (F y) -
      (D.potential (F y) : EReal) =
    smoothLogSum ((m : ℝ)⁻¹) f g (fun t => -ρ t) y
  rw [StrongAnalyticOverlapGluing.smoothLogSum_append_empty]
  change (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator (F y) -
      (D.potential (F y) : EReal) =
    (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator (F y) +
      ((-D.potential (F y) : ℝ) : EReal)
  rw [sub_eq_add_neg, ← EReal.coe_neg]

/-- A finite atlas with exact branch agreement supplies the local data of the
common-potential overlap bridge.  This is a genuine finite-atlas subclass:
the required generators and potentials are those already carried by `A`, not
new abstract presentation data. -/
theorem hasLocalSmoothLogSumPresentations_of_finiteAtlasBranchAgreement
    {θ : SmoothRealForm n M 2} {u w : M → EReal} {m : ℕ}
    (A : FiniteLocalBergmanAtlas θ u m) (hm : 0 < m)
    (hagree : ∀ i (x : M), x ∈ (A.patch i).source →
      w x = bergmanBranch (A.patch i) x) :
    HasLocalSmoothLogSumPresentations θ w := by
  intro e z hz
  obtain ⟨i, hiz⟩ := A.covers (e.val.symm z)
  obtain ⟨W, ρ, p, q, c, f, g, hzW, hρ, hc, hf, hg, hWsource, hrep⟩ :=
    exists_localSmoothLogSumPresentation_bergmanBranch (A.patch i) hm e hz hiz
  refine ⟨W, ρ, p, q, c, f, g, hzW, hρ, hc, hf, hg, ?_⟩
  intro y hy
  have hysource : e.val.symm y ∈ (A.patch i).source := hWsource y hy
  change w (e.val.symm y) = smoothLogSum c f g (fun t => -ρ t) y
  rw [hagree i (e.val.symm y) hysource]
  exact hrep y hy

/-- Forgetting the auxiliary uniform estimates turns a finite uniform Bergman
atlas into the finite generator atlas used by the exact log-sum construction.
The conversion retains every chart, local potential, and generator family. -/
def finiteUniformLocalBergmanAtlas_toFiniteLocalBergmanAtlas
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) : FiniteLocalBergmanAtlas θ u m where
  count := A.count
  patch := fun i => (A.patch i).patch
  covers := A.covers

/-- The preceding bridge applies directly to the finite uniform atlas used by
the shifted-Bergman collar construction.  The uniform estimates are preserved
in `A`; this theorem only exposes the exact branch data needed for curvature
and strong analytic singularities. -/
theorem hasLocalSmoothLogSumPresentations_of_finiteUniformAtlasBranchAgreement
    {θ : SmoothRealForm n M 2} {u w : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (hm : 0 < m)
    (hagree : ∀ i (x : M), x ∈ (A.patch i).patch.source →
      w x = bergmanBranch (A.patch i).patch x) :
    HasLocalSmoothLogSumPresentations θ w :=
  hasLocalSmoothLogSumPresentations_of_finiteAtlasBranchAgreement
    (finiteUniformLocalBergmanAtlas_toFiniteLocalBergmanAtlas A) hm hagree

/-- Under finite-atlas branch agreement, the concrete Bergman data yields
both theta-PSH and the strong smooth-remainder analytic-singularity condition.
-/
theorem thetaPsh_and_strongAnalytic_of_finiteAtlasBranchAgreement
    {θ : SmoothRealForm n M 2} {u w : M → EReal} {m : ℕ}
    (A : FiniteLocalBergmanAtlas θ u m) (hm : 0 < m)
    (hagree : ∀ i (x : M), x ∈ (A.patch i).source →
      w x = bergmanBranch (A.patch i) x) :
    ThetaPlurisubharmonic θ w ∧ HasManifoldSmoothAnalyticSingularities (n := n) w :=
  thetaPsh_and_strongAnalytic_of_localSmoothLogSumPresentations
    (hasLocalSmoothLogSumPresentations_of_finiteAtlasBranchAgreement A hm hagree)

/-- The actual finite uniform atlas therefore gives the theta-PSH and strong
analytic conclusions whenever its branches agree exactly on their sources. -/
theorem thetaPsh_and_strongAnalytic_of_finiteUniformAtlasBranchAgreement
    {θ : SmoothRealForm n M 2} {u w : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (hm : 0 < m)
    (hagree : ∀ i (x : M), x ∈ (A.patch i).patch.source →
      w x = bergmanBranch (A.patch i).patch x) :
    ThetaPlurisubharmonic θ w ∧ HasManifoldSmoothAnalyticSingularities (n := n) w :=
  thetaPsh_and_strongAnalytic_of_localSmoothLogSumPresentations
    (hasLocalSmoothLogSumPresentations_of_finiteUniformAtlasBranchAgreement A hm hagree)

end

end Hironaka.LocalBergmanSmoothLogSum
