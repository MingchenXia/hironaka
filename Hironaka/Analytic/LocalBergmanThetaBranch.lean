import Hironaka.Analytic.LocalBergmanFiniteAtlas
import Hironaka.Analytic.PotentialTheory.AnalyticSingularities
import Hironaka.Analytic.HolomorphicPullback
import Hironaka.Analytic.LocalPotentialPullback
import Hironaka.Analytic.FormPullbackFunctorial
import Hironaka.Analytic.AnalyticGluingData

set_option autoImplicit false

/-!
# A theta-PSH branch carried by one Bergman patch

On the source of a local Bergman patch, the scaled generator logarithm minus
the local potential is a manifold-valued theta-PSH branch.  Its value outside
the source is set to zero, which is harmless for the local statement.  The
proof transports both the local potential and the ordinary PSH generator
logarithm through an arbitrary chart transition.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.QuasiEquisingularBergmanBranch


open Hironaka.AnalyticGluingData
open Hironaka.HolomorphicMaps
open Hironaka.LocalPotentialPullback
open DemaillyAnalyticType

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The local logarithmic Bergman weight, corrected by the patch potential and
extended by zero outside the patch source. -/
noncomputable def bergmanBranch {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : QuasiEquisingularBergmanAtlas.LocalBergmanPatch θ u m) : M → EReal := by
  classical
  exact fun x => if hx : x ∈ D.source then
    (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator (D.chart.val x) -
      (D.potential (D.chart.val x) : EReal)
    else 0

/-- The manifold branch associated to one local Bergman patch is theta-PSH on
the patch source.  The potential is transported through the identity map in
the two charts, while the scaled generator logarithm is pulled back through
the resulting holomorphic coordinate map. -/
theorem bergmanBranch_thetaPlurisubharmonicOn
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : QuasiEquisingularBergmanAtlas.LocalBergmanPatch θ u m) (hm : 0 < m) :
    ThetaPlurisubharmonicOn θ (bergmanBranch D) D.source := by
  intro e z hz hzsource
  let hid : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (id : M → M) := contMDiff_id
  let F : ComplexModel n → ComplexModel n := coordinateMap (id : M → M) e D.chart
  let W : Set (ComplexModel n) := potentialDomain (id : M → M) e D.chart D.domain
  let ρe : ComplexModel n → ℝ := D.potential ∘ F
  have hW : IsOpen W := potentialDomain_isOpen hid e D.chart D.domain.isOpen
  have hzW : z ∈ W := by
    constructor
    · change z ∈ e.val.target ∧ e.val.symm z ∈ D.chart.val.source
      exact ⟨hz, hzsource.1⟩
    · change D.chart.val (e.val.symm z) ∈ D.domain
      exact hzsource.2
  have hρpull : IsSmoothLocalPotential (SmoothRealForm.pullback hid θ) e W ρe :=
    isSmoothLocalPotential_pullback hid e D.localPotential
  have hρe : IsSmoothLocalPotential θ e W ρe :=
    (SmoothRealForm.pullback_id_geometricallyEq θ).localPotential_iff e W ρe |>.mp hρpull
  refine ⟨W, ρe, hzW, hρe, ?_⟩
  have hcoef : 0 < ((m : ℝ)⁻¹) := inv_pos.mpr (by exact_mod_cast hm)
  have hdiff : DifferentiableOn ℂ F W :=
    ((coordinateMap_contDiffOn hid e D.chart).differentiableOn (by simp)).mono inter_subset_left
  intro y hy
  have hygen : HolomorphicGeneratorsAt D.generator (F y) := by
    refine ⟨D.domain, D.domain.isOpen, ?_, fun l => (D.generator_analytic l).differentiableOn⟩
    exact hy.2
  have hlog : PlurisubharmonicAt
      (fun w => (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator w) (F y) :=
    Hironaka.plurisubharmonicAt_scaled_generatorLog hygen hcoef
  have hpull : PlurisubharmonicAt
      (fun w => (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator (F w)) y :=
    HolomorphicPullback.plurisubharmonicAt_comp_holomorphic hW hdiff hy hlog
  refine hpull.congr ?_
  filter_upwards [hW.mem_nhds hy] with w hw
  have hwsource : e.val.symm w ∈ D.source := by
    constructor
    · exact hw.1.2
    · exact hw.2
  change (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator (F w) =
    bergmanBranch D (e.val.symm w) + (ρe w : EReal)
  rw [bergmanBranch, dif_pos hwsource]
  change (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator (F w) =
    ((((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator (F w) -
      (D.potential (F w) : EReal)) + (D.potential (F w) : EReal)
  exact EReal.sub_add_cancel.symm

end

end Hironaka.QuasiEquisingularBergmanBranch
