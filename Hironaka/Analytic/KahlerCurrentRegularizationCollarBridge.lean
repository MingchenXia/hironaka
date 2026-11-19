import Hironaka.Analytic.KahlerCurrentRegularizationBergmanBranch
import Hironaka.Analytic.ThetaPshCollarGluing

set_option autoImplicit false

/-!
# Collar globalization of one local Bergman branch

This is a concrete piece of the global Demailly-regularization construction.
On an inner open set where a local Bergman branch dominates a global
theta-plurisubharmonic branch, its collar maximum has the same analytic type
as the Bergman branch.  The complementary collar inequality lets the existing
`ThetaPshCollarGluing` theorem give a global theta-PSH potential.

The two comparison inequalities are retained explicitly.  In particular, this
module does not assert their construction from weighted Bergman data; obtaining
the required outer orientation is the still-open global gluing step.
-/

open Set Filter
open scoped Topology

namespace Hironaka.KahlerCurrentRegularizationCollarBridge


open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open QuasiEquisingularCollarGluing
open KahlerCurrentRegularizationBergmanBranch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A collar-glued Bergman branch retains the branch's analytic type on the
inner open set where it dominates the global branch. -/
theorem gluedBergmanBranch_thetaPsh_analyticTypeAt
    {theta : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta u m) (hm : 0 < m)
    {U' : Set M} (hU' : IsOpen U') (hclosure : closure U' ⊆ D.source)
    {g : M → EReal} (hcollar : ∀ x ∈ (D.source : Set M) \ U',
      bergmanBranch D x ≤ g x)
    (hcore : ∀ x ∈ U', g x ≤ bergmanBranch D x)
    (hg : IsThetaPshPotential theta g)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzcore : e.val.symm z ∈ U') :
    IsThetaPshPotential theta (gluedMax (D.source : Set M) (bergmanBranch D) g) ∧
      HasAnalyticSingularityTypeAt
        (chartFunction (gluedMax (D.source : Set M) (bergmanBranch D) g) e) z := by
  refine ⟨isThetaPshPotential_gluedMax D.source.isOpen hclosure hcollar
    (bergmanBranch_thetaPlurisubharmonicOn D hm) hg, ?_⟩
  have hzsource : e.val.symm z ∈ D.source :=
    hclosure (subset_closure hzcore)
  have hbranch := bergmanBranch_analyticTypeAt D e hz hzsource
  have hcoreEq : gluedMax (D.source : Set M) (bergmanBranch D) g =ᶠ[𝓝 (e.val.symm z)]
      bergmanBranch D := by
    filter_upwards [hU'.mem_nhds hzcore] with x hx
    rw [gluedMax_eq_max (hclosure (subset_closure hx))]
    exact max_eq_left (hcore x hx)
  have hchartEq : chartFunction (gluedMax (D.source : Set M) (bergmanBranch D) g) e =ᶠ[𝓝 z]
      chartFunction (bergmanBranch D) e := by
    change (gluedMax (D.source : Set M) (bergmanBranch D) g ∘ e.val.symm) =ᶠ[𝓝 z]
      (bergmanBranch D ∘ e.val.symm)
    exact hcoreEq.comp_tendsto (e.val.continuousAt_symm hz)
  obtain ⟨c, N, f, htype⟩ := hbranch
  obtain ⟨hc, hf, b, hb, heq⟩ := htype
  exact ⟨c, N, f, hc, hf, b, hb, hchartEq.trans heq⟩

end

end Hironaka.KahlerCurrentRegularizationCollarBridge
