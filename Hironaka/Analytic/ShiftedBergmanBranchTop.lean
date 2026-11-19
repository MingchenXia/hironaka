import Hironaka.Analytic.RegularizedMaxCollarGluing
import Hironaka.Analytic.ShiftedBergmanBranch

set_option autoImplicit false

/-!
# Global non-topness of shifted Bergman branches

A local shifted Bergman branch is theta-plurisubharmonic on its source and is
by definition a finite constant outside that source. Consequently its values
are never `⊤` on the ambient manifold. This removes a redundant datum from
the finite Demailly regularization interface.
-/

open Set Filter
open scoped Topology

namespace Hironaka.ShiftedBergmanBranchTop


open Hironaka.AnalyticGluingData
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open ShiftedBergmanBranch
open RegularizedMaxCollarGluing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A shifted Bergman branch is globally different from `⊤`: on the patch
source this follows from its theta-PSH property, and outside it the defining
extension is a finite constant. -/
theorem shiftedBergmanBranch_ne_top_of_thetaPlurisubharmonicOn
    {theta : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta u m) (a : ℝ)
    (hpsh : ThetaPlurisubharmonicOn theta (shiftedBergmanBranch D a) D.source) :
    ∀ x, shiftedBergmanBranch D a x ≠ ⊤ := by
  intro x
  by_cases hx : x ∈ D.source
  · exact ThetaPlurisubharmonicOn.ne_top hpsh hx
  · rw [shiftedBergmanBranch, bergmanBranch, dif_neg hx]
    exact EReal.add_ne_top EReal.zero_ne_top (EReal.coe_ne_top a)

end

end Hironaka.ShiftedBergmanBranchTop
