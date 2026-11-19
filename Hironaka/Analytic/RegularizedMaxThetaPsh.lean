import Hironaka.Analytic.RegularizedMaxPsh
import Hironaka.Analytic.RegularizedMaxERealPshRoute
import Hironaka.Analytic.BoundedGlobalTruncation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The regularized maximum in a fixed background: the closure package, discharged

`Hironaka.RegularizedMaxERealPshRoute` isolated the analytic gap for
`eregularizedMax` as `ERegularizedMaxThetaPshClosure θ δ u v`, and proved the
global theta-PSH conclusion *from* it.  That package is no longer an
assumption: `Hironaka.RegularizedMaxPsh` proves the local statement (Demailly
CADG I.5.18), and this file transports it to a background form.

The transport is the same two-line device as for the ordinary maximum
(`Hironaka.BoundedGlobalProduct.ThetaPlurisubharmonic.max`), with one extra
ingredient: `eregularizedMax` is **equivariant** under adding a real function to
both branches, so correcting by a single smooth local potential `ρ` of `θ`
commutes with it:

    M_δ(u, v) ∘ e⁻¹ + ρ = M_δ(u ∘ e⁻¹ + ρ, v ∘ e⁻¹ + ρ).

Both corrected branches are PSH on `W` — by
`ThetaPlurisubharmonic.corrected_plurisubharmonicOn`, which allows *any* smooth
local potential, not just the one produced with the branch — so the left side is
PSH on `W`, which is the raw theta-PSH criterion for `M_δ(u, v)`.

Consequently `isThetaPshPotential_eregularizedMax` needs no hypothesis beyond
the two backgrounds' own theta-PSH data and `0 < δ`: this is the operation the
strong-convention (CT22) multi-chart gluing of Demailly's local approximants
needs, where the plain maximum cannot be used because
`max(c log Σ|f| + b₁, c log Σ|g| + b₂)` is not of the form `c log Σ|h| + smooth`
near the crossing locus.
-/

open Set

namespace Hironaka.RegularizedMaxThetaPsh


open Hironaka.BoundedGlobalProduct
open Hironaka.RegularizedMaxEReal
open Hironaka.RegularizedMaxConvexity
open Hironaka.RegularizedMaxPsh
open Hironaka.RegularizedMaxERealPshRoute

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The regularized maximum of two raw theta-PSH potentials is raw theta-PSH.**
The background form is unchanged: no curvature is lost. -/
theorem thetaPlurisubharmonic_eregularizedMax {θ : SmoothRealForm n M 2} {δ : ℝ}
    (hδ : 0 < δ) {u v : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) (hv : ThetaPlurisubharmonic θ v) :
    ThetaPlurisubharmonic θ (fun x => eregularizedMax δ (u x) (v x)) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, _⟩ := hu e z hz
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  have h1 := ThetaPlurisubharmonic.corrected_plurisubharmonicOn hu e hρ
  have h2 := ThetaPlurisubharmonic.corrected_plurisubharmonicOn hv e hρ
  have hmain := plurisubharmonicOn_eregularizedMax (δ := δ) hδ h1 h2
  have heq : (fun y => chartFunction (fun x => eregularizedMax δ (u x) (v x)) e y
        + (ρ y : EReal))
      = fun y => eregularizedMax δ (chartFunction u e y + (ρ y : EReal))
          (chartFunction v e y + (ρ y : EReal)) := by
    funext y
    rw [eregularizedMax_add_coe]
    rfl
  rw [heq]
  exact hmain

/-- **The closure package of `Hironaka.RegularizedMaxERealPshRoute` is a theorem.**
Both of its fields — the criterion off the common pole set and the criterion
across it — come from the single global statement above. -/
theorem eRegularizedMaxThetaPshClosure {θ : SmoothRealForm n M 2} {δ : ℝ}
    (hδ : 0 < δ) {u v : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) (hv : ThetaPlurisubharmonic θ v) :
    ERegularizedMaxThetaPshClosure θ δ u v := by
  have h := thetaPlurisubharmonic_eregularizedMax hδ hu hv
  exact ⟨fun e z hz _ => h e z hz, ThetaPlurisubharmonic.thetaPshAcross h _⟩

/-- **The regularized maximum of a theta-PSH potential with a raw theta-PSH
function is a theta-PSH potential**, with no closure hypothesis.  Nondegeneracy
comes from the left factor, which the regularized maximum dominates. -/
theorem isThetaPshPotential_eregularizedMax {θ : SmoothRealForm n M 2} {δ : ℝ}
    (hδ : 0 < δ) {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : ThetaPlurisubharmonic θ v) :
    IsThetaPshPotential θ (fun x => eregularizedMax δ (u x) (v x)) :=
  isThetaPshPotential_eregularizedMax_of_closure hδ hu hv
    (eRegularizedMaxThetaPshClosure hδ hu.1 hv)

/-- The symmetric form: two theta-PSH potentials. -/
theorem isThetaPshPotential_eregularizedMax' {θ : SmoothRealForm n M 2} {δ : ℝ}
    (hδ : 0 < δ) {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential θ v) :
    IsThetaPshPotential θ (fun x => eregularizedMax δ (u x) (v x)) :=
  isThetaPshPotential_eregularizedMax hδ hu hv.1

end

end Hironaka.RegularizedMaxThetaPsh
