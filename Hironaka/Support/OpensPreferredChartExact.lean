/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Manifold.HolomorphicMaps
import Hironaka.Analytic.AnalyticSubsetOpens
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Restriction of forms and theta-PSH potentials to an open submanifold

Let `M` be a complex manifold and `U` an open subset, a complex manifold with the restricted
charts `(chartAt x).subtypeRestr` (`TopologicalSpace.Opens.instChartedSpace`,
`AnalyticSubsetOpens.instIsComplexManifoldOpens`).  The inclusion `Subtype.val : U → M` is
holomorphic, and forms, Kähler backgrounds and theta-PSH functions restrict along it:

* `restrictForm U θ` — the closed real `(1,1)`-form `θ|_U` (the pullback along the inclusion);
  in the preferred chart of `U` at `y` its coefficient is that of `θ` in the preferred chart of
  `M` at `y` (`restrictForm_coeff_chartAt`);
* `restrictKahler U ω` — a Kähler background restricts to a Kähler background;
* `thetaPlurisubharmonic_restrict`, `locallyNondegenerate_restrict`,
  `isThetaPshPotential_restrict` — theta-PSH potentials restrict.

The converse is the point of this module.  A theta-PSH witness (a smooth local potential `ρ` of
`θ` with `u + ρ` PSH) in one chart transports to any other chart at the same point
(`exists_witness_of_chart`, holomorphic pullback along the chart transition), so:

* `thetaPlurisubharmonicOn_of_restrict` — if `G|_U` is `θ|_U`-PSH, then `G` is `θ`-PSH over `U`;
* `thetaPlurisubharmonic_piecewise` — on a clopen `U`, a function equal to a `θ|_U`-PSH
  function on `U` and to a `θ`-PSH function off `U` is `θ`-PSH on `M`.

This is the reusable half of the reduction of statements about compact Kähler manifolds to
their connected components (`Hironaka.OpensRestrictionMeasure` carries the measures and the
envelopes).  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.OpensRestriction

open Hironaka.HolomorphicMaps

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]


/-! ### The inclusion of an open submanifold -/

variable (U : Opens M)

omit [IsComplexManifold n M] in
/-- The inclusion of an open submanifold is holomorphic. -/
theorem contMDiff_val :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : U → M) :=
  contMDiff_subtype_val

variable {U}

omit [IsComplexManifold n M] in
/-- The preferred chart of `U` at `y` is the preferred chart of `M` at `y`, restricted. -/
theorem complexChartAt_opens_val (y : U) :
    (complexChartAt (n := n) y).val =
      (chartAt (ComplexModel n) (y : M)).subtypeRestr ⟨y⟩ := rfl

/-- The target of the preferred chart of `U` at `y` lies in that of `M`. -/
theorem complexChartAt_opens_target_subset (y : U) :
    (complexChartAt (n := n) y).val.target ⊆ (complexChartAt (n := n) (y : M)).val.target := by
  rw [complexChartAt_opens_val]
  exact (chartAt (ComplexModel n) (y : M)).subtypeRestr_target_subset ⟨y⟩

/-- The inverse of the preferred chart of `U`, read in `M`. -/
theorem val_complexChartAt_opens_symm (y : U) {z : ComplexModel n}
    (hz : z ∈ (complexChartAt (n := n) y).val.target) :
    ((complexChartAt (n := n) y).val.symm z : M) =
      (complexChartAt (n := n) (y : M)).val.symm z := by
  rw [complexChartAt_opens_val] at hz ⊢
  exact (chartAt (ComplexModel n) (y : M)).subtypeRestr_symm_apply ⟨y⟩ hz

omit [IsComplexManifold n M] in
theorem complexChartAt_opens_apply (y : U) :
    (complexChartAt (n := n) y).val y = (complexChartAt (n := n) (y : M)).val (y : M) := rfl

/-- The coordinate expression of the inclusion in the preferred charts at `y` is the identity on
the chart target of `U`. -/
theorem coordinateMap_val_complexChartAt (y : U) {z : ComplexModel n}
    (hz : z ∈ (complexChartAt (n := n) y).val.target) :
    coordinateMap (Subtype.val : U → M) (complexChartAt (n := n) y)
      (complexChartAt (n := n) (y : M)) z = z := by
  simp only [coordinateMap, Function.comp_apply]
  rw [val_complexChartAt_opens_symm y hz]
  exact (complexChartAt (n := n) (y : M)).val.right_inv (complexChartAt_opens_target_subset y hz)


end

end Hironaka.OpensRestriction
