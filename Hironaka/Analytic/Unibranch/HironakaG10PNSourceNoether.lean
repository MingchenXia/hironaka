import Hironaka.Analytic.Unibranch.ReducedComplexSpaces
import Hironaka.Resolution.HironakaG10PNIdealNoetherModel

/-!
# The Noether property of coherent ideals on reduced complex spaces (lane G10P, run 0080)

For a `SourceReducedComplexSpace` `X` (the category of `HironakaFlattening`), an ascending chain of
locally finitely generated (coherent) ideal families of `𝒪_X` is stationary near every compact set:
ONE tail `N` and ONE open `W ⊇ K` with `J m = J N` on `W` for `m ≥ N`.  The ideals need not be reduced
or radical, so closed complex subspaces WITH NILPOTENTS of `X` (for instance the fibres `𝔪_z 𝒪_Y` of a
morphism and the closed subspaces of a compact fibre) are covered; this is the Noether property used
by the termination step (4.3) of the global flattening route (`G10.COMPACT.01`).  All work is in TN
`Hironaka.HironakaG10PNIdealNoetherModel`; this module only reads the chart condition of the category.
Blueprint: `hironaka-g10-pn-ideal-noether.tex`.
-/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10PNSourceNoether

open Hironaka HironakaG10PNIdealFamily HironakaG10PNIdealNoetherModel

/-- Reduced complex spaces have analytic model charts. -/
theorem hasAnalyticModelCharts (X : SourceReducedComplexSpace) :
    HasAnalyticModelCharts X.obj.left := fun x => by
  obtain ⟨n, U, C, hC, i, hi, -, hx⟩ := X.property.2.2 x
  exact ⟨n, U, C, hC, i, hi, hx⟩

/-- **The local Noether property of a reduced complex space.** -/
theorem hasLocalNoetherProperty (X : SourceReducedComplexSpace) :
    HasLocalNoetherProperty X.obj.left :=
  hasLocalNoetherProperty_of_charts (hasAnalyticModelCharts X)

/-- **Noether property over a compact set.**  On a reduced complex space, an ascending chain of
locally finitely generated ideal families is stationary on ONE open neighbourhood of a compact set
from ONE index on. -/
theorem exists_stationary_nhds (X : SourceReducedComplexSpace)
    {J : ℕ → ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x)} (hJ : IsAscending X.obj.left J)
    (hfg : ∀ m, IsLocallyFinitelyGenerated X.obj.left (J m)) (K : Set X.obj.left)
    (hK : IsCompact K) :
    ∃ (N : ℕ) (W : Opens X.obj.left), K ⊆ (W : Set X.obj.left) ∧
      ∀ m, N ≤ m → ∀ x : X.obj.left, x ∈ W → J m x = J N x :=
  exists_stationary_nhds_of_charts (hasAnalyticModelCharts X) hJ hfg K hK

/-- **Termination form.**  On a reduced complex space, an ascending chain of locally finitely
generated ideal families cannot grow strictly at some point of a fixed compact set at every step. -/
theorem not_forall_exists_strict (X : SourceReducedComplexSpace)
    {J : ℕ → ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x)} (hJ : IsAscending X.obj.left J)
    (hfg : ∀ m, IsLocallyFinitelyGenerated X.obj.left (J m)) (K : Set X.obj.left)
    (hK : IsCompact K) : ¬ ∀ m : ℕ, ∃ x ∈ K, J m x < J (m + 1) x :=
  not_forall_exists_strict_of_charts (hasAnalyticModelCharts X) hJ hfg K hK

end Hironaka.Analytic.Unibranch.HironakaG10PNSourceNoether
