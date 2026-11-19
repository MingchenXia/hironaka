import Hironaka.Analytic.Unibranch.HironakaG10PNSourceNoether
import Hironaka.Resolution.HironakaG10AnalyticChartsUniformArtinRees

/-! # Uniform Artin--Rees for the native reduced complex spaces -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10SourceUniformArtinRees

open Hironaka HironakaG10PNIdealFamily
  HironakaG10ChowUniformArtinRees HironakaG10AnalyticChartsUniformArtinRees
  HironakaG10PNSourceNoether

/-- Near any point of a native reduced complex space, two locally finitely
generated whole ideal families have a common Artin--Rees exponent. -/
theorem exists_local_uniform_artinRees (X : SourceReducedComplexSpace)
    (I K : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hI : IsLocallyFinitelyGenerated X.obj.left I)
    (hK : IsLocallyFinitelyGenerated X.obj.left K) (x : X.obj.left) :
    ∃ α : ℕ, ∃ O : Set X.obj.left, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (I y) (K y) α :=
  exists_charts_uniform_artinRees (hasAnalyticModelCharts X) I K hI hK x

/-- A single exponent works near a compact subset of a native reduced
complex space. The ideal families need not be radical. -/
theorem exists_compact_uniform_artinRees (X : SourceReducedComplexSpace)
    (I K : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hI : IsLocallyFinitelyGenerated X.obj.left I)
    (hK : IsLocallyFinitelyGenerated X.obj.left K) (Q : Set X.obj.left) (hQ : IsCompact Q) :
    ∃ α : ℕ, ∃ O : Set X.obj.left, IsOpen O ∧ Q ⊆ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (I y) (K y) α :=
  exists_charts_compact_uniform_artinRees (hasAnalyticModelCharts X) I K hI hK Q hQ

end Hironaka.Analytic.Unibranch.HironakaG10SourceUniformArtinRees
