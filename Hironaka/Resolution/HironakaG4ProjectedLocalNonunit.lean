import Hironaka.Resolution.HironakaG4ProjectedGammaNonunit

/-! Pointwise ideal inclusion suffices for projected nonunitness. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ProjectedLocalNonunit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal TransformOffCentre GermIdealOrder RelativePrincipalizationSpan

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- An actual mark-one test centre projects to a nonunit germ of any ideal
whose germ is contained in the lower ideal at that projected point. -/
theorem projected_centre_nonunit_of_local_inclusion
    (P : MarkedIdeal n X) (hP : P.IsWellFormed) (hmark : P.d = 1)
    (I : GermIdeal n X) (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hTest : IsGeoTestTower P (.step T C π hπ))
    {x : Y} (hx : x ∈ C)
    (hle : ∀ g, I.mem (T.proj x) g → P.ideal.mem (T.proj x) g) :
    ¬ I.mem (T.proj x) 1 := by
  have hxcos := cosupp_geoTransformAlong_subset P hP.isClosedSubmanifold_N hP.isCoherent
    T hTest.1 (hTest.2.2.1 hx)
  have hzero : T.proj x ∈ P.N ∩ P.ideal.zeroLocus := by
    change T.proj x ∈ cosupport n P.N P.ideal P.d at hxcos
    rw [hmark, cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isCoherent hg)] at hxcos
    exact hxcos
  intro hu
  exact one_ne_zero (hzero.2 1 (hle 1 hu))

end
end Hironaka.HironakaG4ProjectedLocalNonunit
