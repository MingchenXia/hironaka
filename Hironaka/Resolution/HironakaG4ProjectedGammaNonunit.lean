import Hironaka.MarkedIdeal.TransformOffCentre
import Hironaka.MarkedIdeal.RestrictedIdealExtension

/-! An actual marked-one centre projects to a nonunit ambient ideal germ. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ProjectedGammaNonunit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal TransformOffCentre GermIdealOrder
  RelativePrincipalizationSpan RestrictedIdealExtension

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- If the lower mark-one ideal is the restriction of a coherent ambient
ideal, a centre of an actual lower test step projects to a nonunit germ of
that ambient ideal. -/
theorem projected_centre_ambient_nonunit
    (P : MarkedIdeal n X) (hP : P.IsWellFormed) (hmark : P.d = 1)
    (I : GermIdeal n X) (hI : I.IsCoherent) (hrel : P.ideal = restrictOn n P.N I)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step T C π hπ)) {x : Y} (hx : x ∈ C) :
    ¬ I.mem (T.proj x) 1 := by
  have hxcos := cosupp_geoTransformAlong_subset P hP.isClosedSubmanifold_N hP.isCoherent
    T hTest.1 (hTest.2.2.1 hx)
  have hzero : T.proj x ∈ P.N ∩ P.ideal.zeroLocus := by
    change T.proj x ∈ cosupport n P.N P.ideal P.d at hxcos
    rw [hmark, cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isCoherent hg)] at hxcos
    exact hxcos
  intro hu
  have huP : P.ideal.mem (T.proj x) 1 := by
    rw [hrel]
    exact le_restrictOn hI _ _ hu
  exact one_ne_zero (hzero.2 1 huP)

end
end Hironaka.HironakaG4ProjectedGammaNonunit
