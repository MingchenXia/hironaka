import Hironaka.Resolution.HironakaG4UnitTemplate
import Hironaka.Resolution.HironakaG4PermutedFullTest
import Hironaka.Resolution.HironakaG4DirectLocalProtectedWindow
import Hironaka.Resolution.HironakaSharpActualCurveGlobalBoundaryCoordinates

/-! The actual full and lower tests protect the unit branch. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4UnitWindowProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  NormalCrossings NormalCrossingsComparison DivisorExponentAlong MonomialPartAlong
  NonmonomialTransformAlong RestrictedIdealExtension RelativePrincipalizationSpan
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupRestrictOpen
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualCurveGlobalBoundaryCoordinates
  HironakaG4UnitTemplate HironakaG4PermutedFullTest HironakaG4DirectLocalProtectedWindow
  HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- In the monomial-unit branch, the actual lower and full-boundary tests
alone protect the transformed slice with its actual remaining boundary. -/
theorem unit_slice_protected_by_full_test (hn : 0 < n)
    {N Haux H : Set X} {F B L : List (Set X)}
    (hNclosed : IsClosedSubmanifold n N)
    (hEF : IsSNCDivisor n (Haux :: F)) (hTF : IsTransverse n N (Haux :: F))
    (hL : IsSNCDivisor n L) (hHL : H ∈ L)
    (hI : (restrictOn n N (vanishingIdeal (n := n) H)).IsCoherent)
    (P Q : MarkedIdeal n X) (hPN : P.N ⊆ N) (hperm : (H :: F).Perm Q.E)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hP : IsGeoTestTower P (.step T C π hπ))
    (hQ : IsGeoTestTower Q (.step T C π hπ)) (x : Y)
    (hxN : T.proj x ∈ N) (hxHaux : T.proj x ∈ Haux)
    (hnz : IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) (T.proj x))
    (hunit : (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem (T.proj x) 1)
    (hJZ : ∀ g, (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem (T.proj x) g ↔
      (vanishingIdeal (n := n) (N ∩ Haux)).mem (T.proj x) g) :
    let K : MarkedIdeal n X := geometricTemplate N []
    ProtectedWindowAt (strictAlong T N) (strictAlong T (N ∩ Haux))
      (F.map (strictAlong T) ++ (geoTransformAlong K T).E) C x := by
  dsimp only
  let D : MarkedIdeal n X := geometricTemplate N (H :: F)
  let K : MarkedIdeal n X := geometricTemplate N []
  let i : Fin D.E.length := ⟨0,by simp [D,geometricTemplate]⟩
  have hi : D.E.get i = H := by simp [i,D,geometricTemplate]
  obtain ⟨U,hxU,hD,hSlice⟩ := exists_unit_member_template hn hNclosed hEF hTF hL hHL hxN hxHaux hI hnz hunit hJZ
  have htest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T) :=
    restricted_enlarged_test_of_permuted_full_boundary P Q D hPN hperm U hD rfl T hP.1 hQ.1
  have hBoundary : (geoTransformAlong D T).E = strictAlong T (D.E.get i) ::
      (F.map (strictAlong T) ++ (geoTransformAlong K T).E) := by
    rw [hi]
    have h := boundary_geoTransformAlong_decomposition D K rfl T
    simpa only [D,geometricTemplate, List.map_cons, List.cons_append] using h
  have hC : HasNormalCrossings n C (geoTransformAlong D T).E :=
    hasNormalCrossings_of_forall_mem hQ.2.2.2 (perm_geoTransformAlong_boundary D Q hperm T).subset
  have hSlice' : (Subtype.val : U → X) ⁻¹' (N ∩ Haux) =
      (Subtype.val : U → X) ⁻¹' (D.N ∩ D.E.get i) := by
    rw [hi]
    exact hSlice
  exact protected_window_of_local_test_and_full_centre D U hD T htest i (N ∩ Haux) hSlice'
    hxU hBoundary hC

end
end Hironaka.HironakaG4UnitWindowProtection
