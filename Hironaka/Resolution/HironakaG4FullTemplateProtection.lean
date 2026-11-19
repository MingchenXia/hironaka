import Hironaka.Resolution.HironakaG4UnitWindowProtection

/-! Read the actual protected certificate from a local full-boundary template. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4FullTemplateProtection
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold HomogenizedGlueingTower NormalCrossings NormalCrossingsComparison
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupRestrictOpen
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualCurveGlobalBoundaryCoordinates
  HironakaG4PermutedFullTest HironakaG4DirectLocalProtectedWindow HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- A local actual-member template, an arbitrary lower test, and a full
boundary test imply the ambient protected-window certificate. -/
theorem local_member_template_protected_by_full_test
    (N H S : Set X) (F : List (Set X)) (P Q : MarkedIdeal n X)
    (hPN : P.N ⊆ N) (hperm : (H :: F).Perm Q.E) (U : Opens X)
    (hD : (MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate N (H :: F))).IsWellFormed)
    (hSlice : (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' (N ∩ H))
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hP : IsGeoTestTower P (.step T C π hπ))
    (hQ : IsGeoTestTower Q (.step T C π hπ)) (x : Y) (hxU : T.proj x ∈ U) :
    let K : MarkedIdeal n X := geometricTemplate N []
    ProtectedWindowAt (strictAlong T N) (strictAlong T S)
      (F.map (strictAlong T) ++ (geoTransformAlong K T).E) C x := by
  dsimp only
  let D : MarkedIdeal n X := geometricTemplate N (H :: F)
  let K : MarkedIdeal n X := geometricTemplate N []
  let i : Fin D.E.length := ⟨0,by simp [D,geometricTemplate]⟩
  have hi : D.E.get i = H := by simp [i,D,geometricTemplate]
  have htest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T) :=
    restricted_enlarged_test_of_permuted_full_boundary P Q D hPN hperm U hD rfl T hP.1 hQ.1
  have hBoundary : (geoTransformAlong D T).E = strictAlong T (D.E.get i) ::
      (F.map (strictAlong T) ++ (geoTransformAlong K T).E) := by
    rw [hi]
    have h := boundary_geoTransformAlong_decomposition D K rfl T
    simpa only [D,geometricTemplate, List.map_cons, List.cons_append] using h
  have hC : HasNormalCrossings n C (geoTransformAlong D T).E :=
    hasNormalCrossings_of_forall_mem hQ.2.2.2 (perm_geoTransformAlong_boundary D Q hperm T).subset
  have hSlice' : (Subtype.val : U → X) ⁻¹' S = (Subtype.val : U → X) ⁻¹' (D.N ∩ D.E.get i) := by
    rw [hi]
    exact hSlice
  exact protected_window_of_local_test_and_full_centre D U hD T htest i S hSlice' hxU hBoundary hC

end
end Hironaka.HironakaG4FullTemplateProtection
