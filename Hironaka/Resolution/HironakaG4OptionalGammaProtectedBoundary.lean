import Hironaka.Resolution.HironakaG4OptionalGammaProtectedCentre
import Hironaka.Resolution.HironakaSharpActualCurveGlobalBoundaryCoordinates
import Hironaka.Resolution.HironakaPrincipalization

/-! Read the protected certificate with the actual original-plus-birth boundary. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OptionalGammaProtectedBoundary
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism NormalCrossings
  HironakaG34CoordinateScaling HironakaG34MaskFoldEquivariance HironakaG4WeightedGammaParameter
  HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks HironakaG4OptionalGammaProtectedCentre
  HironakaSharpActualCurveGlobalBoundaryCoordinates HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The transformed protected boundary is the strict transform of the original
tail followed by the actual exceptional boundary; no such decomposition or
closedness certificate needs to be supplied. -/
theorem optional_gamma_chart_protects_equivariant_centre_with_actual_boundary
    (P D : MarkedIdeal n X) (hPN : P.N ⊆ D.N) (H : Set X) (F₀ : List (Set X))
    (hDE : D.E = H :: F₀) (hNclosed : IsClosed D.N) (hDclosed : ∀ K ∈ D.E, IsClosed K)
    (U₀ : Opens X) (hD : (MarkedIdeal.pullback (Subtype.val : U₀ → X) D).IsWellFormed)
    (hmark : D.d = 0) (S : Set X)
    (hSlice : (Subtype.val : U₀ → X) ⁻¹' S = (Subtype.val : U₀ → X) ⁻¹' (D.N ∩ H))
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (O : Opens (ComplexModel n)) (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    (hWindow : ∀ x ∈ U₀, x ∈ flatDomain Φ ∧ flatMap Φ x ∈ O)
    (s t : Fin n) (c : Fin n → ℕ) (R R₀ : Finset (Fin n)) (m : Fin D.E.length → Option (Fin n))
    (hs : s ∈ R₀) (hst : t ≠ s) (hcs : c s = 0)
    (hN : ∀ y ∈ flatDomain Φ, y ∈ D.N ↔ flatMap Φ y ∈ coordSubspace R₀)
    (hDcoords : ∀ j y, y ∈ flatDomain Φ → (y ∈ D.E.get j ↔
      flatMap Φ y ∈ optionalCoordLocus ((m j).map (fun k => {k})))) (hm : DivisorMasksValid R₀ m)
    {W : Set X} {E : List (Set X)}
    (hW : ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → (y ∈ W ↔ flatMap Φ y ∈ coordSubspace R))
    (hE : ∀ H' ∈ E, (∃ Q : Finset (Fin n), ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O →
      (y ∈ H' ↔ flatMap Φ y ∈ coordSubspace Q)) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → (y ∈ H' ↔ flatMap Φ y ∈ {w | binomial s t c w = 0})) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → y ∉ H'))
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step T C π hπ)) (hEq : IsEquivariant W E (.step T C π hπ))
    (x : Y) (hxC : x ∈ C) (hxU : T.proj x ∈ U₀) :
    let K : MarkedIdeal n X := {D with E := []}
    ProtectedWindowAt (strictAlong T D.N) (strictAlong T S)
      (F₀.map (strictAlong T) ++ (geoTransformAlong K T).E) C x := by
  dsimp only
  let K : MarkedIdeal n X := {D with E := []}
  let i : Fin D.E.length := ⟨0, by rw [hDE]; simp⟩
  have hi : D.E.get i = H := by simp [i, hDE]
  let F := F₀.map (strictAlong T) ++ (geoTransformAlong K T).E
  have hBoundary : (geoTransformAlong D T).E = strictAlong T (D.E.get i) :: F := by
    have h := boundary_geoTransformAlong_decomposition D K rfl T
    simpa only [hDE, List.map_cons, List.cons_append, hi, F] using h
  have hEclosed : ∀ K ∈ strictAlong T (D.E.get i) :: F, IsClosed K := by
    intro K hK
    apply HironakaPrincipalization.isClosed_of_mem_E_geoTransformAlong D hDclosed T K
    rwa [hBoundary]
  have hSlice' : (Subtype.val : U₀ → X) ⁻¹' S =
      (Subtype.val : U₀ → X) ⁻¹' (D.N ∩ D.E.get i) := by simpa only [hi] using hSlice
  exact optional_gamma_chart_protects_equivariant_test_centre P D hPN hNclosed hDclosed U₀ hD hmark i S hSlice'
    Φ hΦsrc O hOt hWindow s t c R R₀ m hs hst hcs hN hDcoords hm hW hE T C π hπ hTest hEq
    F hBoundary hEclosed x hxC hxU

end
end Hironaka.HironakaG4OptionalGammaProtectedBoundary
