import Hironaka.Resolution.HironakaG34DriverBaseCases

/-! # The smaller-dimensional sharp theorem's output as a lower cleanup (G4K1B, T-L residual in IH form)

Lane G34 (run 0080, round 5).  Blueprint: `hironaka-g34-resume-lower-template-bridge.tex`.

The sharp theorem (as produced by `exists_actual_sharp_cleanup_of_certified_lower_cleanups` /
`exists_actual_sharp_cleanup_dim_one`) states its tests with the TWO templates `(Z, [])` and
`(univ, F)`; the lower cleanup of route (L) uses the single lower template `(Z, F)`.

* `lowerTemplate_test_of_two_tests`: the two tests give the single lower test (only the divisor
  depends on the boundary list; `DropMembers.cosupp_geoTransformAlong_withE` and the boundary
  decomposition).
* `gammaCertifiedLowerCleanup_of_sharp_output`: the output of the sharp theorem for the lower problem
  `(S_j, F_j)` (two tests, `CurrentSharpCentres S_j F_j`, final normal crossings), together with final
  density and Gamma protection, is a Gamma-certified lower cleanup.  So the residual
  `GammaCertifiedLowerCleanupsExist` is exactly: the smaller-dimensional sharp theorem for `(S_j, F_j)`
  plus final density plus protection at Gamma points. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34LowerTemplateBridge
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail
  HomogenizedGlueingTower HironakaG34LowerCleanupLift HironakaG34GammaCertifiedLift

variable {n : ℕ} {Y : CMfd.{u} n}

/-- **The two zero-mark tests give the single lower test.** -/
theorem lowerTemplate_test_of_two_tests (Z : Set Y) (F : List (Set Y)) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate Z []) R →
      IsGeoTestTower (geometricTemplate (univ : Set Y) F) R →
      IsGeoTestTower (geometricTemplate Z F) R
  | _, .refl, _, _ => trivial
  | _, .step R C π hπ, h1, h2 => by
      obtain ⟨h10, hA1⟩ := (isGeoTestTower_step_iff _ R C π hπ).mp h1
      obtain ⟨h20, hA2⟩ := (isGeoTestTower_step_iff _ R C π hπ).mp h2
      refine (isGeoTestTower_step_iff _ R C π hπ).mpr
        ⟨lowerTemplate_test_of_two_tests Z F R h10 h20, ?_⟩
      have hc := DropMembers.cosupp_geoTransformAlong_withE (geometricTemplate Z []) F R
      have hE : (geoTransformAlong (geometricTemplate Z F) R).E =
          (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E := by
        rw [HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
            (geometricTemplate Z F) (geometricTemplate (univ : Set Y) []) rfl R,
          HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
            (geometricTemplate (univ : Set Y) F) (geometricTemplate (univ : Set Y) []) rfl R]
        rfl
      refine ⟨hA1.1, ?_, ?_⟩
      · intro x hx
        have h := hA1.2.1 hx
        change x ∈ (geoTransformAlong ({ geometricTemplate Z [] with E := F } : MarkedIdeal n Y) R).cosupp
        rw [hc]
        exact h
      · rw [hE]
        exact hA2.2.2

variable {X : CMfd.{u} n}

/-- **The smaller-dimensional sharp output is a lower cleanup.**  At a prefix `T`, a tail `R` of the
lower problem `(Z, F) = (S_j, F_j)` with the two zero-mark tests, lower sharp centres, final normal
crossings of the strict lower carrier with the final lower boundary, final density and Gamma protection is
a Gamma-certified lower cleanup. -/
theorem gammaCertifiedLowerCleanup_of_sharp_output {W : Set X} {E : List (Set X)}
    (P : Finset (Fin E.length)) (j : Fin E.length) (T : BlowupTower X Y) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
    let B := geoTransformAlong (geometricTemplate W []) T
    let F := (E.map (strictAlong T)).eraseIdx j.val ++ B.E
    let Z := A.N ∩ A.ideal.zeroLocus
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate Z []) R →
      IsGeoTestTower (geometricTemplate (univ : Set Y) F) R →
      CurrentSharpCentres Z F R →
      HasNormalCrossings n (geoTransformAlong (geometricTemplate Z []) R).N
        (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E →
      (geoTransformAlong (geometricTemplate Z []) R).N ⊆
        closure ((geoTransformAlong (geometricTemplate Z []) R).N \
          ⋃ D ∈ (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E, D) →
      GammaProtectedTail W E P T R →
      GammaCertifiedLowerCleanup W E P j T R := by
  intro A B F Z Q R h1 h2 hS hNC hDen hG
  have hN : (geoTransformAlong (geometricTemplate Z F) R).N =
      (geoTransformAlong (geometricTemplate Z []) R).N := by
    rw [N_geoTransformAlong, N_geoTransformAlong]
    rfl
  have hE : (geoTransformAlong (geometricTemplate Z F) R).E =
      (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E := by
    rw [HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
        (geometricTemplate Z F) (geometricTemplate (univ : Set Y) []) rfl R,
      HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
        (geometricTemplate (univ : Set Y) F) (geometricTemplate (univ : Set Y) []) rfl R]
    rfl
  refine ⟨lowerTemplate_test_of_two_tests Z F R h1 h2, hS, ?_, ?_, hG⟩
  · show HasNormalCrossings n (geoTransformAlong (geometricTemplate Z F) R).N
      (geoTransformAlong (geometricTemplate Z F) R).E
    rw [hN, hE]
    exact hNC
  · show (geoTransformAlong (geometricTemplate Z F) R).N ⊆
      closure ((geoTransformAlong (geometricTemplate Z F) R).N \
        ⋃ D ∈ (geoTransformAlong (geometricTemplate Z F) R).E, D)
    rw [hN, hE]
    exact hDen

end
end Hironaka.HironakaG34LowerTemplateBridge
