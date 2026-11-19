import Hironaka.Resolution.HironakaG4OriginalGammaTailProtection

/-! Combine single-row protected histories for an arbitrary finite family. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OriginalGammaFamilyProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaG34MaskFoldEquivariance
  HironakaSharpActualFiniteChronologicalHistory HironakaG4PreparedCentreCoordinates
  HironakaG4OriginalGammaTailProtection HironakaG34LowerCleanupLift HironakaG34PreparedRowEmptyTail

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- If every selected row has its singleton protected tail, the same actual
tower has the protected tail for the entire selected finite family. -/
theorem protectedTail_of_singletons (W : Set X) (E : List (Set X))
    (I : Finset (Fin E.length)) (T : BlowupTower X Y) :
    ∀ {Z : CMfd.{u} n} (R : BlowupTower Y Z),
      (∀ i ∈ I, ProtectedTail W E {i} T R) → ProtectedTail W E I T R
  | _, .refl, _ => trivial
  | _, .step R C π hπ, h => by
    refine ⟨protectedTail_of_singletons W E I T R (fun i hi => (h i hi).1), ?_⟩
    intro i hi x hx
    exact (h i hi).2 i (by simp) x hx

/-- One equivariant marked-one lower test tower protects every selected
prepared original row whose recorded monomial germ enters the lower ideal on
the intersection with the lower source carrier. -/
theorem original_gamma_tail_protects_prepared_family
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (I : Finset (Fin E.length)) (j : Fin E.length) (hne : ∀ i ∈ I, j ≠ i)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hPrep : ∀ i ∈ I, ActualRowPrepared W E i T)
    (P : MarkedIdeal n Y) (hP : P.IsWellFormed) (hmark : P.d = 1)
    (hPcarrier : P.N = (geoTransformAlong (geometricTemplate W []) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
    (hle : ∀ i ∈ I, let A := geoTransformAlong (geometricTemplate W []) T
      let old := E.map (strictAlong T)
      let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      ∀ y ∈ (A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) ∩ P.N,
        ∀ g, (oldMonomialPart A.N old A.E oi).mem y g → P.ideal.mem y g)
    (R : BlowupTower Y Z) (hTest : IsGeoTestTower P R)
    (hEq : IsEquivariant P.N ((E.map (strictAlong T)) ++ (geoTransformAlong (geometricTemplate W []) T).E) R)
    (hUpper : IsGeoTestTower (geometricTemplate W []) (T.append R))
    (hAmbient : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R)) :
    (∀ i ∈ I, ActualRowPrepared W E i (T.append R) ∧
      ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus =
        strictAlong R ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus))) ∧
      ProtectedTail W E I T R := by
  have hEach : ∀ i ∈ I, ActualRowPrepared W E i (T.append R) ∧
      ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus =
        strictAlong R ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)) ∧
      ProtectedTail W E {i} T R := by
    intro i hi
    exact original_gamma_tail_protects_prepared_row hn hW hE hdense i j (hne i hi) T hT hFull
      (hPrep i hi) P hP hmark hPcarrier (hle i hi) R hTest hEq hUpper hAmbient
  refine ⟨fun i hi => ⟨(hEach i hi).1,(hEach i hi).2.1⟩, ?_⟩
  exact protectedTail_of_singletons W E I T R (fun i hi => (hEach i hi).2.2)

end
end Hironaka.HironakaG4OriginalGammaFamilyProtection
