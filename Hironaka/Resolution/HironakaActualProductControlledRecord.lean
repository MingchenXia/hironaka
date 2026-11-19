import Hironaka.Resolution.HironakaActualProductStrictTransform
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeControlledTower

/-! The entire literal product controlled record, retaining its chronological
old/horizontal/born boundary. No boundary permutation or weak equivalence is
asserted. Blueprint FIRST: `hironaka-actual-product-controlled-record.tex`. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProductControlledRecord
noncomputable section
open Hironaka.BlowupSequences BlowupTowers ProductComplexManifold
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold
  HironakaActualProjectionTestRecord HironakaActualProductBlowup
  HironakaActualProductStrictTransform HironakaAuxiliaryGraphGeometry
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeControlledTower
open scoped ProductComplexManifold
variable {n : ℕ} {X D : CMfd.{u} n} {C : Set X} {π : D → X}

/-- The actual whole carrier, proper-carrier restricted-colon ideal, mark
and every ordered boundary slot, with horizontal BEFORE the born divisor. -/
theorem product_controlled_record
    (hπ : IsBlowupAlong n C π) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hC : M.IsAdmissibleCentre C) :
    (projectionTest M).geoTransform ((Prod.fst : projectionAmbient X → X) ⁻¹' C) (productMap π) =
      { projectionTest (M.geoTransform C π) with
        E := M.E.map (fun H => (Prod.fst : projectionAmbient D → D) ⁻¹' geoStrictTransform π C H) ++
          [horizontal D, (Prod.fst : projectionAmbient D → D) ⁻¹' (π ⁻¹' C)] } := by
  have hf := isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  have hρ := native_product_blowup hπ
  have hLift : actualLift (A := X) (D := D) (B := projectionAmbient X)
      (D' := projectionAmbient D) hf hπ hρ = (Prod.fst : projectionAmbient D → D) := by
    apply Eq.symm
    exact actualLift_unique (A := X) (D := D) (B := projectionAmbient X)
      (D' := projectionAmbient D) hf hπ hρ Prod.fst
      (contMDiff_fst (n := n) (m := 1) (X := D) (Y := ComplexModel 1)) rfl
  have hWhole := markedPullback_geoTransform_actual_relative
    (X := X) (D := D) (Y := projectionAmbient X) (D' := projectionAmbient D)
    hf hπ hρ M hM hC
  rw [hLift] at hWhole
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact congrArg (fun Q => Q.N) hWhole
  · have hOld : M.E.map (fun H => geoStrictTransform (productMap π)
          ((Prod.fst : projectionAmbient X → X) ⁻¹' C)
          ((Prod.fst : projectionAmbient X → X) ⁻¹' H)) =
        M.E.map (fun H => (Prod.fst : projectionAmbient D → D) ⁻¹' geoStrictTransform π C H) :=
      List.map_congr_left fun H _ => product_strictTransform H
    change ((M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]).map
        (geoStrictTransform (productMap π) ((Prod.fst : projectionAmbient X → X) ⁻¹' C))) ++
        [(productMap π) ⁻¹' ((Prod.fst : projectionAmbient X → X) ⁻¹' C)] = _
    simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons, List.map_nil]
    rw [hOld, horizontal_strictTransform hπ, List.append_assoc]
    rfl
  · exact congrArg (fun Q => Q.ideal) hWhole
  · exact congrArg (fun Q => Q.d) hWhole

end
end Hironaka.HironakaActualProductControlledRecord
