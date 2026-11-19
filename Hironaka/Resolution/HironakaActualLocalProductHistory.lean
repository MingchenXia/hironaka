import Hironaka.Resolution.HironakaActualProductControlledRecord
import Hironaka.Resolution.HironakaActualProductAdmissibility
import Hironaka.Resolution.HironakaActualBoundarySlotReindex
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism

/-! Actual product histories, their entire chronological records and every
prefix. Current projected weak equivalence requires TRUE INITIAL projected
weak equivalence; no ordinary-to-projected shortcut is asserted.
Blueprint FIRST: `hironaka-actual-local-product-history.tex`. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualLocalProductHistory
noncomputable section
open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupStrictSubmanifold HironakaActualProjectionTestRecord HironakaActualProductBlowup
  HironakaActualProductStrictTransform HironakaActualProductControlledRecord
  HironakaActualProductAdmissibility HironakaActualBoundarySlotReindex
  MarkedIdealEquivalence.MarkedIdeal MarkedIdealOpenBiholomorphism
open scoped ProductComplexManifold
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Chosen geometrically from the actual tower, BEFORE querying any marked head. -/
def productTower : {Y : CMfd.{u} n} → BlowupTower X Y →
    BlowupTower (projectionAmbient X) (projectionAmbient Y)
  | _, .refl => .refl
  | _, .step T C π hπ =>
      .step (productTower T) (Prod.fst ⁻¹' C) (productMap π) (native_product_blowup hπ)

/-- All original old slots, transformed without filtering. -/
def oldBoundaryAlong (E : List (Set X)) :
    {Y : CMfd.{u} n} → BlowupTower X Y → List (Set Y)
  | _, .refl => E
  | _, .step T C π _ => (oldBoundaryAlong E T).map (geoStrictTransform π C)

/-- Every born slot, in its original chronological position. -/
def bornBoundaryAlong : {Y : CMfd.{u} n} → BlowupTower X Y → List (Set Y)
  | _, .refl => []
  | _, .step T C π _ => (bornBoundaryAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C]

private def pulledOld (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    List (Set (projectionAmbient Y)) :=
  (oldBoundaryAlong M.E T).map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·)

private def pulledBorn (T : BlowupTower X Y) : List (Set (projectionAmbient Y)) :=
  (bornBoundaryAlong T).map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·)

/-- Full projection fields with the actual old/H/born chronology. -/
def chronologicalProduct (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    MarkedIdeal (n+1) (projectionAmbient Y) :=
  { projectionTest (geoTransformAlong M T) with
    E := pulledOld M T ++ [horizontal Y] ++ pulledBorn T }

theorem product_geometry (T : BlowupTower X Y) :
    (productTower T).length = T.length ∧ (productTower T).proj = productMap T.proj := by
  induction T with
  | refl =>
    refine ⟨rfl,?_⟩
    funext p
    exact (Prod.eta p).symm
  | step T C π hπ ih =>
    refine ⟨congrArg (fun r => r+1) ih.1,?_⟩
    change (productTower T).proj ∘ productMap π = productMap (T.proj ∘ π)
    rw [ih.2]
    rfl

theorem productTower_append (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    productTower (T.append S) = (productTower T).append (productTower S) := by
  induction S with
  | refl => rfl
  | step S C π hπ ih =>
    change BlowupTower.step (productTower (T.append S)) _ _ _ =
      BlowupTower.step ((productTower T).append (productTower S)) _ _ _
    rw [ih]

theorem source_boundary_dictionary (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    (geoTransformAlong M T).E = oldBoundaryAlong M.E T ++ bornBoundaryAlong T ∧
      (oldBoundaryAlong M.E T).length = M.E.length ∧ (bornBoundaryAlong T).length = T.length := by
  induction T with
  | refl => exact ⟨(List.append_nil _).symm,rfl,rfl⟩
  | step T C π hπ ih =>
    refine ⟨?_,?_,?_⟩
    · change (geoTransformAlong M T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C] = _
      rw [ih.1,List.map_append,List.append_assoc]
      rfl
    · change ((oldBoundaryAlong M.E T).map (geoStrictTransform π C)).length = _
      rw [List.length_map,ih.2.1]
    · change ((bornBoundaryAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C]).length = T.length+1
      simp only [List.length_append,List.length_map,List.length_singleton,ih.2.2]

private theorem standard_boundary (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    (projectionTest (geoTransformAlong M T)).E = pulledOld M T ++ pulledBorn T ++ [horizontal Y] := by
  change (geoTransformAlong M T).E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ _ = _
  rw [(source_boundary_dictionary M T).1,List.map_append]
  rfl

private theorem slots_congr {α : Type*} {E F A B : List α} (hE : E = A) (hF : F = B)
    (e : Fin A.length ≃ Fin B.length) (he : ∀ i, A.get i = B.get (e i)) :
    ∃ e' : Fin E.length ≃ Fin F.length, ∀ i, E.get i = F.get (e' i) := by
  subst A
  subst B
  exact ⟨e,he⟩

private theorem standard_chronological_slots (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    ∃ e : Fin (projectionTest (geoTransformAlong M T)).E.length ≃
        Fin (chronologicalProduct M T).E.length,
      ∀ i, (projectionTest (geoTransformAlong M T)).E.get i = (chronologicalProduct M T).E.get (e i) := by
  exact slots_congr (standard_boundary M T) rfl
    (boundarySlotEquiv (pulledOld M T) (pulledBorn T) (horizontal Y))
    (boundarySlotEquiv_get (pulledOld M T) (pulledBorn T) (horizontal Y))

private theorem same_fields_admissible {A B : MarkedIdeal n X}
    (hN : A.N = B.N) (hI : A.ideal = B.ideal) (hd : A.d = B.d)
    (e : Fin A.E.length ≃ Fin B.E.length) (he : ∀ i, A.E.get i = B.E.get (e i)) (C : Set X) :
    A.IsAdmissibleCentre C ↔ B.IsAdmissibleCentre C := by
  have hcosupp : A.cosupp = B.cosupp := by simp only [cosupp,hN,hI,hd]
  simp only [IsAdmissibleCentre,hcosupp,centre_nc_reindex_iff e he C]

/-- Every actual product step is internally tested, with the ENTIRE current
record and every old, horizontal and born slot fixed at that same prefix. -/
theorem product_test_and_record (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    IsGeoTestTower (projectionTest M) (productTower T) ∧
      geoTransformAlong (projectionTest M) (productTower T) = chronologicalProduct M T := by
  induction T with
  | refl =>
    refine ⟨trivial,?_⟩
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · change (projectionTest M).E =
        (M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]) ++ []
      rw [List.append_nil]
      rfl
    · rfl
    · rfl
  | @step Y Z T C π hπ ih =>
    obtain ⟨hProd,hRecord⟩ := ih hT.1
    have hWF := isWellFormed_geoTransformAlong hM T hT.1
    have hStd := projection_test_admissible hWF.isCoherent hT.2
    obtain ⟨e,he⟩ := standard_chronological_slots M T
    have hChrono : (chronologicalProduct M T).IsAdmissibleCentre
        ((Prod.fst : projectionAmbient Y → Y) ⁻¹' C) :=
      (same_fields_admissible (A := projectionTest (geoTransformAlong M T))
        (B := chronologicalProduct M T) rfl rfl rfl e he _).mp hStd
    have hActual : (geoTransformAlong (projectionTest M) (productTower T)).IsAdmissibleCentre
        ((Prod.fst : projectionAmbient Y → Y) ⁻¹' C) := by
      rw [hRecord]
      exact hChrono
    refine ⟨⟨hProd,hActual⟩,?_⟩
    change (geoTransformAlong (projectionTest M) (productTower T)).geoTransform
      ((Prod.fst : projectionAmbient Y → Y) ⁻¹' C) (productMap π) = _
    rw [hRecord]
    have hOne := product_controlled_record hπ (geoTransformAlong M T) hWF hT.2
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · exact congrArg (fun Q => Q.N) hOne
    · have hStrict (A : Set Y) :
          geoStrictTransform (productMap π) ((Prod.fst : projectionAmbient Y → Y) ⁻¹' C)
            ((Prod.fst : projectionAmbient Y → Y) ⁻¹' A) =
          (Prod.fst : projectionAmbient Z → Z) ⁻¹' geoStrictTransform π C A :=
        product_strictTransform (X := Y) (D := Z) (C := C) (π := π) A
      change (((oldBoundaryAlong M.E T).map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++
          [horizontal Y] ++ (bornBoundaryAlong T).map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·)).map
          (geoStrictTransform (productMap π) ((Prod.fst : projectionAmbient Y → Y) ⁻¹' C))) ++
          [(productMap π) ⁻¹' ((Prod.fst : projectionAmbient Y → Y) ⁻¹' C)] =
        ((oldBoundaryAlong M.E T).map (geoStrictTransform π C)).map
          ((Prod.fst : projectionAmbient Z → Z) ⁻¹' ·) ++ [horizontal Z] ++
          (((bornBoundaryAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C]).map
            ((Prod.fst : projectionAmbient Z → Z) ⁻¹' ·))
      simp only [List.map_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil,
        hStrict,horizontal_strictTransform hπ,List.append_assoc]
      rfl
    · exact congrArg (fun Q => Q.ideal) hOne
    · exact congrArg (fun Q => Q.d) hOne

private theorem projection_boundary_injective {M N : MarkedIdeal n X}
    (h : (projectionTest M).E = (projectionTest N).E) : M.E = N.E := by
  have hmap : M.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) =
      N.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) := List.append_cancel_right h
  have hinj : Function.Injective (fun A : Set X => (Prod.fst : projectionAmbient X → X) ⁻¹' A) := by
    intro A B hab
    ext x
    exact Iff.of_eq (congrArg (fun S : Set (projectionAmbient X) => (x,0) ∈ S) hab)
  exact List.map_injective_iff.mpr hinj hmap

private theorem chronological_update (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    { chronologicalProduct M T with E := (projectionTest (geoTransformAlong M T)).E } =
      projectionTest (geoTransformAlong M T) := by
  rfl

/-- A TRUE initial projected comparison passes along the SAME actual LOCAL
product history and then through one simultaneous literal common boundary. -/
theorem current_projected_wEquiv (M N : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : N.IsWellFormed)
    (hProjected : WEquiv (projectionTest M) (projectionTest N))
    (T : BlowupTower X Y) (hTM : IsGeoTestTower M T) (hTN : IsGeoTestTower N T) :
    WEquiv (projectionTest (geoTransformAlong M T)) (projectionTest (geoTransformAlong N T)) := by
  obtain ⟨hProdM,hRecordM⟩ := product_test_and_record M hM T hTM
  obtain ⟨_hProdN,hRecordN⟩ := product_test_and_record N hN T hTN
  have hCurrent := hProjected.geoTransformAlong hProdM
  rw [hRecordM,hRecordN] at hCurrent
  have hSourceE : M.E = N.E := projection_boundary_injective hProjected.1
  have hCurrentSourceE := E_geoTransformAlong_eq hSourceE T
  have hF : (projectionTest (geoTransformAlong M T)).E =
      (projectionTest (geoTransformAlong N T)).E := by
    change (geoTransformAlong M T).E.map _ ++ _ = (geoTransformAlong N T).E.map _ ++ _
    rw [hCurrentSourceE]
  obtain ⟨e,he⟩ := standard_chronological_slots M T
  have hGet (j : Fin (chronologicalProduct M T).E.length) :
      (chronologicalProduct M T).E.get j =
        (projectionTest (geoTransformAlong M T)).E.get (e.symm j) := by
    simpa only [e.apply_symm_apply] using (he (e.symm j)).symm
  have hReordered := simultaneous_boundary_wEquiv hCurrent
    (projectionTest (geoTransformAlong M T)).E e.symm hGet
  rw [chronological_update] at hReordered
  have hUpdateN : { chronologicalProduct N T with E := (projectionTest (geoTransformAlong M T)).E } =
      projectionTest (geoTransformAlong N T) := by
    rw [hF]
    rfl
  rw [hUpdateN] at hReordered
  exact hReordered

/-- EVERY genuine factor prefix of the tested LOCAL history, with the same
product factors, full records, tests, and current projected comparison. -/
theorem product_prefix_data (M N : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : N.IsWellFormed)
    (hProjected : WEquiv (projectionTest M) (projectionTest N))
    (P : BlowupTower X Y) (S : BlowupTower Y Z)
    (hPM : IsGeoTestTower M (P.append S)) (hPN : IsGeoTestTower N (P.append S)) :
    productTower (P.append S) = (productTower P).append (productTower S) ∧
      (IsGeoTestTower (projectionTest M) (productTower P) ∧
        geoTransformAlong (projectionTest M) (productTower P) = chronologicalProduct M P) ∧
      (IsGeoTestTower (projectionTest N) (productTower P) ∧
        geoTransformAlong (projectionTest N) (productTower P) = chronologicalProduct N P) ∧
      WEquiv (projectionTest (geoTransformAlong M P)) (projectionTest (geoTransformAlong N P)) := by
  have hMprefix := ((isGeoTestTower_append_iff M P S).mp hPM).1
  have hNprefix := ((isGeoTestTower_append_iff N P S).mp hPN).1
  exact ⟨productTower_append P S,product_test_and_record M hM P hMprefix,
    product_test_and_record N hN P hNprefix,
    current_projected_wEquiv M N hM hN hProjected P hMprefix hNprefix⟩

end
end Hironaka.HironakaActualLocalProductHistory
