import Hironaka.Resolution.HironakaG4RetainedPreparedContinuation

/-! Prepare a finite family of original retained rows using actual compact-relative row services. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparedFold
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower NormalCrossings
  HironakaG4RetainedRelativeLowerService HironakaG4RetainedPreparedContinuation
  HironakaG4RetainedPreparedDefectRerun HironakaG4RetainedPreparedLocalSupport
  HironakaG4OrderedRetainedDefectTrace HironakaActualRetainedBornResidualHistory
  HironakaG4PreparedCentreCoordinates HironakaG4RetainedPreparationTrace
  HironakaG4RetainedPreparationLowerHistory
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  RegularPointDimension AnalyticIrreducibleComponents

/-- A selected-row service on the actual native tuple prepares one more
original row and restores the true distinct defect on a neighbourhood of
the given compact enclosure. -/
def CompactRelativeRetainedRowServicesExist (n d : ℕ) (requireEquivariance : Bool := false) : Prop :=
  ∀ (X : CMfd.{u} n) (N : Set X) (old born : List (Set X)),
    NativeRetainedGeometry N old born →
    (∀ x ∈ N,∃ e ≤ d,RegularAtDim (n := n) N x e) →
    actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅ →
    ∀ (i : Fin old.length) (P : Finset (Fin old.length)), i ∉ P →
      (∀ j ∈ P,RetainedRowPrepared N old born j (.refl : BlowupTower X X)) →
      ∀ (K : Set X),IsCompact K → HasPreparedRetainedDefectExitNear N old born K (insert i P) requireEquivariance [.lower i.val,.defect]

/-- The selected-row service retains a chosen family at every lower leaf. -/
def CompactRelativeRetainedRowServicesExistUsing {n : ℕ} (lower : SharpHistoryPredicate.{u} n) (d : ℕ) (requireEquivariance : Bool := false) : Prop :=
  ∀ (X : CMfd.{u} n) (N : Set X) (old born : List (Set X)),
    NativeRetainedGeometry N old born →
    (∀ x ∈ N,∃ e ≤ d,RegularAtDim (n := n) N x e) →
    actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅ →
    ∀ (i : Fin old.length) (P : Finset (Fin old.length)), i ∉ P →
      (∀ j ∈ P,RetainedRowPrepared N old born j (.refl : BlowupTower X X)) →
      ∀ (K : Set X),IsCompact K → HasPreparedRetainedDefectExitNearUsing lower N old born K (insert i P) requireEquivariance [.lower i.val,.defect]

variable {n : ℕ} {X : CMfd.{u} n}

set_option maxHeartbeats 900000 in
/-- Prepare any finite family of original rows. After each actual phase,
the next service runs on the whole compact fibre with the literal current
carrier, ordered old and born rows, and prepared labels. -/
theorem exists_prepared_retained_rows_in_order_near_compact_using
    (lower : SharpHistoryPredicate.{u} n) (hn : 0 < n) (d : ℕ)
    {requireEquivariance : Bool}
    (hRow : CompactRelativeRetainedRowServicesExistUsing lower d requireEquivariance)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hDim : ∀ x ∈ N,∃ e ≤ d,RegularAtDim (n := n) N x e)
    {K : Set X} (hK : IsCompact K) (indices : List (Fin old.length)) (hIndices : indices.Nodup) :
    HasPreparedRetainedDefectExitNearUsing lower N old born K indices.toFinset requireEquivariance
      (retainedPreparationPhases (indices.map Fin.val)) := by
  induction indices using List.reverseRecOn with
  | nil =>
      exact exists_prepared_retained_defect_exit_near_using lower hn g ∅ (by simp) hK requireEquivariance
  | append_singleton indices i ih =>
      let P := indices.toFinset
      have hi : i ∉ P := by
        intro h
        exact List.disjoint_left.mp hIndices.disjoint (List.mem_toFinset.mp h) (by simp)
      obtain ⟨U,hKU,Y,T,hT,hFullT,hSharpT,hEnd,hPrep,hEqT⟩ := ih hIndices.of_append_left
      let XU := CMfd.of (n := n) U
      let ν := (Subtype.val : U → X)
      let NU := ν ⁻¹' N
      let OU := old.map (ν ⁻¹' ·)
      let BU := born.map (ν ⁻¹' ·)
      let A := geoTransformAlong (geometricTemplate NU BU) T
      let OY := OU.map (strictAlong T)
      let eY : Fin old.length ≃ Fin OY.length := finCongr (by simp [OY,OU])
      let PY := P.map eY.toEmbedding
      let KU := ν ⁻¹' K
      let KY := T.proj ⁻¹' KU
      have gU : NativeRetainedGeometry (X := XU) NU OU BU := g.restrict U
      obtain ⟨hKYcomp,gY,hPY⟩ := prepared_retained_current_on_compact_fibre
        hn g hK U hKU T P hT hFullT hPrep
      have hDimU : ∀ x ∈ NU,∃ e ≤ d,RegularAtDim (n := n) (M := XU) NU x e := by
        intro x hx
        obtain ⟨e,he,hxDim⟩ := hDim x.val hx
        exact ⟨e,he,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hxDim⟩
      have hDimY : ∀ y ∈ A.N,∃ e ≤ d,RegularAtDim (n := n) A.N y e :=
        (carrier_dim_bound_geoTransformAlong (geometricTemplate (X := XU) NU BU) gU.carrier.1
          d hDimU T hT).2
      have hiY : eY i ∉ PY := by
        intro he
        obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp he
        exact hi ((eY.injective hji) ▸ hj)
      have hNext := hRow Y A.N OY A.E gY hDimY hEnd (eY i) PY hiY hPY KY hKYcomp
      have hRows : (indices ++ [i]).toFinset = insert i P := by
        ext j
        simp [P]
      rw [hRows,List.map_append,List.map_singleton,retainedPreparationPhases_append_singleton]
      apply exists_prepared_retained_exit_after_near_using lower hn g U hKU T (insert i P) requireEquivariance
        (retainedPreparationPhases (indices.map Fin.val)) [.lower i.val,.defect] hT hFullT hSharpT (fun h => ⟨(hEqT h).1,(hEqT h).2 hn⟩)
      change HasPreparedRetainedDefectExitNearUsing lower A.N OY A.E KY ((insert i P).map eY.toEmbedding)
        requireEquivariance [.lower i.val,.defect]
      rw [Finset.map_insert]
      change HasPreparedRetainedDefectExitNearUsing lower (X := Y) A.N OY A.E KY (insert (eY i) PY)
        requireEquivariance [.lower (eY i).val,.defect]
      exact hNext

/-- The finite fold with unrestricted lower histories. -/
theorem exists_prepared_retained_rows_in_order_near_compact (hn : 0 < n) (d : ℕ)
    {requireEquivariance : Bool}
    (hRow : CompactRelativeRetainedRowServicesExist.{u} n d requireEquivariance)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hDim : ∀ x ∈ N,∃ e ≤ d,RegularAtDim (n := n) N x e)
    {K : Set X} (hK : IsCompact K) (indices : List (Fin old.length)) (hIndices : indices.Nodup) :
    HasPreparedRetainedDefectExitNear N old born K indices.toFinset requireEquivariance
      (retainedPreparationPhases (indices.map Fin.val)) := by
  let lower : SharpHistoryPredicate.{u} n := fun {_ _} _ _ _ => True
  have hRowUsing : CompactRelativeRetainedRowServicesExistUsing lower d requireEquivariance := by
    intro Y W I C gY hDimY hEmpty i P hi hPrep L hL
    exact (hRow Y W I C gY hDimY hEmpty i P hi hPrep L hL).usingUnrestricted
  exact (exists_prepared_retained_rows_in_order_near_compact_using lower hn d hRowUsing
    g hDim hK indices hIndices).forget

/-- Increasing original order prepares every row and remembers all the
chosen lower histories. -/
theorem exists_all_prepared_retained_rows_near_compact_using
    (lower : SharpHistoryPredicate.{u} n) (hn : 0 < n) (d : ℕ) {requireEquivariance : Bool}
    (hRow : CompactRelativeRetainedRowServicesExistUsing lower d requireEquivariance)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hDim : ∀ x ∈ N,∃ e ≤ d,RegularAtDim (n := n) N x e)
    {K : Set X} (hK : IsCompact K) :
    HasPreparedRetainedDefectExitNearUsing lower N old born K Finset.univ requireEquivariance
      (retainedPreparationPhases (((Finset.univ : Finset (Fin old.length)).sort (· ≤ ·)).map Fin.val)) := by
  let P : Finset (Fin old.length) := Finset.univ
  simpa only [Finset.sort_toFinset] using exists_prepared_retained_rows_in_order_near_compact_using lower hn d
    hRow g hDim hK (P.sort (· ≤ ·)) (P.sort_nodup (· ≤ ·))

/-- Use increasing original label order for the finite family. -/
theorem exists_prepared_retained_rows_near_compact (hn : 0 < n) (d : ℕ)
    {requireEquivariance : Bool}
    (hRow : CompactRelativeRetainedRowServicesExist.{u} n d requireEquivariance)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hDim : ∀ x ∈ N,∃ e ≤ d,RegularAtDim (n := n) N x e)
    {K : Set X} (hK : IsCompact K) (P : Finset (Fin old.length)) :
    HasPreparedRetainedDefectExitNear N old born K P requireEquivariance
      (retainedPreparationPhases ((P.sort (· ≤ ·)).map Fin.val)) := by
  simpa only [Finset.sort_toFinset] using exists_prepared_retained_rows_in_order_near_compact hn d
    hRow g hDim hK (P.sort (· ≤ ·)) (P.sort_nodup (· ≤ ·))

/-- Once the selected-row service is available, every old row is prepared
on one finite actual sharp history near the given compact enclosure. -/
theorem exists_all_prepared_retained_rows_near_compact (hn : 0 < n) (d : ℕ)
    {requireEquivariance : Bool}
    (hRow : CompactRelativeRetainedRowServicesExist.{u} n d requireEquivariance)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hDim : ∀ x ∈ N,∃ e ≤ d,RegularAtDim (n := n) N x e)
    {K : Set X} (hK : IsCompact K) :
    HasPreparedRetainedDefectExitNear N old born K Finset.univ requireEquivariance
      (retainedPreparationPhases (((Finset.univ : Finset (Fin old.length)).sort (· ≤ ·)).map Fin.val)) :=
  exists_prepared_retained_rows_near_compact hn d hRow g hDim hK Finset.univ

end
end Hironaka.HironakaG4RetainedPreparedFold
