import Hironaka.Resolution.HironakaActualGlobalDistinctOrderDrop

/-! A genuine strict natural-valued measured decrease for one internally
constructed block on the SAME original chronological row family. Arbitrary
mixed-prefix iteration and full joint sharp termination remain separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualChronologicalDefectMeasure
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualInitialFullCompatibility
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaActualGlobalDistinctOrderDrop
  HironakaActualOriginalOrderOffFootprint HironakaActualFiniteCompactHistoryExtension
  HironakaAdmissibleSequence HironakaAdmissibleCalculus RestrictEmptyTower
variable {n : ℕ} {X : CMfd.{u} n}

/-- The supremum uses actual current product orders of the unchanged
original chronological rows, with zero for the empty defect. -/
def chronologicalDefectMeasure (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : ℕ :=
  sSup ((fun y=>ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
    (chronologicalMemberProduct W E T) y) '' chronologicalDistinctDefect W E T)

private theorem measure_le (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (b : ℕ)
    (hb : ∀y∈chronologicalDistinctDefect W E T,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) y≤b) : chronologicalDefectMeasure W E T≤b := by
  apply csSup_le'
  rintro _ ⟨y,hy,rfl⟩
  exact hb y hy

private theorem initial_measure_eq_top (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃H∈E,H)) {q : ℕ}
    (hbound : ∀x∈originalDistinctDefectPhase W E,ordinaryTraceOrder W (originalMemberProduct E) x≤q)
    (ha : ∃a∈originalDistinctDefectPhase W E,ordinaryTraceOrder W (originalMemberProduct E) a=q) :
    chronologicalDefectMeasure W E (.refl : BlowupTower X X)=q := by
  have hOrd (x : X) : ordinaryTraceOrder W (chronologicalMemberProduct W E (.refl : BlowupTower X X)) x=
      ordinaryTraceOrder W (originalMemberProduct E) x := by
    exact original_product_order_eq_initial_off_footprint hn hW hE hdense (q:=1) le_rfl
      (∅ : Set X) (.refl : BlowupTower X X) trivial trivial trivial x (by simp)
  have hDef:=initial_actual_defect_eq_source_first hn hW hE hdense
  have hb : ∀x∈chronologicalDistinctDefect W E (.refl : BlowupTower X X),
      ordinaryTraceOrder W (chronologicalMemberProduct W E (.refl : BlowupTower X X)) x≤q := by
    intro x hx
    rw [hOrd]
    exact hbound x (hDef ▸ hx)
  refine le_antisymm (measure_le W E .refl q hb) ?_
  obtain ⟨a,ha,hqa⟩:=ha
  apply le_csSup (s := (fun x=>ordinaryTraceOrder W
    (chronologicalMemberProduct W E (.refl : BlowupTower X X)) x) ''
      chronologicalDistinctDefect W E (.refl : BlowupTower X X))
  · exact ⟨q,by rintro _ ⟨x,hx,rfl⟩;exact hb x hx⟩
  · exact ⟨a,hDef.symm ▸ ha,(hOrd a).trans hqa⟩

theorem exists_actual_original_chronological_measure_drop
    (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃H∈E,H)) (d : ℕ)
    (hreg : ∀x∈W,RegularAtDim (n:=n) W x (d+1)) (hcomp : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃(q : ℕ)(D : Set X)(Y : CMfd.{u} n)(S : BlowupTower X Y),
      1≤q ∧ D.Nonempty ∧ IsCompact D ∧ D⊆originalSharpBadLocus (n:=n) W E ∧
      IsGeoTestTower (originalMemberProductMarked W E q) S ∧
      IsGeoTestTower (geometricTemplate W []) S ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) S ∧
      CentresOver D S ∧ CompactCentres S ∧
      chronologicalDefectMeasure W E (.refl : BlowupTower X X)=q ∧
      chronologicalDefectMeasure W E S<chronologicalDefectMeasure W E (.refl : BlowupTower X X) ∧
      IsAdmissibleBlowupSequence n X E (originalSharpBadLocus (n:=n) W E) Y S.proj
        (geoTransformAlong (geometricTemplate (univ : Set X) E) S).E ∧
      IsProperMap S.proj ∧ IsIsomorphismOver n S.proj (originalSharpBadLocus (n:=n) W E)ᶜ := by
  obtain ⟨q,_U,D,Y,S,hq,hDne,hDK,_hDU,hDBad,hDeq,hmax,hS,hGeom,hFull,hOver,hCompact,hDrop,hAdm,hProper,hIso⟩:=
    exists_actual_global_distinct_order_drop hn hW hE hdense d hreg hcomp hne
  obtain ⟨a,ha⟩:=hDne
  have haBad : a∈originalDistinctDefectPhase W E:=(hDeq ▸ ha).1
  have haCos : a∈(originalMemberProductMarked W E q).cosupp:=(hDeq ▸ ha).2
  have hge : q≤ordinaryTraceOrder W (originalMemberProduct E) a:=
    (ordinaryTraceOrder_cosupport_iff hW (isCoherent_originalMemberProduct hn hE)
      (fun _ hx=>originalMemberProduct_isNonzeroAlongAt hn hE hdense hx) haBad.1 q).mp haCos
  have hInitial:=initial_measure_eq_top hn hW hE hdense hmax
    ⟨a,haBad,le_antisymm (hmax a haBad) hge⟩
  have hLe : chronologicalDefectMeasure W E S≤q-1:=
    measure_le W E S (q-1) (fun y hy=>by have h:=hDrop y hy;omega)
  have hStrict : chronologicalDefectMeasure W E S<chronologicalDefectMeasure W E (.refl : BlowupTower X X):=by
    rw [hInitial]
    omega
  exact ⟨q,D,Y,S,hq,⟨a,ha⟩,hDK,hDBad,hS,hGeom,hFull,hOver,hCompact,hInitial,hStrict,hAdm,hProper,hIso⟩

end
end Hironaka.HironakaActualChronologicalDefectMeasure
