import Hironaka.Resolution.HironakaActualDistinctCountOffCentre
import Hironaka.Resolution.HironakaActualOriginalOrderOffFootprint

/-! One internally constructed ORIGINAL global block strictly decreases the
genuine current distinct-defect product order. Original chronological rows,
all old/born ambient slots and sharp original-good-complement avoidance are
retained. A full iterated mixed-phase driver is not asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGlobalDistinctOrderDrop
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HomogenizedGlueingTower
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualInitialFullCompatibility
  HironakaSharpOriginalFirstMemberRelativeStrict HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaActualGlobalTopOrderBlock HironakaActualOriginalOrderOffFootprint
  HironakaActualDistinctCountOffCentre HironakaActualFiniteCompactHistoryExtension
  HironakaAdmissibleSequence HironakaAdmissibleCalculus RestrictEmptyTower
  RelativePrincipalizationSpan RestrictedIdealExtension DivisorExponentAlong
variable {n : ℕ} {X : CMfd.{u} n}

/-- Literal original chronological quotient classes off the ORIGINAL
centre footprint, including every empty step. -/
theorem original_count_eq_initial_off_footprint
    (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃H∈E,H)) (D : Set X) :
    ∀{Y : CMfd.{u} n}(S : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) S → CentresOver D S →
      ∀y∈(geoTransformAlong (geometricTemplate W []) S).N,S.proj y∉D →
        actualDistinctProperCount (fun i : Fin E.length =>
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) S).ideal) y=
          distinctProperTraceGermCount (n:=n) W E (S.proj y)
  | _,.refl,_hS,_hOver,y,_hyN,_hy => initial_actual_distinct_count_eq_source W E y
  | _,.step S C π hπ,hS,hOver,y,hyN,hy => by
    have hw : (geometricTemplate W []).IsWellFormed:=
      ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwS:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw S hS.1
    have hyC : π y∉C:=fun hc=>hy (hOver.2 hc)
    have hyN' : π y∈(geoTransformAlong (geometricTemplate W []) S).N:=
      geoStrictTransform_subset_preimage hπ.contMDiff.continuous hwS.isClosedSubmanifold_N.1 hyN
    exact (original_chronological_distinct_count_off_centre hn hW hE hdense S hS.1 hπ hyN hyC).trans
      (original_count_eq_initial_off_footprint hn hW hE hdense D S hS.1 hOver.1 (π y) hyN' hy)

private theorem current_carrier_projects {W : Set X} (hW : IsClosed W) :
    ∀{Y : CMfd.{u} n}(S : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate W []) S).N⊆S.proj ⁻¹' W
  | _,.refl => Set.Subset.rfl
  | _,.step S C π hπ => by
    intro y hy
    have hClosed : IsClosed (geoTransformAlong (geometricTemplate W []) S).N:=by
      rw [N_geoTransformAlong]
      exact MemberInterTowerAlong.isClosed_strictAlong S hW
    exact current_carrier_projects hW S
      (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hClosed hy)

/-- Original data construct ONE globally sharp top-defect order-drop
block. No current count/order/centre comparison is a hypothesis. -/
theorem exists_actual_global_distinct_order_drop
    (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃H∈E,H)) (d : ℕ)
    (hreg : ∀x∈W,RegularAtDim (n:=n) W x (d+1)) (hcomp : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃(q : ℕ)(U : Opens X)(D : Set X)(Y : CMfd.{u} n)(S : BlowupTower X Y),
      1≤q ∧ D.Nonempty ∧ IsCompact D ∧ D⊆U ∧ D⊆originalSharpBadLocus (n:=n) W E ∧
      D=originalDistinctDefectPhase W E ∩ (originalMemberProductMarked W E q).cosupp ∧
      (∀x∈originalDistinctDefectPhase W E,ordinaryTraceOrder W (originalMemberProduct E) x≤q) ∧
      IsGeoTestTower (originalMemberProductMarked W E q) S ∧
      IsGeoTestTower (geometricTemplate W []) S ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) S ∧
      CentresOver D S ∧ CompactCentres S ∧
      (∀y∈chronologicalDistinctDefect W E S,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) S).N
          (chronologicalMemberProduct W E S) y<q) ∧
      IsAdmissibleBlowupSequence n X E (originalSharpBadLocus (n:=n) W E) Y S.proj
        (geoTransformAlong (geometricTemplate (univ : Set X) E) S).E ∧
      IsProperMap S.proj ∧ IsIsomorphismOver n S.proj (originalSharpBadLocus (n:=n) W E)ᶜ := by
  obtain ⟨q,U,D,hq,hDne,hDK,hDU,hDBad,hDeq,hmax,_hDq,Y,S,hS,hGeom,hFull,hOver,hCompact,hLow,_hNative⟩:=
    exists_actual_global_top_order_block hn hW hE hdense d hreg hcomp hne
  have hDrop : ∀y∈chronologicalDistinctDefect W E S,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) S).N
        (chronologicalMemberProduct W E S) y<q := by
    intro y hy
    have hyN : y∈(geoTransformAlong (geometricTemplate W []) S).N:=hy.1
    by_cases hyU : S.proj y∈U
    · exact hLow ⟨y,hyU⟩ hyN
    · have hyD : S.proj y∉D:=fun h=>hyU (hDU h)
      have hOrd:=original_product_order_eq_initial_off_footprint hn hW hE hdense hq D S hS hGeom hOver y hyD
      have hCount:=original_count_eq_initial_off_footprint hn hW hE hdense D S hGeom hOver y hyN hyD
      have hyW : S.proj y∈W:=current_carrier_projects hW.1 S hyN
      have hBad : S.proj y∈originalDistinctDefectPhase W E := by
        refine ⟨hyW,?_⟩
        rw [←hCount,←hOrd,chronological_product_eq_actual_family_product]
        exact hy.2
      rw [hOrd]
      by_contra hnot
      have hge : q≤ordinaryTraceOrder W (originalMemberProduct E) (S.proj y):=Nat.le_of_not_gt hnot
      have hCos : S.proj y∈(originalMemberProductMarked W E q).cosupp:=
        (ordinaryTraceOrder_cosupport_iff hW (isCoherent_originalMemberProduct hn hE)
          (fun _ hx=>originalMemberProduct_isNonzeroAlongAt hn hE hdense hx) hyW q).mpr hge
      exact hyD (hDeq.symm ▸ ⟨hBad,hCos⟩)
  have hAdmD:=isAdmissibleBlowupSequence_proj (geometricTemplate (univ : Set X) E) D S hFull hOver
  have hAdm:=hAdmD.mono hDBad
  exact ⟨q,U,D,Y,S,hq,hDne,hDK,hDU,hDBad,hDeq,hmax,hS,hGeom,hFull,hOver,hCompact,hDrop,hAdm,
    isProperMap_of_isBlowupSequence hAdm.isBlowupSequence,
    HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm⟩

end
end Hironaka.HironakaActualGlobalDistinctOrderDrop
