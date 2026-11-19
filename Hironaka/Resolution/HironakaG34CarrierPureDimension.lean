import Hironaka.Resolution.HironakaG34PreparedRowEmptyTail
import Hironaka.Resolution.HironakaActualSharpBadFirstMaximumBlowup

/-! # The current carrier keeps pure dimension along a test tower; the lower entry after the
carrier phase

Lane G34 (run 0080, round 2).  Blueprint: `hironaka-g34-resume-carrier-pure-dimension.tex`.

* `geoTransformAlong_N_regularAtDim` (obligation O4 of `G4K1B-CONTROL-FLOW.md`): if the carrier of a
  marked ideal is closed and regular of dimension `k` at each of its points, then so is the carrier
  of its transform along every test tower (each strict transform of a submanifold containing the
  centre is a submanifold of the same dimension).
* `actual_carrier_regularAtDim`: in particular the current carrier `N` of an actual W-test prefix is
  pure of dimension `d+1` when `W` is: this is the hypothesis `hReg` of the held lower entries
  `actual_compact_sharp_bad_source` and `exists_actual_first_sharp_bad_maximum_blowup`.
* `exists_actual_carrier_phase_lower_entry`: from an actual prefix with current sharp centres and a
  set `P` of prepared rows, the held true-defect exit (carrier phase (C)) reaches a prefix at which
  ALL hypotheses of the held first sharp-bad maximum blowup hold for every row `j ∉ P`: every row
  has order `≤ 1`, the carrier is pure of dimension `d+1`, the true distinct defect is empty, and
  every row of `P` is still prepared (normal crossings and density).
* `exists_actual_carrier_phase_lower_source`: consequently, after the carrier phase, the held lower
  source `actual_compact_sharp_bad_source` applies to EVERY row `j`: its support `L_j` is a closed
  submanifold, `F_j` is SNC, the lower sharp bad locus `B_j` is compact and `(L_j, [], I(B_j), 1)` is
  an invariant domain with boundary-adapted carrier.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34CarrierPureDimension
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower BlowupStrictSubmanifold
  NormalCrossings HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualChronologicalDistinctDefect HironakaG4CompactWholeMonomialMaskPhase
  MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaG34PreparedRowEmptyTail HironakaNormalCrossingsBoundaryTransform
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **O4: the carrier keeps pure dimension along a test tower.** -/
theorem geoTransformAlong_N_regularAtDim (𝔪 : MarkedIdeal n X) (hNc : IsClosed 𝔪.N) {k : ℕ}
    (hN : ∀ x ∈ 𝔪.N,RegularAtDim (n := n) 𝔪.N x k) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower 𝔪 T →
      IsClosed (geoTransformAlong 𝔪 T).N ∧
        ∀ x ∈ (geoTransformAlong 𝔪 T).N,RegularAtDim (n := n) (geoTransformAlong 𝔪 T).N x k
  | _,.refl,_ => ⟨hNc,hN⟩
  | _,.step T C π hπ,hT => by
    obtain ⟨hc,hr⟩ := geoTransformAlong_N_regularAtDim 𝔪 hNc hN T hT.1
    have hCN : C ⊆ (geoTransformAlong 𝔪 T).N := hT.2.subset_N
    refine ⟨isClosed_closure,fun x hx => ?_⟩
    exact regularAtDim_geoStrictTransform hπ hc hr hCN hx

/-- **The current carrier of an actual W-test prefix is pure of dimension `d+1`** when `W` is. -/
theorem actual_carrier_regularAtDim {W : Set X} (hW : IsClosedSubmanifold n W) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1) :=
  (geoTransformAlong_N_regularAtDim (geometricTemplate W []) hW.1 hReg T hT).2

/-- **The carrier phase reaches the lower entry** (steps (C), (T1) and the entry hypotheses of
(L) in the G4K1B control flow).  From an actual prefix with current sharp centres and a set `P` of
prepared rows, the held true-defect exit `Q` (centres over the true distinct defect) ends at a
prefix where every row has order `≤ 1`, the carrier is pure of dimension `d+1`, the true distinct
defect is empty and every row of `P` is still prepared: these are all the hypotheses of the held
first sharp-bad maximum blowup `exists_actual_first_sharp_bad_maximum_blowup` for each `j ∉ P`. -/
theorem exists_actual_carrier_phase_lower_entry (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) (P : Finset (Fin E.length))
    (hP : ∀ i ∈ P,ActualRowPrepared W E i T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) (T.append Q)).ideal x ≤ 1) ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,
        RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) (T.append Q)).N x (d+1)) ∧
      chronologicalDistinctDefect W E (T.append Q)=∅ ∧
      ∀ i ∈ P,ActualRowPrepared W E i (T.append Q) := by
  obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOver,hEmpty,hRows,hKeep⟩ :=
    exists_actual_carrier_phase_keeps_prepared hn hW hE hdense d hReg hK T hT hFull hSharp
  exact ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOver,hRows,actual_carrier_regularAtDim hW d hReg (T.append Q) hTQ,
    hEmpty,fun i hi => hKeep i (hP i hi)⟩

/-- **After the carrier phase, the held lower sharp-bad source applies to every row.** -/
theorem exists_actual_carrier_phase_lower_source (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      (∀ i : Fin E.length,ActualRowPrepared W E i T → ActualRowPrepared W E i (T.append Q)) ∧
      ∀ j : Fin E.length,
        let A := geoTransformAlong (geometricTemplate W []) (T.append Q)
        let L := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).ideal.zeroLocus
        let Fj := (E.map (strictAlong (T.append Q))).eraseIdx j.val ++ A.E
        let Bj := originalSharpBadLocus (n := n) L Fj
        let M : MarkedIdeal n Z := ⟨L,[],vanishingIdeal (n := n) Bj,1⟩
        IsClosedSubmanifold n L ∧ IsSNCDivisor n Fj ∧ IsCompact Bj ∧
          IsInvDomain n M ∧ IsBoundaryAdaptedCarrier (n := n) (⋃ D ∈ Fj,D) [] := by
  obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOver,hEmpty,hRows,hKeep⟩ :=
    exists_actual_carrier_phase_keeps_prepared hn hW hE hdense d hReg hK T hT hFull hSharp
  refine ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOver,hKeep,fun j => ?_⟩
  exact HironakaActualSharpBadFirstMaximumBlowup.actual_compact_sharp_bad_source
    hn hW hE hdense hK (T.append Q) hTQ hFullTQ hSharpTQ hRows d
    (actual_carrier_regularAtDim hW d hReg (T.append Q) hTQ) hEmpty j

end
end Hironaka.HironakaG34CarrierPureDimension
