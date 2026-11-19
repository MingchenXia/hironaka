import Hironaka.Resolution.HironakaG34CarrierPureDimension

/-! # A protected lower step: the sharp-bad maximum keeps every prepared row prepared (G4K1B, route B)

Lane G34 (run 0080, round 3).  Blueprint: `hironaka-g34-resume-protected-lower-step.tex`.

Setting: an actual prefix `T` (both geometric tests, current sharp centres) at the entry of the lower
phase of row `j` (every row of order `≤ 1`, carrier pure of dimension `d + 1`, empty true distinct
defect: the output of the carrier phase, `exists_actual_carrier_phase_lower_entry`), and a set `P ∌ j`
of prepared rows.  The lower phase of row `j` blows up, at each stage, the maximum locus `C` of the
marked-stratum history value of `(S_j, [], I(B_j), 1)` (`B_j` the lower sharp bad locus, recomputed at
each stage; `O2-ROUTE.md` §3(a)).

* `actual_lower_step_keeps_prepared`:
  (protection certificate) for every prepared row `i ∈ P` and every point `x` of `C` on its support
  `S_i`, there is an open window `U ∋ x` and an auxiliary hypersurface `H` of `U` with
  `S_i ∩ U = N ∩ H`, `H :: F_i` simple normal crossings and transverse to the carrier, and `C ∩ U`
  with normal crossings with `H :: F_i` (the hypotheses of `protection_of_nc_centre`);
  (preservation) if `B_j ≠ ∅`, the blowup along `C` is again an actual prefix with current sharp
  centres, `C ⊆ B_j` has normal crossings with the full boundary, and EVERY row of `P` is prepared
  after it (`ActualRowPrepared`).
  Both halves are read off the held `actual_sharp_bad_maximum_processed_slice_locality` and
  `exists_actual_first_sharp_bad_maximum_blowup`; the new content is the assembly in the
  `ActualRowPrepared` form, which composes with the carrier phase (`exists_actual_carrier_phase_lower_entry`)
  into protected rounds.
* `exists_actual_protected_lower_round`: from any actual prefix with current sharp centres and prepared
  rows `P ∌ j`: the carrier phase `Q` (centres over the true defect, literally empty near every
  prepared support, keeps `P` prepared) followed, when `B_j ≠ ∅` at `T·Q`, by the protected lower step
  at `T·Q`; at the end every row of `P` is prepared and the prefix is again actual with current sharp
  centres, so rounds iterate. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34ProtectedLowerStep
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms NormalCrossings SimultaneousNormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaOriginalNCMarkedStratumHistoryValue
  HironakaG34PreparedRowEmptyTail RestrictEmptyTower HomogenizedGlueingTower
open ResolutionDriver (maxLocus)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **The lower step at the entry keeps every prepared row prepared, with an NC certificate.** -/
theorem actual_lower_step_keeps_prepared (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ a : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T)
    (j : Fin E.length) (hj : j ∉ P) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let L := A.N ∩ (J j).zeroLocus
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n := n) L Fj
    let Mbad : MarkedIdeal n Y := ⟨L, [], vanishingIdeal (n := n) Bj, 1⟩
    let H := ⋃ D ∈ Fj, D
    let C := maxLocus (markedStratumHistoryValue Mbad H (BlowupTower.refl : BlowupTower Y Y))
      Mbad.cosupp
    (∀ i ∈ P, ∀ x ∈ C ∩ (A.N ∩ (J i).zeroLocus), ∃ U : Opens Y, x ∈ U ∧ ∃ Haux : Set U,
        (Subtype.val : U → Y) ⁻¹' (A.N ∩ (J i).zeroLocus) =
          (Subtype.val : U → Y) ⁻¹' A.N ∩ Haux ∧
        IsSNCDivisor n (Haux :: (old.eraseIdx i.val ++ A.E).map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
        IsTransverse n ((Subtype.val : U → Y) ⁻¹' A.N)
          (Haux :: (old.eraseIdx i.val ++ A.E).map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
        HasNormalCrossings n ((Subtype.val : U → Y) ⁻¹' C)
          (Haux :: (old.eraseIdx i.val ++ A.E).map ((Subtype.val : U → Y) ⁻¹' ·))) ∧
    (Bj.Nonempty →
      ∃ (Z : CMfd.{u} n) (pi : Z → Y) (hpi : IsBlowupAlong n C pi),
        IsGeoTestTower (geometricTemplate W []) (.step T C pi hpi) ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step T C pi hpi) ∧
        CurrentSharpCentres W E (.step T C pi hpi) ∧
        C.Nonempty ∧ C ⊆ Bj ∧ HasNormalCrossings n C (old ++ A.E) ∧
        ∀ i ∈ P, ActualRowPrepared W E i (.step T C pi hpi)) := by
  intro A old J L Fj Bj Mbad H C
  refine ⟨?_, ?_⟩
  · intro i hi x hx
    have hne : j ≠ i := fun h => hj (h ▸ hi)
    exact HironakaActualSharpBadMaximumProcessedSlice.actual_sharp_bad_maximum_processed_slice_locality
      hn hW hE hdense T hT hFull hOrd d hReg hDistinct i j hne (hP i hi).2.1 (hP i hi).2.2 x hx
  · intro hNe
    have hStep := HironakaActualSharpBadFirstMaximumBlowup.exists_actual_first_sharp_bad_maximum_blowup
      hn hW hE hdense hK T hT hFull hSharp hOrd d hReg hDistinct P j hj
      (fun i hi => (hP i hi).2.1) (fun i hi => (hP i hi).2.2)
    obtain ⟨Z, pi, hpi, hCne, -, -, hCB, -, -, hCNC, -, -, -, -, hTnext, hFullnext, hSharpnext,
      -, -, -, -, -, -, -, -, -, -, hProc, -⟩ := hStep hNe
    refine ⟨Z, pi, hpi, hTnext, hFullnext, hSharpnext, hCne, hCB, hCNC, fun i hi => ?_⟩
    obtain ⟨-, -, hS, hNC, hD, hO⟩ := hProc i hi
    have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i))
      (.step T C pi hpi)).1
    change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C pi hpi)).N =
      (geoTransformAlong (geometricTemplate W []) (.step T C pi hpi)).N at hNi
    refine ⟨?_, ?_, ?_⟩
    · rw [hNi]
      exact hO
    · dsimp only
      rw [hS]
      exact hNC
    · dsimp only
      rw [hS]
      exact hD

/-- **A protected lower round**: the carrier phase, literally empty near every prepared support and
keeping every prepared row prepared, followed (when the lower bad locus of row `j` is nonempty) by the
protected lower step; the end is again an actual prefix with current sharp centres and every row of
`P` prepared, so rounds iterate. -/
theorem exists_actual_protected_lower_round (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T)
    (j : Fin E.length) (hj : j ∉ P) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      (∀ i ∈ P, ∃ U : Opens Y,
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ U ∧
        IsEmptyTower (restrict U Q)) ∧
      (∀ i ∈ P, ActualRowPrepared W E i (T.append Q)) ∧
      ∃ (Z' : CMfd.{u} n) (R : BlowupTower Z Z'),
        R.length ≤ 1 ∧
        CentresOver (originalSharpBadLocus (n := n)
          ((geoTransformAlong (geometricTemplate W []) (T.append Q)).N ∩
            (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).ideal.zeroLocus)
          ((E.map (strictAlong (T.append Q))).eraseIdx j.val ++
            (geoTransformAlong (geometricTemplate W []) (T.append Q)).E)) R ∧
        IsGeoTestTower (geometricTemplate W []) ((T.append Q).append R) ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) ((T.append Q).append R) ∧
        CurrentSharpCentres W E ((T.append Q).append R) ∧
        ∀ i ∈ P, ActualRowPrepared W E i ((T.append Q).append R) := by
  obtain ⟨Z, Q, hTQ, hFullTQ, hSharpTQ, hOver, hEmpty, hRows, hProt⟩ :=
    HironakaG34DefectEmptyOrder.exists_actual_carrier_phase_protected hn hW hE hdense d hRegW hK
      T hT hFull hSharp
  have hPQ : ∀ i ∈ P, ActualRowPrepared W E i (T.append Q) := by
    intro i hi
    obtain ⟨U, hSU, hEmptyU⟩ := hProt i (hP i hi).1 (hP i hi).2.1 (hP i hi).2.2
    exact (actual_prepared_row_empty_tail hn hW hE hdense i T hT hFull (hP i hi) U hSU Q hTQ
      hEmptyU).1
  refine ⟨Z, Q, hOver, fun i hi => hProt i (hP i hi).1 (hP i hi).2.1 (hP i hi).2.2, hPQ, ?_⟩
  have hRegQ := HironakaG34CarrierPureDimension.actual_carrier_regularAtDim hW d hRegW (T.append Q) hTQ
  obtain ⟨-, hStep⟩ := actual_lower_step_keeps_prepared hn hW hE hdense hK (T.append Q) hTQ hFullTQ
    hSharpTQ hRows d hRegQ hEmpty P hPQ j hj
  by_cases hNe : (originalSharpBadLocus (n := n)
      ((geoTransformAlong (geometricTemplate W []) (T.append Q)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).ideal.zeroLocus)
      ((E.map (strictAlong (T.append Q))).eraseIdx j.val ++
        (geoTransformAlong (geometricTemplate W []) (T.append Q)).E)).Nonempty
  · obtain ⟨Z', pi, hpi, hTn, hFn, hSn, -, hCB, -, hPn⟩ := hStep hNe
    exact ⟨Z', .step .refl _ pi hpi, le_rfl, ⟨trivial, hCB⟩, hTn, hFn, hSn, hPn⟩
  · exact ⟨Z, .refl, Nat.zero_le _, trivial, hTQ, hFullTQ, hSharpTQ, hPQ⟩

end
end Hironaka.HironakaG34ProtectedLowerStep
