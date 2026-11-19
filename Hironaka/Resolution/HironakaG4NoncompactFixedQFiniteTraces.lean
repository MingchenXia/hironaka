import Hironaka.Resolution.HironakaG4FiniteTraceComponents
import Hironaka.Resolution.HironakaG4ZeroMaskFixedQFold

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4NoncompactFixedQFiniteTraces
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings NormalCrossingsComparison DivisorExponentAlong RelativePrincipalizationSpan MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  GermIdealOrder MonomialPartAlong RestrictedIdealExtension RestrictEmptyTower HironakaG4FiniteTraceComponents BlowupTowerTransforms HomogenizedGlueingTower
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaSharpOriginalProductTraceOrder
variable {n : ℕ} {X : CMfd.{u} n}

private theorem divExpAlong_zero_off_trace {N H : Set X} {I : GermIdeal n X}
    (hc : IsClosed (N ∩ H)) {x : X} (hx : x ∉ N ∩ H) : divExpAlong n N I H x = 0 := by
  unfold divExpAlong
  rw [dif_neg]
  rintro ⟨e,he⟩
  exact he (isDivNearAlong_of_notMem hc hx (e+1))

/-- Finite component counts on the original carrier/born traces give one
uniform exponent bound for every original old row, not just one SUM. -/
theorem all_old_rows_uniform_of_finite_trace_components (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hComp : ∀ j : Fin born.length, Finite (ConnectedComponents
      {x : X | x ∈ N ∧ x ∈ born.get j})) :
    ∃ B,∀ x ∈ N,∀ i : Fin old.length,∀ j : Fin born.length,
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x ≤ B := by
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hRow (i : Fin old.length) : ∃ B,∀ x ∈ N,∀ j : Fin born.length,
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x ≤ B := by
    have hParts := actual_old_parts_geometry hn hN hE hTr hdense i
    have hc : (oldMonomialPart N old born i).IsCoherent := hParts.2.2.2.2.1
    have hnz : ∀ x ∈ N,IsNonzeroAlongAt N (oldMonomialPart N old born i) x := hParts.2.2.2.2.2.1
    let M : MarkedIdeal n X := ⟨N,born,oldMonomialPart N old born i,0⟩
    have hWF : M.IsWellFormed := ⟨hN,hc,hBorn,hTr⟩
    obtain ⟨B,hB⟩ := incident_exponents_bounded_of_finite_trace_components hn M hWF hnz hComp
    refine ⟨B,?_⟩
    intro x hx j
    by_cases hj : x ∈ born.get j
    · have hxM : x ∈ M.cosupp := by
        change x ∈ cosupport n N (oldMonomialPart N old born i) 0
        rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hc hg)]
        exact hx
      exact hB x hxM j hj
    · have hClosed : IsClosed (N ∩ born.get j) := hN.1.inter (hBorn.1 _ (List.get_mem _ _))
      rw [divExpAlong_zero_off_trace hClosed (fun h => hj h.2)]
      exact Nat.zero_le _
  choose bound hBound using hRow
  refine ⟨Finset.univ.sup bound,?_⟩
  intro x hx i j
  exact (hBound i x hx j).trans (Finset.le_sup (f := bound) (Finset.mem_univ i))

/-- Finite source trace components imply the noncompact fixed-count sharp fold. -/
theorem exists_fixed_q_drop_of_finite_trace_components (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (q : ℕ) (hq : 0 < q) :
    let J := oldResidualPart N old born
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let RJ := fun i => (⟨N,born,J i,0⟩ : MarkedIdeal n X)
    (∀ x ∈ N,tauD (A x) ≤ q) →
    (∀ x ∈ N,tauD (A x)=q → nuOne (A x)=0) →
    (∀ j : Fin born.length, Finite (ConnectedComponents
      {x : X | x ∈ N ∧ x ∈ born.get j})) →
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N born) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
      CurrentSharpCentres N (old ++ born) T ∧
      CentresOver (originalSharpBadLocus (n := n) N (old ++ born)) T ∧
      (∀ i : Fin old.length,IsGeoTestTower (RJ i) T) ∧
      let NT := strictAlong T N
      let BT := (geoTransformAlong (geometricTemplate N born) T).E
      let AT : Y → Fin old.length → Fin BT.length → ℕ := fun z i j =>
        divExpAlong n NT
          (monomialPartAlong n NT
            (restrictOn n NT (vanishingIdeal (n := n) (strictAlong T (old.get i)))) BT)
          (BT.get j) z
      ∀ z ∈ NT,tauD (AT z) < q := by
  dsimp only
  intro hTau hNu hComp
  have hBounds := all_old_rows_uniform_of_finite_trace_components hn hN hE hTr hdense hComp
  exact HironakaG4ZeroMaskFixedQFold.exists_prepared_zero_mask_noncompact_fixed_q_drop
    hn hN hE hTr hdense hOrd hPrepared q hq hTau hNu hBounds

end
end Hironaka.HironakaG4NoncompactFixedQFiniteTraces
