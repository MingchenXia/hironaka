import Hironaka.Resolution.HironakaG4FiniteTraceComponents
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4CompactTraceExponentBound
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DivisorExponentAlong
  HironakaMarkOneGammaBoundedMaxima NormalCrossings NormalCrossingsComparison RelativePrincipalizationSpan
  HironakaG4PreparedCentreCoordinates HironakaG4CompactWholeMonomialMaskPhase
variable {n : ℕ} {X : CMfd.{u} n}

/-- On an arbitrary compact subset, every incident exponent of a well-formed
marked ideal has one numerical bound, irrespective of global trace components. -/
theorem incident_exponents_bounded_on_compact (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (K : Set X) (hK : IsCompact K) :
    ∃ B : ℕ,∀ x ∈ K, x ∈ M.N → ∀ i : Fin M.E.length,x ∈ M.E.get i →
      divExpAlong n M.N M.ideal (M.E.get i) x ≤ B := by
  have hFinite (i : Fin M.E.length) :
      BddAbove ((fun x : X => divExpAlong n M.N M.ideal (M.E.get i) x) ''
        (K ∩ (M.N ∩ M.E.get i))) := by
    let S := M.N ∩ M.E.get i
    have hLoc : IsLocallyConstant (fun x : S =>
        divExpAlong n M.N M.ideal (M.E.get i) x.1) := by
      apply (IsLocallyConstant.iff_eventually_eq _).2
      intro x
      have h := eventually_divExpAlong_get_eq hn hM.isClosedSubmanifold_N hM.isSNCDivisor
        hM.isTransverse hM.isCoherent hne i x.2.1 x.2.2
      filter_upwards [h.filter_mono (continuous_subtype_val.tendsto x)] with y hy
      exact hy y.2.1 y.2.2
    have hCont : ContinuousOn (fun x : X =>
        divExpAlong n M.N M.ideal (M.E.get i) x) S :=
      continuousOn_iff_continuous_domRestrict.mpr hLoc.continuous
    have hClosed : IsClosed S := hM.isClosedSubmanifold_N.1.inter
      (hM.isSNCDivisor.1 _ (List.get_mem M.E i))
    exact ((hK.inter_right hClosed).image_of_continuousOn (hCont.mono inter_subset_right)).bddAbove
  choose bound hBound using hFinite
  refine ⟨Finset.univ.sup bound,?_⟩
  intro x hxK hxN i hi
  exact (hBound i ⟨x,⟨hxK,hxN,hi⟩,rfl⟩).trans
    (Finset.le_sup (f := bound) (Finset.mem_univ i))
/-- Every old row has a common exponent bound on a compact set, without
assuming compactness or finitely many components of its entire born traces. -/
theorem all_old_rows_bounded_on_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (K : Set X) (hK : IsCompact K) :
    ∃ B,∀ x ∈ K, x ∈ N → ∀ i : Fin old.length,∀ j : Fin born.length,
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x ≤ B := by
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hRow (i : Fin old.length) : ∃ B,∀ x ∈ K,x ∈ N → ∀ j : Fin born.length,
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x ≤ B := by
    have hParts := actual_old_parts_geometry hn hN hE hTr hdense i
    have hc : (oldMonomialPart N old born i).IsCoherent := hParts.2.2.2.2.1
    have hnz : ∀ x ∈ N,IsNonzeroAlongAt N (oldMonomialPart N old born i) x := hParts.2.2.2.2.2.1
    let M : MarkedIdeal n X := ⟨N,born,oldMonomialPart N old born i,0⟩
    have hWF : M.IsWellFormed := ⟨hN,hc,hBorn,hTr⟩
    obtain ⟨B,hB⟩ := incident_exponents_bounded_on_compact hn M hWF hnz K hK
    refine ⟨B,?_⟩
    intro x hxK hxN j
    by_cases hj : x ∈ born.get j
    · exact hB x hxK hxN j hj
    · have hClosed : IsClosed (N ∩ born.get j) := hN.1.inter (hBorn.1 _ (List.get_mem _ _))
      have hz : divExpAlong n N (oldMonomialPart N old born i) (born.get j) x=0 := by
        unfold divExpAlong
        rw [dif_neg]
        rintro ⟨e,he⟩
        exact he (isDivNearAlong_of_notMem hClosed (fun h => hj h.2) (e+1))
      rw [hz]
      exact Nat.zero_le _
  choose bound hBound using hRow
  refine ⟨Finset.univ.sup bound,?_⟩
  intro x hxK hxN i j
  exact (hBound i x hxK hxN j).trans (Finset.le_sup (f := bound) (Finset.mem_univ i))

/-- A source-wide bound away from a compact set extends across that set. -/
theorem all_old_rows_uniform_of_bounded_off_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (K : Set X) (hK : IsCompact K)
    (hOut : ∃ B,∀ x ∈ N,x ∉ K → ∀ i : Fin old.length,∀ j : Fin born.length,
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x ≤ B) :
    ∃ B,∀ x ∈ N,∀ i : Fin old.length,∀ j : Fin born.length,
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x ≤ B := by
  obtain ⟨B,hB⟩ := hOut
  obtain ⟨C,hC⟩ := all_old_rows_bounded_on_compact hn hN hE hTr hdense K hK
  refine ⟨max B C,?_⟩
  intro x hx i j
  by_cases hxK : x ∈ K
  · exact (hC x hxK hx i j).trans (le_max_right _ _)
  · exact (hB x hx hxK i j).trans (le_max_left _ _)

end
end Hironaka.HironakaG4CompactTraceExponentBound
