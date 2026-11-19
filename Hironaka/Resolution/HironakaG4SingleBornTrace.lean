import Hironaka.Resolution.HironakaG4NoncompactChainCleanup
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4SingleBornTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings RelativePrincipalizationSpan HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant HironakaG4MonomialRowChain
  HironakaG4CompactWholeMonomialMaskPhase HomogenizedGlueingTower RestrictedIdealExtension
  MonomialPartAlong DivisorExponentAlong GermIdealOrder RestrictEmptyTower
variable {n : ℕ} {X : CMfd.{u} n}

/-- A family supported on at most one column has componentwise comparable rows. -/
theorem rowsChain_of_one_support {ι : Type} {b : ℕ} (A : ι → Fin b → ℕ)
    (h : ∀ j k, (∃ i, A i j ≠ 0) → (∃ i, A i k ≠ 0) → j=k) : RowsChain A := by
  classical
  intro i k
  by_cases hs : ∃ j, A i j ≠ 0 ∨ A k j ≠ 0
  · obtain ⟨j,hj⟩ := hs
    rcases le_total (A i j) (A k j) with hi | hk
    · left
      intro l
      by_cases hlj : l=j
      · subst l; exact hi
      · have hz : A i l=0 := by
          by_contra hne
          have he := h l j ⟨i,hne⟩ (hj.elim (fun q => ⟨i,q⟩) (fun q => ⟨k,q⟩))
          exact hlj he
        simp [hz]
    · right
      intro l
      by_cases hlj : l=j
      · subst l; exact hk
      · have hz : A k l=0 := by
          by_contra hne
          have he := h l j ⟨k,hne⟩ (hj.elim (fun q => ⟨i,q⟩) (fun q => ⟨k,q⟩))
          exact hlj he
        simp [hz]
  · left
    intro j
    have hzero : A i j=0 := by
      by_contra hnz
      exact hs ⟨j,Or.inl hnz⟩
    simp [hzero]

theorem exponent_zero_off_trace {N H : Set X} {I : GermIdeal n X}
    (hc : IsClosed (N ∩ H)) {x : X} (hx : x ∉ N ∩ H) : divExpAlong n N I H x=0 := by
  unfold divExpAlong
  rw [dif_neg]
  rintro ⟨e,he⟩
  exact he (isDivNearAlong_of_notMem hc hx (e+1))

/-- Any exponent-row family is chained at a point with at most one incident born slot. -/
theorem rowsChain_at_of_single_born_incidence {ι : Type} {N : Set X} {B : List (Set X)}
    (hN : IsClosed N) (hB : ∀ j : Fin B.length,IsClosed (B.get j))
    (D : ι → GermIdeal n X) {x : X}
    (hSingle : ∀ j k : Fin B.length,x ∈ B.get j → x ∈ B.get k → j=k) :
    RowsChain (fun i j => divExpAlong n N (D i) (B.get j) x) := by
  apply rowsChain_of_one_support
  intro j k hj hk
  apply hSingle j k
  · by_contra hnot
    obtain ⟨i,hi⟩ := hj
    apply hi
    exact exponent_zero_off_trace (hN.inter (hB j)) (fun h => hnot h.2)
  · by_contra hnot
    obtain ⟨i,hi⟩ := hk
    apply hi
    exact exponent_zero_off_trace (hN.inter (hB k)) (fun h => hnot h.2)

/-- If no two born members meet the carrier at the same point, its actual
old-row exponent matrices are chains; distinct labels are kept separate. -/
theorem actual_rowsChain_of_single_born_incidence {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hSingle : ∀ x ∈ N,∀ j k : Fin B.length,x ∈ B.get j → x ∈ B.get k → j=k) :
    ∀ x ∈ N,RowsChain (fun i j =>
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x) := by
  intro x hx
  exact rowsChain_at_of_single_born_incidence hN.1
    (fun j => hE.1 _ (List.mem_append_right O (List.get_mem B j)))
    (oldMonomialPart N O B) (hSingle x hx)

/-- At most one born incidence and a uniform source exponent bound give a complete
prepared noncompact sharp cleanup on one actual finite history. -/
theorem noncompact_prepared_single_born_cleanup (hn : 0 < n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hTr : IsTransverse n N B) (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1)
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x)
    (hSingle : ∀ x ∈ N,∀ j k : Fin B.length,x ∈ B.get j → x ∈ B.get k → j=k)
    (hBounds : ∃ C,∀ x ∈ N,∀ i : Fin O.length,∀ j : Fin B.length,
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x ≤ C) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N B) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) T ∧
      CurrentSharpCentres N (O ++ B) T ∧
      CentresOver (originalSharpBadLocus (n := n) N (O ++ B)) T ∧
      IsClosedSubmanifold n (strictAlong T N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E ∧
      HasNormalCrossings n (strictAlong T N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalSharpBadLocus (n := n) N (O ++ B))ᶜ := by
  have hChain := actual_rowsChain_of_single_born_incidence hN hE hSingle
  exact HironakaG4NoncompactChainCleanup.noncompact_prepared_chain_cleanup
    hn hN hE hTr hdense hOrd hPrep hChain hBounds

/-- Finite source trace components supply the uniform source bound. -/
theorem noncompact_prepared_single_born_cleanup_of_finite_traces (hn : 0 < n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hTr : IsTransverse n N B) (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1)
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x)
    (hSingle : ∀ x ∈ N,∀ j k : Fin B.length,x ∈ B.get j → x ∈ B.get k → j=k)
    (hComp : ∀ j : Fin B.length,Finite (ConnectedComponents
      {x : X | x ∈ N ∧ x ∈ B.get j})) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N B) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) T ∧
      CurrentSharpCentres N (O ++ B) T ∧
      CentresOver (originalSharpBadLocus (n := n) N (O ++ B)) T ∧
      IsClosedSubmanifold n (strictAlong T N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E ∧
      HasNormalCrossings n (strictAlong T N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalSharpBadLocus (n := n) N (O ++ B))ᶜ := by
  have hChain := actual_rowsChain_of_single_born_incidence hN hE hSingle
  exact HironakaG4NoncompactChainCleanup.noncompact_prepared_chain_cleanup_of_finite_traces
    hn hN hE hTr hdense hOrd hPrep hChain hComp

end
end Hironaka.HironakaG4SingleBornTrace
