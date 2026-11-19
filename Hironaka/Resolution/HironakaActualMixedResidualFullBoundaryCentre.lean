import Hironaka.Resolution.HironakaG4CompactWholeMonomialMaskPhase
import Hironaka.Resolution.HironakaSharpActualMaximumMemberOrders
import Hironaka.Resolution.HironakaG4RecordedTowerResidualCompatibility
import Hironaka.Resolution.HironakaG4IncidentOldBornStratumCentre
import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates

/-! Full original old-plus-born legality of the genuine residual maximum on
an arbitrary actual mixed prefix. Source-first proof:
`hironaka-actual-mixed-residual-full-boundary-centre-20261101.tex`.
Finite residual-phase termination and joint preparedness remain separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualMixedResidualFullBoundaryCentre
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison RelativePrincipalizationSpan RestrictedIdealExtension
  HironakaG4PreparedCentreCoordinates HironakaG4IncidentOldBornStratumCentre
  HironakaSharpActualTraceIncidence HironakaSharpActualMaximumMemberOrders HironakaSharpActualDynamicDistinctCentre
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProductDomain
  MonomialPartAlong DivisorExponentAlong GermIdealOrder BoundaryCount

variable {n : ℕ} {X Y Z : CMfd.{u} n}



/-- At any actual two-template original prefix, the SAME genuine full residual
maximum has full old-plus-born NC. No original-product test, supplied trace
packet, preparedness or inherited-unit-row comparison is required. -/
theorem exists_actual_mixed_residual_full_boundary_centre (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W)
    {d : ℕ} (hd : d+1 ≤ n) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ C : Set Y,C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      (currentProductMarked W E T).IsAdmissibleCentre C ∧
      (geoTransformAlong (geometricTemplate W []) T).IsAdmissibleCentre C ∧
      HasNormalCrossings n C (E.map (strictAlong T) ++
        (geoTransformAlong (geometricTemplate W []) T).E) ∧
      C=ResolutionDriver.maxLocus
        ((CanonicalCentres.invFamily hn (n+1)).inv (currentProductMarked W E T) .refl)
        (chronologicalDistinctDefect W E T) ∧
      ∀ i : Fin E.length,∀ x ∈ C,∀ᶠ y in 𝓝 x,y ∈ C →
        (y ∈ strictAlong T (E.get i) ↔ x ∈ strictAlong T (E.get i)) := by
  obtain ⟨C,hneC,hCZ,hCur,hTemp,hCeq,hProfile⟩ :=
    exists_actual_dynamic_centre_member_order_profile hn hW hE hdense hK hd hr T hT hne
  let A := geoTransformAlong (geometricTemplate W []) T
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hBorn := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_right _ _)
  have hOld := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left _ _)
  have hCN : C ⊆ A.N := hTemp.subset_N
  have hInc : ∀ i : Fin E.length,∀ x ∈ C,∀ᶠ y in 𝓝 x,y ∈ C →
      (y ∈ strictAlong T (E.get i) ↔ x ∈ strictAlong T (E.get i)) := by
    intro i x hx
    let j : Fin (E.map (strictAlong T)).length := ⟨i.val,by simp⟩
    have hGet : (E.map (strictAlong T)).get j=strictAlong T (E.get i) := by simp [j]
    have hHi : IsClosedSubmanifold n (strictAlong T (E.get i)) := by
      rw [←hGet]
      exact MonomialPart.isClosedSubmanifold_get hn hOld j
    obtain ⟨_hNi,_hEi,_hdi,hwi,_hnzi,_hpri⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    have hUnit : ∀ᶠ y in 𝓝 x,y ∈ C → ((F i).mem y 1 ↔ (F i).mem x 1) := by
      filter_upwards [hProfile x hx] with y hy hyC
      have hp := (hy hyC).2.1
      have hm : (i ∈ actualProperPositions F y ↔ i ∈ actualProperPositions F x) := by rw [hp]
      simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and] at hm
      exact not_iff_not.mp hm
    apply eventually_trace_incidence_of_factor hn hRecorded.1 hHi hBorn hRecorded.2.2.1
      (hRecorded.2.2.2.2 i).2.1 (F i) hwi.isCoherent hCN
      (hRecorded.2.2.2.2 i).2.2.2 hx ?_ hUnit
    filter_upwards [hProfile x hx] with y hy hyC
    exact (hy hyC).2.2
  have hNC : HasNormalCrossings n C (E.map (strictAlong T) ++ A.E) := by
    intro x hx
    apply actual_incident_old_normalCrossingsAt hRecorded.2.1 hTemp.2.2 hx
    intro j hj
    let i : Fin E.length := ⟨j.val,by simpa using j.isLt⟩
    have hGet : (E.map (strictAlong T)).get j=strictAlong T (E.get i) := by simp [i]
    rw [hGet] at hj ⊢
    filter_upwards [hInc i x hx] with y hy hyC
    exact (hy hyC).mpr hj
  exact ⟨C,hneC,hCZ,hCur,hTemp,hNC,hCeq,hInc⟩


/-- A real blowup of the SAME full native residual maximum appends both
original geometric tests at this arbitrary mixed old/born prefix. -/
theorem exists_actual_mixed_residual_full_boundary_blowup (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W)
    {d : ℕ} (hd : d+1 ≤ n) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      IsGeoTestTower (geometricTemplate W []) (.step T C π hπ) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step T C π hπ) ∧
      IsProperMap π ∧ ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (chronologicalDistinctDefect W E T)ᶜ ∧
      C=ResolutionDriver.maxLocus
        ((CanonicalCentres.invFamily hn (n+1)).inv (currentProductMarked W E T) .refl)
        (chronologicalDistinctDefect W E T) := by
  obtain ⟨C,hneC,hCZ,hCur,hTemp,hNC,hCeq,_hInc⟩ :=
    exists_actual_mixed_residual_full_boundary_centre hn hW hE hdense hK hd hr T hT hFull hne
  have hdom := currentProductMarked_isInvDomain hn hW hE hdense hK hd hr T hT
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hCur.2.1).trans (ResolutionInvariantDriver.interior_cosupp_eq_empty hdom).subset)
  obtain ⟨Z,π,hπ⟩ := ResolutionDriver.exists_blowup C hCur.1 hint
  have hCos : (geoTransformAlong (geometricTemplate (univ : Set X) E) T).cosupp=univ := by
    rw [HironakaG4CompactWholeMonomialMaskPhase.template_current,
      HironakaG4CompactWholeMonomialMaskPhase.strict_univ]
    change cosupport n (univ : Set Y) (IdealWeightPowers.unitIdeal n Y) 0=univ
    rw [cosupport_zero (fun _ _ hg => hg)]
  have hFullAdm : (geoTransformAlong (geometricTemplate (univ : Set X) E) T).IsAdmissibleCentre C := by
    refine ⟨hCur.1,?_,?_⟩
    · rw [hCos]
      exact subset_univ C
    · rw [HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T]
      exact hNC
  have hsub : (chronologicalDistinctDefect W E T)ᶜ ⊆ Cᶜ := fun _ hx hC => hx (hCZ hC)
  have hi := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hiso : IsIsomorphismOver n π (chronologicalDistinctDefect W E T)ᶜ := by
    refine ⟨⟨fun _ hz => hz,?_,?_⟩,hi.2.mono_left (preimage_mono hsub)⟩
    · exact hi.1.2.1.mono (preimage_mono hsub)
    · intro y hy
      obtain ⟨z,_hz,hz⟩ := hi.1.2.2 (hsub hy)
      exact ⟨z,by change π z ∈ (chronologicalDistinctDefect W E T)ᶜ;rwa [hz],hz⟩
  exact ⟨C,Z,π,hπ,hneC,hCZ,⟨hT,hTemp⟩,⟨hFull,hFullAdm⟩,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,hiso,hCeq⟩

end
end Hironaka.HironakaActualMixedResidualFullBoundaryCentre
