import Hironaka.Resolution.HironakaG4RecordedTowerResidualCompatibility
import Hironaka.Resolution.HironakaG4ActiveMonomialSharpBad
import Hironaka.Resolution.HironakaSharpActualInitialFullCompatibility
import Hironaka.Resolution.HironakaActualMixedResidualFullBoundaryCentre
import Hironaka.Resolution.HironakaG4SharpBadFootprint

/-! Intrinsic CURRENT sharp badness of the SAME original chronological distinct
residual defect at arbitrary mixed two-template test prefixes. No residual
history is restarted and every original/born position remains present.
Source-first proof: `hironaka-actual-chronological-defect-sharp-bad-20261101.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualChronologicalDefectSharpBad
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings SimultaneousNormalCrossings NormalCrossingsComparison
  RelativePrincipalizationSpan RestrictedIdealExtension
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualInitialFullCompatibility
  HironakaSharpActualDynamicDistinctCentre
  HironakaG4RecordedTowerResidualCompatibility HironakaG4ActiveMonomialSharpBad
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpOriginalProductTraceOrder MonomialPartAlong NonmonomialTransformAlong
  DivisorExponentAlong GermIdealOrder MarkedIdealOperationsAlong

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem normalCrossingsAt_subfamily {N : Set X} {E F : List (Set X)}
    {x : X} (h : normalCrossingsAt (n := n) N E x)
    (hsub : ∀ H ∈ F,H ∈ E) : normalCrossingsAt (n := n) N F x := by
  obtain ⟨S₀,S,⟨Φ,ht,h0,hfam⟩,hcard⟩ := h
  have hidx : ∀ j : Fin F.length,∃ i : Fin E.length,E.get i=F.get j :=
    fun j => List.mem_iff_get.mp (hsub _ (List.get_mem _ _))
  choose idx hidx using hidx
  refine ⟨S₀,fun j => S (idx j),⟨Φ,ht,h0,?_⟩,
    fun j hj => hcard (idx j) (by rw [hidx]; exact hj)⟩
  rintro (_ | j) hj y hy hyΦ
  · exact hfam none hj hy hyΦ
  · have h := hfam (some (idx j)) (by simp only [Option.elim]; rw [hidx]; exact hj) hy hyΦ
    simp only [Option.elim] at h ⊢
    rwa [hidx] at h

private theorem old_factor_unit_at_full_nc (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born))
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    {x : X} (hx : x ∈ N) (hNC : normalCrossingsAt (n := n) N (old ++ born) x)
    (i : Fin old.length) :
    (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) (old.get i))) born).mem x 1 := by
  let k : Fin (old ++ born).length := ⟨i.val,by simp only [List.length_append]; omega⟩
  let L : List (Fin (old ++ born).length) := List.ofFn fun j : Fin born.length =>
    ⟨old.length+j.val,by simp only [List.length_append]; omega⟩
  have hOld : (old ++ born).get k=old.get i := by
    simp only [k,List.get_eq_getElem,List.getElem_append_left i.isLt]
  have hBorn : L.map (old ++ born).get=born := by
    calc
      L.map (old ++ born).get=List.ofFn (fun j : Fin born.length => born.get j) := by
        dsimp only [L]
        rw [List.map_ofFn]
        congr 1
        funext j
        simp only [Function.comp_apply,List.get_eq_getElem]
        rw [List.getElem_append_right (Nat.le_add_right old.length j.val)]
        simp only [Nat.add_sub_cancel_left]
      _=born := List.ofFn_get born
  have hL : ∀ j ∈ L,k ≠ j := by
    intro j hj
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hj
    intro h
    have hval := congrArg Fin.val h
    change i.val=old.length+a.val at hval
    omega
  simpa only [hOld,hBorn] using
    one_mem_old_monomialPartAlong_at_normalCrossings hn hN hE hdense hx hNC k L hL

/-- At actual CURRENT full NC, every SAME original chronological residual has
exactly the whole current strict-original trace stalk, including normal germs. -/
theorem actual_residual_stalk_eq_trace_at_full_normalCrossings (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N)
    (hNC : normalCrossingsAt (n := n) (geoTransformAlong (geometricTemplate W []) T).N
      (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) x)
    (i : Fin E.length) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
    (monomialPartAlong n A.N I A.E).mem x 1 ∧
      ∀ g,(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem x g ↔ I.mem x g := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
  let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let D := monomialPartAlong n A.N I A.E
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  let old := E.map (strictAlong T)
  let j : Fin old.length := Fin.cast (List.length_map _).symm i
  have hGet : old.get j=strictAlong T (E.get i) := by simp [old,j]
  have hUnit : D.mem x 1 := by
    have h := old_factor_unit_at_full_nc hn hRec.1 hRec.2.1 hRec.2.2.2.1 hx hNC j
    rw [hGet] at h
    exact h
  have hcI : I.IsCoherent := (hRec.2.2.2.2 i).1
  have hNm : nonmonomialPartAlong n A.N I A.E=J := (hRec.2.2.2.2 i).2.2.1
  have hFac : I=restrictOn n A.N (D.mul J) := (hRec.2.2.2.2 i).2.2.2
  have hcJ : J.IsCoherent :=
    (original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT).2.2.2.1.isCoherent
  have hIncl : I.Le J := by
    rw [←hNm]
    exact le_nonmonomialPartAlong_self hcI
  refine ⟨hUnit,fun g => ⟨?_,hIncl x g⟩⟩
  intro hg
  have hgHol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcJ hg
  have hMul : (D.mul J).mem x g := by
    change IsInSpanAt (n := n) (fun f => ∃ a b,D.mem x a ∧ J.mem x b ∧ f=a*b) x g
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨1,g,hUnit,hg,by simp⟩ hgHol
  change I.mem x g
  rw [hFac]
  exact ⟨hgHol,IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hMul hgHol)⟩

private theorem ordinary_order_eq_of_stalk {N : Set X} (hN : IsClosedSubmanifold n N)
    {I J : GermIdeal n X} (hcI : I.IsCoherent) (hcJ : J.IsCoherent)
    (hnzI : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hnzJ : ∀ y ∈ N,IsNonzeroAlongAt N J y)
    {x : X} (hx : x ∈ N) (hMem : ∀ g,I.mem x g ↔ J.mem x g) :
    ordinaryTraceOrder N I x=ordinaryTraceOrder N J x := by
  apply Nat.le_antisymm
  · apply (ordinaryTraceOrder_cosupport_iff hN hcJ hnzJ hx _).mp
    have h := (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx (ordinaryTraceOrder N I x)).mpr le_rfl
    exact ⟨hx,fun g hg => h.2 g ((hMem g).mpr hg)⟩
  · apply (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx _).mp
    have h := (ordinaryTraceOrder_cosupport_iff hN hcJ hnzJ hx (ordinaryTraceOrder N J x)).mpr le_rfl
    exact ⟨hx,fun g hg => h.2 g ((hMem g).mp hg)⟩

private theorem family_geometry (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    ∀ i : Fin E.length,
      let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
      J.IsCoherent ∧ (∀ y ∈ N,IsNonzeroAlongAt N J y) ∧
        ∀ y ∈ N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,J.mem y g ↔
          HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g := by
  dsimp only
  intro i
  obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  rw [hNi] at hnzi hpri
  exact ⟨hwi.isCoherent,hnzi,hpri⟩

/-- The literal actual DISTINCT defect at any arbitrary original mixed prefix
is intrinsically current sharp bad. No product test, profile or sharp selector
is assumed; the reference initial family is only a stalk comparator. -/
theorem actual_chronological_distinct_defect_subset_current_sharp_bad (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) :
    chronologicalDistinctDefect W E T ⊆ originalSharpBadLocus (n := n)
      (geoTransformAlong (geometricTemplate W []) T).N
      (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let F := fun i : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let G := fun j : Fin old.length => (originalRelativeMemberMarked A.N (old.get j)).ideal
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hOld : IsSNCDivisor n old := isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_left _ _)
  have hDenseOld : A.N ⊆ closure (A.N \ ⋃ H ∈ old,H) := by
    apply hRec.2.2.2.1.trans (closure_mono ?_)
    intro x hx
    exact ⟨hx.1,fun h => hx.2 (by
      obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp h
      exact mem_iUnion₂.mpr ⟨H,List.mem_append_left _ hH,hxH⟩)⟩
  have hGeomF := family_geometry hn hW hE hdense T hT
  have hFC : ∀ i,(F i).IsCoherent := fun i => (hGeomF i).1
  have hFN : ∀ i,∀ y ∈ A.N,IsNonzeroAlongAt A.N (F i) y := fun i => (hGeomF i).2.1
  have hFP : ∀ i,∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,(F i).mem y g ↔
      HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g := fun i => (hGeomF i).2.2
  have hGeomG := family_geometry hn hRec.1 hOld hDenseOld (.refl : BlowupTower Y Y) trivial
  have hGC : ∀ j,(G j).IsCoherent := fun j => (hGeomG j).1
  have hGN : ∀ j,∀ y ∈ A.N,IsNonzeroAlongAt A.N (G j) y := fun j => (hGeomG j).2.1
  have hGP : ∀ j,∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,(G j).mem y g ↔
      HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g := fun j => (hGeomG j).2.2
  let e : Fin E.length ≃ Fin old.length := finCongr (List.length_map _).symm
  have hGet (i : Fin E.length) : old.get (e i)=strictAlong T (E.get i) := by simp [old,e]
  intro x hx
  have hxN : x ∈ A.N := hx.1
  refine ⟨hxN,fun hNC => ?_⟩
  have hNCOld : normalCrossingsAt (n := n) A.N old x :=
    normalCrossingsAt_subfamily hNC (fun H hH => List.mem_append_left _ hH)
  have hMem (i : Fin E.length) (g : Y → ℂ) : (F i).mem x g ↔ (G (e i)).mem x g := by
    change (F i).mem x g ↔ (restrictOn n A.N (vanishingIdeal (n := n) (old.get (e i)))).mem x g
    rw [hGet]
    exact (actual_residual_stalk_eq_trace_at_full_normalCrossings hn hW hE hdense T hT hFull hxN hNC i).2 g
  have hOrder (i : Fin E.length) : ordinaryTraceOrder A.N (F i) x=ordinaryTraceOrder A.N (G (e i)) x :=
    ordinary_order_eq_of_stalk hRec.1 (hFC i) (hGC (e i)) (hFN i) (hGN (e i)) hxN (hMem i)
  have hProper (i : Fin E.length) : i ∈ actualProperPositions F x ↔ e i ∈ actualProperPositions G x := by
    simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and]
    exact not_congr (hMem i 1)
  have hWitness := (actual_distinct_defect_iff_witness hRec.1 hFC hFN hFP hxN).mp hx
  have hWitnessG : (∃ j,2 ≤ ordinaryTraceOrder A.N (G j) x) ∨
      ∃ i j,i ≠ j ∧ i ∈ actualProperPositions G x ∧ j ∈ actualProperPositions G x ∧
        (actualIdealGermSetoid G x).r i j := by
    rcases hWitness with ⟨i,hi⟩ | ⟨i,j,hne,hpi,hpj,hrel⟩
    · exact Or.inl ⟨e i,by rwa [←hOrder]⟩
    · refine Or.inr ⟨e i,e j,fun h => hne (e.injective h),(hProper i).mp hpi,(hProper j).mp hpj,?_⟩
      intro g
      exact (hMem i g).symm.trans ((hrel g).trans (hMem j g))
  have hDefG := (actual_distinct_defect_iff_witness hRec.1 hGC hGN hGP hxN).mpr hWitnessG
  change x ∈ chronologicalDistinctDefect A.N old (.refl : BlowupTower Y Y) at hDefG
  exact (initial_actual_defect_subset_sharp_bad hn hRec.1 hOld hDenseOld hDefG).2 hNCOld

/-- A concrete consumer of intrinsic current badness: the SAME genuine mixed
full maximum blowup appends CurrentSharp and derives the ORIGINAL footprint.
The compact pure positive carrier hypotheses belong to the actual selector. -/
theorem exists_actual_mixed_residual_current_sharp_blowup (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W)
    {d : ℕ} (hd : d+1 ≤ n) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : HironakaG4CompactWholeMonomialMaskPhase.CurrentSharpCentres W E T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      IsGeoTestTower (geometricTemplate W []) (.step T C π hπ) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step T C π hπ) ∧
      HironakaG4CompactWholeMonomialMaskPhase.CurrentSharpCentres W E (.step T C π hπ) ∧
      RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) (.step T C π hπ) ∧
      IsProperMap π ∧ ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (chronologicalDistinctDefect W E T)ᶜ ∧
      C=ResolutionDriver.maxLocus
        ((CanonicalCentres.invFamily hn (n+1)).inv (currentProductMarked W E T) .refl)
        (chronologicalDistinctDefect W E T) := by
  obtain ⟨C,Z,π,hπ,hneC,hCZ,hTestNext,hFullNext,hProper,hHol,hIso,hMax⟩ :=
    HironakaActualMixedResidualFullBoundaryCentre.exists_actual_mixed_residual_full_boundary_blowup
      hn hW hE hdense hK hd hr T hT hFull hne
  have hCBad := hCZ.trans
    (actual_chronological_distinct_defect_subset_current_sharp_bad hn hW hE hdense T hT hFull)
  have hN : (geoTransformAlong (geometricTemplate W []) T).N=strictAlong T W := N_geoTransformAlong _ _
  have hBoundary := HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T
  rw [hN,←hBoundary] at hCBad
  have hSharpNext : HironakaG4CompactWholeMonomialMaskPhase.CurrentSharpCentres W E (.step T C π hπ) :=
    ⟨hSharp,hCBad⟩
  have hOver := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
    hW.1 hE.1 (.step T C π hπ) hSharpNext).2
  exact ⟨C,Z,π,hπ,hneC,hCZ,hTestNext,hFullNext,hSharpNext,hOver,hProper,hHol,hIso,hMax⟩

end
end Hironaka.HironakaActualChronologicalDefectSharpBad
