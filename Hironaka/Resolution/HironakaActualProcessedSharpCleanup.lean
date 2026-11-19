import Hironaka.Resolution.HironakaActualProcessedAllMasksDrop
import Hironaka.Resolution.HironakaG4ZeroMaskFixedQFold
import Hironaka.Resolution.HironakaActualGeometricCleanupComposition
import Hironaka.Resolution.HironakaAdmissibleCalculus

/-! Actual count-one and zero-count completion of the SAME original processed
boundary-cleaning history. Source-first proof:
`hironaka-actual-processed-sharp-cleanup-20261101.tex`.
Production of the processed residual state from arbitrary original input remains
an explicit separate obligation of the original joint G4 theorem. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProcessedSharpCleanup
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison RelativePrincipalizationSpan
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4PreparedCentreCoordinates
  HironakaG4MonomialFamilyInvariant HironakaActualProcessedMaskFiniteBlock
  HironakaG4CompactWholeMonomialMaskPhase HomogenizedGlueingTower RestrictedIdealExtension
  MonomialPartAlong DivisorExponentAlong GermIdealOrder

variable {n : ℕ} {X Y Z V : CMfd.{u} n}

theorem nuOne_eq_zero_of_tauD_eq_one {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (h : tauD A=1) : nuOne A=0 := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp h
  have hne : (properRows A).Nonempty := by rw [hi];exact Finset.singleton_nonempty i
  apply (nuOne_eq_zero_iff_exists_gcd_row A hne).mpr
  refine ⟨i,by rw [hi];exact Finset.mem_singleton_self i,?_⟩
  intro j
  simp only [gcdColumn,dif_pos hne,hi,Finset.inf'_singleton]

theorem tauD_row_equiv {r s b : ℕ} (e : Fin r ≃ Fin s)
    (A : Fin s → Fin b → ℕ) : tauD (fun i => A (e i))=tauD A := by
  have hRows : (properRows (fun i => A (e i))).map e.toEmbedding=properRows A := by
    ext i
    simp only [Finset.mem_map,properRows,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact hj
    · intro hi
      exact ⟨e.symm i,by simpa only [rowOrder,e.apply_symm_apply] using hi,e.apply_symm_apply i⟩
  unfold tauD
  rw [←hRows,Finset.card_map]

def tupleMatrix (N : Set X) (O B : List (Set X))
    {Y : CMfd.{u} n} (R : BlowupTower X Y) (x : Y) :
    Fin O.length → Fin (geoTransformAlong (geometricTemplate N B) R).E.length → ℕ :=
  fun i j => divExpAlong n (strictAlong R N)
    (monomialPartAlong n (strictAlong R N)
      (restrictOn n (strictAlong R N) (vanishingIdeal (n := n) (strictAlong R (O.get i))))
      (geoTransformAlong (geometricTemplate N B) R).E)
    ((geoTransformAlong (geometricTemplate N B) R).E.get j) x

private def tuplePrepared (N : Set X) (O B : List (Set X))
    {Y : CMfd.{u} n} (R : BlowupTower X Y) : Prop :=
  let NR := strictAlong R N
  let OR := O.map (strictAlong R)
  let BR := (geoTransformAlong (geometricTemplate N B) R).E
  IsClosedSubmanifold n NR ∧ IsSNCDivisor n (OR ++ BR) ∧ IsTransverse n NR BR ∧
    NR ⊆ closure (NR \ ⋃ H ∈ OR ++ BR,H) ∧
    (∀ x ∈ NR,∀ i,ordinaryTraceOrder NR (oldResidualPart NR OR BR i) x ≤ 1) ∧
    (∀ x ∈ NR,IsPreparedResidualSNCAt NR OR BR x)

/-- A prepared state with no positive old monomial row is already normal
crossings with the whole literal boundary. -/
theorem prepared_tau_zero_normalCrossings (hn : 0 < n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hTr : IsTransverse n N B) (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1)
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x)
    (hZero : ∀ x ∈ N,tauD (fun i j =>
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x)=0) :
    HasNormalCrossings n N (O ++ B) := by
  let A : X → Fin O.length → Fin B.length → ℕ := fun x i j =>
    divExpAlong n N (oldMonomialPart N O B i) (B.get j) x
  have hBorn : IsSNCDivisor n B := isSNCDivisor_of_sublist hE (List.sublist_append_right O B)
  have hUnit (x : X) (hx : x ∈ N) (i : Fin O.length) :
      (oldMonomialPart N O B i).mem x 1 := by
    have hNoProper : properRows (A x)=∅ := Finset.card_eq_zero.mp (hZero x hx)
    have hRowZero : rowOrder (A x) i=0 := by
      by_contra hne
      have hi : i ∈ properRows (A x) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      rw [hNoProper] at hi
      exact Finset.notMem_empty i hi
    have hColumns (j : Fin B.length) : A x i j=0 := by
      have hj : A x i j ≤ rowOrder (A x) i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hp := actual_old_parts_geometry hn hN hE hTr hdense i
    exact HironakaG4CanonicalZeroRowUnit.one_mem_of_zero_canonical_row hn hN hBorn hTr
      hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hx hColumns
  have hNC := (prepared_selected_born_centre_geometry hn hN hE hTr hdense
    hOrd hPrep (∅ : Finset (Fin B.length))
    (fun x hx i hNot => (hNot (hUnit x hx.1 i)).elim)).2
  have hEmpty : N ∩ BoundaryCount.memberInter B ∅=N := by
    ext x
    simp [BoundaryCount.memberInter]
  rw [hEmpty] at hNC
  exact hNC

private theorem count_one_cleanup_terminal_readback (hn : 0 < n)
    {N : Set X} {O B : List (Set X)} (R : BlowupTower X Y)
    (hEnd : tuplePrepared N O B R)
    (hDrop : ∀ x ∈ strictAlong R N,tauD (tupleMatrix N O B R x) < 1) :
    (∀ x ∈ strictAlong R N,tauD (tupleMatrix N O B R x) = 0) ∧
    IsClosedSubmanifold n (strictAlong R N) ∧
    IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E ∧
    HasNormalCrossings n (strictAlong R N)
      (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E := by
  rcases hEnd with ⟨hNR,hER,hTrR,hDenseR,hOrdR,hPrepR⟩
  let NR := strictAlong R N
  let OR := O.map (strictAlong R)
  let BR := (geoTransformAlong (geometricTemplate N B) R).E
  let A : Y → Fin OR.length → Fin BR.length → ℕ := fun x i j =>
    divExpAlong n NR (oldMonomialPart NR OR BR i) (BR.get j) x
  let e : Fin O.length ≃ Fin OR.length := finCongr (by simp [OR])
  have hGet (i : Fin O.length) : OR.get (e i)=strictAlong R (O.get i) := by simp [OR,e]
  have hMatrix (x : Y) : (fun i => A x (e i))=tupleMatrix N O B R x := by
    funext i j
    simp only [A,oldMonomialPart,oldTraceIdeal,hGet,tupleMatrix,NR,BR]
  have hZero (x : Y) (hx : x ∈ NR) : tauD (A x)=0 := by
    rw [←tauD_row_equiv e (A x),hMatrix]
    have hh : tauD (tupleMatrix N O B R x)<1 := hDrop x hx
    omega
  have hNC := prepared_tau_zero_normalCrossings hn hNR hER hTrR hDenseR hOrdR hPrepR hZero
  have hBoundary : (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E=OR ++ BR := by
    have h := full_ordered N O.get B R
    have ho : List.ofFn O.get=O := List.ofFn_get O
    have ht : (List.ofFn fun i => strictAlong R (O.get i))=O.map (strictAlong R) := by
      simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map O (strictAlong R)
    rw [ho,ht] at h
    exact h
  refine ⟨?_,hNR,?_,?_⟩
  · intro x hx
    have hh := hDrop x hx
    omega
  · rw [hBoundary]
    exact hER
  · rw [hBoundary]
    exact hNC

theorem native_count_one_cleanup (hn : 0 < n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hTr : IsTransverse n N B) (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H))
    (hK : IsCompact (originalSharpBadLocus (n := n) N (O ++ B)))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1)
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x)
    (hCount : ∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower X X) x) ≤ 1) :
    ∃ (Y : CMfd.{u} n) (R : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N B) R ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) R ∧
      CurrentSharpCentres N (O ++ B) R ∧
      (∀ x ∈ strictAlong R N,tauD (tupleMatrix N O B R x)=0) ∧
      IsClosedSubmanifold n (strictAlong R N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E ∧
      HasNormalCrossings n (strictAlong R N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E := by
  have hNu : ∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower X X) x)=1 →
      nuOne (tupleMatrix N O B (.refl : BlowupTower X X) x)=0 :=
    fun x _hx he => nuOne_eq_zero_of_tauD_eq_one _ he
  obtain ⟨Y,R,hCarrier,hFull,hSharp,_hOver,_hResidualTests,hPrefixes,hDrop⟩ :=
    HironakaG4ZeroMaskFixedQFold.exists_prepared_zero_mask_fixed_q_drop
      hn hN hE hTr hdense hOrd hPrep 1 (by omega) hK hCount hNu
  have hEnd : tuplePrepared N O B (BlowupTowerSplit.split R 0).2.1 := by
    have h := hPrefixes 0
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩
  rw [StepOneEmptyPrefix.split_zero R] at hEnd
  obtain ⟨hZero,hSmooth,hSNC,hNC⟩ := count_one_cleanup_terminal_readback hn R hEnd hDrop
  exact ⟨Y,R,hCarrier,hFull,hSharp,hZero,hSmooth,hSNC,hNC⟩

/-- The actual native count-one tail retains the prescribed singleton order
and the same terminal prepared readback. -/
theorem native_count_one_labelled_cleanup_of_bounded_exponents (hn : 0 < n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hTr : IsTransverse n N B) (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1)
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x)
    (hCount : ∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower X X) x) ≤ 1)
    (L : List (Finset (Fin O.length)))
    (hLabels : L.toFinset = (Finset.univ : Finset (Fin O.length)).powersetCard 1)
    (hExponents : ∃ L : ℕ,∀ x ∈ N,∀ i : Fin O.length,∀ j : Fin B.length,
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x ≤ L) :
    ∃ (Y : CMfd.{u} n) (R : BlowupTower X Y),
      HironakaG4ZeroMaskFixedQFold.OrderedNativeMaskHistory hn N O B R L.reverse ∧
      IsGeoTestTower (geometricTemplate N B) R ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) R ∧
      CurrentSharpCentres N (O ++ B) R ∧
      (∀ x ∈ strictAlong R N,tauD (tupleMatrix N O B R x)=0) ∧
      IsClosedSubmanifold n (strictAlong R N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E ∧
      HasNormalCrossings n (strictAlong R N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E := by
  have hNu : ∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower X X) x)=1 →
      nuOne (tupleMatrix N O B (.refl : BlowupTower X X) x)=0 :=
    fun x _hx he => nuOne_eq_zero_of_tauD_eq_one _ he
  obtain ⟨Y,R,hTape,hCarrier,hFull,hSharp,_hOver,_hResidualTests,hDrop,
    hNR,hER,hTrR,hDenseR,hOrdR,hPrepR,_hControl⟩ :=
    HironakaG4ZeroMaskFixedQFold.exists_ordered_prepared_zero_mask_noncompact_fixed_q_drop
      hn hN hE hTr hdense hOrd hPrep 1 (by decide) L hLabels hCount hNu hExponents
  have hEnd : tuplePrepared N O B R := ⟨hNR,hER,hTrR,hDenseR,hOrdR,hPrepR⟩
  obtain ⟨hZero,hSmooth,hSNC,hNC⟩ := count_one_cleanup_terminal_readback hn R hEnd hDrop
  exact ⟨Y,R,hTape,hCarrier,hFull,hSharp,hZero,hSmooth,hSNC,hNC⟩

/-- The actual native count-one tail requires only a source-wide bound on
the incident exponents. The sharp bad locus itself may be noncompact. -/
theorem native_count_one_cleanup_of_bounded_exponents (hn : 0 < n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hTr : IsTransverse n N B) (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1)
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x)
    (hCount : ∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower X X) x) ≤ 1)
    (hExponents : ∃ L : ℕ,∀ x ∈ N,∀ i : Fin O.length,∀ j : Fin B.length,
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x ≤ L) :
    ∃ (Y : CMfd.{u} n) (R : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N B) R ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) R ∧
      CurrentSharpCentres N (O ++ B) R ∧
      (∀ x ∈ strictAlong R N,tauD (tupleMatrix N O B R x)=0) ∧
      IsClosedSubmanifold n (strictAlong R N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E ∧
      HasNormalCrossings n (strictAlong R N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E := by

  classical
  let F := (Finset.univ : Finset (Fin O.length)).powersetCard 1
  have hF : F.toList.toFinset = F := by simp
  obtain ⟨Y,R,_hTape,h⟩ := native_count_one_labelled_cleanup_of_bounded_exponents
    hn hN hE hTr hdense hOrd hPrep hCount F.toList hF hExponents
  exact ⟨Y,R,h⟩

theorem original_tuple_count (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (R : BlowupTower Y Z) (x : Z) :
    tauD (factorMatrix W E (T.append R) x)=
      tauD (tupleMatrix (strictAlong T W) (E.map (strictAlong T))
        (geoTransformAlong (geometricTemplate W []) T).E R x) := by
  let O := E.map (strictAlong T)
  let e : Fin E.length ≃ Fin O.length := finCongr (by simp [O])
  have hGet (i : Fin E.length) : O.get (e i)=strictAlong T (E.get i) := by simp [O,e]
  let A := geoTransformAlong (geometricTemplate W []) T
  have hTemplate : A=geometricTemplate (strictAlong T W) A.E := template_current W [] T
  unfold factorMatrix oldFactor
  rw [geoTransformAlong_append]
  change tauD (fun i j => divExpAlong n
    (geoTransformAlong A R).N
    (monomialPartAlong n (geoTransformAlong A R).N
      (restrictOn n (geoTransformAlong A R).N
        (vanishingIdeal (n := n) (strictAlong (T.append R) (E.get i))))
      (geoTransformAlong A R).E) ((geoTransformAlong A R).E.get j) x)=_
  rw [hTemplate]
  rw [←tauD_row_equiv e]
  congr 1
  funext i j
  simp only [O] at hGet
  simp only [tupleMatrix,N_geoTransformAlong,MemberInterLocusAlong.strictAlong_append]
  rw [hGet]
  rfl

private theorem current_full_template (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) :
    geoTransformAlong (geometricTemplate (univ : Set X) E) T=
      geometricTemplate (univ : Set Y) (E.map (strictAlong T) ++
        (geoTransformAlong (geometricTemplate W []) T).E) := by
  rw [template_current,strict_univ,
    HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T]


/-- The actual prepared original prefix determines its current geometric state. -/
theorem original_prepared_prefix_dictionary (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)
 :
    let N := strictAlong T W
    let O := E.map (strictAlong T)
    let B := (geoTransformAlong (geometricTemplate W []) T).E
    IsClosedSubmanifold n N ∧ IsSNCDivisor n (O ++ B) ∧ IsTransverse n N B ∧
    N ⊆ closure (N \ ⋃ H ∈ O ++ B,H) ∧
    (∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1) ∧
    (∀ x ∈ N,IsPreparedResidualSNCAt N O B x) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let N := strictAlong T W
  let O := E.map (strictAlong T)
  let B := A.E
  have hN : A.N=N := N_geoTransformAlong _ _
  have hD := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  change IsClosedSubmanifold n A.N ∧ IsSNCDivisor n (O ++ B) ∧ IsTransverse n A.N B ∧
    A.N ⊆ closure (A.N \ ⋃ H ∈ O ++ B,H) ∧ _ at hD
  rw [hN] at hD
  let e : Fin E.length ≃ Fin O.length := finCongr (by simp [O])
  have hGet (i : Fin E.length) : O.get (e i)=strictAlong T (E.get i) := by simp [O,e]
  have hRow (i : Fin E.length) : oldResidualPart N O B (e i)=
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal := by
    unfold oldResidualPart oldTraceIdeal
    rw [hGet]
    exact (hD.2.2.2.2 i).2.2.1
  have hOrdN : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1 := by
    intro x hx i
    have h := hOrd x (hN.symm ▸ hx) (e.symm i)
    change ordinaryTraceOrder A.N _ x ≤ 1 at h
    rw [hN,←hRow (e.symm i),e.apply_symm_apply] at h
    exact h
  have hPrepN : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x := by
    change ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N O B x at hPrepared
    rw [hN] at hPrepared
    exact hPrepared
  exact ⟨hD.1,hD.2.1,hD.2.2.1,hD.2.2.2.1,hOrdN,hPrepN⟩

theorem original_count_one_prefix_dictionary (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)
    (hCount : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ 1) :
    let N := strictAlong T W
    let O := E.map (strictAlong T)
    let B := (geoTransformAlong (geometricTemplate W []) T).E
    IsClosedSubmanifold n N ∧ IsSNCDivisor n (O ++ B) ∧ IsTransverse n N B ∧
    N ⊆ closure (N \ ⋃ H ∈ O ++ B,H) ∧
    (∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1) ∧
    (∀ x ∈ N,IsPreparedResidualSNCAt N O B x) ∧
    (∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower Y Y) x) ≤ 1) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let N := strictAlong T W
  let O := E.map (strictAlong T)
  let B := A.E
  obtain ⟨hN,hSNC,hTr,hDense,hOrdN,hPrepN⟩ :=
    original_prepared_prefix_dictionary hn hW hE hdense T hT hFull hOrd hPrepared
  have hNid : A.N=N := N_geoTransformAlong _ _
  have hCountN : ∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower Y Y) x) ≤ 1 := by
    intro x hx
    rw [←original_tuple_count W E T (.refl : BlowupTower Y Y) x]
    exact hCount x (hNid.symm ▸ hx)
  exact ⟨hN,hSNC,hTr,hDense,hOrdN,hPrepN,hCountN⟩


/-- Append a sharp full-NC tail to the actual original prefix. -/
theorem append_sharp_nc_tail {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) (R : BlowupTower Y Z) :
    let N := strictAlong T W
    let O := E.map (strictAlong T)
    let B := (geoTransformAlong (geometricTemplate W []) T).E
    IsGeoTestTower (geometricTemplate N B) R →
    IsGeoTestTower (geometricTemplate (univ : Set Y) (O ++ B)) R →
    CurrentSharpCentres N (O ++ B) R →
    IsClosedSubmanifold n (strictAlong R N) →
    IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set Y) (O ++ B)) R).E →
    HasNormalCrossings n (strictAlong R N)
      (geoTransformAlong (geometricTemplate (univ : Set Y) (O ++ B)) R).E →
    let U := T.append R
    let A := geoTransformAlong (geometricTemplate W []) U
    let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
    IsGeoTestTower (geometricTemplate W []) U ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
    CurrentSharpCentres W E U ∧
    RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
    IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  dsimp only
  intro hNative hNativeFull hNativeSharp hSmooth hSNC hNC
  let A := geoTransformAlong (geometricTemplate W []) T
  let N := strictAlong T W
  let O := E.map (strictAlong T)
  let B := A.E
  have hBoundary := HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T
  have hTemplate : A=geometricTemplate N B := template_current W [] T
  have hFullTemplate : geoTransformAlong (geometricTemplate (univ : Set X) E) T=
      geometricTemplate (univ : Set Y) (O ++ B) := current_full_template W E T
  have hTestU : IsGeoTestTower (geometricTemplate W []) (T.append R) := by
    apply (isGeoTestTower_append_iff _ T R).mpr
    refine ⟨hT,?_⟩
    change IsGeoTestTower A R
    rw [hTemplate]
    exact hNative
  have hFullU : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) := by
    apply (isGeoTestTower_append_iff _ T R).mpr
    exact ⟨hFull,hFullTemplate.symm ▸ hNativeFull⟩
  have hSharpU : CurrentSharpCentres W E (T.append R) := by
    apply currentSharp_append W E T R hSharp
    rw [hBoundary]
    exact hNativeSharp
  have hOverU := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
    hW.1 hE.1 (T.append R) hSharpU).2
  have hCarrier : (geoTransformAlong (geometricTemplate W []) (T.append R)).N=strictAlong R N := by
    rw [geoTransformAlong_append]
    change (geoTransformAlong A R).N=_
    rw [hTemplate,N_geoTransformAlong]
    rfl
  have hFullBoundary : (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append R)).E=
      (geoTransformAlong (geometricTemplate (univ : Set Y) (O ++ B)) R).E := by
    rw [geoTransformAlong_append,hFullTemplate]
  have hSeq := HironakaAdmissibleSequence.isAdmissibleBlowupSequence_proj
    (geometricTemplate (univ : Set X) E) (originalSharpBadLocus (n := n) W E)
    (T.append R) hFullU hOverU
  refine ⟨hTestU,hFullU,hSharpU,hOverU,?_,?_,?_,?_,?_⟩
  · exact hCarrier.symm ▸ hSmooth
  · exact hFullBoundary.symm ▸ hSNC
  · rw [hCarrier,hFullBoundary]
    exact hNC
  · exact HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence hSeq.isBlowupSequence
  · exact HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hSeq


theorem append_count_one_tail {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) (R : BlowupTower Y Z) :
    let N := strictAlong T W
    let O := E.map (strictAlong T)
    let B := (geoTransformAlong (geometricTemplate W []) T).E
    IsGeoTestTower (geometricTemplate N B) R →
    IsGeoTestTower (geometricTemplate (univ : Set Y) (O ++ B)) R →
    CurrentSharpCentres N (O ++ B) R →
    (∀ x ∈ strictAlong R N,tauD (tupleMatrix N O B R x)=0) →
    IsClosedSubmanifold n (strictAlong R N) →
    IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set Y) (O ++ B)) R).E →
    HasNormalCrossings n (strictAlong R N)
      (geoTransformAlong (geometricTemplate (univ : Set Y) (O ++ B)) R).E →
    let U := T.append R
    let A := geoTransformAlong (geometricTemplate W []) U
    let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
    IsGeoTestTower (geometricTemplate W []) U ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
    CurrentSharpCentres W E U ∧
    RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
    (∀ x ∈ A.N,tauD (factorMatrix W E U x)=0) ∧
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
    IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  dsimp only
  intro hNative hNativeFull hNativeSharp hZero hSmooth hSNC hNC
  obtain ⟨hTestU,hFullU,hSharpU,hOverU,hSmoothU,hSNCU,hNCU,hProperU,hIsoU⟩ :=
    append_sharp_nc_tail hW hE T hT hFull hSharp R
      hNative hNativeFull hNativeSharp hSmooth hSNC hNC
  refine ⟨hTestU,hFullU,hSharpU,hOverU,?_,hSmoothU,hSNCU,hNCU,hProperU,hIsoU⟩
  intro x hx
  rw [original_tuple_count W E T R x]
  have hCarrier : (geoTransformAlong (geometricTemplate W []) (T.append R)).N=
      strictAlong R (strictAlong T W) := by
    rw [geoTransformAlong_append,N_geoTransformAlong,N_geoTransformAlong]
    rfl
  exact hZero x (hCarrier ▸ hx)


theorem exists_actual_count_one_sharp_cleanup (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)
    (hCount : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ 1) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      let U := T.append R
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      (∀ x ∈ A.N,tauD (factorMatrix W E U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧
      IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let N := strictAlong T W
  let O := E.map (strictAlong T)
  let B := A.E
  obtain ⟨hN,hSNC,hTr,hDense,hOrdN,hPrepN,hCountN⟩ :=
    original_count_one_prefix_dictionary hn hW hE hdense T hT hFull hOrd hPrepared hCount
  obtain ⟨hBad,_hOverT⟩ := HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
    hW.1 hE.1 T hSharp
  have hBoundary := HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T
  have hBadSub : originalSharpBadLocus (n := n) N (O ++ B) ⊆
      T.proj ⁻¹' originalSharpBadLocus (n := n) W E := by
    rw [←hBoundary]
    exact hBad
  have hCompact : IsCompact (originalSharpBadLocus (n := n) N (O ++ B)) :=
    ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
      (isClosed_originalSharpBadLocus hN.1 hSNC.1) hBadSub
  obtain ⟨Z,R,hNative,hNativeFull,hNativeSharp,hZero,hSmooth,hSNC',hNC⟩ :=
    native_count_one_cleanup hn hN hSNC hTr hDense hCompact hOrdN hPrepN hCountN
  exact ⟨Z,R,append_count_one_tail hW hE T hT hFull hSharp R
    hNative hNativeFull hNativeSharp hZero hSmooth hSNC' hNC⟩


private def originalReady (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : Prop :=
  let A := geoTransformAlong (geometricTemplate W []) T
  IsGeoTestTower (geometricTemplate W []) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
    CurrentSharpCentres W E T ∧
    (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1) ∧
    (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)

private def cleanupEndpoint (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (U : BlowupTower X Y) : Prop :=
  let A := geoTransformAlong (geometricTemplate W []) U
  let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
  IsGeoTestTower (geometricTemplate W []) U ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
    CurrentSharpCentres W E U ∧
    RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
    (∀ x ∈ A.N,tauD (factorMatrix W E U x)=0) ∧
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
    IsProperMap U.proj ∧
    IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ

/-- Full sharp cleanup of the original processed phase. The actual count is
bounded internally by the number of original rows, then genuinely decreased;
all original indices and the entire accumulated born boundary are retained. -/
theorem exists_actual_processed_sharp_cleanup (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hNC : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      let U := T.append R
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      (∀ x ∈ A.N,tauD (factorMatrix W E U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧
      IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  obtain ⟨Z,R,hHeads,hCount⟩ := HironakaActualProcessedAllMasksDrop.exists_actual_processed_count_at_most_one
    hn hW hE hdense T hT hFull hSharp hK hOrd hNC hDenseS hPrepared
  have hReady : originalReady W E (T.append (BlowupTowerSplit.split R 0).2.1) := by
    have h := hHeads 0
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2.2.1⟩
  rw [StepOneEmptyPrefix.split_zero R] at hReady
  rcases hReady with ⟨hTR,hFullR,hSharpR,hOrdR,hPrepR⟩
  obtain ⟨V,S,hS⟩ := exists_actual_count_one_sharp_cleanup hn hW hE hdense
    (T.append R) hTR hFullR hSharpR hK hOrdR hPrepR hCount
  refine ⟨V,R.append S,?_⟩
  change cleanupEndpoint W E (T.append (R.append S))
  rw [←BlowupTower.append_assoc]
  exact hS

end
end Hironaka.HironakaActualProcessedSharpCleanup
