import Hironaka.Resolution.HironakaG34PreparedRowCarrierOrder
import Hironaka.Resolution.HironakaG34DefectEmptyOrder

/-! # A prepared row stays prepared across a tail that is empty near its support

Lane G34 (run 0080, round 2).  Blueprint: `hironaka-g34-resume-prepared-row-empty-tail.tex`.

Setting: an actual original mixed prefix `T` (both geometric tests), carrier `N`, row `i` with
residual `J_i`, support `S_i = N ∩ V(J_i)` and boundary `F_i = old.eraseIdx i ++ born`.  Row `i` is
*prepared* at `T` (`ActualRowPrepared`) when `J_i` has order `≤ 1` on `N`, `S_i` has normal
crossings with `F_i`, and `S_i` is dense off `F_i`.

* `nextRelativeStrict_support_of_disjoint`: one blowup whose centre misses the support of a
  relatively principal row: the new support is the PREIMAGE of the old one, and the order does not
  increase (it is unchanged off the centre).  Key point: the row is a unit along the centre.
* `actual_prepared_row_empty_tail` (obligation O1 of `G4K1B-CONTROL-FLOW.md`): if `R` is a W-test
  tail after `T` whose restriction to an open `U ⊇ S_i` is an empty tower, then row `i` is prepared
  at `T·R`, its new support is the preimage of `S_i`, and over `U` the row order is transported.
  (No full-boundary test of the tail is needed.)
* `exists_actual_carrier_phase_keeps_prepared`: the held true-defect exit (carrier phase (C)) keeps
  EVERY row prepared at its start prepared at its end (step (T1) of the control flow).
* `actual_prepared_row_carrier_phase_keeps_prepared`: the same for every carrier-preparation history
  of another row (phase (C')).
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34PreparedRowEmptyTail
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower BlowupStrictSubmanifold
  NormalCrossings NormalCrossingsInvariance HironakaSharpNormalCrossingsOpenLocus
  HironakaG4OriginalSelectedResidualTail HironakaG4RecordedTowerResidualCompatibility
  HironakaG4EquimultipleRelativeOrder HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualChronologicalDistinctDefect
  HironakaG4CompactWholeMonomialMaskPhase
  GermIdealOrder RelativePrincipalizationSpan MarkedIdeals MarkedIdeals.MarkedIdeal
  RestrictEmptyTower DivisorExponentAlong
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- **Row `i` is prepared at the actual prefix `T`**: order `≤ 1` of its residual on the carrier,
normal crossings of its support with its boundary, density of its support off its boundary.
(The three hypotheses `hOrd`, `hNC`, `hDenseS` of the round-1 G34 theorems, verbatim.) -/
def ActualRowPrepared (W : Set X) (E : List (Set X)) (i : Fin E.length) (T : BlowupTower X Y) :
    Prop :=
  (∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1) ∧
    (let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E)) ∧
    (let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))

/-- Private copy (`HironakaG4SharpBadFootprint`, private there): pointwise normal crossings of
strict transforms at a point off the centre. -/
private theorem normalCrossingsAt_strict_of_notMem {N : Set X} {E : List (Set X)}
    (hN : IsClosed N) (hE : ∀ H ∈ E,IsClosed H) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) {y : Y} (hy : π y ∉ C)
    (hNC : normalCrossingsAt (n := n) N E (π y)) :
    normalCrossingsAt (n := n) (geoStrictTransform π C N)
      (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) y := by
  let E' := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hflat⟩,hcard⟩ := hNC
  let A : Option (Fin E'.length) → Set X := fun o =>
    o.elim N (fun i => if hi : i.val<E.length then E.get ⟨i.val,hi⟩ else C)
  let J : Option (Fin E'.length) → Finset (Fin n) := fun o =>
    o.elim S₀ (fun i => if hi : i.val<E.length then S ⟨i.val,hi⟩ else ∅)
  have hOld : IsCoordinateFamilyAt n A J (π y) := by
    refine ⟨Φ,hsrc,hzero,?_⟩
    rintro (_ | i) hi u hu huΦ
    · exact hflat none hi hu huΦ
    · by_cases hidx : i.val<E.length
      · simpa only [A,J,Option.elim,dif_pos hidx] using
          hflat (some ⟨i.val,hidx⟩)
            (by simpa only [A,Option.elim,dif_pos hidx] using hi) hu huΦ
      · exact False.elim (hy (by simpa only [A,Option.elim,dif_neg hidx] using hi))
  have hGetOld (i : Fin E'.length) (hi : i.val<E.length) :
      E'.get i=geoStrictTransform π C (E.get ⟨i.val,hi⟩) := by
    simp only [E',List.get_eq_getElem]
    rw [List.getElem_append_left (by simpa only [List.length_map] using hi)]
    simp only [List.getElem_map]
  have hGetLast (i : Fin E'.length) (hi : ¬i.val<E.length) : E'.get i=π ⁻¹' C := by
    have hlt : i.val<E.length+1 := by simpa [E'] using i.isLt
    have hv : i.val=E.length := by omega
    simp [E',List.get_eq_getElem,hv]
  have hOpen : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
  have hDictionary : ∀ o : Option (Fin E'.length),∀ u ∈ π ⁻¹' Cᶜ,
      u ∈ o.elim (geoStrictTransform π C N) E'.get ↔ π u ∈ A o := by
    rintro (_ | i) u hu
    · exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN hu
    · change u ∈ E'.get i ↔ π u ∈ A (some i)
      by_cases hidx : i.val<E.length
      · rw [hGetOld i hidx]
        simpa only [A,Option.elim,dif_pos hidx] using
          mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
            (hE _ (List.get_mem E ⟨i.val,hidx⟩)) hu
      · rw [hGetLast i hidx]
        simp only [A,Option.elim,dif_neg hidx,Set.mem_preimage]
  have hNonexc : y ∉ exceptionalLocus n π :=
    fun h => hy (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
  have hNew := isCoordinateFamilyAt_of_preimage hπ.contMDiff hNonexc hOpen hy hDictionary hOld
  refine ⟨S₀,fun i => if hi : i.val<E.length then S ⟨i.val,hi⟩ else ∅,hNew,?_⟩
  intro i hi
  by_cases hidx : i.val<E.length
  · have hi' : y ∈ geoStrictTransform π C (E.get ⟨i.val,hidx⟩) := by
      rwa [hGetOld i hidx] at hi
    have hOldMem := (mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
      (hE _ (List.get_mem E ⟨i.val,hidx⟩)) hy).mp hi'
    simpa only [dif_pos hidx] using hcard ⟨i.val,hidx⟩ hOldMem
  · have hyC : π y ∈ C := by rwa [hGetLast i hidx] at hi
    exact False.elim (hy hyC)

/-- On the carrier, the support of a coherent row nonzero along the carrier is its locus of
order `≥ 1`. -/
theorem mem_support_iff_one_le_order {N : Set Y} {I : GermIdeal n Y}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y) {y : Y} :
    y ∈ N ∩ I.zeroLocus ↔ y ∈ N ∧ 1 ≤ ordinaryTraceOrder N I y := by
  rw [←cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
  constructor
  · intro hy
    exact ⟨hy.1,(ordinaryTraceOrder_cosupport_iff hN hI hnz hy.1 1).mp hy⟩
  · rintro ⟨hyN,hle⟩
    exact (ordinaryTraceOrder_cosupport_iff hN hI hnz hyN 1).mpr hle

/-- Off the support, a row has order `0` on the carrier. -/
theorem ordinaryTraceOrder_eq_zero_of_notMem_support {N : Set Y} {I : GermIdeal n Y}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y) {y : Y} (hy : y ∈ N)
    (hyS : y ∉ N ∩ I.zeroLocus) : ordinaryTraceOrder N I y=0 := by
  by_contra h
  exact hyS ((mem_support_iff_one_le_order hN hI hnz).mpr ⟨hy,Nat.one_le_iff_ne_zero.mpr h⟩)

/-- **One blowup whose centre misses the support of a relatively principal row.**  The order of
the next relative strict row is at most the old one (it is a unit along the centre, so the
equimultiple bound applies with level `0`), equal to it off the centre, and the new support is
exactly the preimage of the old support. -/
theorem nextRelativeStrict_support_of_disjoint (hn : 0 < n) {N C : Set Y} {I : GermIdeal n Y}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ x ∈ N,∃ f : Y → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    {π : Z → Y} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (hCS : Disjoint C (N ∩ I.zeroLocus))
    (hN' : IsClosedSubmanifold n (geoStrictTransform π C N)) :
    (∀ z ∈ geoStrictTransform π C N,
      ordinaryTraceOrder (geoStrictTransform π C N) (nextRelativeStrict N I C π) z ≤
        ordinaryTraceOrder N I (π z)) ∧
    (∀ z ∈ geoStrictTransform π C N,π z ∉ C →
      ordinaryTraceOrder (geoStrictTransform π C N) (nextRelativeStrict N I C π) z=
        ordinaryTraceOrder N I (π z)) ∧
    geoStrictTransform π C N ∩ (nextRelativeStrict N I C π).zeroLocus=π ⁻¹' (N ∩ I.zeroLocus) := by
  have hzero : ∀ x ∈ C,ordinaryTraceOrder N I x=0 := fun x hx =>
    ordinaryTraceOrder_eq_zero_of_notMem_support hN hI hnz (hCN hx) (Set.disjoint_left.mp hCS hx)
  have hle : ∀ z ∈ geoStrictTransform π C N,
      ordinaryTraceOrder (geoStrictTransform π C N) (nextRelativeStrict N I C π) z ≤
        ordinaryTraceOrder N I (π z) := by
    intro z hz
    exact nextRelativeStrict_order_le_of_locally_constant_on_centre hn hN hI hnz hpr hπ hCN
      (fun x hx => Eventually.of_forall fun x' hx' => by rw [hzero x' hx',hzero x hx]) hz
  have heq : ∀ z ∈ geoStrictTransform π C N,π z ∉ C →
      ordinaryTraceOrder (geoStrictTransform π C N) (nextRelativeStrict N I C π) z=
        ordinaryTraceOrder N I (π z) := fun z hz hzC =>
    nextRelativeStrict_order_eq_off_centre hn hN hI hnz hpr hπ hCN hz hzC
  obtain ⟨_hEq,hS,hSNz,_⟩ := nextRelativeStrict_actual_geometry hn hN hI hnz hpr hπ hCN
  have hS' : (nextRelativeStrict N I C π).IsCoherent := hS
  have hSNz' : ∀ z ∈ geoStrictTransform π C N,
      IsNonzeroAlongAt (geoStrictTransform π C N) (nextRelativeStrict N I C π) z := hSNz
  refine ⟨hle,heq,?_⟩
  ext z
  constructor
  · intro hz
    have hpos := ((mem_support_iff_one_le_order hN' hS' hSNz').mp hz).2
    have hzN : π z ∈ N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz.1
    exact (mem_support_iff_one_le_order hN hI hnz).mpr ⟨hzN,hpos.trans (hle z hz.1)⟩
  · intro hz
    have hzC : π z ∉ C := fun hc => Set.disjoint_left.mp hCS hc hz
    have hzN' : z ∈ geoStrictTransform π C N :=
      (mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN.1 hzC).mpr hz.1
    have hpos := ((mem_support_iff_one_le_order hN hI hnz).mp hz).2
    refine (mem_support_iff_one_le_order hN' hS' hSNz').mpr ⟨hzN',?_⟩
    rw [heq z hzN' hzC]
    exact hpos

/-- The strict transform of a closed set missing the centre is its preimage. -/
theorem geoStrictTransform_eq_preimage_of_disjoint {S C : Set Y} {π : Z → Y}
    (hπ : Continuous π) (hS : IsClosed S) (hCS : Disjoint C S) :
    geoStrictTransform π C S=π ⁻¹' S := by
  have hSC : S \ C=S := by
    ext z
    exact ⟨fun hz => hz.1,fun hz => ⟨hz,fun hc => Set.disjoint_left.mp hCS hc hz⟩⟩
  change closure (π ⁻¹' (S \ C))=π ⁻¹' S
  rw [hSC]
  exact (hS.preimage hπ).closure_eq

/-- **Density across one blowup off the centre**: if `S` is dense off the members of `F` and
misses the centre, its preimage is dense off the strict transforms of the members and the new
exceptional divisor. -/
theorem preimage_subset_closure_strict_of_disjoint {S C : Set Y} {F : List (Set Y)} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hF : ∀ G ∈ F,IsClosed G) (hCS : Disjoint C S)
    (hDense : S ⊆ closure (S \ ⋃ G ∈ F,G)) :
    π ⁻¹' S ⊆ closure (π ⁻¹' S \ ⋃ G ∈ F.map (geoStrictTransform π C) ++ [π ⁻¹' C],G) := by
  obtain ⟨s,hs,hsπ,hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  let O : Opens Y := ⟨Cᶜ,hπ.1.1.isOpen_compl⟩
  let D : Set Y := S \ ⋃ G ∈ F,G
  intro y hy
  have hyC : π y ∉ C := fun hc => Set.disjoint_left.mp hCS hc hy
  let p : O := ⟨π y,hyC⟩
  have hpD : p ∈ closure ((Subtype.val : O → Y) ⁻¹' D) := by
    have h : p ∈ (Subtype.val : O → Y) ⁻¹' closure D := hDense hy
    erw [O.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val D] at h
    exact h
  have hImage : s '' ((Subtype.val : O → Y) ⁻¹' D) ⊆
      π ⁻¹' S \ ⋃ G ∈ F.map (geoStrictTransform π C) ++ [π ⁻¹' C],G := by
    rintro _ ⟨q,hq,rfl⟩
    have hπs : π (s q)=q.val := congrFun hsπ q
    refine ⟨by rw [mem_preimage,hπs]; exact hq.1,?_⟩
    rw [mem_iUnion₂]
    rintro ⟨G,hG,hsG⟩
    rcases List.mem_append.mp hG with hOld | hExc
    · obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hOld
      have hqC : π (s q) ∉ C := by rw [hπs]; exact q.property
      have hK' := (mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous (hF K hK) hqC).mp hsG
      rw [hπs] at hK'
      exact hq.2 (mem_iUnion₂.mpr ⟨K,hK,hK'⟩)
    · rw [List.mem_singleton] at hExc
      rw [hExc,mem_preimage,hπs] at hsG
      exact q.property hsG
  have hy' : y=s p := (hsec y hyC).symm
  rw [hy']
  exact closure_mono hImage (image_closure_subset_closure_image hs.continuous ⟨p,hpD,rfl⟩)

/-- The current support `S = N ∩ V(J)` of the original row `H` after the actual prefix `T`. -/
def rowSupport (W H : Set X) (T : BlowupTower X Y) : Set Y :=
  (geoTransformAlong (geometricTemplate W []) T).N ∩
    (chronologicalMarked (originalRelativeMemberMarked W H) T).ideal.zeroLocus

/-- The current boundary `F_i = old.eraseIdx i ++ born` of row `i` after the actual prefix `T`. -/
def rowBoundary (W : Set X) (E : List (Set X)) (i : ℕ) (T : BlowupTower X Y) : List (Set Y) :=
  (E.map (strictAlong T)).eraseIdx i ++ (geoTransformAlong (geometricTemplate W []) T).E

/-- The boundary of a row after one more blowup: strict transforms of the old boundary, then the
new exceptional divisor. -/
theorem rowBoundary_step (W : Set X) (E : List (Set X)) (i : ℕ) {Q : CMfd.{u} n}
    (T : BlowupTower X Q) (C : Set Q) (π : Z → Q) (hπ : IsBlowupAlong n C π) :
    rowBoundary W E i (.step T C π hπ)=
      (rowBoundary W E i T).map (geoStrictTransform π C) ++ [π ⁻¹' C] := by
  have hOld : E.map (strictAlong (.step T C π hπ))=(E.map (strictAlong T)).map (geoStrictTransform π C) := by
    rw [List.map_map]
    rfl
  change (E.map (strictAlong (.step T C π hπ))).eraseIdx i ++
      ((geoTransformAlong (geometricTemplate W []) T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C])=
    ((E.map (strictAlong T)).eraseIdx i ++ (geoTransformAlong (geometricTemplate W []) T).E).map
      (geoStrictTransform π C) ++ [π ⁻¹' C]
  rw [hOld,List.eraseIdx_map,List.map_append,List.append_assoc]

/-- The invariant carried along an empty-near-the-support tail. -/
private theorem empty_tail_aux (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hPrep : ActualRowPrepared W E i T)
    (U : Opens Y) (hSU : rowSupport W (E.get i) T ⊆ U) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate W []) (T.append R) → CentresAvoid U R →
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal y ≤ 1) ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,R.proj y ∈ U →
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal y=
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (R.proj y)) ∧
      rowSupport W (E.get i) (T.append R)=R.proj ⁻¹' rowSupport W (E.get i) T ∧
      (∀ G ∈ rowBoundary W E i.val (T.append R),IsClosed G) ∧
      HasNormalCrossings n (rowSupport W (E.get i) (T.append R)) (rowBoundary W E i.val (T.append R)) ∧
      rowSupport W (E.get i) (T.append R) ⊆
        closure (rowSupport W (E.get i) (T.append R) \ ⋃ G ∈ rowBoundary W E i.val (T.append R),G) := by
  obtain ⟨hOrd,hNC,hDenseS⟩ := hPrep
  have hAN : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=
      (geoTransformAlong (geometricTemplate W []) T).N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  obtain ⟨hZ,_hWhole,_hTail⟩ := actual_original_selected_residual_tail hn hW hE hdense i T hT hOrd
  have hSTc : IsClosed (rowSupport W (E.get i) T) := by
    have h := hZ.1
    unfold rowSupport
    rwa [hAN] at h
  intro Q R
  induction R with
  | refl =>
    intro _hR _hAv
    have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
    refine ⟨?_,fun y _ _ => rfl,rfl,?_,hNC,hDenseS⟩
    · intro y hy
      have h := hOrd y (hAN ▸ hy)
      rw [hAN] at h
      exact h
    · intro G hG
      apply hRecorded.2.1.1 G
      rcases List.mem_append.mp hG with hOld | hBorn
      · exact List.mem_append_left _ (List.mem_of_mem_eraseIdx hOld)
      · exact List.mem_append_right _ hBorn
  | step R C π hπ ih =>
    intro hR hAv
    obtain ⟨hOrdR,hDictR,hSuppR,hClosedR,hNCR,hDenseR⟩ := ih hR.1 hAv.1
    let A := geoTransformAlong (geometricTemplate W []) (T.append R)
    let M := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)
    obtain ⟨hMN,_hME,_hMark,hwM,hnzM,hprM⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense i (T.append R) hR.1
    obtain ⟨_hMN',_hME',_hMark',hwM',_hnzM',_hprM'⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense i
        (T.append (.step R C π hπ)) hR
    have hCN : C ⊆ M.N := by
      rw [hMN]
      exact hR.2.subset_N
    have hSR : rowSupport W (E.get i) (T.append R)=M.N ∩ M.ideal.zeroLocus := by
      change A.N ∩ M.ideal.zeroLocus=M.N ∩ M.ideal.zeroLocus
      rw [hMN]
    have hSRc : IsClosed (rowSupport W (E.get i) (T.append R)) := by
      rw [hSuppR]
      exact hSTc.preimage R.contMDiff_proj.continuous
    have hCS : Disjoint C (rowSupport W (E.get i) (T.append R)) := by
      rw [hSuppR]
      exact Set.disjoint_of_subset_right (Set.preimage_mono hSU) hAv.2
    have hN' : IsClosedSubmanifold n (geoStrictTransform π C M.N) := hwM'.isClosedSubmanifold_N
    have hStep := nextRelativeStrict_support_of_disjoint hn hwM.isClosedSubmanifold_N hwM.isCoherent
      hnzM hprM hπ hCN (hSR ▸ hCS) hN'
    have hNewN : (geoTransformAlong (geometricTemplate W []) (T.append (.step R C π hπ))).N=
        geoStrictTransform π C M.N := by
      change geoStrictTransform π C A.N=geoStrictTransform π C M.N
      rw [hMN]
    have hNewS : rowSupport W (E.get i) (T.append (.step R C π hπ))=
        π ⁻¹' rowSupport W (E.get i) (T.append R) := by
      rw [hSR,←hStep.2.2]
      change (geoTransformAlong (geometricTemplate W []) (T.append (.step R C π hπ))).N ∩
        (nextRelativeStrict M.N M.ideal C π).zeroLocus=_
      rw [hNewN]
    have hNewF : rowBoundary W E i.val (T.append (.step R C π hπ))=
        (rowBoundary W E i.val (T.append R)).map (geoStrictTransform π C) ++ [π ⁻¹' C] :=
      rowBoundary_step W E i.val (T.append R) C π hπ
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro y hy
      rw [hNewN] at hy ⊢
      change ordinaryTraceOrder (geoStrictTransform π C M.N) (nextRelativeStrict M.N M.ideal C π) y ≤ 1
      have hyN : π y ∈ A.N := by
        rw [←hMN]
        exact geoStrictTransform_subset_preimage hπ.contMDiff.continuous hwM.isClosedSubmanifold_N.1 hy
      have h1 := hOrdR (π y) hyN
      rw [←hMN] at h1
      exact (hStep.1 y hy).trans h1
    · intro y hy hyU
      rw [hNewN] at hy ⊢
      change ordinaryTraceOrder (geoStrictTransform π C M.N) (nextRelativeStrict M.N M.ideal C π) y=_
      have hyC : π y ∉ C := fun hc => Set.disjoint_left.mp hAv.2 hc hyU
      have hyN : π y ∈ A.N := by
        rw [←hMN]
        exact geoStrictTransform_subset_preimage hπ.contMDiff.continuous hwM.isClosedSubmanifold_N.1 hy
      have h1 := hDictR (π y) hyN hyU
      rw [←hMN] at h1
      exact (hStep.2.1 y hy hyC).trans h1
    · rw [hNewS,hSuppR]
      rfl
    · rw [hNewF]
      intro G hG
      rcases List.mem_append.mp hG with hOld | hExc
      · obtain ⟨K,_hK,rfl⟩ := List.mem_map.mp hOld
        exact isClosed_closure
      · rw [List.mem_singleton] at hExc
        rw [hExc]
        exact hπ.1.1.preimage hπ.contMDiff.continuous
    · rw [hNewS,hNewF]
      intro y hy
      have hyC : π y ∉ C := fun hc => Set.disjoint_left.mp hCS hc hy
      have h := normalCrossingsAt_strict_of_notMem hSRc hClosedR hπ hyC (hNCR (π y) hy)
      rw [geoStrictTransform_eq_preimage_of_disjoint hπ.contMDiff.continuous hSRc hCS] at h
      exact h
    · rw [hNewS,hNewF]
      exact preimage_subset_closure_strict_of_disjoint hπ hClosedR hCS hDenseR

/-- **O1: a prepared row stays prepared across a tail that is empty near its support.**
Row `i` prepared at the actual prefix `T`, `U` an open neighbourhood of its support `S_i`, and `R`
a W-test tail after `T` whose restriction to `U` is an empty tower.  Then row `i` is prepared at
`T·R`, its new support is the preimage of `S_i`, and at every point of the new carrier over `U` the
row order is the old one. -/
theorem actual_prepared_row_empty_tail (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hPrep : ActualRowPrepared W E i T) (U : Opens Y)
    (hSU : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ U)
    {Q : CMfd.{u} n} (R : BlowupTower Y Q)
    (hR : IsGeoTestTower (geometricTemplate W []) (T.append R))
    (hEmpty : IsEmptyTower (restrict U R)) :
    ActualRowPrepared W E i (T.append R) ∧
      rowSupport W (E.get i) (T.append R)=R.proj ⁻¹' rowSupport W (E.get i) T ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,R.proj y ∈ U →
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal y=
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (R.proj y) := by
  have hAN : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=
      (geoTransformAlong (geometricTemplate W []) T).N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hSU' : rowSupport W (E.get i) T ⊆ U := by
    unfold rowSupport
    rw [←hAN]
    exact hSU
  obtain ⟨hOrdR,hDictR,hSuppR,_hClosedR,hNCR,hDenseR⟩ :=
    empty_tail_aux hn hW hE hdense i T hT hFull hPrep U hSU' R hR
      ((isEmptyTower_restrict_iff U R).mp hEmpty)
  have hRN : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).N=
      (geoTransformAlong (geometricTemplate W []) (T.append R)).N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) (T.append R)).1
  refine ⟨⟨?_,hNCR,hDenseR⟩,hSuppR,hDictR⟩
  intro y hy
  rw [hRN] at hy ⊢
  exact hOrdR y hy

/-- **The carrier phase keeps every prepared row prepared** (step (T1) of the G4K1B control flow).
The held true-defect exit, with centres over the true distinct defect, ends with every row of order
`≤ 1` and empty defect, and every row prepared at its start is prepared at its end. -/
theorem exists_actual_carrier_phase_keeps_prepared (hn : 0 < n)
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
      chronologicalDistinctDefect W E (T.append Q)=∅ ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) (T.append Q)).ideal x ≤ 1) ∧
      ∀ i : Fin E.length,ActualRowPrepared W E i T → ActualRowPrepared W E i (T.append Q) := by
  obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOver,hEmpty,hRows,hProt⟩ :=
    HironakaG34DefectEmptyOrder.exists_actual_carrier_phase_protected hn hW hE hdense d hReg hK
      T hT hFull hSharp
  refine ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOver,hEmpty,hRows,fun i hPrep => ?_⟩
  obtain ⟨U,hSU,hEmptyU⟩ := hProt i hPrep.1 hPrep.2.1 hPrep.2.2
  exact (actual_prepared_row_empty_tail hn hW hE hdense i T hT hFull hPrep U hSU Q hTQ hEmptyU).1

/-- **A carrier-preparation history of another row keeps a prepared row prepared** (phase (C')). -/
theorem actual_prepared_row_carrier_phase_keeps_prepared
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hPrep : ActualRowPrepared W E i T) (j : Fin E.length) (hne : j ≠ i)
    {Q : CMfd.{u} n} (R : BlowupTower Y Q)
    (hR : IsGeoTestTower (geometricTemplate W []) (T.append R))
    (hC : HironakaG34PreparedRowCarrierOrder.CentresInRowSingular n W (E.get j) T R) :
    ActualRowPrepared W E i (T.append R) := by
  obtain ⟨U,hSU,hU⟩ := HironakaG34PreparedRowCarrierOrder.actual_prepared_row_carrier_phase_empty
    hn hW hE hdense i T hT hFull hPrep.1 hPrep.2.1 hPrep.2.2 j hne
  exact (actual_prepared_row_empty_tail hn hW hE hdense i T hT hFull hPrep U hSU R hR
    (hU R hR hC)).1

end
end Hironaka.HironakaG34PreparedRowEmptyTail
