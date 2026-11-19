import Hironaka.Resolution.HironakaG4SelectedSupportUnitRowOrder
import Hironaka.Resolution.HironakaG34PreparedRowLowerGammaOrEmpty

/-! # The carrier-preparation phase of another row is empty near a prepared row

Lane G34 (run 0080).  Blueprint: `hironaka-g34-resume-prepared-row-carrier-order.tex`.

Setting: an actual original mixed prefix `T` (both geometric tests), carrier `N = A.N`, old list
`old = E.map (strictAlong T)`, born list `A.E`, residual rows `J_k` (the chronological strict
residuals of the original members), supports `S_k = N ∩ V(J_k)`, `F_k = old.eraseIdx k ++ A.E`.

* `actual_prepared_row_other_order_le_one`: if row `i` is prepared (order `≤ 1`, `S_i` has normal
  crossings with `F_i`, `S_i` dense off `F_i`) then for EVERY other row `j ≠ i` the residual `J_j`
  has ordinary trace order `≤ 1` at every point of `S_i`.  Proof: the old member `H_j` is a member of
  `F_i`, so `S_i` has normal crossings with `[H_j]` and is dense off it; hence the trace of `I(H_j)`
  on `S_i` has order `≤ 1` (singleton sharp-bad locus = trace cosupport of mark 2); the whole trace
  `I(H_j)|N` lies in `J_j` (its non-monomial part), and the order along `N` is at most the order
  along the smaller `S_i`.
* `actual_prepared_row_other_order_le_one_near`: the open set `U_j = N ∖ {ord J_j ≥ 2}`-complement
  (the complement of the closed cosupport of `(J_j, 2)`) contains `S_i`, and on `N` it is exactly
  the locus `ord J_j ≤ 1`.
* `CentresInRowSingular`: a tail `R` after `T` is a carrier-preparation history of the original row
  `H` when each centre lies in the locus where the CURRENT strict residual of that row has order
  `≥ 2` on the current carrier.
* `centresOver_rowSingular`: the centres of every such W-test tail lie over the ORIGINAL closed set
  `{ord J_j ≥ 2}` (order is unchanged off the centres).
* `actual_prepared_row_carrier_phase_empty`: hence EVERY carrier-preparation history of row `j`
  restricts to a literal empty tower on an open neighbourhood of the prepared support `S_i`.

No carrier-preparation history is constructed and no global driver is assumed. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34PreparedRowCarrierOrder
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower BlowupStrictSubmanifold
  NormalCrossings NormalCrossingsComparison HironakaSharpNormalCrossingsOpenLocus
  HironakaG4OriginalSelectedLowerBoundaryHistory HironakaG4OriginalSelectedResidualTail
  HironakaG4RecordedTowerResidualCompatibility HironakaG4EquimultipleRelativeOrder
  HironakaG4OrderOneTransverseCoordinates HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  GermIdealOrder RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong
  NonmonomialTransformAlong MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaSharpActualChronologicalStrictStep DivisorExponentAlong
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Pointwise normal crossings with a subfamily (private copies exist in several modules). -/
private theorem normalCrossingsAt_of_forall_mem {N : Set X} {E E' : List (Set X)}
    {x : X} (h : normalCrossingsAt (n := n) N E x)
    (hsub : ∀ G ∈ E', G ∈ E) : normalCrossingsAt (n := n) N E' x := by
  obtain ⟨S₀, S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hS⟩ := h
  have hidx : ∀ j : Fin E'.length, ∃ i : Fin E.length, E.get i = E'.get j :=
    fun j => List.mem_iff_get.mp (hsub _ (List.get_mem _ _))
  choose idx hidx using hidx
  refine ⟨S₀, fun j => S (idx j), ⟨Φ, hΦt, hΦ0, ?_⟩,
    fun j hj => hS (idx j) (by rw [hidx]; exact hj)⟩
  rintro (_ | j) hj y hy hyΦ
  · exact hΦA none hj hy hyΦ
  · have h1 := hΦA (some (idx j)) (by simp only [Option.elim]; rw [hidx]; exact hj) hy hyΦ
    simp only [Option.elim] at h1 ⊢
    rw [hidx] at h1
    exact h1

/-- **Order of another row on a prepared support.**  Row `i` prepared, `j ≠ i`: at every point of
`S_i` the residual `J_j` of row `j` has ordinary trace order `≤ 1` on the current carrier. -/
theorem actual_prepared_row_other_order_le_one
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (j : Fin E.length) (hne : j ≠ i) {x : Y}
    (hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) :
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal x ≤ 1 := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let Ai := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  let Jj := (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal
  let S := A.N ∩ Ai.ideal.zeroLocus
  let H := strictAlong T (E.get j)
  let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
  have hAN : Ai.N = A.N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hxS : x ∈ S := ⟨hAN ▸ hxi.1,hxi.2⟩
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  obtain ⟨hcI,_hnzI,hNm,_hFactor⟩ := hRecorded.2.2.2.2 j
  -- `S_i` is a closed submanifold
  obtain ⟨hZ,_hWhole,_hTail⟩ := actual_original_selected_residual_tail hn hW hE hdense i T hT hOrd
  have hS : IsClosedSubmanifold n S := by
    have hZS : Ai.N ∩ Ai.ideal.zeroLocus = S := by
      change Ai.N ∩ Ai.ideal.zeroLocus = A.N ∩ Ai.ideal.zeroLocus
      rw [hAN]
    rw [←hZS]
    exact hZ
  -- the old member `H_j` belongs to `F_i`
  have hHmem : H ∈ E.map (strictAlong T) ++ A.E :=
    List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E j))
  have hH : IsSNCDivisor n [H] :=
    isSNCDivisor_of_sublist hRecorded.2.1 (List.singleton_sublist.mpr hHmem)
  let jj : Fin (E.map (strictAlong T)).length := ⟨j.val,by simp⟩
  have hGet : (E.map (strictAlong T)).get jj = H := by simp [jj,H]
  have hHF : H ∈ F :=
    List.mem_append_left _ (List.mem_eraseIdx_iff_getElem.mpr
      ⟨j.val,jj.isLt,(fun heq => hne (Fin.ext heq)),by
        simpa only [List.get_eq_getElem] using hGet⟩)
  have hDenseH : S ⊆ closure (S \ H) := by
    apply (show S ⊆ closure (S \ ⋃ G ∈ F,G) from hDenseS).trans (closure_mono ?_)
    intro z hz
    exact ⟨hz.1,fun hzH => hz.2 (mem_iUnion₂.mpr ⟨H,hHF,hzH⟩)⟩
  have hNCx : normalCrossingsAt (n := n) S [H] x := by
    have h := (show HasNormalCrossings n S F from hNC) x hxS
    exact normalCrossingsAt_of_forall_mem h (fun G hG => by
      rw [List.mem_singleton] at hG
      rw [hG]
      exact hHF)
  -- the coherent residual `J_j` and its order/cosupport dictionary on `N`
  obtain ⟨hNj,_hEj,_hDj,hwJj,hnzJj,_hprJj⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
  have hJnz : ∀ z ∈ A.N, IsNonzeroAlongAt A.N Jj z := by
    rw [←hNj]
    exact hnzJj
  have hxN : x ∈ A.N := hxS.1
  by_contra hNot
  have hGe : 2 ≤ ordinaryTraceOrder A.N Jj x := by
    change ¬ ordinaryTraceOrder A.N Jj x ≤ 1 at hNot
    omega
  have hCosJ := (ordinaryTraceOrder_cosupport_iff hN hwJj.isCoherent hJnz hxN 2).mpr hGe
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (HironakaSharpSingleBoundaryTraceCentre.originalBoundary_isClosedSubmanifold hn hH)
  have hCosH : x ∈ cosupport n S (vanishingIdeal (n := n) H) 2 := by
    refine ⟨hxS,fun g hg => ?_⟩
    have hgJ : Jj.mem x g := by
      change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.mem x g
      rw [←hNm]
      exact le_nonmonomialPartAlong_self hcI x g (le_restrictOn hcH x g hg)
    exact (hCosJ.2 g hgJ).mono_set (fun z hz => hz.1)
  rw [←originalSharpBadLocus_singleton_eq_cosupport hn hS hH hDenseH] at hCosH
  exact hCosH.2 hNCx

/-- The closed locus `{ord J_j ≥ 2}` of the residual of row `j` on the current carrier. -/
theorem isClosed_rowSingular (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (j : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) :
    IsClosed (cosupport n (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal 2) := by
  obtain ⟨hNj,_hEj,_hDj,hwJj,_hnzJj,_hprJj⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
  have hN := hwJj.isClosedSubmanifold_N
  rw [hNj] at hN
  exact GiraudAlong.isClosed_cosupport_along hwJj.isCoherent hN 2

/-- **The order-`≤ 1` locus of another row is an open neighbourhood of a prepared support.**
With `U_j` the complement of the closed cosupport `{ord J_j ≥ 2}` on the carrier `N`: `S_i ⊆ U_j`,
and a point of `N` lies in `U_j` iff `J_j` has order `≤ 1` there. -/
theorem actual_prepared_row_other_order_le_one_near
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (j : Fin E.length) (hne : j ≠ i) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let Jj := (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal
    let Fj := cosupport n A.N Jj 2
    ∃ U : Opens Y, (U : Set Y) = Fjᶜ ∧
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ U ∧
      ∀ y ∈ A.N, (y ∈ (U : Set Y) ↔ ordinaryTraceOrder A.N Jj y ≤ 1) := by
  intro A Jj Fj
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  obtain ⟨hNj,_hEj,_hDj,hwJj,hnzJj,_hprJj⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
  have hJnz : ∀ z ∈ A.N, IsNonzeroAlongAt A.N Jj z := by
    rw [←hNj]
    exact hnzJj
  have hClosed : IsClosed Fj := isClosed_rowSingular hn hW hE hdense j T hT
  refine ⟨⟨Fjᶜ,hClosed.isOpen_compl⟩,rfl,?_,?_⟩
  · intro x hx hxF
    have hle := actual_prepared_row_other_order_le_one hn hW hE hdense i T hT hFull hOrd hNC
      hDenseS j hne hx
    have hge : 2 ≤ ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal x :=
      (ordinaryTraceOrder_cosupport_iff hN hwJj.isCoherent hJnz hxF.1 2).mp hxF
    omega
  · intro y hy
    change y ∉ Fj ↔ ordinaryTraceOrder A.N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1
    rw [ordinaryTraceOrder_cosupport_iff hN hwJj.isCoherent hJnz hy 2]
    omega

variable (n) in
/-- **A carrier-preparation history of an original row.**  Every centre of the tail `R` (appended
to the actual prefix `T`) lies in the locus where the CURRENT strict residual of the original
member `H` has ordinary trace order `≥ 2` on the current carrier. -/
def CentresInRowSingular (W H : Set X) (T : BlowupTower X Y) :
    {Q : CMfd.{u} n} → BlowupTower Y Q → Prop
  | _, .refl => True
  | _, .step R C _ _ => CentresInRowSingular W H T R ∧
      ∀ y ∈ C, y ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N ∧
        2 ≤ ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          (chronologicalMarked (originalRelativeMemberMarked W H) (T.append R)).ideal y

/-- Along a carrier-preparation tail of row `j`, the centres lie over the ORIGINAL locus
`{ord J_j ≥ 2}`, and off it the order of the current residual is still `≤ 1`. -/
private theorem centresOver_rowSingular_aux (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (j : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let Fj := cosupport n A.N (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal 2
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate W []) (T.append R) →
      CentresInRowSingular n W (E.get j) T R →
      CentresOver Fj R ∧
        ∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N, R.proj y ∉ Fj →
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append R)).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal y ≤ 1 := by
  intro A Fj Q R
  induction R with
  | refl =>
    intro _hR _hC
    refine ⟨trivial,fun y hy hyF => ?_⟩
    obtain ⟨hNj,_hEj,_hDj,hwJj,hnzJj,_hprJj⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
    have hN := hwJj.isClosedSubmanifold_N
    rw [BlowupTower.append_refl] at hy ⊢
    rw [←hNj] at hy ⊢
    have hy' : y ∉ cosupport n (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal 2 := by
      rw [hNj]
      exact hyF
    rw [ordinaryTraceOrder_cosupport_iff hN hwJj.isCoherent hnzJj hy 2] at hy'
    omega
  | step R C π hπ ih =>
    intro hR hC
    obtain ⟨hOverR,hOrdR⟩ := ih hR.1 hC.1
    let M := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)
    obtain ⟨hMN,_hME,_hMark,hwM,hnzM,hprM⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense j (T.append R) hR.1
    have hCover : C ⊆ R.proj ⁻¹' Fj := by
      intro y hyC
      obtain ⟨hyN,hy2⟩ := hC.2 y hyC
      by_contra hyF
      have := hOrdR y hyN hyF
      omega
    refine ⟨⟨hOverR,hCover⟩,fun y hy hyF => ?_⟩
    have hyC : π y ∉ C := fun hc => hyF (hCover hc)
    have hCN : C ⊆ M.N := by
      rw [hMN]
      exact hR.2.subset_N
    have hNewN : (geoTransformAlong (geometricTemplate W [])
        (T.append (.step R C π hπ))).N = geoStrictTransform π C M.N := by
      change geoStrictTransform π C (geoTransformAlong (geometricTemplate W []) (T.append R)).N =
        geoStrictTransform π C M.N
      rw [hMN]
    have hyM : y ∈ geoStrictTransform π C M.N := by
      rw [←hNewN]
      exact hy
    have hyOldM : π y ∈ M.N :=
      geoStrictTransform_subset_preimage hπ.contMDiff.continuous hwM.isClosedSubmanifold_N.1 hyM
    have hyOld : π y ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N :=
      hMN ▸ hyOldM
    have hBefore : ordinaryTraceOrder M.N M.ideal (π y) ≤ 1 := by
      rw [hMN]
      exact hOrdR (π y) hyOld hyF
    have hEq := nextRelativeStrict_order_eq_off_centre hn hwM.isClosedSubmanifold_N
      hwM.isCoherent hnzM hprM hπ hCN hyM hyC
    rw [hNewN]
    change ordinaryTraceOrder (geoStrictTransform π C M.N)
      (nextRelativeStrict M.N M.ideal C π) y ≤ 1
    exact hEq.trans_le hBefore

/-- **Centres of a carrier-preparation history lie over the original singular locus of the row.** -/
theorem centresOver_rowSingular (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (j : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    {Q : CMfd.{u} n} (R : BlowupTower Y Q)
    (hR : IsGeoTestTower (geometricTemplate W []) (T.append R))
    (hC : CentresInRowSingular n W (E.get j) T R) :
    CentresOver (cosupport n (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal 2) R :=
  (centresOver_rowSingular_aux hn hW hE hdense j T hT R hR hC).1

/-- **The carrier-preparation phase of another row is a literal empty phase near a prepared row.**
Row `i` prepared, `j ≠ i`: there is ONE open neighbourhood `U` of the prepared support `S_i` (the
order-`≤ 1` locus of `J_j`) such that EVERY carrier-preparation W-test history of row `j` after `T`
restricts to an empty tower on `U`. -/
theorem actual_prepared_row_carrier_phase_empty
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (j : Fin E.length) (hne : j ≠ i) :
    ∃ U : Opens Y,
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ U ∧
      ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
        IsGeoTestTower (geometricTemplate W []) (T.append R) →
        CentresInRowSingular n W (E.get j) T R → IsEmptyTower (restrict U R) := by
  obtain ⟨U,hUeq,hSU,_hU⟩ := actual_prepared_row_other_order_le_one_near hn hW hE hdense i T hT
    hFull hOrd hNC hDenseS j hne
  refine ⟨U,hSU,fun R hR hC => ?_⟩
  have hDisj : Disjoint (U : Set Y) (cosupport n (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal 2) := by
    rw [hUeq]
    exact disjoint_compl_left
  exact isEmptyTower_restrict_of_centresOver U hDisj R
    (centresOver_rowSingular hn hW hE hdense j T hT R hR hC)

end
end Hironaka.HironakaG34PreparedRowCarrierOrder
