import Hironaka.Resolution.HironakaG4OrderedDefectStamp
import Hironaka.Resolution.HironakaNormalCrossingsOrderedMonomialTail
import Hironaka.Resolution.HironakaG8E4cProduct
import Mathlib.Data.Fin.Embedding

/-! Inserting a literal empty old boundary slot preserves the native retained
rows, their distinct defect, and their ordered stamp under the insertion. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4OrderedCrestEmptyOld

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings
  MonomialPartAlong RestrictedIdealExtension DivisorExponentAlong GermIdealOrder
  IdealWeightPowers InvertibleIdealQuotient RelativePrincipalizationSpan
  HironakaG4PreparedCentreCoordinates HironakaG4OrderedDefectStamp
  HironakaActualRetainedBoundaryJointStep HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualChronologicalDistinctDefect

variable {n : ℕ} {X : CMfd.{u} n}

def oldBoundaryInsert (old : List (Set X)) (j : Fin (old.length + 1)) :
    List (Set X) := old.insertIdx j.val ∅

/-- The literal length identification after inserting the empty slot. -/
theorem oldBoundaryInsert_length (old : List (Set X)) (j : Fin (old.length + 1)) :
    (oldBoundaryInsert old j).length = old.length + 1 :=
  List.length_insertIdx_of_le_length (Nat.le_of_lt_succ j.isLt) ∅

def oldBoundaryInsertPos {old : List (Set X)} (j : Fin (old.length + 1)) :
    Fin (oldBoundaryInsert old j).length :=
  finCongr (oldBoundaryInsert_length old j).symm j

/-- Order-preserving indexing of the original slots in the enlarged list. -/
def oldBoundaryInsertEmb {old : List (Set X)} (j : Fin (old.length + 1)) :
    Fin old.length ↪ Fin (oldBoundaryInsert old j).length :=
  (Fin.succAboveEmb j).trans (finCongr (oldBoundaryInsert_length old j).symm).toEmbedding

theorem oldBoundaryInsert_get_pos {old : List (Set X)} (j : Fin (old.length + 1)) :
    (oldBoundaryInsert old j).get (oldBoundaryInsertPos (old := old) j) = ∅ :=
  List.getElem_insertIdx_self (oldBoundaryInsertPos (old := old) j).isLt

theorem oldBoundaryInsert_get_emb {old : List (Set X)} (j : Fin (old.length + 1))
    (i : Fin old.length) :
    (oldBoundaryInsert old j).get (oldBoundaryInsertEmb (old := old) j i) = old.get i := by
  have he : (oldBoundaryInsertEmb (old := old) j i).val = (j.succAbove i).val := rfl
  change (old.insertIdx j.val ∅)[(oldBoundaryInsertEmb (old := old) j i).val] = old[i.val]
  by_cases h : i.castSucc < j
  · rw [List.getElem_insertIdx_of_lt (by rw [he, Fin.succAbove_of_castSucc_lt _ _ h]; exact h)]
    congr 1
    exact he.trans (congrArg Fin.val (Fin.succAbove_of_castSucc_lt _ _ h))
  · have h' := Fin.succAbove_of_le_castSucc j i (le_of_not_gt h)
    rw [List.getElem_insertIdx_of_gt (by rw [he, h']; exact Nat.lt_succ_of_le (le_of_not_gt h))]
    congr 1
    rw [he, h', Fin.val_succ, Nat.add_sub_cancel]

theorem oldBoundaryInsert_cases {old : List (Set X)} (j : Fin (old.length + 1))
    (i : Fin (oldBoundaryInsert old j).length) :
    i = oldBoundaryInsertPos (old := old) j ∨
      ∃ k, oldBoundaryInsertEmb (old := old) j k = i := by
  by_cases h : i = oldBoundaryInsertPos (old := old) j
  · exact Or.inl h
  · right
    let e := finCongr (oldBoundaryInsert_length old j)
    have hne : e i ≠ j := fun he => h (e.injective (he.trans (e.apply_symm_apply j).symm))
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
    exact ⟨k, e.injective ((e.apply_symm_apply (j.succAbove k)).trans hk)⟩

private theorem restrictOn_unit (N : Set X) : restrictOn n N (unitIdeal n X) = unitIdeal n X := by
  ext x g
  exact ⟨fun hg => hg.1, le_restrictOn isCoherent_unitIdeal x g⟩

private theorem monomialPartAlong_unit (N : Set X) (born : List (Set X)) :
    monomialPartAlong n N (unitIdeal n X) born = unitIdeal n X := by
  ext x g
  change (HolomorphicAt n g x ∧ _) ↔ HolomorphicAt n g x
  refine ⟨fun hg => hg.1, fun hg => ⟨hg, ?_⟩⟩
  intro i hxN hxH
  have he : divExpAlong n N (unitIdeal n X) (born.get i) x = 0 := by
    apply HironakaG8E4cProduct.divExpAlong_eq_zero_of_not
    intro hDiv
    have hVan := (hDiv.self_of_nhds hxN hxH).2 (fun _ => (1 : ℂ)) (holomorphicAt_const 1)
    exact one_ne_zero ((vanishesToOrderOn_one_iff hxN (holomorphicAt_const 1)).mp hVan)
  rw [he, idealPow_zero]
  exact IsInSpanAt.restrict (isInSpanAt_self hg hg)

private theorem nonmonomialPartAlong_unit (N : Set X) (born : List (Set X)) :
    nonmonomialPartAlong n N (unitIdeal n X) born = unitIdeal n X := by
  change InvertibleIdealQuotient.colon (restrictOn n N (unitIdeal n X))
    (monomialPartAlong n N (unitIdeal n X) born) = _
  rw [restrictOn_unit, monomialPartAlong_unit, BlowupControlledTransform.colon_unitIdeal isCoherent_unitIdeal]

theorem ordinaryTraceOrder_unit (N : Set X) (x : X) :
    ordinaryTraceOrder N (unitIdeal n X) x = 0 := by
  have hnot : x ∉ NonmonomialOrderLocal.ordGe (ordinaryTraceMarked N (unitIdeal n X)) 1 := by
    rw [ordGe_ordinaryTraceMarked_eq_cosupport N _ isCoherent_unitIdeal, cosupport_unitIdeal le_rfl]
    simp
  exact Nat.eq_zero_of_le_zero (NonmonomialOrderLocal.nmOrd_le_of_notMem hnot)

/-- The inserted old slot gives the unit trace, its unit original monomial
factor, and its unit actual residual ideal. -/
theorem inserted_old_row_units (N : Set X) {old : List (Set X)} (born : List (Set X))
    (j : Fin (old.length + 1)) :
    let old' := oldBoundaryInsert old j
    let p := oldBoundaryInsertPos (old := old) j
    oldTraceIdeal N old' p = unitIdeal n X ∧
      oldMonomialPart N old' born p = unitIdeal n X ∧
      oldResidualPart N old' born p = unitIdeal n X := by
  dsimp only
  have hI : oldTraceIdeal N (oldBoundaryInsert old j) (oldBoundaryInsertPos (old := old) j) =
      unitIdeal n X := by
    unfold oldTraceIdeal
    rw [oldBoundaryInsert_get_pos,
      HironakaNormalCrossingsOrderedMonomialTail.vanishingIdeal_empty_eq_unit, restrictOn_unit]
  exact ⟨hI, by rw [oldMonomialPart, hI, monomialPartAlong_unit],
    by rw [oldResidualPart, hI, nonmonomialPartAlong_unit]⟩

/-- Every original actual row and its native factors are read back along the
same ordered insertion embedding. -/
theorem original_old_rows_insert_empty (N : Set X) {old : List (Set X)}
    (born : List (Set X)) (j : Fin (old.length + 1)) (i : Fin old.length) :
    let old' := oldBoundaryInsert old j
    let k := oldBoundaryInsertEmb (old := old) j i
    oldTraceIdeal N old' k = oldTraceIdeal N old i ∧
      oldMonomialPart N old' born k = oldMonomialPart N old born i ∧
      oldResidualPart N old' born k = oldResidualPart N old born i := by
  dsimp only
  have hI : oldTraceIdeal N (oldBoundaryInsert old j) (oldBoundaryInsertEmb (old := old) j i) =
      oldTraceIdeal N old i := by
    unfold oldTraceIdeal
    rw [oldBoundaryInsert_get_emb]
  exact ⟨hI, by rw [oldMonomialPart, hI, oldMonomialPart],
    by rw [oldResidualPart, hI, oldResidualPart]⟩

/-- The complete native stamp has an inserted zero order and the same
inactive positions, embedded through the literal insertion. -/
theorem retainedDefectStamp_insert_empty_old (N : Set X) {old : List (Set X)}
    (born : List (Set X)) (j : Fin (old.length + 1)) (x : X) :
    let old' := oldBoundaryInsert old j
    let S := retainedDefectStamp N old born x
    let S' := retainedDefectStamp N old' born x
    let e := finCongr (oldBoundaryInsert_length old j).symm
    (fun i => S'.1 (e i)) = j.insertNth 0 S.1 ∧
      S'.2 = S.2.map (oldBoundaryInsertEmb (old := old) j) := by
  classical
  dsimp only
  have hzero : (retainedDefectStamp N (oldBoundaryInsert old j) born x).1
      (oldBoundaryInsertPos (old := old) j) = 0 := by
    change ordinaryTraceOrder N (oldResidualPart N (oldBoundaryInsert old j) born
      (oldBoundaryInsertPos (old := old) j)) x = 0
    rw [(inserted_old_row_units N born j).2.2, ordinaryTraceOrder_unit]
  have hrow (i : Fin old.length) :
      (retainedDefectStamp N (oldBoundaryInsert old j) born x).1
        (oldBoundaryInsertEmb (old := old) j i) = (retainedDefectStamp N old born x).1 i :=
    congrArg (fun I => ordinaryTraceOrder N I x) (original_old_rows_insert_empty N born j i).2.2
  refine ⟨Fin.eq_insertNth_iff.mpr ⟨hzero, funext hrow⟩, ?_⟩
  ext k
  rcases oldBoundaryInsert_cases j k with hk | ⟨i, hi⟩
  · subst k
    have hUnit := (inserted_old_row_units N born j).2.1
    have hnot : ∀ i, oldBoundaryInsertEmb (old := old) j i ≠ oldBoundaryInsertPos (old := old) j :=
      fun i hi => Fin.succAbove_ne j i ((finCongr (oldBoundaryInsert_length old j).symm).injective hi)
    simp only [retainedDefectStamp, inactiveCanonicalRows, Finset.mem_filter, Finset.mem_univ,
      true_and, hUnit, Finset.mem_map]
    exact ⟨fun h => (h.2 (holomorphicAt_const 1)).elim,
      by rintro ⟨i, _, hi⟩; exact (hnot i hi).elim⟩
  · subst k
    have hmap :
        oldBoundaryInsertEmb (old := old) j i ∈
            (retainedDefectStamp N old born x).2.map (oldBoundaryInsertEmb (old := old) j) ↔
          i ∈ (retainedDefectStamp N old born x).2 := by
      rw [Finset.mem_map]
      exact ⟨by
        rintro ⟨k, hk, heq⟩
        obtain rfl := (oldBoundaryInsertEmb (old := old) j).injective heq
        exact hk, fun hk => ⟨i, hk, rfl⟩⟩
    rw [hmap]
    change (_ ∈ inactiveCanonicalRows N (oldBoundaryInsert old j) born _ x) ↔
      i ∈ inactiveCanonicalRows N old born _ x
    obtain ⟨_, hM, hR⟩ := original_old_rows_insert_empty N born j i
    simp only [inactiveCanonicalRows, Finset.mem_filter, Finset.mem_univ, true_and, hM, hR]

private theorem relativeIdealListProduct_coherent (N : Set X) (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n X)) (hL : ∀ I ∈ L, I.IsCoherent) :
    (relativeIdealListProduct N L).IsCoherent := by
  induction L with
  | nil => exact isCoherent_unitIdeal
  | cons I L ih =>
    refine isCoherent_restrictOn_of_isClosedSubmanifold (isCoherent_mul (hL I (by simp)) ?_) hN
    exact ih fun J hJ => hL J (List.mem_cons_of_mem _ hJ)

private theorem relativeIdealListProduct_insert_unit (N : Set X) (hN : IsClosedSubmanifold n N)
    (L : List (GermIdeal n X)) (hL : ∀ I ∈ L, I.IsCoherent) (k : ℕ) :
    relativeIdealListProduct N (L.insertIdx k (unitIdeal n X)) =
      relativeIdealListProduct N L := by
  induction k generalizing L with
  | zero =>
    rw [List.insertIdx_zero, relativeIdealListProduct,
      BlowupControlledTransform.unitIdeal_mul (relativeIdealListProduct_coherent N hN L hL)]
    cases L with
    | nil => exact restrictOn_unit N
    | cons I L =>
      change restrictOn n N (restrictOn n N (I.mul (relativeIdealListProduct N L))) = _
      exact MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN.1 restrictLe_restrictOn
        (restrictLe_self_restrictOn (isCoherent_mul (hL I (by simp))
          (relativeIdealListProduct_coherent N hN L fun J hJ => hL J (List.mem_cons_of_mem _ hJ))))
  | succ k ih =>
    cases L with
    | nil => rfl
    | cons I L =>
      rw [List.insertIdx_succ_cons, relativeIdealListProduct,
        ih L (fun J hJ => hL J (List.mem_cons_of_mem _ hJ))]
      rfl

private theorem canonicalResidualFamily_ofFn (N : Set X) (old born : List (Set X)) :
    canonicalResidualFamily N old born = List.ofFn (oldResidualPart N old born) := by
  unfold canonicalResidualFamily
  conv_lhs => rw [← List.ofFn_get old, List.map_ofFn]
  rfl

/-- The literal canonical row list acquires just the unit ideal at the inserted slot. -/
theorem canonicalResidualFamily_insert_empty_old (N : Set X) {old : List (Set X)}
    (born : List (Set X)) (j : Fin (old.length + 1)) :
    canonicalResidualFamily N (oldBoundaryInsert old j) born =
      (canonicalResidualFamily N old born).insertIdx j.val (unitIdeal n X) := by
  change (old.insertIdx j.val ∅).map _ = (old.map _).insertIdx j.val _
  rw [List.map_insertIdx, HironakaNormalCrossingsOrderedMonomialTail.vanishingIdeal_empty_eq_unit,
    restrictOn_unit, nonmonomialPartAlong_unit]

/-- The actual canonical product marked ideal is unchanged by insertion. -/
theorem canonicalProductMarked_insert_empty_old (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (j : Fin (old.length + 1)) (q : ℕ) :
    canonicalProductMarked N (oldBoundaryInsert old j) born q =
      canonicalProductMarked N old born q := by
  unfold canonicalProductMarked
  rw [canonicalResidualFamily_insert_empty_old, relativeIdealListProduct_insert_unit N hN]
  intro I hI
  rw [canonicalResidualFamily_ofFn] at hI
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
  exact (actual_old_parts_geometry hn hN hE hTr hDense i).2.2.1

/-- A genuine family reindexing preserves the count of proper germ classes
when it contains every proper row. -/
private theorem actualDistinctProperCount_eq_of_embedding {a b : ℕ}
    {F : Fin a → GermIdeal n X} {G : Fin b → GermIdeal n X}
    (e : Fin a ↪ Fin b) (hRows : ∀ i, G (e i) = F i) (x : X)
    (hProper : ∀ j ∈ actualProperPositions G x, ∃ i, e i = j) :
    actualDistinctProperCount G x = actualDistinctProperCount F x := by
  classical
  have hRel (i j : Fin a) :
      (actualIdealGermSetoid F x).r i j ↔ (actualIdealGermSetoid G x).r (e i) (e j) := by
    change (∀ g, (F i).mem x g ↔ (F j).mem x g) ↔
      (∀ g, (G (e i)).mem x g ↔ (G (e j)).mem x g)
    rw [hRows, hRows]
  let lift := Quotient.map' e (fun i j h => (hRel i j).mp h)
  have hInj : Function.Injective lift := by
    intro q q'
    refine Quotient.inductionOn₂ q q' ?_
    intro i j hij
    exact Quotient.sound ((hRel i j).mpr (Quotient.exact hij))
  let eqQ := Function.Embedding.mk lift hInj
  have hMem (i : Fin a) : e i ∈ actualProperPositions G x ↔ i ∈ actualProperPositions F x := by
    simp [actualProperPositions, hRows]
  have hImage :
      ((actualProperPositions F x).image (Quotient.mk (actualIdealGermSetoid F x))).map eqQ =
        (actualProperPositions G x).image (Quotient.mk (actualIdealGermSetoid G x)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨e i, (hMem i).mpr hi, rfl⟩
    · intro hq
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨i, rfl⟩ := hProper j hj
      exact Finset.mem_map.mpr ⟨_, Finset.mem_image.mpr ⟨i, (hMem i).mp hj, rfl⟩, rfl⟩
  simpa only [actualDistinctProperCount, Finset.card_map] using (congrArg Finset.card hImage).symm

/-- The inserted unit never enters the actual quotient count of proper rows. -/
theorem actualDistinctProperCount_insert_empty_old (N : Set X) {old : List (Set X)}
    (born : List (Set X)) (j : Fin (old.length + 1)) (x : X) :
    actualDistinctProperCount (oldResidualPart N (oldBoundaryInsert old j) born) x =
      actualDistinctProperCount (oldResidualPart N old born) x := by
  classical
  apply actualDistinctProperCount_eq_of_embedding (oldBoundaryInsertEmb (old := old) j)
    (fun i => (original_old_rows_insert_empty N born j i).2.2) x
  intro k hk
  rcases oldBoundaryInsert_cases j k with hSame | hOther
  · subst k
    exact (Finset.mem_filter.mp hk).2 (by
      rw [(inserted_old_row_units N born j).2.2]
      exact holomorphicAt_const 1) |>.elim
  · exact hOther

/-- The genuine distinct defect of the native retained family persists
under literal insertion of an originally empty boundary slot. -/
theorem actualFamilyDistinctDefect_insert_empty_old (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (j : Fin (old.length + 1)) :
    actualFamilyDistinctDefect N (oldResidualPart N (oldBoundaryInsert old j) born) =
      actualFamilyDistinctDefect N (oldResidualPart N old born) := by
  have hProd := congrArg MarkedIdeals.MarkedIdeal.ideal
    (canonicalProductMarked_insert_empty_old hn hN hE hTr hDense j 1)
  change relativeIdealListProduct N (canonicalResidualFamily N (oldBoundaryInsert old j) born) =
    relativeIdealListProduct N (canonicalResidualFamily N old born) at hProd
  simp only [canonicalResidualFamily_ofFn] at hProd
  ext x
  simp only [actualFamilyDistinctDefect, mem_ofPred_eq,
    actualDistinctProperCount_insert_empty_old, hProd]

end
end Hironaka.HironakaG4OrderedCrestEmptyOld
