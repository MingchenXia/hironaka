import Hironaka.Resolution.HironakaG4SharpBadFootprint
import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates
import Hironaka.Resolution.HironakaG4ActiveMonomialSharpBad
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Resolution.HironakaOriginalCrossingLowerHistory
import Hironaka.Resolution.HironakaG4ZeroMaskSameGammaHistory
import Hironaka.Resolution.HironakaG34ProcessedMaskEquivariance

set_option autoImplicit false

/-!
# The zero-mask fixed-count fold with an equivariance conclusion (eleventh brick of EQ_d)

Lane G34 (run 0080, round 10).  Blueprint: `hironaka-g34-resume-zero-mask-fold-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §1 (row "K3 zero mask"), §2(c)(iii).

The held `HironakaG4ZeroMaskFixedQFold.exists_prepared_zero_mask_fixed_q_drop` is existential and its tower is built by
PRIVATE helpers (`CurrentData`, `FoldState`, `single_mask_state`, ...).  This module re-derives it verbatim (the helpers
below are copies of the held ones; the held file is not edited) and adds ONE conclusion: the fold is equivariant for
`(N, old ++ born)` (`HironakaG34MaskFoldEquivariance.IsEquivariant`).  Each single-mask block is a canonical segment of the
monomial invariant of a mark-one sum of canonical old factors of the CURRENT data, hence equivariant for the current data
(`HironakaG34ProcessedMaskEquivariance.isEquivariant_zero_mask_history`); the blocks are appended along an equivariant
prefix (`IsEquivariant.append_of_current`).

## Main results

* **`exists_prepared_zero_mask_fixed_q_drop_equivariant`**: the held conclusions together with
  `IsEquivariant N (old ++ born) T`.

New file; no existing statement changed; no named input.  Sorry-free.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG34ZeroMaskFoldEquivariance

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalProductTraceOrder
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  RestrictedIdealExtension RelativePrincipalizationSpan MonomialPartAlong DivisorExponentAlong
  NormalCrossings RestrictEmptyTower GermIdealOrder InvertibleIdealQuotient
  HironakaG34MaskFoldEquivariance

variable {n : ℕ} {X Y Z : CMfd.{u} n}

private def maskSum {r : ℕ} (D : Fin r → GermIdeal n X) (P : Finset (Fin r)) :
    GermIdeal n X :=
  ⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩

private theorem cosupport_maskSum_one {r : ℕ} (N : Set X)
    (D : Fin r → GermIdeal n X) (hD : ∀ i,(D i).IsCoherent)
    {P : Finset (Fin r)} (hP : P.Nonempty) :
    cosupport n N (maskSum D P) 1 = ⋂ i ∈ P,cosupport n N (D i) 1 := by
  have hSum : ∀ x g,(maskSum D P).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => hg.1
  have hRow (i : Fin r) : ∀ x g,(D i).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hD i) hg
  rw [cosupport_one hSum]
  ext x
  constructor
  · rintro ⟨hxN,hzero⟩
    refine mem_iInter.mpr fun i => mem_iInter.mpr fun hi => ?_
    rw [cosupport_one (hRow i)]
    refine ⟨hxN,fun g hg => hzero g ?_⟩
    exact isInSpanAt_self (S := fun f => ∃ i ∈ P,(D i).mem x f)
      ⟨i,hi,hg⟩ (hRow i x g hg)
  · intro hx
    have hxRow (i : Fin r) (hi : i ∈ P) : x ∈ N ∩ (D i).zeroLocus := by
      have h := mem_iInter.mp (mem_iInter.mp hx i) hi
      rwa [cosupport_one (hRow i)] at h
    obtain ⟨i₀,hi₀⟩ := hP
    refine ⟨(hxRow i₀ hi₀).1,?_⟩
    intro g hg
    obtain ⟨_hg,m,s,a,hs,_ha,hsum⟩ := hg
    rw [hsum.self_of_nhds]
    apply Finset.sum_eq_zero
    intro k _hk
    obtain ⟨i,hi,hmem⟩ := hs k
    rw [(hxRow i hi).2 (s k) hmem,mul_zero]

private theorem isClosed_cosupport_maskSum {r : ℕ} {N : Set X}
    (hN : IsClosedSubmanifold n N) (D : Fin r → GermIdeal n X)
    (hD : ∀ i,(D i).IsCoherent) {P : Finset (Fin r)} (hP : P.Nonempty) :
    IsClosed (cosupport n N (maskSum D P) 1) := by
  rw [cosupport_maskSum_one N D hD hP]
  exact isClosed_iInter fun i => isClosed_iInter fun _hi =>
    GiraudAlong.isClosed_cosupport_along (hD i) hN 1

private theorem canonical_proper_subset_bad (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born))
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length) :
    {x | x ∈ N ∧ ¬(oldMonomialPart N old born i).mem x 1} ⊆
      originalSharpBadLocus (n := n) N (old ++ born) := by
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
  have hBad := HironakaG4ActiveMonomialSharpBad.active_old_monomial_subset_originalSharpBadLocus
    hn hN hE hdense k L hL
  simpa only [hOld,hBorn,oldMonomialPart,oldTraceIdeal] using hBad

private theorem isCompact_canonical_mask_cosupport (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hK : IsCompact (originalSharpBadLocus (n := n) N (old ++ born)))
    {P : Finset (Fin old.length)} (hP : P.Nonempty) :
    IsCompact (cosupport n N (maskSum (oldMonomialPart N old born) P) 1) := by
  let D := oldMonomialPart N old born
  have hD (i : Fin old.length) : (D i).IsCoherent :=
    (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1
  refine hK.of_isClosed_subset (isClosed_cosupport_maskSum hN D hD hP) ?_
  intro x hx
  rw [cosupport_maskSum_one N D hD hP] at hx
  obtain ⟨i,hi⟩ := hP
  have hxD := mem_iInter.mp (mem_iInter.mp hx i) hi
  have hxN := hxD.1
  have hhol : ∀ y g,(D i).mem y g → HolomorphicAt n g y :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hD i) hg
  rw [cosupport_one hhol] at hxD
  apply canonical_proper_subset_bad hn hN hE hdense i
  refine ⟨hxN,?_⟩
  intro hOne
  exact one_ne_zero (hxD.2 1 hOne)

private theorem current_bad_compact {N : Set X} {E : List (Set X)}
    (hN : IsClosed N) (hE : ∀ H ∈ E,IsClosed H)
    (hK : IsCompact (originalSharpBadLocus (n := n) N E))
    (T : BlowupTower X Y) (hSharp : CurrentSharpCentres N E T)
    (hCurrent : IsSNCDivisor n
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E) :
    IsCompact (originalSharpBadLocus (n := n) (strictAlong T N)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E) ∧
      CentresOver (originalSharpBadLocus (n := n) N E) T := by
  obtain ⟨hBad,hOver⟩ :=
    HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hN hE T hSharp
  refine ⟨(HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK
    |>.of_isClosed_subset ?_ hBad,hOver⟩
  exact isClosed_originalSharpBadLocus (MemberInterTowerAlong.isClosed_strictAlong T hN)
    hCurrent.1

private theorem old_map_append (old : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    old.map (strictAlong (T.append S))=
      (old.map (strictAlong T)).map (strictAlong S) := by
  rw [List.map_map]
  congr 1
  funext H
  exact MemberInterLocusAlong.strictAlong_append T H S

private def oldEquiv (old : List (Set X)) (T : BlowupTower X Y) :
    Fin old.length ≃ Fin (old.map (strictAlong T)).length :=
  finCongr (by simp)

private theorem get_oldEquiv (old : List (Set X)) (T : BlowupTower X Y)
    (i : Fin old.length) :
    (old.map (strictAlong T)).get (oldEquiv old T i)=strictAlong T (old.get i) := by
  simp [oldEquiv]

private theorem oldEquiv_append (old : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) (i : Fin old.length) :
    finCongr (congrArg List.length (old_map_append old T S))
        (oldEquiv old (T.append S) i)=
      oldEquiv (old.map (strictAlong T)) S (oldEquiv old T i) := by
  apply Fin.ext
  rfl

private theorem mask_map_append (old : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) (P : Finset (Fin old.length)) :
    (P.map (oldEquiv old (T.append S)).toEmbedding).map
        (finCongr (congrArg List.length (old_map_append old T S))).toEmbedding=
      (P.map (oldEquiv old T).toEmbedding).map
        (oldEquiv (old.map (strictAlong T)) S).toEmbedding := by
  rw [Finset.map_map,Finset.map_map]
  congr 1

private def actualMatrix (N : Set X) (old born : List (Set X)) :
    X → Fin old.length → Fin born.length → ℕ :=
  fun x i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x

private def residualMarked (N : Set X) (old born : List (Set X))
    (i : Fin old.length) : MarkedIdeal n X :=
  ⟨N,born,oldResidualPart N old born i,0⟩

private structure CurrentData (N : Set X) (old born : List (Set X)) (q : ℕ) : Prop where
  smooth : IsClosedSubmanifold n N
  full : IsSNCDivisor n (old ++ born)
  transverse : IsTransverse n N born
  dense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)
  order : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1
  prepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x
  bound : ∀ x ∈ N,tauD (actualMatrix N old born x) ≤ q
  topZero : ∀ x ∈ N,tauD (actualMatrix N old born x)=q → nuOne (actualMatrix N old born x)=0
  compactBad : IsCompact (originalSharpBadLocus (n := n) N (old ++ born))

private def currentStateData (N : Set X) (old born : List (Set X)) (q : ℕ)
    (T : BlowupTower X Y) (labels : Σ L : List (Set Y),Fin old.length ≃ Fin L.length) : Prop :=
  let NQ := strictAlong T N
  let oldQ := labels.1
  let bornQ := (geoTransformAlong (geometricTemplate N born) T).E
  let eQ := labels.2
  CurrentData NQ oldQ bornQ q ∧
    (∀ z ∈ NQ,∀ i : Fin old.length,
      eQ i ∈ properRows (actualMatrix NQ oldQ bornQ z) →
        i ∈ properRows (actualMatrix N old born (T.proj z))) ∧
    ∀ i : Fin old.length,
      (geoTransformAlong (residualMarked N old born i) T).ideal=
        oldResidualPart NQ oldQ bornQ (eQ i)

private def currentState (N : Set X) (old born : List (Set X)) (q : ℕ)
    (T : BlowupTower X Y) : Prop :=
  currentStateData N old born q T ⟨old.map (strictAlong T),oldEquiv old T⟩

private def maskErasedData (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) (labels : Σ L : List (Set Y),Fin old.length ≃ Fin L.length)
    (P : Finset (Fin old.length)) : Prop :=
  ∀ z ∈ strictAlong T N,¬P.map labels.2.toEmbedding ⊆ properRows
    (actualMatrix (strictAlong T N) labels.1
      (geoTransformAlong (geometricTemplate N born) T).E z)

private def maskErased (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) (P : Finset (Fin old.length)) : Prop :=
  maskErasedData N old born T ⟨old.map (strictAlong T),oldEquiv old T⟩ P

private structure FoldState (N : Set X) (old born : List (Set X)) (q : ℕ)
    (F : Finset (Finset (Fin old.length))) (T : BlowupTower X Y) : Prop where
  bornTest : IsGeoTestTower (geometricTemplate N born) T
  fullTest : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T
  sharp : CurrentSharpCentres N (old ++ born) T
  residualTest : ∀ i,IsGeoTestTower (residualMarked N old born i) T
  prefixData : ∀ k : ℕ,currentState N old born q (BlowupTowerSplit.head T k)
  erased : ∀ P ∈ F,maskErased N old born T P

private theorem count_lt_of_all_original_masks {r s b q : ℕ}
    (e : Fin r ≃ Fin s) (A : Fin s → Fin b → ℕ) (hBound : tauD A ≤ q)
    (hEmpty : ∀ P ∈ (Finset.univ : Finset (Fin r)).powersetCard q,
      ¬P.map e.toEmbedding ⊆ properRows A) :
    tauD A < q := by
  apply lt_of_le_of_ne hBound
  intro hEq
  let P := (properRows A).map e.symm.toEmbedding
  have hP : P ∈ (Finset.univ : Finset (Fin r)).powersetCard q := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _,?_⟩
    simpa only [P,Finset.card_map,tauD] using hEq
  have hMap : P.map e.toEmbedding=properRows A := by
    simp only [P,Finset.map_map]
    have hComp : e.symm.toEmbedding.trans e.toEmbedding=Function.Embedding.refl _ := by
      ext i
      exact congrArg Fin.val (e.apply_symm_apply i)
    rw [hComp,Finset.map_refl]
  exact hEmpty P hP (hMap ▸ Finset.Subset.refl _)

private theorem labels_refl (old : List (Set X)) :
    (⟨old.map (strictAlong (BlowupTower.refl : BlowupTower X X)),
      oldEquiv old (BlowupTower.refl : BlowupTower X X)⟩ :
      Σ L : List (Set X),Fin old.length ≃ Fin L.length)=⟨old,Equiv.refl _⟩ := by
  have aux (L : List (Set X)) (hL : L=old) (he : old.length=L.length) :
      (⟨L,finCongr he⟩ : Σ K : List (Set X),Fin old.length ≃ Fin K.length)=
        ⟨old,Equiv.refl _⟩ := by
    subst L
    rfl
  unfold oldEquiv
  exact aux _ (List.map_id old) (by simp)

private theorem currentState_refl {N : Set X} {old born : List (Set X)} {q : ℕ}
    (h : CurrentData N old born q) :
    currentState N old born q (BlowupTower.refl : BlowupTower X X) := by
  unfold currentState
  rw [labels_refl]
  simpa [currentStateData,HomogenizedGlueingTower.strictAlong,residualMarked,geometricTemplate] using h

private theorem foldState_refl {N : Set X} {old born : List (Set X)} {q : ℕ}
    (h : CurrentData N old born q) :
    FoldState N old born q ∅ (BlowupTower.refl : BlowupTower X X) := by
  refine ⟨trivial,trivial,trivial,fun _ => trivial,?_,?_⟩
  · intro k
    cases k <;> exact currentState_refl h
  · intro P hP
    exact (Finset.notMem_empty P hP).elim

private theorem labels_append (old : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    (⟨old.map (strictAlong (T.append S)),oldEquiv old (T.append S)⟩ :
      Σ L : List (Set Z),Fin old.length ≃ Fin L.length)=
      ⟨(old.map (strictAlong T)).map (strictAlong S),
        (oldEquiv old T).trans (oldEquiv (old.map (strictAlong T)) S)⟩ := by
  have aux (L K : List (Set Z)) (h : L=K)
      (hL : old.length=L.length) (hK : old.length=K.length) :
      (⟨L,finCongr hL⟩ : Σ L : List (Set Z),Fin old.length ≃ Fin L.length)=
        ⟨K,finCongr hK⟩ := by
    subst K
    rfl
  have he : (oldEquiv old T).trans (oldEquiv (old.map (strictAlong T)) S)=
      finCongr (show old.length=((old.map (strictAlong T)).map (strictAlong S)).length
        by simp) := by
    ext i
    rfl
  rw [he]
  exact aux _ _ (old_map_append old T S) _ _

private theorem residual_full_record {N : Set X} {old born : List (Set X)} {q : ℕ}
    (T : BlowupTower X Y) (h : currentState N old born q T) (i : Fin old.length) :
    geoTransformAlong (residualMarked N old born i) T=
      residualMarked (strictAlong T N) (old.map (strictAlong T))
        (geoTransformAlong (geometricTemplate N born) T).E (oldEquiv old T i) := by
  have hE := HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq
    (𝔪 := geometricTemplate N born) (𝔍 := residualMarked N old born i) rfl T
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact N_geoTransformAlong _ T
  · exact hE
  · exact h.2.2 i
  · exact d_geoTransformAlong _ T

private theorem full_ordered_list (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) :
    (geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) T).E=
      old.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N born) T).E := by
  have h := full_ordered N old.get born T
  have ho : List.ofFn old.get=old := List.ofFn_get old
  have hm : List.ofFn (fun i => strictAlong T (old.get i))=old.map (strictAlong T) := by
    simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map old (strictAlong T)
  rw [ho,hm] at h
  exact h

private theorem full_template_list (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) :
    geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) T=
      geometricTemplate (univ : Set Y)
        (old.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N born) T).E) := by
  rw [template_current,strict_univ,full_ordered_list N old born T]

private theorem currentSharp_head (N : Set X) (E : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CurrentSharpCentres N E T →
      ∀ k,CurrentSharpCentres N E (BlowupTowerSplit.head T k)
  | _,.refl,_,0 => trivial
  | _,.refl,_,_+1 => trivial
  | _,.step _ _ _ _,h,0 => h
  | _,.step T _ _ _,h,k+1 => currentSharp_head N E T h.1 k

private theorem currentState_append {N : Set X} {old born : List (Set X)} {q : ℕ}
    (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (hT : currentState N old born q T)
    (hS : currentState (strictAlong T N) (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E q S) :
    currentState N old born q (T.append S) := by
  unfold currentState
  rw [labels_append]
  dsimp only [currentStateData]
  rw [MemberInterLocusAlong.strictAlong_append T N S,born_append N born T S]
  refine ⟨hS.1,?_,?_⟩
  · intro z hz i hi
    have hzT : S.proj z ∈ strictAlong T N :=
      MemberInterTowerAlong.strictAlong_subset_preimage S hT.1.smooth.1 hz
    have hiT := hS.2.1 z hz (oldEquiv old T i) hi
    have hi0 := hT.2.1 (S.proj z) hzT i hiT
    simpa only [BlowupTower.proj_append,Function.comp_apply] using hi0
  · intro i
    rw [geoTransformAlong_append,residual_full_record T hT i]
    exact hS.2.2 (oldEquiv old T i)

private theorem tauD_row_equiv {r s b : ℕ} (e : Fin r ≃ Fin s)
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

private theorem maskErased_append_old {N : Set X} {old born : List (Set X)} {q : ℕ}
    (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (hT : currentState N old born q T)
    (hS : currentState (strictAlong T N) (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E q S)
    {P : Finset (Fin old.length)} (hP : maskErased N old born T P) :
    maskErased N old born (T.append S) P := by
  unfold maskErased
  rw [labels_append]
  dsimp only [maskErasedData]
  rw [MemberInterLocusAlong.strictAlong_append T N S,born_append N born T S]
  intro z hz hAll
  have hzT : S.proj z ∈ strictAlong T N :=
    MemberInterTowerAlong.strictAlong_subset_preimage S hT.1.smooth.1 hz
  apply hP (S.proj z) hzT
  intro j hj
  obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
  have hNew := hAll (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  exact hS.2.1 z hz (oldEquiv old T i) hNew

private theorem maskErased_append_new (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) (P : Finset (Fin old.length))
    (hP : maskErased (strictAlong T N) (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E S
        (P.map (oldEquiv old T).toEmbedding)) :
    maskErased N old born (T.append S) P := by
  unfold maskErased at hP ⊢
  rw [labels_append]
  dsimp only [maskErasedData] at hP ⊢
  rw [MemberInterLocusAlong.strictAlong_append T N S,born_append N born T S]
  have he : ((oldEquiv old T).trans (oldEquiv (old.map (strictAlong T)) S)).toEmbedding=
      (oldEquiv old T).toEmbedding.trans (oldEquiv (old.map (strictAlong T)) S).toEmbedding := by
    ext i
    rfl
  simpa only [Finset.map_map,he] using hP

private theorem foldState_insert {N : Set X} {old born : List (Set X)} {q : ℕ}
    {F : Finset (Finset (Fin old.length))} {P : Finset (Fin old.length)}
    (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (hT : FoldState N old born q F T)
    (hS : FoldState (strictAlong T N) (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E q
      {P.map (oldEquiv old T).toEmbedding} S) :
    FoldState N old born q (insert P F) (T.append S) := by
  have hTend : currentState N old born q T := by
    have h := hT.prefixData 0
    change currentState N old born q (BlowupTowerSplit.split T 0).2.1 at h
    rw [StepOneEmptyPrefix.split_zero T] at h
    exact h
  have hSend : currentState (strictAlong T N) (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E q S := by
    have h := hS.prefixData 0
    change currentState (strictAlong T N) (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E q (BlowupTowerSplit.split S 0).2.1 at h
    rw [StepOneEmptyPrefix.split_zero S] at h
    exact h
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · apply (isGeoTestTower_append_iff _ T S).mpr
    refine ⟨hT.bornTest,?_⟩
    rw [template_current]
    exact hS.bornTest
  · apply (isGeoTestTower_append_iff _ T S).mpr
    refine ⟨hT.fullTest,?_⟩
    rw [full_template_list N old born T]
    exact hS.fullTest
  · apply currentSharp_append N (old ++ born) T S hT.sharp
    rw [full_ordered_list N old born T]
    exact hS.sharp
  · intro i
    apply (isGeoTestTower_append_iff _ T S).mpr
    refine ⟨hT.residualTest i,?_⟩
    rw [residual_full_record T hTend i]
    exact hS.residualTest (oldEquiv old T i)
  · intro k
    by_cases hk : k ≤ S.length
    · have hs := StepOneEmptyPrefix.split_append_of_le T S k hk
      change currentState N old born q (BlowupTowerSplit.split (T.append S) k).2.1
      rw [hs]
      exact currentState_append T (BlowupTowerSplit.head S k)
        hTend (hS.prefixData k)
    · have hs := HironakaOriginalCrossingLowerHistory.split_append_above_tail
        T S k (by omega)
      change currentState N old born q (BlowupTowerSplit.split (T.append S) k).2.1
      rw [hs]
      exact hT.prefixData (k-S.length)
  · intro R hR
    rcases Finset.mem_insert.mp hR with hRP | hRF
    · rw [hRP]
      exact maskErased_append_new N old born T S P
        (hS.erased _ (Finset.mem_singleton_self _))
    · exact maskErased_append_old T S hTend hSend (hT.erased R hRF)

private theorem matrix_oldEquiv (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) (z : Y) (i : Fin old.length)
    (j : Fin (geoTransformAlong (geometricTemplate N born) T).E.length) :
    actualMatrix (strictAlong T N) (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E z (oldEquiv old T i) j=
      divExpAlong n (strictAlong T N)
        (monomialPartAlong n (strictAlong T N)
          (restrictOn n (strictAlong T N) (vanishingIdeal (n := n) (strictAlong T (old.get i))))
          (geoTransformAlong (geometricTemplate N born) T).E)
        ((geoTransformAlong (geometricTemplate N born) T).E.get j) z := by
  simp only [actualMatrix,oldMonomialPart,oldTraceIdeal,get_oldEquiv]

private theorem subset_map_proper_iff {r s b : ℕ} (e : Fin r ≃ Fin s)
    (A : Fin s → Fin b → ℕ) (P : Finset (Fin r)) :
    P.map e.toEmbedding ⊆ properRows A ↔ P ⊆ properRows (fun i => A (e i)) := by
  constructor
  · intro h i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (h (Finset.mem_map.mpr ⟨i,hi,rfl⟩))).2⟩
  · intro h j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp (h hi)).2⟩

private theorem foldState_current {N : Set X} {old born : List (Set X)} {q : ℕ}
    {F : Finset (Finset (Fin old.length))} (T : BlowupTower X Y)
    (hT : FoldState N old born q F T) : currentState N old born q T := by
  have h := hT.prefixData 0
  change currentState N old born q (BlowupTowerSplit.split T 0).2.1 at h
  rw [StepOneEmptyPrefix.split_zero T] at h
  exact h

private theorem current_state_readout (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} {q : ℕ} (h0 : CurrentData N old born q)
    (Q : BlowupTower X Y) (hSharp : CurrentSharpCentres N (old ++ born) Q)
    (h : currentState N old born q Q) :
    let NQ := strictAlong Q N
    let oldQ := old.map (strictAlong Q)
    let bornQ := (geoTransformAlong (geometricTemplate N born) Q).E
    let eQ : Fin old.length ≃ Fin oldQ.length := finCongr (by simp [oldQ])
    let IQ := oldTraceIdeal NQ oldQ
    let DQ := oldMonomialPart NQ oldQ bornQ
    let JQ := oldResidualPart NQ oldQ bornQ
    let AQ : Y → Fin oldQ.length → Fin bornQ.length → ℕ :=
      fun z i j => divExpAlong n NQ (DQ i) (bornQ.get j) z
    IsClosedSubmanifold n NQ ∧ IsSNCDivisor n (oldQ ++ bornQ) ∧
    IsTransverse n NQ bornQ ∧
    NQ ⊆ closure (NQ \ ⋃ H ∈ oldQ ++ bornQ,H) ∧
    (∀ z ∈ NQ,∀ i,ordinaryTraceOrder NQ (JQ i) z ≤ 1) ∧
    (∀ z ∈ NQ,IsPreparedResidualSNCAt NQ oldQ bornQ z) ∧
    (∀ z ∈ NQ,tauD (AQ z) ≤ q) ∧
    (∀ z ∈ NQ,tauD (AQ z)=q → nuOne (AQ z)=0) ∧
    (∀ z ∈ NQ,∀ i : Fin old.length,
      eQ i ∈ properRows (AQ z) → i ∈ properRows (actualMatrix N old born (Q.proj z))) ∧
    originalSharpBadLocus (n := n) NQ (oldQ ++ bornQ) ⊆
      Q.proj ⁻¹' originalSharpBadLocus (n := n) N (old ++ born) ∧
    IsCompact (originalSharpBadLocus (n := n) NQ (oldQ ++ bornQ)) ∧
    (∀ P : Finset (Fin oldQ.length),P.Nonempty →
      IsCompact (cosupport n NQ
        (⟨fun z g => IsInSpanAt (n := n)
          (fun f => ∃ i ∈ P,(DQ i).mem z f) z g⟩ :
            GermIdeal n Y) 1)) ∧
    ∀ i : Fin old.length,
      (geoTransformAlong (residualMarked N old born i) Q).ideal=JQ (eQ i) ∧
      IQ (eQ i)=restrictOn n NQ ((DQ (eQ i)).mul (JQ (eQ i))) ∧
      (IQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (IQ (eQ i)) z) ∧
      (DQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (DQ (eQ i)) z) ∧
      IsMonomialAlong n NQ (DQ (eQ i)) bornQ ∧
      (JQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (JQ (eQ i)) z) := by
  dsimp only
  have hCur := h.1
  have hBad := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
    h0.smooth.1 h0.full.1 Q hSharp).1
  rw [full_ordered_list N old born Q] at hBad
  refine ⟨hCur.smooth,hCur.full,hCur.transverse,hCur.dense,hCur.order,hCur.prepared,
    hCur.bound,hCur.topZero,h.2.1,hBad,hCur.compactBad,?_,?_⟩
  · intro P hP
    exact isCompact_canonical_mask_cosupport hn hCur.smooth hCur.full hCur.transverse
      hCur.dense hCur.compactBad hP
  · intro i
    obtain ⟨hIc,hIn,hJc,hJn,hDc,hDn,hDm,hFact⟩ :=
      actual_old_parts_geometry hn hCur.smooth hCur.full hCur.transverse hCur.dense
        (oldEquiv old Q i)
    exact ⟨h.2.2 i,hFact,hIc,hIn,hDc,hDn,hDm,hJc,hJn⟩

private theorem foldState_endpoint_lt {N : Set X} {old born : List (Set X)} {q : ℕ}
    (T : BlowupTower X Y)
    (hT : FoldState N old born q ((Finset.univ : Finset (Fin old.length)).powersetCard q) T) :
    let NT := strictAlong T N
    let BT := (geoTransformAlong (geometricTemplate N born) T).E
    let AT : Y → Fin old.length → Fin BT.length → ℕ := fun z i j =>
      divExpAlong n NT
        (monomialPartAlong n NT
          (restrictOn n NT (vanishingIdeal (n := n) (strictAlong T (old.get i)))) BT)
        (BT.get j) z
    ∀ z ∈ NT,tauD (AT z) < q := by
  dsimp only
  intro z hz
  have hc := foldState_current T hT
  have hlt := count_lt_of_all_original_masks (oldEquiv old T)
    (actualMatrix (strictAlong T N) (old.map (strictAlong T))
      (geoTransformAlong (geometricTemplate N born) T).E z) (hc.1.bound z hz)
    (fun P hP => hT.erased P hP z hz)
  have hm := funext fun i => funext fun j => matrix_oldEquiv N old born T z i j
  rw [←hm,tauD_row_equiv]
  exact hlt

private theorem single_mask_state (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} {q : ℕ} (h : CurrentData N old born q)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) (hCard : P.card=q) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),FoldState N old born q {P} T ∧
      IsEquivariant N (old ++ born) T := by
  have hTau := h.bound
  have hNu := h.topZero
  rw [←hCard] at hTau hNu
  have hK := isCompact_canonical_mask_cosupport hn h.smooth h.full h.transverse
    h.dense h.compactBad hP
  have hSame := HironakaG4ZeroMaskSameGammaHistory.exists_prepared_zero_mask_same_gamma_history
    hn h.smooth h.full h.transverse h.dense h.order h.prepared P hP hTau hNu hK
  obtain ⟨Y,T,_hCanonical,_hResolution,hBorn,hFull,hSharp,hRows,hPrefix,hErase⟩ := hSame
  have hEq : IsEquivariant N (old ++ born) T :=
    HironakaG34ProcessedMaskEquivariance.isEquivariant_zero_mask_history hn h.smooth h.full h.transverse h.dense
      P hP hTau hNu hK T _hCanonical _hResolution.1
  refine ⟨Y,T,⟨hBorn,hFull,hSharp,fun i => (hRows i).2.2,?_,?_⟩,hEq⟩
  · intro k
    let Q := BlowupTowerSplit.head T k
    have hp := hPrefix k
    dsimp only at hp
    obtain ⟨_hSum,hNQ,hEQ,hTrQ,hDenseQ,hOrdQ,hPrepQ,hTauQ,hActQ,hNuQ,
      _hWFQ,_hNZQ,_hMonoQ,_hCompactSum,_hCosQ,hPartsQ⟩ := hp
    have hSharpQ := currentSharp_head N (old ++ born) T hSharp k
    have hFullQ : IsSNCDivisor n
        (geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) Q).E := by
      rw [full_ordered_list N old born Q]
      exact hEQ
    have hCompactQ := (current_bad_compact h.smooth.1 h.full.1 h.compactBad Q hSharpQ hFullQ).1
    rw [full_ordered_list N old born Q] at hCompactQ
    change currentStateData N old born q Q ⟨old.map (strictAlong Q),oldEquiv old Q⟩
    dsimp only [currentStateData]
    refine ⟨⟨hNQ,hEQ,hTrQ,hDenseQ,hOrdQ,hPrepQ,?_,?_,hCompactQ⟩,hActQ,?_⟩
    · rw [←hCard]
      exact hTauQ
    · rw [←hCard]
      exact hNuQ
    · intro i
      exact (hPartsQ i).2.2.1
  · intro R hR
    rw [Finset.mem_singleton.mp hR]
    unfold maskErased maskErasedData
    intro z hz
    rw [subset_map_proper_iff]
    have hm := funext fun i => funext fun j => matrix_oldEquiv N old born T z i j
    simpa only [hm] using hErase z hz

/-- **One actual finite history removes every original mask of this fixed positive count, equivariantly**: the
conclusions of `HironakaG4ZeroMaskFixedQFold.exists_prepared_zero_mask_fixed_q_drop`, plus `IsEquivariant N (old ++ born) T`. -/
theorem exists_prepared_zero_mask_fixed_q_drop_equivariant (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (q : ℕ) (hq : 0 < q)
    (hK : IsCompact (originalSharpBadLocus (n := n) N (old ++ born))) :
    let J := oldResidualPart N old born
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let RJ := fun i => (⟨N,born,J i,0⟩ : MarkedIdeal n X)
    (∀ x ∈ N,tauD (A x) ≤ q) →
    (∀ x ∈ N,tauD (A x)=q → nuOne (A x)=0) →
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N born) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
      CurrentSharpCentres N (old ++ born) T ∧
      CentresOver (originalSharpBadLocus (n := n) N (old ++ born)) T ∧
      IsEquivariant N (old ++ born) T ∧
      (∀ i : Fin old.length,IsGeoTestTower (RJ i) T) ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head T k
        let NQ := strictAlong Q N
        let oldQ := old.map (strictAlong Q)
        let bornQ := (geoTransformAlong (geometricTemplate N born) Q).E
        let eQ : Fin old.length ≃ Fin oldQ.length := finCongr (by simp [oldQ])
        let IQ := oldTraceIdeal NQ oldQ
        let DQ := oldMonomialPart NQ oldQ bornQ
        let JQ := oldResidualPart NQ oldQ bornQ
        let AQ : (BlowupTowerSplit.split T k).1 → Fin oldQ.length → Fin bornQ.length → ℕ :=
          fun z i j => divExpAlong n NQ (DQ i) (bornQ.get j) z
        IsClosedSubmanifold n NQ ∧ IsSNCDivisor n (oldQ ++ bornQ) ∧
        IsTransverse n NQ bornQ ∧
        NQ ⊆ closure (NQ \ ⋃ H ∈ oldQ ++ bornQ,H) ∧
        (∀ z ∈ NQ,∀ i,ordinaryTraceOrder NQ (JQ i) z ≤ 1) ∧
        (∀ z ∈ NQ,IsPreparedResidualSNCAt NQ oldQ bornQ z) ∧
        (∀ z ∈ NQ,tauD (AQ z) ≤ q) ∧
        (∀ z ∈ NQ,tauD (AQ z)=q → nuOne (AQ z)=0) ∧
        (∀ z ∈ NQ,∀ i : Fin old.length,
          eQ i ∈ properRows (AQ z) → i ∈ properRows (A (Q.proj z))) ∧
        originalSharpBadLocus (n := n) NQ (oldQ ++ bornQ) ⊆
          Q.proj ⁻¹' originalSharpBadLocus (n := n) N (old ++ born) ∧
        IsCompact (originalSharpBadLocus (n := n) NQ (oldQ ++ bornQ)) ∧
        (∀ P : Finset (Fin oldQ.length),P.Nonempty →
          IsCompact (cosupport n NQ
            (⟨fun z g => IsInSpanAt (n := n)
              (fun f => ∃ i ∈ P,(DQ i).mem z f) z g⟩ :
                GermIdeal n (BlowupTowerSplit.split T k).1) 1)) ∧
        ∀ i : Fin old.length,
          (geoTransformAlong (RJ i) Q).ideal=JQ (eQ i) ∧
          IQ (eQ i)=restrictOn n NQ ((DQ (eQ i)).mul (JQ (eQ i))) ∧
          (IQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (IQ (eQ i)) z) ∧
          (DQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (DQ (eQ i)) z) ∧
          IsMonomialAlong n NQ (DQ (eQ i)) bornQ ∧
          (JQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (JQ (eQ i)) z)) ∧
      let NT := strictAlong T N
      let BT := (geoTransformAlong (geometricTemplate N born) T).E
      let AT : Y → Fin old.length → Fin BT.length → ℕ := fun z i j =>
        divExpAlong n NT
          (monomialPartAlong n NT
            (restrictOn n NT (vanishingIdeal (n := n) (strictAlong T (old.get i)))) BT)
          (BT.get j) z
      ∀ z ∈ NT,tauD (AT z) < q := by
  classical
  dsimp only
  intro hTau hNu
  have h0 : CurrentData N old born q :=
    ⟨hN,hE,hTr,hdense,hOrd,hPrepared,hTau,hNu,hK⟩
  have fold (F : Finset (Finset (Fin old.length))) :
      (∀ P ∈ F,P.card=q) →
        ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),FoldState N old born q F T ∧
          IsEquivariant N (old ++ born) T := by
    induction F using Finset.induction_on with
    | empty =>
      intro _hF
      exact ⟨X,BlowupTower.refl,foldState_refl h0,isEquivariant_refl N (old ++ born)⟩
    | @insert P F _hPF ih =>
      intro hF
      obtain ⟨Y,T,hT,hEqT⟩ := ih (fun R hR => hF R (Finset.mem_insert_of_mem hR))
      have hCard : P.card=q := hF P (Finset.mem_insert_self P F)
      have hP : P.Nonempty := by
        apply Finset.card_pos.mp
        rw [hCard]
        exact hq
      have hCur := foldState_current T hT
      have hMappedCard : (P.map (oldEquiv old T).toEmbedding).card=q := by
        simpa only [Finset.card_map] using hCard
      obtain ⟨Z,S,hS,hEqS⟩ := single_mask_state hn hCur.1
        (P.map (oldEquiv old T).toEmbedding) hP.map hMappedCard
      have hEqS' : IsEquivariant (geoTransformAlong (geometricTemplate N born) T).N
          (old.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N born) T).E) S := by
        rw [N_geoTransformAlong]
        exact hEqS
      exact ⟨Z,T.append S,foldState_insert T S hT hS,
        IsEquivariant.append_of_current hN T hT.bornTest hT.fullTest hEqT S hEqS'⟩
  obtain ⟨Y,T,hT,hEqT⟩ := fold ((Finset.univ : Finset (Fin old.length)).powersetCard q)
    (fun P hP => (Finset.mem_powersetCard.mp hP).2)
  have hOver := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
    hN.1 hE.1 T hT.sharp).2
  refine ⟨Y,T,hT.bornTest,hT.fullTest,hT.sharp,hOver,hEqT,hT.residualTest,?_,?_⟩
  · intro k
    exact current_state_readout hn h0 (BlowupTowerSplit.head T k)
      (currentSharp_head N (old ++ born) T hT.sharp k) (hT.prefixData k)
  · exact foldState_endpoint_lt T hT

end
end Hironaka.HironakaG34ZeroMaskFoldEquivariance
