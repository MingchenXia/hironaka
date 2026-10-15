/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalGeneralCrossingHistory
/-! Exact original short-history filtered index from genuine SNC geometry.
Complete four-node mathematics written first in `Mathematics.tex`.
Crossing recursive values and full scheduling remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalShortUniformIndex
noncomputable section
open Classical
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers
  BlowupTowerTransforms BlowupTowerSplit CanonicalCentres BoundaryCount
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  HironakaOriginalInvariantEmptyInsertion HironakaOriginalInteriorPositiveLower
  HironakaOriginalShortLowerValues HironakaOriginalInteriorEmptyHistory
  HironakaOriginalCrossingLowerHistory InvDomainMemberRestriction

private theorem exists_original_index_of_mem_take {α : Type*} (L : List α) (m : ℕ) {a : α}
    (ha : a∈L.take m) : ∃ i : Fin L.length, i.val<m ∧ L.get i=a := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
  have hm : i.val<m := by have := i.isLt;simp only [List.length_take] at this;omega
  have hlen : i.val<L.length := by have := i.isLt;simp only [List.length_take] at this;omega
  exact ⟨⟨i.val,hlen⟩,hm,by simpa only [List.get_eq_getElem,List.getElem_take] using hi⟩

private theorem exists_original_index_of_mem_drop {α : Type*} (L : List α) (m : ℕ) {a : α}
    (ha : a∈L.drop m) : ∃ i : Fin L.length, m ≤ i.val ∧ L.get i=a := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
  have hlen : m+i.val<L.length := by have := i.isLt;simp only [List.length_drop] at this;omega
  exact ⟨⟨m+i.val,hlen⟩,by dsimp;omega,by simpa only [List.get_eq_getElem,List.getElem_drop] using hi⟩

private theorem boundaryCount_eq_filter_length {M : Type*} [TopologicalSpace M]
    (E : List (Set M)) (x : M) : boundaryCount E x=(E.filter fun W => decide (x∈W)).length := by
  classical
  have hc : boundaryCount E x=(List.finRange E.length).countP (fun i => decide (x∈E.get i)) := by
    simpa only [boundaryCount,List.toFinset_finRange] using
      (List.nodup_finRange E.length).card_eq_countP (P := fun i => x∈E.get i)
  calc
    _ = ((List.finRange E.length).filter fun i => decide (x∈E.get i)).length := by
      rw [hc,List.countP_eq_length_filter]
    _ = (((List.finRange E.length).map E.get).filter fun W => decide (x∈W)).length := by
      rw [List.filter_map,List.length_map]
      rfl
    _ = _ := by rw [List.map_get_finRange]

/-- True SNC geometry eliminates selected future copies INTERNALLY, so
the whole original retained prefix has its exact indexed boundary count. -/
theorem original_filtered_prefix_exact_count {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (E : List (Set M)) (hE : IsSNCDivisor n E) (x : M) (m j : ℕ)
    (hmj : m≤j) (hjE : j≤E.length) :
    ((E.take j).filter fun W => decide ¬(W∈E.take m ∧ x∈W)).length =
      j-boundaryCount (E.take m) x := by
  classical
  let Q : Set M → Bool := fun W => decide (W∈E.take m ∧ x∈W)
  have hfuture : ∀ W∈E.drop m, ¬(W∈E.take m ∧ x∈W) := by
    intro W hW hsel
    obtain ⟨i,him,hgeti⟩ := exists_original_index_of_mem_take E m hsel.1
    obtain ⟨j,hmj,hgetj⟩ := exists_original_index_of_mem_drop E m hW
    have he := SimultaneousNormalCrossings.eq_of_eventually_mem_iff hE
      (i := i) (j := j) (by rw [hgeti];exact hsel.2) (by rw [hgetj];exact hsel.2)
      (Eventually.of_forall fun _ => by rw [hgeti,hgetj])
    have hv := congrArg Fin.val he
    omega
  have htail : (((E.drop m).take (j-m)).filter Q)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro W hW
    simpa only [Q,decide_eq_true_eq] using hfuture W (List.mem_of_mem_take hW)
  have hsplit : E.take j=E.take m ++ (E.drop m).take (j-m) := by
    have h := List.take_add (l := E) (i := m) (j := j-m)
    rwa [Nat.add_sub_of_le hmj] at h
  have hQ : ((E.take j).filter Q).length=boundaryCount (E.take m) x := by
    rw [hsplit,List.filter_append,htail,List.append_nil,boundaryCount_eq_filter_length]
    congr 1
    apply List.filter_congr
    intro W hW
    simp only [Q,hW,true_and]
  have hpart := List.length_eq_length_filter_add (l := E.take j) Q
  rw [List.length_take,min_eq_left hjE,hQ] at hpart
  have hret : ((E.take j).filter (!Q ·)).length=j-boundaryCount (E.take m) x := by omega
  simpa [Q] using hret

variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Original actual bar-test geometry internally supplies SNC distinctness
and the exact true lower insertion index, at EVERY original stage point. -/
theorem original_positive_lower_index_exact (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (P : BlowupTower A Y)
    (hT : IsGeoTestTower (barMarked M) (H.append P)) (p : Y) :
    interiorPositiveLowerIndex M H P p = M.E.length+H.length-level M (H.append P) p := by
  let J := geoTransformAlong (barMarked M) (H.append P)
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked M hM) (H.append P) hT
  have hj : M.E.length+H.length≤J.E.length := by
    rw [length_E_geoTransformAlong,BlowupTower.length_append]
    change M.E.length+H.length≤M.E.length+(H.length+P.length)
    omega
  change ((J.E.take (M.E.length+H.length)).filter
    fun W => decide ¬(W∈J.E.take M.E.length ∧ p∈W)).length =
      M.E.length+H.length-boundaryCount (J.E.take M.E.length) p
  exact original_filtered_prefix_exact_count J.E hw.isSNCDivisor p M.E.length
    (M.E.length+H.length) (by omega) hj

/-- A single genuine strict history map on WHOLE Step One values; its
actual family index is selected by the original first-coordinate level. -/
def historyStepShift (k j : ℕ) (v : ℕ ×ₗ WithTop (ValTy k)) : ℕ ×ₗ WithTop (ValTy k) :=
  toLex ((ofLex v).1,WithTop.map (shiftFamily k (j-(ofLex v).1)) (ofLex v).2)

theorem strictMono_historyStepShift (k j : ℕ) : StrictMono (historyStepShift k j) := by
  intro a b hab
  change toLex ((ofLex a).1,WithTop.map (shiftFamily k (j-(ofLex a).1)) (ofLex a).2) <
    toLex ((ofLex b).1,WithTop.map (shiftFamily k (j-(ofLex b).1)) (ofLex b).2)
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases Prod.Lex.toLex_lt_toLex.mp hab with h | ⟨hℓ,hv⟩
  · exact Or.inl h
  · refine Or.inr ⟨hℓ,?_⟩
    change (ofLex a).1=(ofLex b).1 at hℓ
    change WithTop.map (shiftFamily k (j-(ofLex a).1)) (ofLex a).2 <
      WithTop.map (shiftFamily k (j-(ofLex b).1)) (ofLex b).2
    rw [hℓ]
    exact (strictMono_shiftFamily k (j-(ofLex b).1)).withTop_map hv

def historyStepShiftEmbedding (k j : ℕ) : (ℕ ×ₗ WithTop (ValTy k)) ↪o (ℕ ×ₗ WithTop (ValTy k)) :=
  OrderEmbedding.ofStrictMono (historyStepShift k j) (strictMono_historyStepShift k j)

/-- A SINGLE strict map computes the ENTIRE actual original StepOne value
on its true short branch, at ALL levels and ALL recursive lower orders. -/
theorem actual_entire_short_stepOne_value (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (ht : IsGeoTestTower (barMarked M) (H.append S)) (y : Y)
    (hshort : regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y<S.length) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y =
      historyStepShift k (M.E.length+H.length)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) := by
  have hparts := (isGeoTestTower_append_iff (barMarked M) H S).mp ht
  have hfst := Seq.StepOneValueMasked.stepOneInvL_fst (invFamily hn k) M (lowerMarkedM M) (H.append S) y
  change (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y)).1 =
    level M (H.append S) y at hfst
  by_cases hsp : IsSpecial M (H.append S) y
  · have hspnew := (isSpecial_dictionary M hM H hparts.1 S y).mpr hsp
    have hl := level_dictionary M hM H hparts.1 S y
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hspnew,if_pos hsp]
    simp only [historyStepShift,ofLex_toLex,WithTop.map_top,hl]
  · cases hl : level M (H.append S) y with
    | zero =>
      have hs0 : regimeRun (stepRegime M 0) (H.append S) y<S.length := by simpa only [hl] using hshort
      have hv := actual_short_zero_stepOne_value hn k M hM H hparts.1 S y hl hs0
      rw [hl] at hfst
      simpa only [pairShift,historyStepShift,hfst,Nat.sub_zero] using hv
    | succ s =>
      have hs : regimeRun (stepRegime M (s+1)) (H.append S) y<S.length := by simpa only [hl] using hshort
      let r := regimeRun (stepRegime M (s+1)) (H.append S) y
      let P := head S r
      let Q := tail S r
      have hprefix := ((isGeoTestTower_iff_head_tail (geoTransformAlong (barMarked M) H) S r).mp hparts.2).1
      have hHP : IsGeoTestTower (barMarked M) (H.append P) :=
        (isGeoTestTower_append_iff (barMarked M) H P).mpr ⟨hparts.1,hprefix⟩
      have hwhole : (H.append P).append Q=H.append S := by
        rw [BlowupTower.append_assoc,head_append_tail]
      have hQL : Q.length=r := by
        rw [length_tail,min_eq_left (le_of_lt hs)]
      have hreg : stepRegime M (s+1) ((H.append P).append Q) y := by
        rw [hwhole]
        exact ⟨hl,hsp⟩
      have hreach : Q.length≤regimeRun (stepRegime M (s+1)) ((H.append P).append Q) y := by
        rw [hwhole,hQL]
      have hbase := regime_at_base_of_reaching_run (stepRegime M (s+1)) (H.append P) Q y hreg hreach
      have hc := original_positive_lower_index_exact M hM H P hHP (Q.proj y)
      rw [hbase.1] at hc
      have hv := actual_short_positive_stepOne_value hn k M hM H hparts.1 S y s hl hs
      dsimp only at hv
      rw [hc] at hv
      rw [hl] at hfst
      simpa only [pairShift,historyStepShift,hfst] using hv

/-- All actual short-run points, with NO same-level or nonzero lower-order
restriction, have their whole strict/weak/equality spectrum reflected. -/
theorem actual_entire_short_spectrum_comparisons (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (ht : IsGeoTestTower (barMarked M) (H.append S)) (y z : Y)
    (hy : regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y<S.length)
    (hz : regimeRun (stepRegime M (level M (H.append S) z)) (H.append S) z<S.length) :
    let v := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y
    let w := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) z
    let v' := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y
    let w' := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) z
    (v'<w' ↔ v<w) ∧ (v'≤w' ↔ v≤w) ∧ (v'=w' ↔ v=w) := by
  dsimp only
  rw [actual_entire_short_stepOne_value hn k M hM H S ht y hy,
    actual_entire_short_stepOne_value hn k M hM H S ht z hz]
  have hm := strictMono_historyStepShift k (M.E.length+H.length)
  exact ⟨hm.lt_iff_lt,hm.le_iff_le,hm.injective.eq_iff⟩

end
end Hironaka.HironakaOriginalShortUniformIndex
