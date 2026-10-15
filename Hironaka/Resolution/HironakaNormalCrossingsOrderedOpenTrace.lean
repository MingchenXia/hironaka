/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceBaseChange
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation
/-!
# Actual ordered marking-one open trace and genuine empty-stage compression

Only actual open U and a genuine indexed SNC family F are original geometric
consumer inputs. Simultaneous recursion internally produces the actual retained
provenance embedding, independent source maximum steps, whole controlled ideals,
all-prefix marked data and true unequal-length stage compression. Empty original
and retained historical entries stay literal. Coefficients at empty carriers
may differ as metadata; their true entire vanishing ideals are unit, and all
intrinsic empty exponents are zero. Creation-event indices, not current carrier
nonemptiness, control deletion. Actual nested-open inputs and independently
generated procedures coincide; genuine globally labelled event masks compose.

This is OWN OFFLIB mathematics, awaiting root formal write-set registration.
General higher-driver functoriality, identification with the preceding general
separation driver, arbitrary unrelated ideals and higher-invariant nonsurjective
smooth base change remain OPEN. No output certificate is original caller input.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsOrderedOpenTrace
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaNormalCrossingsOrderedChoiceComparison NormalCrossings
  HironakaSmoothSubmersionOrderedMonomialProcedure HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionCoefficientIdeals HironakaNormalCrossingsOrderedMonomialTail
  HironakaNormalCrossingsFiniteMarkedCompletion BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers MonomialInvariant HironakaDivisorResidual BlowupTowerIsomorphism
noncomputable section
variable {n : ℕ} {X Y : Type u}

theorem singletonKey_lt_iff (F : List (Set X × ℕ)) (i j : Fin F.length) :
    singletonKey (n := n) F i < singletonKey (n := n) F j ↔
      (F.get i).2 < (F.get j).2 ∨ (F.get i).2 = (F.get j).2 ∧ i.val < j.val := by
  simp only [singletonKey,key_lt_key_iff,Finset.card_singleton,lt_self_iff_false,
    true_and,false_or,Finset.sum_singleton,indexedPowerData,dif_pos i.isLt,dif_pos j.isLt,
    Finset.Colex.singleton_lt_singleton]

theorem singletonKey_le_iff (F : List (Set X × ℕ)) (i j : Fin F.length) :
    singletonKey (n := n) F i ≤ singletonKey (n := n) F j ↔
      (F.get i).2 < (F.get j).2 ∨ (F.get i).2 = (F.get j).2 ∧ i.val ≤ j.val := by
  rw [le_iff_lt_or_eq,singletonKey_lt_iff]
  have he : singletonKey (n := n) F i = singletonKey (n := n) F j ↔ i = j :=
    (singletonKey_injective F).eq_iff
  rw [he]
  constructor
  · rintro (h|h)
    · rcases h with h|⟨h,hij⟩
      · exact Or.inl h
      · exact Or.inr ⟨h,hij.le⟩
    · subst j
      exact Or.inr ⟨rfl,le_rfl⟩
  · rintro (h|⟨h,hij⟩)
    · exact Or.inl (Or.inl h)
    · rcases lt_or_eq_of_le hij with hlt|heq
      · exact Or.inl (Or.inr ⟨h,hlt⟩)
      · exact Or.inr (Fin.ext heq)

structure RetainedTrace (f : Y → X) (S : List (Set Y × ℕ)) (G : List (Set X × ℕ)) where
  embed : Fin S.length ↪o Fin G.length
  carrier : ∀ i, (S.get i).1 = f ⁻¹' (G.get (embed i)).1
  power : ∀ i, (S.get i).1.Nonempty → (S.get i).2 = (G.get (embed i)).2
  covers : ∀ j, (f ⁻¹' (G.get j).1).Nonempty → ∃ i, embed i = j

namespace RetainedTrace
variable {f : Y → X} {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}

theorem active_iff (h : RetainedTrace f S G) (i : Fin S.length) :
    i ∈ activeIndices S ↔ 0 < (G.get (h.embed i)).2 ∧ (f ⁻¹' (G.get (h.embed i)).1).Nonempty := by
  classical
  simp only [activeIndices,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [h.carrier i]
  constructor
  · rintro ⟨hp,hne⟩
    rw [h.power i (by rw [h.carrier i]; exact hne)] at hp
    exact ⟨hp,hne⟩
  · rintro ⟨hp,hne⟩
    rw [← h.power i (by rw [h.carrier i]; exact hne)] at hp
    exact ⟨hp,hne⟩

theorem key_le_iff (h : RetainedTrace f S G) (i j : Fin S.length)
    (hi : (S.get i).1.Nonempty) (hj : (S.get j).1.Nonempty) :
    singletonKey (n := n) S i ≤ singletonKey (n := n) S j ↔
      singletonKey (n := n) G (h.embed i) ≤ singletonKey (n := n) G (h.embed j) := by
  rw [singletonKey_le_iff,singletonKey_le_iff,h.power i hi,h.power j hj]
  have he : i.val ≤ j.val ↔ (h.embed i).val ≤ (h.embed j).val := h.embed.le_iff_le.symm
  rw [he]

theorem selection_of_trace_nonempty (h : RetainedTrace f S G) (j : Fin G.length)
    (hsel : selectedIndex n G = some j) (hne : (f ⁻¹' (G.get j).1).Nonempty) :
    ∃ i : Fin S.length, h.embed i = j ∧ selectedIndex n S = some i := by
  classical
  obtain ⟨i,hei⟩ := h.covers j hne
  have hja := (selectedIndex_some_spec G hsel).1
  have hjp := (Finset.mem_filter.mp hja).2.1
  have hia : i ∈ activeIndices S := (h.active_iff i).mpr (by rw [hei]; exact ⟨hjp,hne⟩)
  refine ⟨i,hei,selectedIndex_eq_some_of_maximum S i hia ?_⟩
  intro k hk
  have hka := (h.active_iff k).mp hk
  have hGka : h.embed k ∈ activeIndices G := by
    apply Finset.mem_filter.mpr
    obtain ⟨y,hy⟩ := hka.2
    exact ⟨Finset.mem_univ _,hka.1,⟨f y,hy⟩⟩
  apply (h.key_le_iff k i (Finset.mem_filter.mp hk).2.2 (Finset.mem_filter.mp hia).2.2).mpr
  rw [hei]
  exact (selectedIndex_some_spec G hsel).2.1 _ hGka

end RetainedTrace

theorem dividedWeights_length (F : List (Set X × ℕ)) (j : Fin F.length) :
    (dividedWeights F j).length = F.length+1 := by simp [dividedWeights]

def oldIndex (F : List (Set X × ℕ)) (j i : Fin F.length) : Fin (dividedWeights F j).length :=
  ⟨i.val,by rw [dividedWeights_length]; omega⟩

def newIndex (F : List (Set X × ℕ)) (j : Fin F.length) : Fin (dividedWeights F j).length :=
  ⟨F.length,by rw [dividedWeights_length]; omega⟩

theorem dividedWeights_get_old (F : List (Set X × ℕ)) (j i : Fin F.length) :
    (dividedWeights F j).get (oldIndex F j i) = if i = j then (∅,0) else F.get i := by
  classical
  simp only [dividedWeights,List.get_eq_getElem,oldIndex]
  rw [List.getElem_append_left (by simpa only [List.length_set] using i.isLt)]
  by_cases hij : i = j
  · subst i
    simp
  · have hval : j.val ≠ i.val := fun he => hij (Fin.ext he.symm)
    rw [List.getElem_set_of_ne hval,if_neg hij]

theorem dividedWeights_get_new (F : List (Set X × ℕ)) (j : Fin F.length) :
    (dividedWeights F j).get (newIndex F j) = ((F.get j).1,(F.get j).2-1) := by
  simp [dividedWeights,newIndex,List.get_eq_getElem]

theorem index_old_or_new (F : List (Set X × ℕ)) (j : Fin F.length)
    (k : Fin (dividedWeights F j).length) :
    (∃ i, k = oldIndex F j i) ∨ k = newIndex F j := by
  have hk : k.val < F.length+1 := by rw [← dividedWeights_length F j]; exact k.isLt
  by_cases ho : k.val < F.length
  · exact Or.inl ⟨⟨k.val,ho⟩,Fin.ext rfl⟩
  · exact Or.inr (Fin.ext (by simp [newIndex]; omega))

def skipEmbed {f : Y → X} {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}
    (h : RetainedTrace f S G) (j : Fin G.length) : Fin S.length ↪o Fin (dividedWeights G j).length where
  toFun i := oldIndex G j (h.embed i)
  inj' := by
    intro i k he
    apply h.embed.injective
    apply Fin.ext
    have hv := congrArg (fun t : Fin (dividedWeights G j).length => t.val) he
    exact hv
  map_rel_iff' := by intro i k; change (h.embed i).val ≤ (h.embed k).val ↔ i.val ≤ k.val; exact h.embed.le_iff_le

namespace RetainedTrace
variable {f : Y → X} {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}

def skip (h : RetainedTrace f S G) (j : Fin G.length)
    (he : f ⁻¹' (G.get j).1 = ∅) : RetainedTrace f S (dividedWeights G j) where
  embed := skipEmbed h j
  carrier := by
    intro i
    rw [show (skipEmbed h j) i = oldIndex G j (h.embed i) from rfl,dividedWeights_get_old]
    split_ifs with hij
    · have hc := h.carrier i
      rw [hij,he] at hc
      simpa only [Set.preimage_empty] using hc
    · exact h.carrier i
  power := by
    intro i hne
    rw [show (skipEmbed h j) i = oldIndex G j (h.embed i) from rfl,dividedWeights_get_old]
    have hneq : h.embed i ≠ j := by
      intro hij
      rw [h.carrier i,hij,he] at hne
      exact not_nonempty_empty hne
    rw [if_neg hneq]
    exact h.power i hne
  covers := by
    intro k hne
    rcases index_old_or_new G j k with ⟨l,rfl⟩|rfl
    · rw [dividedWeights_get_old] at hne
      by_cases hlj : l = j
      · simp [hlj] at hne
      · rw [if_neg hlj] at hne
        obtain ⟨i,hei⟩ := h.covers l hne
        exact ⟨i,by change oldIndex G j (h.embed i) = oldIndex G j l; rw [hei]⟩
    · rw [dividedWeights_get_new,he] at hne
      exact (not_nonempty_empty hne).elim

end RetainedTrace

def keepEmbed {f : Y → X} {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}
    (h : RetainedTrace f S G) (i : Fin S.length) (j : Fin G.length) :
    Fin (dividedWeights S i).length ↪o Fin (dividedWeights G j).length :=
  OrderEmbedding.ofStrictMono
    (fun k => if hk : k.val < S.length then oldIndex G j (h.embed ⟨k.val,hk⟩) else newIndex G j)
    (by
      intro k l hkl
      change k.val < l.val at hkl
      dsimp only
      split_ifs with hk hl
      · change (h.embed ⟨k.val,hk⟩).val < (h.embed ⟨l.val,hl⟩).val
        exact h.embed.strictMono hkl
      · change (h.embed ⟨k.val,hk⟩).val < G.length
        exact (h.embed ⟨k.val,hk⟩).isLt
      · omega
      · have hk' : k.val < S.length+1 := by rw [← dividedWeights_length S i]; exact k.isLt
        have hl' : l.val < S.length+1 := by rw [← dividedWeights_length S i]; exact l.isLt
        omega)

theorem keepEmbed_old {f : Y → X} {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}
    (h : RetainedTrace f S G) (i l : Fin S.length) (j : Fin G.length) :
    keepEmbed h i j (oldIndex S i l) = oldIndex G j (h.embed l) := by
  simp [keepEmbed,oldIndex,l.isLt]

theorem keepEmbed_new {f : Y → X} {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}
    (h : RetainedTrace f S G) (i : Fin S.length) (j : Fin G.length) :
    keepEmbed h i j (newIndex S i) = newIndex G j := by
  simp [keepEmbed,newIndex]

namespace RetainedTrace
variable {f : Y → X} {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}

def keep (h : RetainedTrace f S G) (i : Fin S.length) (j : Fin G.length)
    (hei : h.embed i = j) : RetainedTrace f (dividedWeights S i) (dividedWeights G j) where
  embed := keepEmbed h i j
  carrier := by
    intro k
    rcases index_old_or_new S i k with ⟨l,rfl⟩|rfl
    · rw [keepEmbed_old,dividedWeights_get_old,dividedWeights_get_old]
      by_cases hli : l = i
      · subst l
        simp [hei]
      · have heq : h.embed l ≠ j := fun he => hli (h.embed.injective (he.trans hei.symm))
        rw [if_neg hli,if_neg heq]
        exact h.carrier l
    · rw [keepEmbed_new,dividedWeights_get_new,dividedWeights_get_new]
      simpa only [hei] using h.carrier i
  power := by
    intro k hne
    rcases index_old_or_new S i k with ⟨l,rfl⟩|rfl
    · rw [dividedWeights_get_old] at hne
      by_cases hli : l = i
      · simp [hli] at hne
      · rw [if_neg hli] at hne
        rw [keepEmbed_old,dividedWeights_get_old,dividedWeights_get_old]
        have heq : h.embed l ≠ j := fun he => hli (h.embed.injective (he.trans hei.symm))
        rw [if_neg hli,if_neg heq]
        exact h.power l hne
    · rw [dividedWeights_get_new] at hne
      rw [keepEmbed_new,dividedWeights_get_new,dividedWeights_get_new,← hei,h.power i hne]
  covers := by
    intro k hne
    rcases index_old_or_new G j k with ⟨l,rfl⟩|rfl
    · rw [dividedWeights_get_old] at hne
      by_cases hlj : l = j
      · simp [hlj] at hne
      · rw [if_neg hlj] at hne
        obtain ⟨l',hel⟩ := h.covers l hne
        exact ⟨oldIndex S i l',by rw [keepEmbed_old,hel]⟩
    · exact ⟨newIndex S i,keepEmbed_new h i j⟩


theorem selection_none (h : RetainedTrace f S G) (hg : selectedIndex n G = none) :
    selectedIndex n S = none := by
  classical
  apply (selectedIndex_eq_none_iff S).mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hp,y,hy⟩ := (h.active_iff i).mp hi
  have hgi : h.embed i ∈ activeIndices G :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,⟨f y,hy⟩⟩
  rw [(selectedIndex_eq_none_iff G).mp hg] at hgi
  simp at hgi

end RetainedTrace

open Classical in
def traceCentres (f : Y → X) (n q : ℕ) (G : List (Set X × ℕ)) : List (Set Y) :=
  (centreTrace n q G).filterMap fun C => if (f ⁻¹' C).Nonempty then some (f ⁻¹' C) else none

def traceCount (f : Y → X) (n q : ℕ) (G : List (Set X × ℕ)) : ℕ :=
  (traceCentres f n q G).length

theorem traceCentres_zero (f : Y → X) (G : List (Set X × ℕ)) : traceCentres f n 0 G = [] := rfl

theorem traceCentres_none (f : Y → X) (q : ℕ) (G : List (Set X × ℕ))
    (he : selectedIndex n G = none) : traceCentres f n (q+1) G = [] := by
  unfold traceCentres centreTrace
  rw [he]
  rfl

theorem traceCentres_some_empty (f : Y → X) (q : ℕ) (G : List (Set X × ℕ)) (j : Fin G.length)
    (he : selectedIndex n G = some j) (hne : f ⁻¹' (G.get j).1 = ∅) :
    traceCentres f n (q+1) G = traceCentres f n q (dividedWeights G j) := by
  classical
  unfold traceCentres
  conv_lhs => unfold centreTrace
  rw [he,List.filterMap_cons]
  simp only [hne,Set.not_nonempty_empty,if_false]

theorem traceCentres_some_nonempty (f : Y → X) (q : ℕ) (G : List (Set X × ℕ)) (j : Fin G.length)
    (he : selectedIndex n G = some j) (hne : (f ⁻¹' (G.get j).1).Nonempty) :
    traceCentres f n (q+1) G = f ⁻¹' (G.get j).1 :: traceCentres f n q (dividedWeights G j) := by
  classical
  unfold traceCentres
  conv_lhs => unfold centreTrace
  rw [he,List.filterMap_cons,if_pos hne]

theorem trace_run {f : Y → X} (q : ℕ) {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}
    (h : RetainedTrace f S G) :
    Nonempty (RetainedTrace f (terminalState n (traceCount f n q G) S) (terminalState n q G)) ∧
      centreTrace n (traceCount f n q G) S = traceCentres f n q G := by
  classical
  induction q generalizing S G with
  | zero => exact ⟨⟨h⟩,rfl⟩
  | succ q ih =>
    cases hg : selectedIndex n G with
    | none =>
      have hp : traceCount f n (q+1) G = 0 := by
        unfold traceCount
        rw [traceCentres_none f q G hg]
        rfl
      rw [hp,terminalState_succ_none q G hg,traceCentres_none f q G hg]
      exact ⟨⟨h⟩,rfl⟩
    | some j =>
      by_cases hne : (f ⁻¹' (G.get j).1).Nonempty
      · obtain ⟨i,hei,hsel⟩ := h.selection_of_trace_nonempty j hg hne
        obtain ⟨hr,hc⟩ := ih (h.keep i j hei)
        have hp : traceCount f n (q+1) G = traceCount f n q (dividedWeights G j)+1 := by
          unfold traceCount
          rw [traceCentres_some_nonempty f q G j hg hne,List.length_cons]
        rw [hp,terminalState_succ_some q G j hg,terminalState_succ_some _ S i hsel]
        refine ⟨hr,?_⟩
        conv_lhs => unfold centreTrace
        simp only [hsel]
        rw [traceCentres_some_nonempty f q G j hg hne,hc,h.carrier i,hei]
      · have hempty : f ⁻¹' (G.get j).1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        obtain ⟨hr,hc⟩ := ih (h.skip j hempty)
        have hp : traceCount f n (q+1) G = traceCount f n q (dividedWeights G j) := by
          unfold traceCount
          rw [traceCentres_some_empty f q G j hg hempty]
        rw [hp,terminalState_succ_some q G j hg,traceCentres_some_empty f q G j hg hempty]
        exact ⟨hr,hc⟩


def initialTrace (f : Y → X) (G : List (Set X × ℕ)) : RetainedTrace f (pulledWeights f G) G where
  embed := OrderEmbedding.ofStrictMono (fun i => (pulledIndex f G).symm i) (by
    intro i j hij
    exact hij)
  carrier := by
    intro i
    change ((pulledWeights f G).get i).1 = f ⁻¹' (G.get ((pulledIndex f G).symm i)).1
    have hg := pulledWeights_get f G ((pulledIndex f G).symm i)
    simpa only [Equiv.apply_symm_apply] using congrArg Prod.fst hg
  power := by
    intro i _
    change ((pulledWeights f G).get i).2 = (G.get ((pulledIndex f G).symm i)).2
    have hg := pulledWeights_get f G ((pulledIndex f G).symm i)
    simpa only [Equiv.apply_symm_apply] using congrArg Prod.snd hg
  covers := by
    intro j _
    exact ⟨pulledIndex f G j,(pulledIndex f G).symm_apply_apply j⟩

theorem actual_trace_run (f : Y → X) (q : ℕ) (G : List (Set X × ℕ)) :
    Nonempty (RetainedTrace f (terminalState n (traceCount f n q G) (pulledWeights f G))
      (terminalState n q G)) ∧
      centreTrace n (traceCount f n q G) (pulledWeights f G) = traceCentres f n q G :=
  trace_run q (initialTrace f G)


theorem terminalState_of_none (q : ℕ) (G : List (Set X × ℕ)) (he : selectedIndex n G = none) :
    terminalState n q G = G := by
  cases q with
  | zero => rfl
  | succ q => exact terminalState_succ_none q G he

theorem centreTrace_of_none (q : ℕ) (G : List (Set X × ℕ)) (he : selectedIndex n G = none) :
    centreTrace n q G = [] := by
  cases q with
  | zero => rfl
  | succ q => unfold centreTrace; rw [he]

theorem terminalState_add (p q : ℕ) (G : List (Set X × ℕ)) :
    terminalState n (p+q) G = terminalState n q (terminalState n p G) := by
  induction p generalizing G with
  | zero => simp [terminalState]
  | succ p ih =>
    cases he : selectedIndex n G with
    | none =>
      rw [Nat.succ_add,terminalState_succ_none _ G he,terminalState_succ_none _ G he,
        terminalState_of_none _ G he]
    | some j =>
      rw [Nat.succ_add,terminalState_succ_some _ G j he,terminalState_succ_some _ G j he,ih]

theorem centreTrace_add (p q : ℕ) (G : List (Set X × ℕ)) :
    centreTrace n (p+q) G = centreTrace n p G ++ centreTrace n q (terminalState n p G) := by
  induction p generalizing G with
  | zero => simp [terminalState,centreTrace]
  | succ p ih =>
    cases he : selectedIndex n G with
    | none =>
      rw [Nat.succ_add,terminalState_succ_none _ G he,centreTrace_of_none _ G he,
        centreTrace_of_none _ G he,centreTrace_of_none _ G he]
      rfl
    | some j =>
      rw [Nat.succ_add,terminalState_succ_some _ G j he]
      conv_lhs => unfold centreTrace
      conv_rhs => lhs; unfold centreTrace
      simp only [he]
      rw [ih,List.cons_append]

theorem actual_division_sum_drop (G : List (Set X × ℕ)) (j : Fin G.length)
    (hj : 0 < (G.get j).2) : coefficientSum (dividedWeights G j)+1 = coefficientSum G := by
  have hOld := ((List.getElem_cons_eraseIdx_perm (l := G) j.isLt).map Prod.snd).sum_eq
  have hNew := ((List.set_perm_cons_eraseIdx (l := G) j.isLt (∅,0)).map Prod.snd).sum_eq
  simp only [List.map_cons,List.sum_cons,zero_add] at hOld hNew
  change (G.get j).2 + (G.eraseIdx j.val |>.map Prod.snd).sum = (G.map Prod.snd).sum at hOld
  unfold coefficientSum
  rw [dividedWeights,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,hNew]
  change (List.map Prod.snd (G.eraseIdx j.val)).sum + ((G.get j).2-1) +1 = (G.map Prod.snd).sum
  omega

theorem centreTrace_length_le_sum (q : ℕ) (G : List (Set X × ℕ)) :
    (centreTrace n q G).length ≤ coefficientSum G := by
  classical
  induction q generalizing G with
  | zero => exact Nat.zero_le _
  | succ q ih =>
    cases he : selectedIndex n G with
    | none => rw [centreTrace_of_none _ G he]; exact Nat.zero_le _
    | some j =>
      have hj := (Finset.mem_filter.mp (selectedIndex_some_spec G he).1).2.1
      have hd := actual_division_sum_drop G j hj
      have hl := ih (dividedWeights G j)
      unfold centreTrace
      simp only [he,List.length_cons]
      omega

theorem terminalState_inactive (q : ℕ) (G : List (Set X × ℕ))
    (hq : coefficientSum G ≤ q) : activeIndices (terminalState n q G) = ∅ := by
  classical
  induction q generalizing G with
  | zero =>
    change activeIndices G = ∅
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hp := (Finset.mem_filter.mp hj).2.1
    have hs := ((List.getElem_cons_eraseIdx_perm (l := G) j.isLt).map Prod.snd).sum_eq
    simp only [List.map_cons,List.sum_cons] at hs
    change (G.get j).2+(G.eraseIdx j.val |>.map Prod.snd).sum = (G.map Prod.snd).sum at hs
    unfold coefficientSum at hq
    omega
  | succ q ih =>
    cases he : selectedIndex n G with
    | none => rw [terminalState_succ_none q G he]; exact (selectedIndex_eq_none_iff G).mp he
    | some j =>
      rw [terminalState_succ_some q G j he]
      apply ih
      have hj := (Finset.mem_filter.mp (selectedIndex_some_spec G he).1).2.1
      have hd := actual_division_sum_drop G j hj
      omega

theorem traceCount_le_own_sum (f : Y → X) (q : ℕ) (G : List (Set X × ℕ)) :
    traceCount f n q G ≤ coefficientSum (pulledWeights f G) := by
  have hc := (actual_trace_run (n := n) f q G).2
  have hb := centreTrace_length_le_sum (n := n) (traceCount f n q G) (pulledWeights f G)
  rw [hc] at hb
  exact hb

theorem actual_completed_trace (f : Y → X) (G : List (Set X × ℕ)) :
    centreTrace n (coefficientSum (pulledWeights f G)) (pulledWeights f G) =
      traceCentres f n (coefficientSum G) G ∧
    Nonempty (RetainedTrace f
      (terminalState n (coefficientSum (pulledWeights f G)) (pulledWeights f G))
      (terminalState n (coefficientSum G) G)) := by
  let p := traceCount f n (coefficientSum G) G
  obtain ⟨⟨hr⟩,hc⟩ := actual_trace_run (n := n) f (coefficientSum G) G
  have hg : selectedIndex n (terminalState n (coefficientSum G) G) = none :=
    (selectedIndex_eq_none_iff _).mpr (terminalState_inactive _ G le_rfl)
  have hs := hr.selection_none (n := n) hg
  have hp : p ≤ coefficientSum (pulledWeights f G) := traceCount_le_own_sum f _ G
  have hqe : p+(coefficientSum (pulledWeights f G)-p) = coefficientSum (pulledWeights f G) :=
    Nat.add_sub_of_le hp
  have hstate : terminalState n (coefficientSum (pulledWeights f G)) (pulledWeights f G) =
      terminalState n p (pulledWeights f G) := by
    rw [← hqe,terminalState_add,terminalState_of_none _ _ hs]
  refine ⟨?_,?_⟩
  · rw [← hqe,centreTrace_add,centreTrace_of_none _ _ hs,List.append_nil]
    exact hc
  · rw [hstate]
    exact ⟨hr⟩



/-- Global OWN completion internally already reaches the independent source OWN state. -/
theorem actual_completed_state (f : Y → X) (G : List (Set X × ℕ)) :
    terminalState n (coefficientSum (pulledWeights f G)) (pulledWeights f G) =
      terminalState n (traceCount f n (coefficientSum G) G) (pulledWeights f G) := by
  let p := traceCount f n (coefficientSum G) G
  obtain ⟨⟨hr⟩,_⟩ := actual_trace_run (n := n) f (coefficientSum G) G
  have hg : selectedIndex n (terminalState n (coefficientSum G) G) = none :=
    (selectedIndex_eq_none_iff _).mpr (terminalState_inactive _ G le_rfl)
  have hs := hr.selection_none (n := n) hg
  have hp : p ≤ coefficientSum (pulledWeights f G) := traceCount_le_own_sum f _ G
  have he : p+(coefficientSum (pulledWeights f G)-p) = coefficientSum (pulledWeights f G) :=
    Nat.add_sub_of_le hp
  rw [← he,terminalState_add,terminalState_of_none _ _ hs]


namespace RetainedTrace
variable {f : Y → X} {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}

def indexWord (h : RetainedTrace f S G) : List ℕ := List.ofFn fun i => (h.embed i).val

theorem indexWord_skip (h : RetainedTrace f S G) (j : Fin G.length)
    (he : f ⁻¹' (G.get j).1 = ∅) : (h.skip j he).indexWord = h.indexWord := rfl

theorem indexWord_keep (h : RetainedTrace f S G) (i : Fin S.length) (j : Fin G.length)
    (hei : h.embed i = j) : (h.keep i j hei).indexWord = h.indexWord ++ [G.length] := by
  unfold indexWord
  rw [List.ofFn_congr (dividedWeights_length S i),List.ofFn_succ']
  change (List.ofFn fun k : Fin S.length =>
      ((h.keep i j hei).embed (Fin.cast (dividedWeights_length S i).symm k.castSucc)).val).concat
      (((h.keep i j hei).embed (Fin.cast (dividedWeights_length S i).symm (Fin.last S.length))).val) = _
  have hold : ∀ k : Fin S.length,
      (h.keep i j hei).embed (Fin.cast (dividedWeights_length S i).symm k.castSucc) = oldIndex G j (h.embed k) := by
    intro k
    have heq : Fin.cast (dividedWeights_length S i).symm k.castSucc = oldIndex S i k := Fin.ext rfl
    rw [heq]
    exact keepEmbed_old h i k j
  have hnew : (h.keep i j hei).embed (Fin.cast (dividedWeights_length S i).symm (Fin.last S.length)) = newIndex G j := by
    have heq : Fin.cast (dividedWeights_length S i).symm (Fin.last S.length) = newIndex S i := Fin.ext rfl
    rw [heq]
    exact keepEmbed_new h i j
  simp only [hold,hnew,oldIndex,newIndex,List.concat_eq_append]

end RetainedTrace

open Classical in
def newHistoryTrace (f : Y → X) (n : ℕ) : ℕ → List (Set X × ℕ) → List ℕ
  | 0,_ => []
  | q+1,G => match selectedIndex n G with
    | none => []
    | some j => (if (f ⁻¹' (G.get j).1).Nonempty then [G.length] else []) ++
        newHistoryTrace f n q (dividedWeights G j)


theorem trace_run_full_history {f : Y → X} (q : ℕ) {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}
    (h : RetainedTrace f S G) :
    ∃ hr : RetainedTrace f (terminalState n (traceCount f n q G) S) (terminalState n q G),
      hr.indexWord = h.indexWord ++ newHistoryTrace f n q G ∧
      centreTrace n (traceCount f n q G) S = traceCentres f n q G := by
  classical
  induction q generalizing S G with
  | zero => exact ⟨h,by simp only [newHistoryTrace,List.append_nil]; rfl,rfl⟩
  | succ q ih =>
    cases hg : selectedIndex n G with
    | none =>
      have hp : traceCount f n (q+1) G = 0 := by
        unfold traceCount
        rw [traceCentres_none f q G hg]
        rfl
      rw [hp,terminalState_succ_none q G hg,traceCentres_none f q G hg]
      refine ⟨h,?_,rfl⟩
      simp only [newHistoryTrace,hg,List.append_nil]
      rfl
    | some j =>
      by_cases hne : (f ⁻¹' (G.get j).1).Nonempty
      · obtain ⟨i,hei,hsel⟩ := h.selection_of_trace_nonempty j hg hne
        obtain ⟨hr,hw,hc⟩ := ih (h.keep i j hei)
        have hp : traceCount f n (q+1) G = traceCount f n q (dividedWeights G j)+1 := by
          unfold traceCount
          rw [traceCentres_some_nonempty f q G j hg hne,List.length_cons]
        rw [hp,terminalState_succ_some q G j hg,terminalState_succ_some _ S i hsel]
        refine ⟨hr,?_,?_⟩
        · rw [hw,RetainedTrace.indexWord_keep]
          simp only [newHistoryTrace,hg,hne,if_true,List.append_assoc]
        · conv_lhs => unfold centreTrace
          simp only [hsel]
          rw [traceCentres_some_nonempty f q G j hg hne,hc,h.carrier i,hei]
      · have hempty : f ⁻¹' (G.get j).1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        obtain ⟨hr,hw,hc⟩ := ih (h.skip j hempty)
        have hp : traceCount f n (q+1) G = traceCount f n q (dividedWeights G j) := by
          unfold traceCount
          rw [traceCentres_some_empty f q G j hg hempty]
        rw [hp,terminalState_succ_some q G j hg,traceCentres_some_empty f q G j hg hempty]
        refine ⟨hr,?_,hc⟩
        rw [hw,RetainedTrace.indexWord_skip]
        simp only [newHistoryTrace,hg,hne,if_false,List.nil_append]

namespace RetainedTrace
variable {f : Y → X} {S : List (Set Y × ℕ)} {G : List (Set X × ℕ)}

theorem whole_carriers (h : RetainedTrace f S G) :
    S.map Prod.fst = h.indexWord.map (fun k => f ⁻¹' ((G[k]?).getD (∅,0)).1) := by
  rw [indexWord,List.map_ofFn]
  have he : (fun i : Fin S.length => f ⁻¹' ((G[(h.embed i).val]?).getD (∅,0)).1) =
      (fun i : Fin S.length => (S.get i).1) := by
    funext i
    rw [List.getElem?_eq_getElem (h.embed i).isLt]
    exact (h.carrier i).symm
  change S.map Prod.fst = List.ofFn (fun i : Fin S.length => f ⁻¹' ((G[(h.embed i).val]?).getD (∅,0)).1)
  rw [he]
  exact (List.ofFn_getElem_eq_map S Prod.fst).symm

end RetainedTrace

theorem initialTrace_indexWord (f : Y → X) (G : List (Set X × ℕ)) :
    (initialTrace f G).indexWord = List.range G.length := by
  unfold RetainedTrace.indexWord
  have he : (fun i : Fin (pulledWeights f G).length => ((initialTrace f G).embed i).val) =
      (fun i : Fin (pulledWeights f G).length => i.val) := rfl
  rw [he,List.ofFn_eq_map]
  simp [pulledWeights]

theorem actual_trace_full_history (f : Y → X) (q : ℕ) (G : List (Set X × ℕ)) :
    ∃ hr : RetainedTrace f (terminalState n (traceCount f n q G) (pulledWeights f G)) (terminalState n q G),
      hr.indexWord = List.range G.length ++ newHistoryTrace f n q G ∧
      (terminalState n (traceCount f n q G) (pulledWeights f G)).map Prod.fst =
        (List.range G.length ++ newHistoryTrace f n q G).map
          (fun k => f ⁻¹' (((terminalState n q G)[k]?).getD (∅,0)).1) ∧
      centreTrace n (traceCount f n q G) (pulledWeights f G) = traceCentres f n q G := by
  obtain ⟨hr,hw,hc⟩ := trace_run_full_history (n := n) q (initialTrace f G)
  rw [initialTrace_indexWord] at hw
  exact ⟨hr,hw,by rw [hr.whole_carriers,hw],hc⟩


/-- OWN endpoint retains every original entry and exactly the genuine creation-time kept history. -/
theorem actual_completed_full_history (f : Y → X) (G : List (Set X × ℕ)) :
    ∃ hr : RetainedTrace f
        (terminalState n (coefficientSum (pulledWeights f G)) (pulledWeights f G))
        (terminalState n (coefficientSum G) G),
      hr.indexWord = List.range G.length ++ newHistoryTrace f n (coefficientSum G) G ∧
      (terminalState n (coefficientSum (pulledWeights f G)) (pulledWeights f G)).map Prod.fst =
        (List.range G.length ++ newHistoryTrace f n (coefficientSum G) G).map
          (fun k => f ⁻¹' (((terminalState n (coefficientSum G) G)[k]?).getD (∅,0)).1) ∧
      centreTrace n (coefficientSum (pulledWeights f G)) (pulledWeights f G) =
        traceCentres f n (coefficientSum G) G := by
  rw [actual_completed_state]
  obtain ⟨hr,hw,hcar,_⟩ := actual_trace_full_history (n := n) f (coefficientSum G) G
  exact ⟨hr,hw,hcar,(actual_completed_trace (n := n) f G).1⟩


section WholeIdeals
variable {B : CMfd.{u} n}

theorem controlled_product_congr (S T : List (Set B × ℕ))
    (hS : IsSNCDivisor n (S.map Prod.fst)) (hT : IsSNCDivisor n (T.map Prod.fst))
    (i : Fin S.length) (j : Fin T.length) (hi : 0 < (S.get i).2) (hj : 0 < (T.get j).2)
    (hC : (S.get i).1 = (T.get j).1)
    (hI : componentPowerProduct (n := n) S = componentPowerProduct (n := n) T) :
    componentPowerProduct (n := n) (dividedWeights S i) =
      componentPowerProduct (n := n) (dividedWeights T j) := by
  have hs := congrArg (fun M : MarkedIdeal n B => M.ideal) (geoTransform_indexed_positive S hS i hi)
  have ht := congrArg (fun M : MarkedIdeal n B => M.ideal) (geoTransform_indexed_positive T hT j hj)
  change _ = componentPowerProduct (n := n) (dividedWeights S i) at hs
  change _ = componentPowerProduct (n := n) (dividedWeights T j) at ht
  rw [← hs,← ht]
  change RestrictedIdealQuotient.colonAlong n (BlowupStrictSubmanifold.geoStrictTransform (id : B → B) (S.get i).1 univ)
      (GermIdeal.pullback (m := n) (id : B → B) (componentPowerProduct (n := n) S))
      (idealPow (GermIdeal.pullback (m := n) (id : B → B) (vanishingIdeal (n := n) (S.get i).1)) 1) = _
  rw [hC,hI]
  rfl

theorem controlled_product_empty (S : List (Set B × ℕ)) (hS : IsSNCDivisor n (S.map Prod.fst))
    (j : Fin S.length) (hj : 0 < (S.get j).2) (he : (S.get j).1 = ∅) :
    componentPowerProduct (n := n) (dividedWeights S j) = componentPowerProduct (n := n) S := by
  have hc : (componentPowerProduct (n := n) S).IsCoherent := (isWellFormed_monomialMarkedIdeal hS S
    (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)).isCoherent
  have hstep := congrArg (fun M : MarkedIdeal n B => M.ideal) (geoTransform_indexed_positive S hS j hj)
  change _ = componentPowerProduct (n := n) (dividedWeights S j) at hstep
  rw [← hstep]
  change RestrictedIdealQuotient.colonAlong n (BlowupStrictSubmanifold.geoStrictTransform (id : B → B) (S.get j).1 univ)
      (GermIdeal.pullback (m := n) (id : B → B) (componentPowerProduct (n := n) S))
      (idealPow (GermIdeal.pullback (m := n) (id : B → B) (vanishingIdeal (n := n) (S.get j).1)) 1) = _
  have hstrict : BlowupStrictSubmanifold.geoStrictTransform (id : B → B) (∅ : Set B) univ = univ := by
    simp [BlowupStrictSubmanifold.geoStrictTransform]
  rw [he,hstrict,vanishingIdeal_empty_eq_unit,BlowupControlledTransform.pullback_id hc,
    BlowupControlledTransform.pullback_id (DivisorMetric.isCoherent_of_isInvertible
      BlowupExceptionalDivisor.isInvertible_unitIdeal),BlowupControlledTransform.idealPow_unitIdeal]
  unfold RestrictedIdealQuotient.colonAlong
  rw [BlowupTowerTransforms.restrictOn_univ hc,BlowupControlledTransform.colon_unitIdeal hc]


theorem trace_run_whole_ideal {f : B → X} (q : ℕ) {S : List (Set B × ℕ)} {G : List (Set X × ℕ)}
    (h : RetainedTrace f S G) (hS : IsSNCDivisor n (S.map Prod.fst))
    (hP : IsSNCDivisor n ((pulledWeights f G).map Prod.fst))
    (hI : componentPowerProduct (n := n) S = componentPowerProduct (n := n) (pulledWeights f G)) :
    componentPowerProduct (n := n) (terminalState n (traceCount f n q G) S) =
      componentPowerProduct (n := n) (pulledWeights f (terminalState n q G)) := by
  classical
  induction q generalizing S G with
  | zero => exact hI
  | succ q ih =>
    cases hg : selectedIndex n G with
    | none =>
      have hp : traceCount f n (q+1) G = 0 := by unfold traceCount; rw [traceCentres_none f q G hg]; rfl
      rw [hp,terminalState_succ_none q G hg]
      exact hI
    | some j =>
      let j' := pulledIndex f G j
      have hj : 0 < (G.get j).2 := (Finset.mem_filter.mp (selectedIndex_some_spec G hg).1).2.1
      have hj' : 0 < ((pulledWeights f G).get j').2 := by simpa only [j',pulledWeights_get] using hj
      have hD : IsSNCDivisor n ((pulledWeights f (dividedWeights G j)).map Prod.fst) := by
        rw [pulledWeights_dividedWeights]
        exact dividedWeights_isSNCDivisor _ hP j' hj'
      by_cases hne : (f ⁻¹' (G.get j).1).Nonempty
      · obtain ⟨i,hei,hsel⟩ := h.selection_of_trace_nonempty j hg hne
        have hi : 0 < (S.get i).2 := (Finset.mem_filter.mp (selectedIndex_some_spec S hsel).1).2.1
        have hC : (S.get i).1 = ((pulledWeights f G).get j').1 := by
          rw [h.carrier i,hei]
          simp only [j',pulledWeights_get]
        have hI' : componentPowerProduct (n := n) (dividedWeights S i) =
            componentPowerProduct (n := n) (pulledWeights f (dividedWeights G j)) := by
          rw [pulledWeights_dividedWeights]
          exact controlled_product_congr S _ hS hP i j' hi hj' hC hI
        have hp : traceCount f n (q+1) G = traceCount f n q (dividedWeights G j)+1 := by
          unfold traceCount
          rw [traceCentres_some_nonempty f q G j hg hne,List.length_cons]
        rw [hp,terminalState_succ_some q G j hg,terminalState_succ_some _ S i hsel]
        exact ih (h.keep i j hei) (dividedWeights_isSNCDivisor S hS i hi) hD hI'
      · have hempty : f ⁻¹' (G.get j).1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        have he : ((pulledWeights f G).get j').1 = ∅ := by simp only [j',pulledWeights_get,hempty]
        have hI' : componentPowerProduct (n := n) S =
            componentPowerProduct (n := n) (pulledWeights f (dividedWeights G j)) := by
          rw [pulledWeights_dividedWeights,controlled_product_empty _ hP j' hj' he]
          exact hI
        have hp : traceCount f n (q+1) G = traceCount f n q (dividedWeights G j) := by
          unfold traceCount
          rw [traceCentres_some_empty f q G j hg hempty]
        rw [hp,terminalState_succ_some q G j hg]
        exact ih (h.skip j hempty) hS hD hI'

end WholeIdeals

section ActualOpens
variable {A : CMfd.{u} n}

theorem openWeights_isSNCDivisor (U : TopologicalSpace.Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSNCDivisor n ((pulledWeights (Subtype.val : U → A) F).map Prod.fst) := by
  rw [pulledWeights_carriers]
  exact HironakaBaseChange.IsOpenHoloEmbedding.isSNCDivisor_map_preimage (HironakaBaseChange.isOpenHoloEmbedding_val U) hF

theorem open_pullback_vanishingIdeal_member (U : TopologicalSpace.Opens A)
    (E : List (Set A)) (hE : IsSNCDivisor n E) (i : Fin E.length) :
    GermIdeal.pullback (m := n) (Subtype.val : U → A) (vanishingIdeal (n := n) (E.get i)) =
      vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' E.get i) := by
  let E' := E.map ((Subtype.val : U → A) ⁻¹' ·)
  have hE' : IsSNCDivisor n E' := HironakaBaseChange.IsOpenHoloEmbedding.isSNCDivisor_map_preimage
    (HironakaBaseChange.isOpenHoloEmbedding_val U) hE
  let i' : Fin E'.length := ⟨i.val,by simp only [E',List.length_map]; exact i.isLt⟩
  have he : E'.get i' = (Subtype.val : U → A) ⁻¹' E.get i := by simp [E',i',List.get_eq_getElem]
  have hc : (vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' E.get i)).IsCoherent :=
    DivisorMetric.isCoherent_of_isInvertible (he ▸ isInvertible_vanishingIdeal_snc_member hE' i')
  have h := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) (E.get i)
  rw [BlowupControlledTransform.pullback_id hc] at h
  simpa only [Function.comp_id] using h.symm

private theorem open_pullback_product_present (U : TopologicalSpace.Opens A)
    {E : List (Set A)} (hE : IsSNCDivisor n E) (F : List (Set A × ℕ))
    (hF : ∀ p ∈ F, p.1 ∈ E) :
    GermIdeal.pullback (m := n) (Subtype.val : U → A) (componentPowerProduct (n := n) F) =
      componentPowerProduct (n := n) (pulledWeights (Subtype.val : U → A) F) := by
  induction F with
  | nil => exact pullback_unitIdeal
  | cons p F ih =>
    have ht : ∀ q ∈ F, q.1 ∈ E := fun q hq => hF q (List.mem_cons_of_mem p hq)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hF p (by simp))
    have hc : (vanishingIdeal (n := n) p.1).IsCoherent :=
      DivisorMetric.isCoherent_of_isInvertible (hi ▸ isInvertible_vanishingIdeal_snc_member hE i)
    have htc : (componentPowerProduct (n := n) F).IsCoherent :=
      (isWellFormed_monomialMarkedIdeal hE F ht).isCoherent
    have hpull : GermIdeal.pullback (m := n) (Subtype.val : U → A) (vanishingIdeal (n := n) p.1) =
        vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' p.1) := hi ▸ open_pullback_vanishingIdeal_member U E hE i
    change GermIdeal.pullback (m := n) (Subtype.val : U → A) ((idealPow (vanishingIdeal (n := n) p.1) p.2).mul
      (componentPowerProduct (n := n) F)) =
      (idealPow (vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' p.1)) p.2).mul
        (componentPowerProduct (n := n) (pulledWeights (Subtype.val : U → A) F))
    rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul contMDiff_subtype_val
      (GermIdealPullbackCalculus.isCoherent_idealPow hc p.2) htc,
      HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow contMDiff_subtype_val hc,hpull,ih ht]

theorem open_pullback_componentPowerProduct (U : TopologicalSpace.Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    GermIdeal.pullback (m := n) (Subtype.val : U → A) (componentPowerProduct (n := n) F) =
      componentPowerProduct (n := n) (pulledWeights (Subtype.val : U → A) F) :=
  open_pullback_product_present U hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)

theorem actual_open_trace_whole_ideal (U : TopologicalSpace.Opens A) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    componentPowerProduct (n := n)
        (terminalState n (traceCount (Subtype.val : U → A) n q F) (pulledWeights (Subtype.val : U → A) F)) =
      GermIdeal.pullback (m := n) (Subtype.val : U → A) (componentPowerProduct (n := n) (terminalState n q F)) := by
  rw [open_pullback_componentPowerProduct U _ (terminalState_isSNCDivisor q F hF)]
  exact trace_run_whole_ideal (B := CMfd.of (n := n) U) q (initialTrace (Subtype.val : U → A) F)
    (openWeights_isSNCDivisor U F hF) (openWeights_isSNCDivisor U F hF) rfl

end ActualOpens

section TracedTowers
variable {B : CMfd.{u} n}

private theorem traced_successor_snc (f : B → X) (G : List (Set X × ℕ))
    (hP : IsSNCDivisor n ((pulledWeights f G).map Prod.fst))
    (j : Fin G.length) (hs : selectedIndex n G = some j) :
    IsSNCDivisor n ((pulledWeights f (dividedWeights G j)).map Prod.fst) := by
  classical
  rw [pulledWeights_dividedWeights]
  apply dividedWeights_isSNCDivisor _ hP
  simpa only [pulledWeights_get] using (Finset.mem_filter.mp (selectedIndex_some_spec G hs).1).2.1

private theorem traced_head_blowup (f : B → X) (G : List (Set X × ℕ))
    (hP : IsSNCDivisor n ((pulledWeights f G).map Prod.fst)) (j : Fin G.length) :
    IsBlowupAlong n (f ⁻¹' (G.get j).1) (id : B → B) := by
  simpa only [pulledWeights_get] using
    isBlowupAlong_id_indexed_member (pulledWeights f G) hP (pulledIndex f G j)

open Classical in
def tracedTower (omitEmpty : Bool) (f : B → X) : ∀ (_q : ℕ) (G : List (Set X × ℕ)),
    IsSNCDivisor n ((pulledWeights f G).map Prod.fst) → BlowupTower B B
  | 0,_,_ => .refl
  | q+1,G,hP => match hs : selectedIndex n G with
    | none => .refl
    | some j =>
      let R := tracedTower omitEmpty f q (dividedWeights G j) (traced_successor_snc f G hP j hs)
      if omitEmpty = true ∧ f ⁻¹' (G.get j).1 = ∅ then R else
        (BlowupTower.step BlowupTower.refl (f ⁻¹' (G.get j).1) id (traced_head_blowup f G hP j)).append R

theorem tracedTower_none (b : Bool) (f : B → X) (q : ℕ) (G : List (Set X × ℕ))
    (hP : IsSNCDivisor n ((pulledWeights f G).map Prod.fst)) (hs : selectedIndex n G = none) :
    tracedTower b f (q+1) G hP = .refl := by
  unfold tracedTower
  split
  · rfl
  · rename_i j he
    have hc := hs.symm.trans he
    contradiction

private theorem tracedTower_some (b : Bool) (f : B → X) (q : ℕ) (G : List (Set X × ℕ))
    (hP : IsSNCDivisor n ((pulledWeights f G).map Prod.fst)) (j : Fin G.length)
    (hs : selectedIndex n G = some j) :
    tracedTower b f (q+1) G hP =
      if b = true ∧ f ⁻¹' (G.get j).1 = ∅ then
        tracedTower b f q (dividedWeights G j) (traced_successor_snc f G hP j hs)
      else (BlowupTower.step BlowupTower.refl (f ⁻¹' (G.get j).1) id (traced_head_blowup f G hP j)).append
        (tracedTower b f q (dividedWeights G j) (traced_successor_snc f G hP j hs)) := by
  classical
  conv_lhs => unfold tracedTower
  split
  · rename_i he
    have hc := he.symm.trans hs
    contradiction
  · rename_i k hk
    have heq : k = j := Option.some.inj (hk.symm.trans hs)
    subst k
    rfl

theorem tracedTower_is_independent_procedure (f : B → X) (q : ℕ)
    (S : List (Set B × ℕ)) (G : List (Set X × ℕ)) (h : RetainedTrace f S G)
    (hS : IsSNCDivisor n (S.map Prod.fst)) (hP : IsSNCDivisor n ((pulledWeights f G).map Prod.fst)) :
    tracedTower true f q G hP = procedureTower (traceCount f n q G) S hS := by
  classical
  induction q generalizing S G with
  | zero => rfl
  | succ q ih =>
    cases hg : selectedIndex n G with
    | none =>
      have hp : traceCount f n (q+1) G = 0 := by unfold traceCount; rw [traceCentres_none f q G hg]; rfl
      rw [tracedTower_none true f q G hP hg,hp]
      rfl
    | some j =>
      rw [tracedTower_some true f q G hP j hg]
      by_cases hne : (f ⁻¹' (G.get j).1).Nonempty
      · have hnot : f ⁻¹' (G.get j).1 ≠ ∅ := Set.nonempty_iff_ne_empty.mp hne
        rw [if_neg (fun he => hnot he.2)]
        obtain ⟨i,hei,hsel⟩ := h.selection_of_trace_nonempty j hg hne
        have hi : 0 < (S.get i).2 := (Finset.mem_filter.mp (selectedIndex_some_spec S hsel).1).2.1
        have hp : traceCount f n (q+1) G = traceCount f n q (dividedWeights G j)+1 := by
          unfold traceCount
          rw [traceCentres_some_nonempty f q G j hg hne,List.length_cons]
        rw [hp,procedureTower_succ_some _ S hS i hsel,
          ih (dividedWeights S i) (dividedWeights G j) (h.keep i j hei)
            (dividedWeights_isSNCDivisor S hS i hi)]
        have hC : (S.get i).1 = f ⁻¹' (G.get j).1 := by rw [h.carrier i,hei]
        congr 1
        congr 1
        exact hC.symm
      · have hempty : f ⁻¹' (G.get j).1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        rw [if_pos ⟨rfl,hempty⟩]
        have hp : traceCount f n (q+1) G = traceCount f n q (dividedWeights G j) := by
          unfold traceCount
          rw [traceCentres_some_empty f q G j hg hempty]
        rw [hp]
        exact ih S (dividedWeights G j) (h.skip j hempty) hS _


theorem tracedTower_genuine_empty_compression (f : B → X) (q : ℕ) (G : List (Set X × ℕ))
    (hP : IsSNCDivisor n ((pulledWeights f G).map Prod.fst)) :
    HironakaNormalCrossingsOpenRestrictionSeparation.IsStageCompression
      (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) B ∞)
      (tracedTower false f q G hP) (tracedTower true f q G hP)
      (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) B ∞) := by
  classical
  induction q generalizing G with
  | zero => exact .refl
  | succ q ih =>
    cases hs : selectedIndex n G with
    | none => rw [tracedTower_none false f q G hP hs,tracedTower_none true f q G hP hs]; exact .refl
    | some j =>
      rw [tracedTower_some false f q G hP j hs,tracedTower_some true f q G hP j hs]
      simp only [Bool.false_eq_true,false_and,if_false,true_and]
      have htail := ih (dividedWeights G j) (traced_successor_snc f G hP j hs)
      by_cases he : f ⁻¹' (G.get j).1 = ∅
      · rw [if_pos he]
        have hhead : HironakaNormalCrossingsOpenRestrictionSeparation.IsStageCompression
            (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) B ∞)
            (.step .refl (f ⁻¹' (G.get j).1) id (traced_head_blowup f G hP j)) .refl
            (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) B ∞) := by
          have hπempty : IsBlowupAlong n (∅ : Set B) (id : B → B) := he ▸ traced_head_blowup f G hP j
          have heq : (BlowupTower.step (.refl : BlowupTower B B) (f ⁻¹' (G.get j).1) id (traced_head_blowup f G hP j)) =
              .step .refl ∅ id hπempty := by congr 1
          rw [heq]
          exact .silent .refl hπempty (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) B ∞) (fun _ => rfl)
        simpa only [BlowupTower.refl_append] using hhead.append htail
      · rw [if_neg he]
        have hhead : HironakaNormalCrossingsOpenRestrictionSeparation.IsStageCompression
            (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) B ∞)
            (.step .refl (f ⁻¹' (G.get j).1) id (traced_head_blowup f G hP j))
            (.step .refl (f ⁻¹' (G.get j).1) id (traced_head_blowup f G hP j))
            (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) B ∞) :=
          .matched .refl _ _ (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) B ∞) (fun _ => rfl) rfl
        exact hhead.append htail

end TracedTowers

section LiteralRestriction
variable {A B : CMfd.{u} n}

theorem literal_restrict_to_uncompressed_trace (q : ℕ) (U : TopologicalSpace.Opens A)
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (hP : IsSNCDivisor n ((pulledWeights (fun b : B => (Φ b : A)) F).map Prod.fst)) :
    ∃ χ : CMfd.of (n := n) (openPreimage (procedureTower q F hF) U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ B,
      IsTowerIso Φ.symm (restrict U (procedureTower q F hF))
        (tracedTower false (fun b : B => (Φ b : A)) q F hP) χ := by
  classical
  induction q generalizing F U with
  | zero => exact ⟨Φ.symm,.refl⟩
  | succ q ih =>
    cases hs : selectedIndex n F with
    | none =>
      rw [procedureTower_eq_refl_of_none (q+1) F hF hs,tracedTower_none false _ q F hP hs]
      exact ⟨Φ.symm,.refl⟩
    | some j =>
      have hj : 0 < (F.get j).2 := (Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2.1
      let T₀ : BlowupTower A A := .step .refl (F.get j).1 id (isBlowupAlong_id_indexed_member F hF j)
      let V := openPreimage T₀ U
      have hVU : V = U := by ext x; rfl
      let ε := BlowupTowerIsoTail.opensCongr (n := n) hVU
      let η := ε.trans Φ.symm
      have hf : (fun b : B => (η.symm b : A)) = (fun b : B => (Φ b : A)) := by
        funext b
        rfl
      let hD := dividedWeights_isSNCDivisor F hF j hj
      have hP' : IsSNCDivisor n ((pulledWeights (fun b : B => (η.symm b : A)) (dividedWeights F j)).map Prod.fst) := by
        rw [hf]
        exact traced_successor_snc _ F hP j hs
      obtain ⟨χ,hχ⟩ := ih V η.symm (dividedWeights F j) hD hP'
      have hhead : IsTowerIso Φ.symm (restrict U T₀)
          (.step (.refl : BlowupTower B B) ((fun b : B => (Φ b : A)) ⁻¹' (F.get j).1) id
            (traced_head_blowup _ F hP j)) η := by
        apply IsTowerIso.step IsTowerIso.refl _ _ η
        · intro z
          apply Φ.injective
          apply Subtype.ext
          rfl
        · ext z
          change (Φ (Φ.symm z) : A) ∈ (F.get j).1 ↔ (z : A) ∈ (F.get j).1
          rw [Φ.apply_symm_apply]
      have hχ' : IsTowerIso η
          (restrict V (procedureTower q (dividedWeights F j) hD))
          (tracedTower false (fun b : B => (Φ b : A)) q (dividedWeights F j)
            (traced_successor_snc _ F hP j hs)) χ := by
        simpa only [show η.symm.symm = η from Diffeomorph.ext (fun _ => rfl),hf] using hχ
      have hcat := hhead.append hχ'
      have hfull := (BlowupTowerIsoTail.isTowerIso_restrict_append U T₀
        (procedureTower q (dividedWeights F j) hD)).trans hcat
      rw [procedureTower_succ_some q F hF j hs,tracedTower_some false _ q F hP j hs]
      simp only [Bool.false_eq_true,false_and,if_false]
      exact ⟨_,by simpa only [Diffeomorph.refl_trans] using hfull⟩

end LiteralRestriction

section CompletedGeometry
variable {B : CMfd.{u} n}

theorem actual_completed_trace_tower (f : B → X) (G : List (Set X × ℕ))
    (hP : IsSNCDivisor n ((pulledWeights f G).map Prod.fst)) :
    tracedTower true f (coefficientSum G) G hP =
      procedureTower (coefficientSum (pulledWeights f G)) (pulledWeights f G) hP := by
  classical
  rw [tracedTower_is_independent_procedure f (coefficientSum G) (pulledWeights f G) G (initialTrace f G) hP hP]
  let p := traceCount f n (coefficientSum G) G
  obtain ⟨⟨hr⟩,_⟩ := actual_trace_run (n := n) f (coefficientSum G) G
  have hg : selectedIndex n (terminalState n (coefficientSum G) G) = none :=
    (selectedIndex_eq_none_iff _).mpr (terminalState_inactive _ G le_rfl)
  have hs := hr.selection_none (n := n) hg
  have hp : p ≤ coefficientSum (pulledWeights f G) := traceCount_le_own_sum f _ G
  have hqe : p+(coefficientSum (pulledWeights f G)-p) = coefficientSum (pulledWeights f G) :=
    Nat.add_sub_of_le hp
  rw [← hqe,procedureTower_add,procedureTower_eq_refl_of_none _ _ _ hs,BlowupTower.append_refl]

variable {A : CMfd.{u} n}

theorem actual_completed_open_compression (U : TopologicalSpace.Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃ χ : CMfd.of (n := n) (openPreimage (procedureTower (coefficientSum F) F hF) U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U,
      HironakaNormalCrossingsOpenRestrictionSeparation.IsStageCompression
        (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (procedureTower (coefficientSum F) F hF))
        (procedureTower (coefficientSum (pulledWeights (Subtype.val : U → A) F))
          (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)) χ := by
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞
  obtain ⟨χ,hχ⟩ := literal_restrict_to_uncompressed_trace (coefficientSum F) U Φ F hF (openWeights_isSNCDivisor U F hF)
  have hc := tracedTower_genuine_empty_compression (B := CMfd.of (n := n) U)
    (Subtype.val : U → A) (coefficientSum F) F (openWeights_isSNCDivisor U F hF)
  have hfull := hc.source_iso hχ
  rw [actual_completed_trace_tower] at hfull
  refine ⟨χ,?_⟩
  have hsym : Φ.symm = Φ := Diffeomorph.ext (fun _ => rfl)
  simpa only [hsym,Φ,Diffeomorph.refl_trans,Diffeomorph.trans_refl] using hfull

end CompletedGeometry

section WholeStages
variable {A : CMfd.{u} n}

def traceStageMarked (U : TopologicalSpace.Opens A) (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) : MarkedIdeal n (CMfd.of (n := n) U) :=
  let M := geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)
  { N := (Subtype.val : U → A) ⁻¹' M.N
    E := (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n q F).map
      (fun k => (Subtype.val : U → A) ⁻¹' ((M.E[k]?).getD ∅))
    ideal := GermIdeal.pullback (m := n) (Subtype.val : U → A) M.ideal
    d := M.d }

private theorem carrier_getD (G : List (Set X × ℕ)) (k : ℕ) :
    ((G.map Prod.fst)[k]?).getD ∅ = ((G[k]?).getD (∅,0)).1 := by
  rw [List.getElem?_map]
  cases G[k]? <;> rfl

theorem actual_open_trace_whole_marked (U : TopologicalSpace.Opens A) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong (monomialMarkedIdeal (n := n)
        ((pulledWeights (Subtype.val : U → A) F).map Prod.fst) (pulledWeights (Subtype.val : U → A) F))
      (procedureTower (traceCount (Subtype.val : U → A) n q F)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)) =
      traceStageMarked U q F hF := by
  rw [procedureTower_marked_dictionary]
  unfold traceStageMarked
  rw [procedureTower_marked_dictionary]
  obtain ⟨hr,hw,hE,_⟩ := actual_trace_full_history (n := n) (Subtype.val : U → A) q F
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact preimage_univ.symm
  · change _ = (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n q F).map
        (fun k => (Subtype.val : U → A) ⁻¹' (((terminalState n q F).map Prod.fst)[k]?.getD ∅))
    simp_rw [carrier_getD]
    exact hE
  · exact actual_open_trace_whole_ideal U q F hF
  · rfl

theorem actual_open_trace_domain (U : TopologicalSpace.Opens A) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ResolutionInvariantSpec.IsInvDomain n (traceStageMarked U q F hF) := by
  rw [← actual_open_trace_whole_marked,procedureTower_marked_dictionary]
  exact isInvDomain_monomialMarkedIdeal
    (terminalState_isSNCDivisor (A := CMfd.of (n := n) U) (traceCount (Subtype.val : U → A) n q F)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF))
    _ (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)


/-- At completion the entire source marked record is the literal provenance-filtered restriction. -/
theorem actual_completed_open_whole_marked (U : TopologicalSpace.Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong
      (monomialMarkedIdeal (n := n) ((pulledWeights (Subtype.val : U → A) F).map Prod.fst)
        (pulledWeights (Subtype.val : U → A) F))
      (procedureTower (coefficientSum (pulledWeights (Subtype.val : U → A) F))
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)) =
      traceStageMarked U (coefficientSum F) F hF := by
  rw [procedureTower_marked_dictionary,actual_completed_state]
  have h := actual_open_trace_whole_marked U (coefficientSum F) F hF
  rw [procedureTower_marked_dictionary] at h
  exact h

/-- True filtered endpoint has the WHOLE unit ideal with its literal retained boundary. -/
theorem actual_completed_open_unit (U : TopologicalSpace.Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (traceStageMarked U (coefficientSum F) F hF).ideal = unitIdeal n (CMfd.of (n := n) U) := by
  rw [← actual_completed_open_whole_marked]
  exact procedureTower_ideal_eq_unit _ (openWeights_isSNCDivisor U F hF)

end WholeStages

section Composition
attribute [local instance] Classical.propDecidable
variable {Z : Type u}

theorem nonempty_preimage_words_composition (f : Y → X) (g : Z → Y) (L : List (Set X)) :
    L.filterMap (fun C => if ((f ∘ g) ⁻¹' C).Nonempty then some ((f ∘ g) ⁻¹' C) else none) =
      (L.filterMap (fun C => if (f ⁻¹' C).Nonempty then some (f ⁻¹' C) else none)).filterMap
        (fun D => if (g ⁻¹' D).Nonempty then some (g ⁻¹' D) else none) := by
  classical
  induction L with
  | nil => rfl
  | cons C L ih =>
    simp only [List.filterMap_cons]
    by_cases hf : (f ⁻¹' C).Nonempty
    · rw [if_pos hf]
      simp only [List.filterMap_cons,← Set.preimage_comp]
      by_cases hg : ((f ∘ g) ⁻¹' C).Nonempty
      · simp only [if_pos hg]
        exact congrArg (List.cons ((f ∘ g) ⁻¹' C)) ih
      · simp only [if_neg hg]
        exact ih
    · have hfg : ¬((f ∘ g) ⁻¹' C).Nonempty := by
        rintro ⟨z,hz⟩
        exact hf ⟨g z,hz⟩
      rw [if_neg hf,if_neg hfg]
      exact ih

theorem traceCentres_composition (f : Y → X) (g : Z → Y) (q : ℕ) (F : List (Set X × ℕ)) :
    traceCentres (f ∘ g) n q F =
      (traceCentres f n q F).filterMap
        (fun D => if (g ⁻¹' D).Nonempty then some (g ⁻¹' D) else none) :=
  nonempty_preimage_words_composition f g (centreTrace n q F)

theorem completed_independent_words_composition (f : Y → X) (g : Z → Y) (F : List (Set X × ℕ)) :
    centreTrace n (coefficientSum (pulledWeights (f ∘ g) F)) (pulledWeights (f ∘ g) F) =
      (centreTrace n (coefficientSum (pulledWeights f F)) (pulledWeights f F)).filterMap
        (fun D => if (g ⁻¹' D).Nonempty then some (g ⁻¹' D) else none) := by
  rw [(actual_completed_trace (n := n) (f ∘ g) F).1,(actual_completed_trace (n := n) f F).1]
  exact traceCentres_composition f g _ F

theorem completed_direct_and_iterated_words (f : Y → X) (g : Z → Y) (F : List (Set X × ℕ)) :
    centreTrace n (coefficientSum (pulledWeights (f ∘ g) F)) (pulledWeights (f ∘ g) F) =
      centreTrace n (coefficientSum (pulledWeights g (pulledWeights f F))) (pulledWeights g (pulledWeights f F)) := by
  have he : pulledWeights g (pulledWeights f F) = pulledWeights (f ∘ g) F := by
    simp only [pulledWeights,List.map_map]
    rfl
  rw [he]


/-- Genuine creation-time events retain the global appended index, never a current nonempty mask. -/
def historyEvents (f : Y → X) (n q : ℕ) (F : List (Set X × ℕ)) : List (Set Y × ℕ) :=
  (centreTrace n q F).zipIdx F.length |>.filterMap
    (fun e => if (f ⁻¹' e.1).Nonempty then some (f ⁻¹' e.1,e.2) else none)

/-- The actual retained indices are precisely the labels of actual kept creation events. -/
theorem historyEvents_indices (f : Y → X) (q : ℕ) (F : List (Set X × ℕ)) :
    (historyEvents f n q F).map Prod.snd = newHistoryTrace f n q F := by
  classical
  induction q generalizing F with
  | zero => rfl
  | succ q ih =>
    cases hj : selectedIndex n F with
    | none => simp [historyEvents,centreTrace,hj,newHistoryTrace]
    | some j =>
      have hc : centreTrace n (q+1) F = (F.get j).1 :: centreTrace n q (dividedWeights F j) := by
        conv_lhs => unfold centreTrace
        rw [hj]
      unfold historyEvents
      rw [hc,List.zipIdx_cons,List.filterMap_cons]
      by_cases hne : (f ⁻¹' (F.get j).1).Nonempty
      · rw [if_pos hne,List.map_cons]
        have ht := ih (dividedWeights F j)
        unfold historyEvents at ht
        rw [dividedWeights_length] at ht
        rw [ht]
        simp only [newHistoryTrace,hj,hne,if_true,List.singleton_append]
      · rw [if_neg hne]
        have ht := ih (dividedWeights F j)
        unfold historyEvents at ht
        rw [dividedWeights_length] at ht
        rw [ht]
        simp only [newHistoryTrace,hj,hne,if_false,List.nil_append]

/-- Every actual creation event is filtered compatibly by true composed inverse images. -/
theorem nonempty_preimage_events_composition (f : Y → X) (g : Z → Y)
    (L : List (Set X × ℕ)) :
    L.filterMap (fun e => if ((f ∘ g) ⁻¹' e.1).Nonempty then some ((f ∘ g) ⁻¹' e.1,e.2) else none) =
      (L.filterMap (fun e => if (f ⁻¹' e.1).Nonempty then some (f ⁻¹' e.1,e.2) else none)).filterMap
        (fun e => if (g ⁻¹' e.1).Nonempty then some (g ⁻¹' e.1,e.2) else none) := by
  classical
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.filterMap_cons]
    by_cases hf : (f ⁻¹' e.1).Nonempty
    · rw [if_pos hf]
      simp only [List.filterMap_cons,← Set.preimage_comp]
      by_cases hg : ((f ∘ g) ⁻¹' e.1).Nonempty
      · simp only [if_pos hg]
        exact congrArg (List.cons (((f ∘ g) ⁻¹' e.1),e.2)) ih
      · simp only [if_neg hg]
        exact ih
    · have hfg : ¬((f ∘ g) ⁻¹' e.1).Nonempty := by
        rintro ⟨z,hz⟩
        exact hf ⟨g z,hz⟩
      rw [if_neg hf,if_neg hfg]
      exact ih

/-- Direct and iterated true masks keep exactly the SAME globally labelled creation events. -/
theorem historyEvents_composition (f : Y → X) (g : Z → Y) (q : ℕ) (F : List (Set X × ℕ)) :
    historyEvents (f ∘ g) n q F =
      (historyEvents f n q F).filterMap
        (fun e => if (g ⁻¹' e.1).Nonempty then some (g ⁻¹' e.1,e.2) else none) :=
  nonempty_preimage_events_composition f g ((centreTrace n q F).zipIdx F.length)

/-- Exact global history indices compose through the actual recorded creation events. -/
theorem newHistoryTrace_composition (f : Y → X) (g : Z → Y) (q : ℕ) (F : List (Set X × ℕ)) :
    newHistoryTrace (f ∘ g) n q F =
      ((historyEvents f n q F).filterMap
        (fun e => if (g ⁻¹' e.1).Nonempty then some (g ⁻¹' e.1,e.2) else none)).map Prod.snd := by
  rw [← historyEvents_indices,historyEvents_composition]


namespace RetainedTrace
variable {f : Y → X} {g : Z → Y} {S : List (Set Z × ℕ)} {P : List (Set Y × ℕ)} {G : List (Set X × ℕ)}

def comp (hf : RetainedTrace f P G) (hg : RetainedTrace g S P) : RetainedTrace (f ∘ g) S G where
  embed := hg.embed.trans hf.embed
  carrier := by
    intro i
    rw [hg.carrier i,hf.carrier (hg.embed i)]
    rfl
  power := by
    intro i hne
    rw [hg.power i hne]
    apply hf.power
    rw [hg.carrier i] at hne
    obtain ⟨z,hz⟩ := hne
    exact ⟨g z,hz⟩
  covers := by
    intro j hne
    obtain ⟨z,hz⟩ := hne
    obtain ⟨i,hei⟩ := hf.covers j ⟨g z,hz⟩
    have htrace : (g ⁻¹' (P.get i).1).Nonempty := by
      refine ⟨z,?_⟩
      rw [hf.carrier i,hei]
      exact hz
    obtain ⟨k,hek⟩ := hg.covers i htrace
    exact ⟨k,by change hf.embed (hg.embed k) = j; rw [hek,hei]⟩


/-- Literal index enumeration composes, even for retained entries which have become empty. -/
theorem indexWord_comp (hf : RetainedTrace f P G) (hg : RetainedTrace g S P) :
    (hf.comp hg).indexWord = hg.indexWord.map
      (fun k => (hf.indexWord[k]?).getD 0) := by
  unfold indexWord
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  change (hf.embed (hg.embed i)).val =
    ((List.ofFn fun j : Fin P.length => (hf.embed j).val)[(hg.embed i).val]?).getD 0
  rw [List.getElem?_ofFn,dif_pos (hg.embed i).isLt]
  rfl

end RetainedTrace
end Composition


section NestedActualOpens
variable {A : CMfd.{u} n}

def nestedInclusion (U V : TopologicalSpace.Opens A) (hVU : V ≤ U) : V → U :=
  fun x => ⟨x.val,hVU x.property⟩

theorem nestedInclusion_actual_open_holomorphic (U V : TopologicalSpace.Opens A) (hVU : V ≤ U) :
    HironakaBaseChange.IsOpenHoloEmbedding n (nestedInclusion U V hVU) :=
  (HironakaBaseChange.isOpenHoloEmbedding_val V).codRestrict U (fun x => hVU x.property)

theorem actual_nested_weights (U V : TopologicalSpace.Opens A) (hVU : V ≤ U)
    (F : List (Set A × ℕ)) :
    pulledWeights (nestedInclusion U V hVU) (pulledWeights (Subtype.val : U → A) F) =
      pulledWeights (Subtype.val : V → A) F := by
  simp only [pulledWeights,List.map_map]
  rfl

/-- Both independently generated inputs have genuine SNC from actual open charts. -/
theorem actual_nested_weights_snc (U V : TopologicalSpace.Opens A) (hVU : V ≤ U)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSNCDivisor n
      ((pulledWeights (nestedInclusion U V hVU) (pulledWeights (Subtype.val : U → A) F)).map Prod.fst) := by
  rw [actual_nested_weights]
  exact openWeights_isSNCDivisor V F hF

/-- Direct and nested independent procedures coincide literally on the SAME actual source manifold. -/
theorem actual_nested_procedure_tower (U V : TopologicalSpace.Opens A) (hVU : V ≤ U)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    procedureTower (A := CMfd.of (n := n) V)
      (coefficientSum (pulledWeights (nestedInclusion U V hVU) (pulledWeights (Subtype.val : U → A) F)))
      (pulledWeights (nestedInclusion U V hVU) (pulledWeights (Subtype.val : U → A) F))
      (actual_nested_weights_snc U V hVU F hF) =
    procedureTower (A := CMfd.of (n := n) V) (coefficientSum (pulledWeights (Subtype.val : V → A) F))
      (pulledWeights (Subtype.val : V → A) F) (openWeights_isSNCDivisor V F hF) := by
  simp only [actual_nested_weights]

end NestedActualOpens

section Intrinsic
variable {B : CMfd.{u} n}

theorem intrinsic_empty_zero (I : GermIdeal n B) (x : B) :
    DivisorExponent.divExp n I (∅ : Set B) x = 0 := by
  classical
  unfold DivisorExponent.divExp
  rw [dif_neg]
  rintro ⟨e,he⟩
  apply he
  exact Eventually.of_forall fun _ hx => hx.elim

private theorem positive_dimension_through_index (F : List (Set B × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (x : B) (i : Fin F.length) (hx : x ∈ (F.get i).1) : 0 < n := by
  obtain ⟨S,_,hcard,_⟩ := hF.2 x
  let i' : Fin (F.map Prod.fst).length := ⟨i.val,by simp only [List.length_map]; exact i.isLt⟩
  have hx' : x ∈ (F.map Prod.fst).get i' := by simpa [i',List.get_eq_getElem] using hx
  have hc := hcard i' hx'
  have hb := Finset.card_le_univ (S i')
  simp only [Fintype.card_fin] at hb
  omega

variable {A : CMfd.{u} n}

theorem actual_open_trace_intrinsic_exponents (U : TopologicalSpace.Opens A) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃ hr : RetainedTrace (Subtype.val : U → A)
        (terminalState n (traceCount (Subtype.val : U → A) n q F) (pulledWeights (Subtype.val : U → A) F))
        (terminalState n q F),
      hr.indexWord = List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n q F ∧
      ∀ (x : U) (i : Fin (terminalState n (traceCount (Subtype.val : U → A) n q F)
          (pulledWeights (Subtype.val : U → A) F)).length),
        x ∈ ((terminalState n (traceCount (Subtype.val : U → A) n q F) (pulledWeights (Subtype.val : U → A) F)).get i).1 →
        DivisorExponent.divExp n (traceStageMarked U q F hF).ideal
          ((terminalState n (traceCount (Subtype.val : U → A) n q F) (pulledWeights (Subtype.val : U → A) F)).get i).1 x =
          ((terminalState n q F).get (hr.embed i)).2 := by
  obtain ⟨hr,hw,_,_⟩ := actual_trace_full_history (n := n) (Subtype.val : U → A) q F
  refine ⟨hr,hw,?_⟩
  intro x i hx
  let S := terminalState n (traceCount (Subtype.val : U → A) n q F) (pulledWeights (Subtype.val : U → A) F)
  have hS := terminalState_isSNCDivisor (A := CMfd.of (n := n) U)
    (traceCount (Subtype.val : U → A) n q F) (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)
  have hI := congrArg (fun M : MarkedIdeal n (CMfd.of (n := n) U) => M.ideal) (actual_open_trace_whole_marked U q F hF)
  rw [procedureTower_marked_dictionary] at hI
  change componentPowerProduct (n := n) S = (traceStageMarked U q F hF).ideal at hI
  rw [← hI]
  exact (indexed_product_divExp (positive_dimension_through_index (B := CMfd.of (n := n) U) S hS x i hx) S hS x i hx).trans
    (hr.power i ⟨x,hx⟩)

end Intrinsic
end
end Hironaka.HironakaNormalCrossingsOrderedOpenTrace
