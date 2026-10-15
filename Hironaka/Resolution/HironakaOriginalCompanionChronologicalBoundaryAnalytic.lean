/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.ControlledOriginalContextExact
import Hironaka.Resolution.HironakaOriginalCompanionHistoryYearAnalytic
import Hironaka.Resolution.HironakaBoundaryCountAnalyticSuperlevels
/-! True chronological companion-boundary thresholds on the SAME original
canonical history. Complete source-first blueprint precedes this module.
Arbitrary recursive lower and special/contact presentations remain further work. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCompanionChronologicalBoundaryAnalytic
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail StepOneRegime
  CanonicalCentres GeneralValue GeneralCanonicalTail StepOneValue BoundaryCount NormalCrossings
  HironakaOriginalCompanionHistoryYearAnalytic
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y : CMfd.{u} n}

/-- The actual minimum of the literal recursively constructed original value type. -/
def minimumValTy : (k : ℕ) → ValTy k
  | 0 => (0 : ℕ)
  | _k+1 => toLex (0,toLex (Sum.inl ⊥))

theorem minimumValTy_le (k : ℕ) (α : ValTy k) : minimumValTy k ≤ α := by
  cases k with
  | zero =>
    change (0 : ℕ) ≤ α
    exact Nat.zero_le α
  | succ k =>
    change ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy k))) at α
    change toLex (0,toLex (Sum.inl (⊥ : WithBot MonomialInvariant.Val))) ≤ α
    apply Prod.Lex.le_iff.mpr
    change 0 < (ofLex α).1 ∨ 0 = (ofLex α).1 ∧ toLex (Sum.inl ⊥) ≤ (ofLex α).2
    by_cases h0 : (ofLex α).1=0
    · refine Or.inr ⟨h0.symm,?_⟩
      rw [Sum.Lex.inl_bot]
      exact bot_le
    · exact Or.inl (Nat.pos_of_ne_zero h0)

private theorem minimumValTy_coe_le (k : ℕ) (α : WithTop (ValTy k)) :
    (minimumValTy k : WithTop (ValTy k)) ≤ α := by
  cases α with
  | top => exact le_top
  | coe α => exact WithTop.coe_le_coe.mpr (minimumValTy_le k α)

/-- A minimum lower threshold reads precisely the original Step One boundary level. -/
theorem stepOneMinimumThreshold_iff_level (hn : 0 < n) (J : MarkedIdeal n X)
    (T : BlowupTower X Y) (y : Y) (s : ℕ) :
    toLex (s,(minimumValTy k : WithTop (ValTy k))) ≤
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y ↔ s ≤ level J T y := by
  change toLex (s,(minimumValTy k : WithTop (ValTy k))) ≤
    Seq.StepOneValueMasked.stepOneInvL (invFamily hn k) J (StepOneValueMasked.lowerMarkedM J) T y ↔ _
  rw [Prod.Lex.le_iff,Seq.StepOneValueMasked.stepOneInvL_fst]
  constructor
  · rintro (h | ⟨h,_⟩)
    · exact h.le
    · exact h.le
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,minimumValTy_coe_le k _⟩

/-- The genuine full boundary's chronological prefix for a split with r tail stages. -/
def chronologicalMembers (m : MarkedIdeal n X) (T : BlowupTower X Y) (r : ℕ) : List (Set Y) :=
  (geoTransformAlong m T).E.take (m.E.length+(T.length-r))

private theorem boundaryCount_take_mono {M : Type*} [TopologicalSpace M]
    (E : List (Set M)) (y : M) {a b : ℕ} (hab : a ≤ b) :
    boundaryCount (E.take a) y ≤ boundaryCount (E.take b) y := by
  classical
  have hlen : (E.take a).length ≤ (E.take b).length := by simp only [List.length_take]; omega
  unfold boundaryCount
  apply Finset.card_le_card_of_injOn (Fin.castLE hlen)
  · intro i hi
    simp only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    simpa only [List.get_eq_getElem,List.getElem_take,Fin.castLE] using hi
  · intro i _ j _ hij
    exact Fin.ext (congrArg (Fin.val : Fin (E.take b).length → ℕ) hij)

/-- Real companion formation, its coefficient ideal, and its actual restricted
history retain exactly the chronological original-boundary prefix. -/
theorem actualCompanionLevel_eq_chronologicalBoundaryCount
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y)
    (hT : IsGeoTestTower m T) (q r : ℕ)
    (p : openPreimage (tail T r) (ordMask (geoTransformAlong m (head T r)) q)) :
    level (compAt m q (head T r))
      (restrict (ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p =
      boundaryCount (chronologicalMembers m T r) (p : Y) := by
  let J := geoTransformAlong m (head T r)
  let W := ordMask J q
  let K := compAt m q (head T r)
  obtain ⟨hhead,htail⟩ := (isGeoTestTower_iff_head_tail m T r).mp hT
  have hJ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T r) hhead
  have hKE : K.E = (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → (split T r).1) J).E := by
    apply CompanionReductionAlong.companionAlong_E
  have hE : (barMarked K).E = (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → (split T r).1) J).E :=
    (barMarked_E K).trans hKE
  have hfinal := E_geoTransformAlong_congr hE (restrict W (tail T r))
  have hrestrict := MarkedIdealRestrictOpen.geoTransformAlong_restrict W
    hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent (tail T r) htail
  have hwhole : (geoTransformAlong J (tail T r)).E = (geoTransformAlong m T).E := by
    rw [← geoTransformAlong_head_tail]
  have hlen : K.E.length = m.E.length+(T.length-r) := by
    rw [hKE]
    change (J.E.map ((Subtype.val : W → (split T r).1) ⁻¹' ·)).length = _
    rw [List.length_map,MarkedIdeal.length_E_geoTransformAlong,length_head]
  unfold level origMembers
  change boundaryCount ((geoTransformAlong (barMarked K) (restrict W (tail T r))).E.take K.E.length) p = _
  rw [hfinal, hrestrict]
  change boundaryCount (((geoTransformAlong J (tail T r)).E.map (Subtype.val ⁻¹' ·)).take K.E.length) p = _
  rw [hwhole,hlen,← List.map_take]
  exact CodimOnePartCanonical.boundaryCount_map_preimage _ _ p

/-- Indexed count selected by the original order-regime run, including empty steps. -/
def companionChronologicalCount (m : MarkedIdeal n X) (T : BlowupTower X Y) (q : ℕ) (y : Y) : ℕ :=
  boundaryCount (chronologicalMembers m T (regimeRun (OrdRegime m q) T y)) y

/-- The actual point-dependent chronological count has an entire finite dictionary. -/
theorem companionChronologicalCount_superlevel_eq_biUnion
    (m : MarkedIdeal n X) (T : BlowupTower X Y) (q s : ℕ) :
    {y | y ∈ (geoTransformAlong m T).cosupp ∧ q ≤ nmOrd (geoTransformAlong m T) y ∧
      s ≤ companionChronologicalCount m T q y} =
    ⋃ r ∈ Finset.range (T.length+1), companionHistoryYearSuperlevel m T q r ∩
      {y | s ≤ boundaryCount (chronologicalMembers m T r) y} := by
  classical
  ext y
  constructor
  · rintro ⟨hy,hq,hs⟩
    refine mem_iUnion₂.mpr ⟨regimeRun (OrdRegime m q) T y,?_,⟨hy,hq,le_rfl⟩,hs⟩
    exact Finset.mem_range.mpr (by have := regimeRun_le_length (OrdRegime m q) T y; omega)
  · rintro hy
    obtain ⟨r,_,⟨hy,hq,hr⟩,hs⟩ := mem_iUnion₂.mp hy
    refine ⟨hy,hq,hs.trans ?_⟩
    exact boundaryCount_take_mono _ _ (by omega)

private theorem analytic_finset_union {ι : Type*} (t : Finset ι) (A : ι → Set Y)
    (hA : ∀ i ∈ t,IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t,A i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hA i (Finset.mem_insert_self i t)) (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

/-- Only original canonical inputs supply all chronological companion-count loci. -/
theorem isComplexAnalyticSubset_companionChronologicalCount_superlevel
    (hn : 0 < n) (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (T : BlowupTower X Y) (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q s : ℕ) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong m T).cosupp ∧ q ≤ nmOrd (geoTransformAlong m T) y ∧
        s ≤ companionChronologicalCount m T q y} := by
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hwf := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT).isWellFormed
  rw [companionChronologicalCount_superlevel_eq_biUnion]
  apply analytic_finset_union
  intro r _
  apply (isComplexAnalyticSubset_originalCompanionHistoryYearSuperlevel hn m h T hc q r).inter
  have hE : IsSNCDivisor n (chronologicalMembers m T r) :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hwf.isSNCDivisor (List.take_sublist _ _)
  apply HironakaBoundaryCountAnalyticSuperlevels.isComplexAnalyticSubset_boundaryCount_superlevel
  intro H hH
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH
  have hinter := isClosedSubmanifold_memberInter hn hE {i}
  have heq : memberInter (chronologicalMembers m T r) {i}=H := by
    ext y
    simp only [memberInter,mem_ofPred_eq,Finset.mem_singleton,forall_eq]
    rw [hi]
  rw [heq] at hinter
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hinter

/-- The literal positive companion-count threshold in the original value type. -/
def positiveCanonicalCompanionCountThreshold (k q s : ℕ) : ValTy (k+1) :=
  toLex (q,toLex (Sum.inr
    ((toLex (s,(minimumValTy k : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) :
      WithTop (ℕ ×ₗ WithTop (ValTy k)))))

/-- The entire original positive canonical value has a genuine order/count dictionary. -/
theorem canonical_positive_companion_count_superlevel_eq_union
    (hn : 0 < n) (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (T : BlowupTower X Y) (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (q s : ℕ) (hq : 1 ≤ q) :
    {y | y ∈ (geoTransformAlong m T).cosupp ∧
      positiveCanonicalCompanionCountThreshold k q s ≤ (invFamily hn (k+1)).inv m T y} =
    ((geoTransformAlong m T).cosupp ∩ ordGe (geoTransformAlong m T) (q+1)) ∪
    {y | y ∈ (geoTransformAlong m T).cosupp ∧ q ≤ nmOrd (geoTransformAlong m T) y ∧
      s ≤ companionChronologicalCount m T q y} := by
  let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J S z
  have hM := StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+1) (invFamily hn k) hn
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hD := hasGenLowerData_of_isCanonical lower hM hn h T hT
    (show IsCanonical m (genInv lower m) T from hc)
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  ext y
  by_cases hy : y ∈ (geoTransformAlong m T).cosupp
  · have hq1 : y ∈ ordGe (geoTransformAlong m T) (q+1) ↔ q < nmOrd (geoTransformAlong m T) y := by
      rw [mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt hy.1]
      omega
    have hv : positiveCanonicalCompanionCountThreshold k q s ≤ (invFamily hn (k+1)).inv m T y ↔
        q < nmOrd (geoTransformAlong m T) y ∨
          (q ≤ nmOrd (geoTransformAlong m T) y ∧ s ≤ companionChronologicalCount m T q y) := by
      change @LE.le (ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy k))))
        (inferInstance : LE (ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy k)))))
        (toLex (q,toLex (Sum.inr
          ((toLex (s,(minimumValTy k : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) :
            WithTop (ℕ ×ₗ WithTop (ValTy k)))))) (genInv lower m T y) ↔ _
      by_cases heq : nmOrd (geoTransformAlong m T) y=q
      · obtain ⟨hmask,_hK,_hmax,_hcanK,_hcos⟩ := hD y hy q heq hq
        let r := regimeRun (OrdRegime m q) T y
        let p : openPreimage (tail T r) (ordMask (geoTransformAlong m (head T r)) q) := ⟨y,hmask⟩
        have hlevel := actualCompanionLevel_eq_chronologicalBoundaryCount m h T hT q r p
        have hm := stepOneMinimumThreshold_iff_level (k := k) hn (compAt m q (head T r))
          (restrict (ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p s
        rw [genInv_of_nmOrd_ne_zero lower m T heq (by omega),genLowerValue_eq_of_mem lower m hmask]
        change toLex (q,toLex (Sum.inr
          ((toLex (s,(minimumValTy k : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) :
            WithTop (ℕ ×ₗ WithTop (ValTy k))))) ≤
          toLex (q,toLex (Sum.inr ((lower (compAt m q (head T r))
            (restrict (ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p) :
            WithTop (ℕ ×ₗ WithTop (ValTy k))))) ↔ _
        simp only [Prod.Lex.toLex_le_toLex,lt_self_iff_false,true_and,false_or,
          Sum.Lex.inr_le_inr_iff,WithTop.coe_le_coe]
        change toLex (s,(minimumValTy k : WithTop (ValTy k))) ≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (compAt m q (head T r))
            (restrict (ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p ↔ _
        rw [hm,hlevel,heq]
        simp only [lt_self_iff_false,le_refl,true_and,false_or]
        rfl
      · rw [Prod.Lex.le_iff,genInv_fst]
        simp only [ofLex_toLex]
        have hneq : q ≠ nmOrd (geoTransformAlong m T) y := Ne.symm heq
        simp only [hneq,false_and,or_false]
        constructor
        · exact Or.inl
        · rintro (h | ⟨h,_⟩)
          · exact h
          · exact lt_of_le_of_ne h hneq
    simp only [mem_ofPred_eq,mem_union,mem_inter_iff,hy,true_and,hq1,hv]
  · simp only [mem_ofPred_eq,mem_union,mem_inter_iff,hy,false_and,false_or]

/-- Only original data construct the global analytic literal positive companion-count threshold. -/
theorem isComplexAnalyticSubset_canonical_positive_companion_count_superlevel
    (hn : 0 < n) (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m)
    (T : BlowupTower X Y) (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T)
    (q s : ℕ) (hq : 1 ≤ q) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong m T).cosupp ∧
        positiveCanonicalCompanionCountThreshold k q s ≤ (invFamily hn (k+1)).inv m T y} := by
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hcos : IsComplexAnalyticSubset (n := n) (geoTransformAlong m T).cosupp :=
    CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hd.isWellFormed.isCoherent
      hd.isWellFormed.isClosedSubmanifold_N hd.one_le_d
  have hord : IsComplexAnalyticSubset (n := n) (ordGe (geoTransformAlong m T) (q+1)) := by
    have ha := isComplexAnalyticSubset_originalHistoryOrderSuperlevel hn m h T hT 0 (q+1)
    cases T <;> simpa only [originalHistoryOrderSuperlevel,head,tail,split,
      BlowupTower.proj_refl,Set.preimage_id] using ha
  rw [canonical_positive_companion_count_superlevel_eq_union hn m h T hc q s hq]
  exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union (hcos.inter hord)
    (isComplexAnalyticSubset_companionChronologicalCount_superlevel hn m h T hc q s)

end
end Hironaka.HironakaOriginalCompanionChronologicalBoundaryAnalytic
