import Hironaka.Invariant.CanonicalCentres
import Hironaka.Invariant.GeneralRepresentative
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Invariant.StepOneEmptyPrefix

/-! At a geometric order reset, the original companion is formed after
the occupied part of the tower with its full ordered inherited boundary. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8OccupiedOrderReset
noncomputable section

open Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime NonmonomialOrderTransport
  GeneralValue GeneralRepresentative GeneralValueOrderZero StepOneRegime StepOneEmptyPrefix
  CanonicalCentres ResolutionDriver ResolutionInvariantSpec

variable {n : ℕ} {X D Y : CMfd.{0} (n+1)}

private abbrev evaluator : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
    ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
  fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z

/-- The earlier tower contributes to the order run precisely if the
rebased run reaches its source and the earlier run is positive. -/
theorem append_order_run_eq_iff
    (M : MarkedIdeal (n+1) X) (o : ℕ) (P : BlowupTower X D) (S : BlowupTower D Y) (z : Y) :
    let B := geoTransformAlong M P
    let r := regimeRun (OrdRegime B o) S z
    regimeRun (OrdRegime M o) (P.append S) z = r ↔
      r < S.length ∨ regimeRun (OrdRegime M o) P (S.proj z) = 0 := by
  let B := geoTransformAlong M P
  let r := regimeRun (OrdRegime B o) S z
  have hG : ∀ {A B : CMfd.{0} (n+1)} (T : BlowupTower D A) (C : Set A)
      (π : B → A) (hπ : IsBlowupAlong (n+1) C π), True → True := fun _ _ _ _ h => h
  have hQ : ∀ {A : CMfd.{0} (n+1)} (T : BlowupTower D A) (z : A), True →
      (OrdRegime M o (P.append T) z ↔ OrdRegime B o T z) :=
    fun T z _ => ordRegime_append_iff M o P T z
  change regimeRun (OrdRegime M o) (P.append S) z = r ↔
    r < S.length ∨ regimeRun (OrdRegime M o) P (S.proj z) = 0
  rcases (regimeRun_le_length (OrdRegime B o) S z).lt_or_eq with hlt | heq
  · exact iff_of_true (regimeRun_append_of_lt (OrdRegime M o) (OrdRegime B o) P
      (fun _ => True) hG hQ S z trivial hlt) (Or.inl hlt)
  · change r = S.length at heq
    have hr := regimeRun_append_of_eq (OrdRegime M o) (OrdRegime B o) P
      (fun _ => True) hG hQ S z trivial heq
    rw [hr,heq]
    omega

/-- When the positive-order run does not continue into the prefix, the
original value is exactly the value on the actual controlled record at
the cut, with all its ordered boundary slots. -/
theorem canonical_value_rebase_of_order_reset
    (M : MarkedIdeal (n+1) X) (P : BlowupTower X D) (S : BlowupTower D Y)
    (z : Y) (o : ℕ) (hOrder : nmOrd (geoTransformAlong M (P.append S)) z = o)
    (hReset : regimeRun (OrdRegime (geoTransformAlong M P) o) S z < S.length ∨
      regimeRun (OrdRegime M o) P (S.proj z) = 0) :
    (canonicalInvariant (n+1)).inv M (P.append S) z =
      (canonicalInvariant (n+1)).inv (geoTransformAlong M P) S z := by
  let B := geoTransformAlong M P
  let r := regimeRun (OrdRegime B o) S z
  change genInv evaluator M (P.append S) z = genInv evaluator B S z
  by_cases ho : o = 0
  · exact genInv_append_of_nmOrd_eq_zero evaluator M P S (hOrder.trans ho)
  have hOrdB : nmOrd (geoTransformAlong B S) z = o := by
    change nmOrd (geoTransformAlong (geoTransformAlong M P) S) z = o
    rwa [← geoTransformAlong_append]
  have hr : regimeRun (OrdRegime M o) (P.append S) z = r :=
    (append_order_run_eq_iff M o P S z).mpr hReset
  have hLe : r ≤ S.length := regimeRun_le_length (OrdRegime B o) S z
  rw [genInv_of_nmOrd_ne_zero evaluator M _ hOrder ho,genInv_of_nmOrd_ne_zero evaluator B S hOrdB ho,hr]
  simp only [head,tail]
  rw [split_append_of_le P S r hLe]
  dsimp only
  rw [genLowerValue_congr_of_eq evaluator (𝔫 := B) o (geoTransformAlong_append M P _)]

/-- A genuine drop in order at the last occupied higher step forces the
run of the lower order to restart after that step. -/
theorem canonical_value_after_occupied_order_drop
    {A : CMfd.{0} (n+1)} (M : MarkedIdeal (n+1) X) (P : BlowupTower X A)
    (C : Set A) (π : D → A) (hπ : IsBlowupAlong (n+1) C π)
    (S : BlowupTower D Y) (z : Y) (o : ℕ)
    (hOrder : nmOrd (geoTransformAlong M ((P.step C π hπ).append S)) z = o)
    (hDrop : o < nmOrd (geoTransformAlong M P) (π (S.proj z))) :
    (canonicalInvariant (n+1)).inv M ((P.step C π hπ).append S) z =
      (canonicalInvariant (n+1)).inv (geoTransformAlong M (P.step C π hπ)) S z := by
  apply canonical_value_rebase_of_order_reset M _ S z o hOrder
  refine Or.inr (regimeRun_step_of_not (OrdRegime M o) P C π hπ ?_)
  exact fun h => (Nat.ne_of_lt hDrop) h.2.symm

/-- A reset on the attained positive top-order stratum suffices to compare
entire maxima. Points below that stratum cannot compete on either side. -/
theorem canonical_maximum_rebase_of_top_order_reset
    (M : MarkedIdeal (n+1) X) (P : BlowupTower X D) (S : BlowupTower D Y) (q : ℕ)
    (hCap : ∀ y ∈ (geoTransformAlong M (P.append S)).cosupp,
      nmOrd (geoTransformAlong M (P.append S)) y ≤ q)
    (hTop : ∃ y ∈ (geoTransformAlong M (P.append S)).cosupp,
      nmOrd (geoTransformAlong M (P.append S)) y = q)
    (hReset : ∀ y ∈ (geoTransformAlong M (P.append S)).cosupp,
      nmOrd (geoTransformAlong M (P.append S)) y = q →
      regimeRun (OrdRegime (geoTransformAlong M P) q) S y < S.length ∨
        regimeRun (OrdRegime M q) P (S.proj y) = 0) :
    let B := geoTransformAlong M P
    maxLocus ((canonicalInvariant (n+1)).inv M (P.append S))
        (geoTransformAlong M (P.append S)).cosupp =
      maxLocus ((canonicalInvariant (n+1)).inv B S) (geoTransformAlong B S).cosupp := by
  let B := geoTransformAlong M P
  let A := geoTransformAlong M (P.append S)
  let o := nmOrd A
  let v := (canonicalInvariant (n+1)).inv M (P.append S)
  let w := (canonicalInvariant (n+1)).inv B S
  have hRecord : A = geoTransformAlong B S := geoTransformAlong_append M P S
  have hv {x y : Y} (h : o x < o y) : v x < v y := genInv_lt_of_nmOrd_lt evaluator M h
  have hw {x y : Y} (h : o x < o y) : w x < w y := by
    change genInv evaluator B S x < genInv evaluator B S y
    apply genInv_lt_of_nmOrd_lt evaluator B
    rw [← hRecord]
    exact h
  obtain ⟨a,ha,haq⟩ := hTop
  change o a = q at haq
  have he (y : Y) (hy : y ∈ A.cosupp) (hyq : o y = q) : v y = w y :=
    canonical_value_rebase_of_order_reset M P S y q hyq (hReset y hy hyq)
  change maxLocus v A.cosupp = maxLocus w (geoTransformAlong B S).cosupp
  rw [← hRecord]
  ext y
  constructor
  · intro hy
    have hyq : o y = q := le_antisymm (hCap y hy.1) (by
      by_contra hn
      exact (not_lt_of_ge (hy.2 a ha)) (hv (by rw [haq]; exact Nat.lt_of_not_ge hn)))
    refine ⟨hy.1,fun z hz => ?_⟩
    by_cases hzq : o z = q
    · rw [← he z hz hzq,← he y hy.1 hyq]
      exact hy.2 z hz
    · exact le_of_lt (hw (by rw [hyq]; exact lt_of_le_of_ne (hCap z hz) hzq))
  · intro hy
    have hyq : o y = q := le_antisymm (hCap y hy.1) (by
      by_contra hn
      exact (not_lt_of_ge (hy.2 a ha)) (hw (by rw [haq]; exact Nat.lt_of_not_ge hn)))
    refine ⟨hy.1,fun z hz => ?_⟩
    by_cases hzq : o z = q
    · rw [he z hz hzq,he y hy.1 hyq]
      exact hy.2 z hz
    · exact le_of_lt (hv (by rw [hyq]; exact lt_of_le_of_ne (hCap z hz) hzq))

/-- The next physical blowup is canonical on either side of the cut
when the attained top stratum has genuinely dropped from the previous
occupied stage. Geometric conditions determine the maximum comparison. -/
theorem next_canonical_iff_rebased_after_occupied_drop
    {A Z : CMfd.{0} (n+1)} (M : MarkedIdeal (n+1) X) (P : BlowupTower X A)
    (C : Set A) (π : D → A) (hπ : IsBlowupAlong (n+1) C π)
    (S : BlowupTower D Y) (K : Set Y) (σ : Z → Y) (hσ : IsBlowupAlong (n+1) K σ)
    (q : ℕ) :
    let H := P.step C π hπ
    let B := geoTransformAlong M H
    let A := geoTransformAlong M (H.append S)
    let R := canonicalInvariant.{0} (n+1)
    (∀ y ∈ A.cosupp, nmOrd A y ≤ q) →
    (∃ y ∈ A.cosupp, nmOrd A y = q) →
    (∀ y ∈ A.cosupp, nmOrd A y = q → q < nmOrd (geoTransformAlong M P) (π (S.proj y))) →
    IsCanonical M (R.inv M) (H.append S) →
    IsCanonical B (R.inv B) S →
    (IsCanonical M (R.inv M) (.step (H.append S) K σ hσ) ↔
      IsCanonical B (R.inv B) (.step S K σ hσ)) := by
  dsimp only
  intro hCap hTop hDrop hCan hLocal
  let H := P.step C π hπ
  let B := geoTransformAlong M H
  let R := canonicalInvariant.{0} (n+1)
  have hMax := canonical_maximum_rebase_of_top_order_reset M H S q hCap hTop
    (fun y hy hq => Or.inr (regimeRun_step_of_not (OrdRegime M q) P C π hπ
      (fun h => (Nat.ne_of_lt (hDrop y hy hq)) h.2.symm)))
  dsimp only at hMax
  constructor
  · intro h
    exact ⟨hLocal,h.2.imp id (fun hc => hc.trans hMax)⟩
  · intro h
    exact ⟨hCan,h.2.imp id (fun hc => hc.trans hMax.symm)⟩

/-- If the lower positive run covers its suffix after the occupied reset,
then it uses the companion of the actual current record on the literal
order mask. Membership in the mask follows from the active order. -/
theorem canonical_value_on_actual_companion_after_occupied_drop
    {A : CMfd.{0} (n+1)} (M : MarkedIdeal (n+1) X) (P : BlowupTower X A)
    (C : Set A) (π : D → A) (hπ : IsBlowupAlong (n+1) C π)
    (S : BlowupTower D Y) (z : Y) (q : ℕ) (hq : 1 ≤ q) :
    let H := P.step C π hπ
    let B := geoTransformAlong M H
    let O := ordMask B q
    IsInvDomain (n+1) B →
    z ∈ (geoTransformAlong M (H.append S)).cosupp →
    nmOrd (geoTransformAlong M (H.append S)) z = q →
    q < nmOrd (geoTransformAlong M P) (π (S.proj z)) →
    regimeRun (OrdRegime B q) S z = S.length →
    ∃ hz : S.proj z ∈ O,
      (canonicalInvariant (n+1)).inv M (H.append S) z =
      toLex (q,toLex (Sum.inr
        (↑(evaluator (compAt M q H) (restrict O S) (⟨z,hz⟩ : openPreimage S O)) :
          WithTop (ℕ ×ₗ WithTop (ValTy n))))) := by
  dsimp only
  intro hB hz hOrd hDrop hRun
  let H := P.step C π hπ
  let B := geoTransformAlong M H
  let O := ordMask B q
  have hCur : z ∈ (geoTransformAlong B S).cosupp ∧ nmOrd (geoTransformAlong B S) z = q := by
    change z ∈ (geoTransformAlong (geoTransformAlong M H) S).cosupp ∧
      nmOrd (geoTransformAlong (geoTransformAlong M H) S) z = q
    rw [← geoTransformAlong_append]
    exact ⟨hz,hOrd⟩
  have hBase : OrdRegime B q (.refl : BlowupTower D D) (S.proj z) :=
    regime_base_of_regimeRun_eq (OrdRegime B q) S z hCur hRun
  have hm : S.proj z ∈ O := by
    apply (mem_ordMask_iff (Nat.succ_pos n) hB.isWellFormed hB.isNonzeroAlongAt q _).mpr
    intro hGe
    have hOrdBase := (mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt (B.cosupp_subset_N hBase.1) _).mp hGe
    exact (Nat.not_succ_le_self q) (hBase.2 ▸ hOrdBase)
  refine ⟨hm,(canonical_value_after_occupied_order_drop M P C π hπ S z q hOrd hDrop).trans ?_⟩
  change genInv evaluator B S z = _
  have hNonzero : q ≠ 0 := by omega
  rw [genInv_of_nmOrd_ne_zero evaluator B S hCur.2 hNonzero,hRun]
  let lower (s : Σ D' : CMfd.{0} (n+1), BlowupTower D D' × BlowupTower D' Y) :=
    genLowerValue evaluator B q s.2.1 s.2.2 z
  change toLex (q,toLex (Sum.inr (lower (split S S.length)))) = _
  rw [split_of_length_le S S.length le_rfl]
  change toLex (q,toLex (Sum.inr (genLowerValue evaluator B q .refl S z))) = _
  exact congrArg (fun w => toLex (q,toLex (Sum.inr w)))
    (genLowerValue_eq_of_mem evaluator B (T₀ := (.refl : BlowupTower D D)) (T₁ := S) (y := z) hm)

/-- An active chronological canonical tower which drops into a full
positive suffix run supplies the exact domain, canonical tail and
cosupport on the companion formed at the occupied cut. -/
theorem actual_companion_data_after_occupied_drop
    {A : CMfd.{0} (n+1)} (M : MarkedIdeal (n+1) X) (hM : IsInvDomain (n+1) M)
    (P : BlowupTower X A) (C : Set A) (π : D → A) (hπ : IsBlowupAlong (n+1) C π)
    (S : BlowupTower D Y) (z : Y) (q : ℕ) (hq : 1 ≤ q) :
    let H := P.step C π hπ
    let B := geoTransformAlong M H
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (H.append S) →
    z ∈ (geoTransformAlong M (H.append S)).cosupp →
    nmOrd (geoTransformAlong M (H.append S)) z = q →
    q < nmOrd (geoTransformAlong M P) (π (S.proj z)) →
    regimeRun (OrdRegime B q) S z = S.length →
    GenLowerData evaluator (n+1) M q H S z := by
  dsimp only
  intro hCan hz hOrder hDrop hRun
  let H := P.step C π hπ
  let T := H.append S
  have hTest := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hM T hCan
  have hClock : regimeRun (OrdRegime M q) T z = S.length := by
    have h := (append_order_run_eq_iff M q H S z).mpr
      (Or.inr (regimeRun_step_of_not (OrdRegime M q) P C π hπ
        (fun h => (Nat.ne_of_lt hDrop) h.2.symm)))
    rw [h,hRun]
  have hMaxOrder := StepOneSeq.isMaxOrderValue_stepOneInvM (k := n+1)
    (invFamily (Nat.succ_pos n) n) (Nat.succ_pos n)
  have hData := GeneralCanonicalTail.hasGenLowerData_of_isCanonical evaluator hMaxOrder
    (Nat.succ_pos n) hM T hTest hCan z hz q hOrder hq
  rw [hClock] at hData
  let Data (s : Σ B' : CMfd.{0} (n+1), BlowupTower X B' × BlowupTower B' Y) :=
    GenLowerData evaluator (n+1) M q s.2.1 s.2.2 z
  change Data (split (H.append S) S.length) at hData
  rw [split_append_of_le H S S.length le_rfl] at hData
  let pack (s : Σ B' : CMfd.{0} (n+1), BlowupTower D B' × BlowupTower B' Y) :
      Σ B' : CMfd.{0} (n+1), BlowupTower X B' × BlowupTower B' Y :=
    ⟨s.1,H.append s.2.1,s.2.2⟩
  change Data (pack (split S S.length)) at hData
  rw [split_of_length_le S S.length le_rfl] at hData
  exact hData

end
end Hironaka.HironakaG8OccupiedOrderReset
