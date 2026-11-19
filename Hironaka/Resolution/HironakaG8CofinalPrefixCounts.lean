import Hironaka.Resolution.HironakaG8CofinalEventLimit
import Hironaka.Resolution.HironakaG8OccupiedSlotComparison

/-! # Detecting finite event ancestry by actual occupied prefix counts -/
set_option autoImplicit false

namespace Hironaka.HironakaG8CofinalPrefixCounts

open Set
open BlowupTowers HironakaG3RTowerClass HironakaG8CofinalOccupiedAncestry
  HironakaG8CofinalEventLimit HironakaG8OccupiedSlotComparison

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X} {K : LocalTowerClass X}
  {c : ℕ → TowerChart K Z P} {I : Type*} (A : CofinalEvents c I)

/-- The actual number of occupied slots preceding the lifted occurrence
on a larger chart. Empty slots make no contribution. -/
noncomputable def localEarlierCount {i j : ℕ} (h : i ≤ j) (p : Slots c i) : ℕ :=
  ((occupiedOrdinalIso (c j).T).symm (A.lift h p)).val

/-- A represented event has finitely many global predecessors exactly
when the occupied prefix counts of its lifts are bounded. -/
theorem finite_predecessors_iff_bounded_localEarlierCount
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : Slots c i), A.event i p = a)
    {i : ℕ} (p : Slots c i) :
    {a | A.Before a (A.event i p)}.Finite ↔
      ∃ b : ℕ, ∀ (j : ℕ) (h : i ≤ j), localEarlierCount A h p ≤ b := by
  classical
  constructor
  · intro hFinite
    let _ : Fintype {a // A.Before a (A.event i p)} := hFinite.fintype
    refine ⟨Fintype.card {a // A.Before a (A.event i p)},fun j h => ?_⟩
    let e := occupiedOrdinalIso (c j).T
    let last := e.symm (A.lift h p)
    let index (r : Fin last.val) : Fin (occupiedSlots (c j).T).length := ⟨r.val,r.isLt.trans last.isLt⟩
    let f (r : Fin last.val) : {a // A.Before a (A.event i p)} :=
      ⟨A.event j (e (index r)),by
        rw [← A.lift_event h p]
        apply (A.before_iff_slot_lt j _ _).mpr
        exact (e.strictMono (show index r < last from r.isLt)).trans_eq (e.apply_symm_apply _)⟩
    have hInj : Function.Injective f := by
      intro r s he
      have hIdx := e.injective (A.injective j (congrArg Subtype.val he))
      exact Fin.ext (congrArg (fun q : Fin (occupiedSlots (c j).T).length => q.val) hIdx)
    simpa only [Fintype.card_fin,localEarlierCount,e,last] using Fintype.card_le_of_injective f hInj
  · rintro ⟨b,hBound⟩
    by_contra hInf
    obtain ⟨s,hs,hCard⟩ := (show {a | A.Before a (A.event i p)}.Infinite from hInf).exists_subset_card_eq (b+1)
    obtain ⟨k,hk⟩ := A.exists_chart_of_finset hOccurs s
    let j := max i k
    have hij : i ≤ j := le_max_left _ _
    have hkj : k ≤ j := le_max_right _ _
    have hLift (a : s) : ∃ q : Slots c j, A.event j q = a.val := by
      obtain ⟨q,hq⟩ := hk a a.property
      exact ⟨A.lift hkj q,(A.lift_event hkj q).trans hq⟩
    choose t ht using hLift
    let e := occupiedOrdinalIso (c j).T
    let f (a : s) : Fin (localEarlierCount A hij p) :=
      ⟨(e.symm (t a)).val,by
        have ha : A.Before a.val (A.event i p) := hs a.property
        rw [← ht a, ← A.lift_event hij p] at ha
        exact e.symm.strictMono ((A.before_iff_slot_lt j _ _).mp ha)⟩
    have hInj : Function.Injective f := by
      intro a a' he
      have hVal := congrArg (fun q : Fin (localEarlierCount A hij p) => q.val) he
      have hSlots : t a = t a' := e.symm.injective (Fin.ext hVal)
      exact Subtype.ext ((ht a).symm.trans ((congrArg (A.event j) hSlots).trans (ht a')))
    have hLe := Fintype.card_le_of_injective f hInj
    simp only [Fintype.card_fin, Fintype.card_coe, hCard] at hLe
    exact (Nat.not_succ_le_self b) (hLe.trans (hBound j hij))

end Hironaka.HironakaG8CofinalPrefixCounts
