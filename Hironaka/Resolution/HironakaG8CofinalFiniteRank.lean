import Hironaka.Resolution.HironakaG8CofinalOccupiedAncestry

/-! A common chart gives a finite serial rank to the occupied events. -/
set_option autoImplicit false

namespace Hironaka.HironakaG8CofinalFiniteRank

open BlowupTowers HironakaG3RTowerClass HironakaG8CofinalOccupiedAncestry

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*}

/-- Rank each event by its raw occupied slot in one chart that represents
every event, preserving the order even for disjoint footprints. -/
theorem finite_serial_rank_of_reference_chart
    (E : CofinalEvents c ι) (i₀ : ℕ)
    (hAll : ∀ a, ∃ p : {k // Occupied (c i₀).T k}, E.event i₀ p = a) :
    Finite ι ∧ ∃ rank : ι → ℕ, Function.Injective rank ∧
      (∀ a, rank a < (c i₀).T.length) ∧
      (∀ ⦃a b⦄, E.Before a b → rank a < rank b) := by
  classical
  choose slot hSlot using hAll
  let rank : ι→ℕ := fun a => (slot a).val
  have hBound (a : ι) : rank a<(c i₀).T.length := occupied_lt_length _ (slot a).property
  have hInj : Function.Injective rank := by
    intro a b hab
    have hs : slot a=slot b := Subtype.ext hab
    exact (hSlot a).symm.trans ((congrArg (E.event i₀) hs).trans (hSlot b))
  have hOrder ⦃a b : ι⦄ (hab : E.Before a b) : rank a<rank b := by
    apply (E.before_iff_slot_lt i₀ (slot a) (slot b)).mp
    rwa [hSlot a,hSlot b]
  have hFinInj : Function.Injective (fun a => (⟨rank a,hBound a⟩ : Fin (c i₀).T.length)) := by
    intro a b hab
    exact hInj (congrArg Fin.val hab)
  have hFinite : Finite ι := Finite.of_injective _ hFinInj
  exact ⟨hFinite,rank,hInj,hBound,fun {_ _} h => hOrder h⟩

end Hironaka.HironakaG8CofinalFiniteRank
