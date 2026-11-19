import Hironaka.Resolution.HironakaG11PresLineDivision

/-! Supported division with a new degree-one normal equation. -/
set_option autoImplicit false

open Set Classical

namespace Hironaka.HironakaG1ClosedNormalDivision

noncomputable section

open HironakaActualHistoricalWholeJetFrames HironakaActualCauchyMonomialDivision
  HironakaActualCauchyDiagramPartition HironakaActualHistoricalFormalSupportedDivision
  HironakaG11PresLineFormal HironakaG11PresLineJet HironakaG11PresLineDivision

variable {n k : ℕ}

def normalWord (n : ℕ) : CoordinateWord (n+1) :=
  wordOfExponent (Finsupp.single (Fin.last n) 1)

def normalWords (w : Fin k → CoordinateWord n) : Fin (k+1) → CoordinateWord (n+1) :=
  Fin.cons (normalWord n) (fun j => liftWord (w j))

def normalFamily (g : Fin k → MvPowerSeries (Fin n) ℂ) :
    Fin (k+1) → MvPowerSeries (Fin (n+1)) ℂ :=
  Fin.cons (MvPowerSeries.X (Fin.last n)) (fun j => MvPowerSeries.rename (Fin.castAdd 1) (g j))

private theorem normal_word_exponent :
    wordExponent (normalWord n) = Finsupp.single (Fin.last n) 1 :=
  wordExponent_wordOfExponent _

/-- A positive normal exponent has first owner given by the actual normal equation. -/
theorem normalOwner_of_one_le (w : Fin k → CoordinateWord n) (β : Fin (n+1) →₀ ℕ)
    (hβ : 1 ≤ β (Fin.last n)) :
    historicalOwner (normalWords w) β = some 0 := by
  rw [historicalOwner_eq_some_iff]
  constructor
  · change wordExponent (normalWord n) ≤ β
    rwa [normal_word_exponent, Finsupp.single_le_iff]
  · simp [AvoidsCones]

private theorem avoids_normalWords_succ_iff (w : Fin k → CoordinateWord n)
    (i : Fin k) (α : Fin n →₀ ℕ) :
    AvoidsCones ((List.ofFn (normalWords w)).take i.succ.val) (liftExp α) ↔
      AvoidsCones ((List.ofFn w).take i.val) α := by
  have hl : List.ofFn (normalWords w) = normalWord n :: List.ofFn (fun j => liftWord (w j)) :=
    List.ofFn_succ
  rw [hl, Fin.val_succ, List.take_succ_cons, take_ofFn_liftWord]
  constructor
  · intro h u hu hle
    apply h (liftWord u) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨u,hu,rfl⟩))
    rwa [wordExponent_liftWord, liftExp_le_liftExp_iff]
  · intro h u hu hle
    rcases List.mem_cons.mp hu with rfl | hu
    · rw [normal_word_exponent, Finsupp.single_le_iff, liftExp_apply_last] at hle
      omega
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
      rw [wordExponent_liftWord, liftExp_le_liftExp_iff] at hle
      exact h v hv hle

/-- The inherited ownership on the normal-zero slice is precisely the original ownership. -/
theorem normalOwner_liftExp_iff (w : Fin k → CoordinateWord n) (α : Fin n →₀ ℕ) (i : Fin k) :
    historicalOwner (normalWords w) (liftExp α) = some i.succ ↔
      historicalOwner w α = some i := by
  rw [historicalOwner_eq_some_iff, historicalOwner_eq_some_iff, avoids_normalWords_succ_iff]
  change (wordExponent (liftWord (w i)) ≤ liftExp α ∧ _) ↔ _
  rw [wordExponent_liftWord, liftExp_le_liftExp_iff]

private theorem coeff_mul_normal (F : MvPowerSeries (Fin (n+1)) ℂ) (β : Fin (n+1) →₀ ℕ) :
    MvPowerSeries.coeff β (F * MvPowerSeries.X (Fin.last n)) =
      if 1 ≤ β (Fin.last n) then
        MvPowerSeries.coeff (β - Finsupp.single (Fin.last n) 1) F else 0 := by
  simp only [MvPowerSeries.X, MvPowerSeries.coeff_mul_monomial, Finsupp.single_le_iff, mul_one]

private theorem normal_division_decompose (F : MvPowerSeries (Fin (n+1)) ℂ) :
    F = assembleSeries (fun t => sliceSeries (t+1) F) * MvPowerSeries.X (Fin.last n) +
      MvPowerSeries.rename (Fin.castAdd 1) (sliceSeries 0 F) := by
  ext β
  rw [map_add, coeff_mul_normal]
  by_cases h : 1 ≤ β (Fin.last n)
  · rw [if_pos h, coeff_assembleSeries, coeff_sliceSeries]
    rw [coeff_rename_of_notMem _ (fun α he => by
      have hv := congrArg (fun γ : Fin (n+1) →₀ ℕ => γ (Fin.last n)) he
      simp only [liftExp_apply_last] at hv
      omega), add_zero]
    congr 1
    have hold : oldExp (β - Finsupp.single (Fin.last n) 1) = oldExp β := by
      ext i
      simp only [oldExp_apply, Finsupp.tsub_apply, Finsupp.single_eq_of_ne (Fin.castSucc_lt_last i).ne,
        tsub_zero]
    rw [hold, Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.sub_add_cancel h, liftExp_oldExp_add]
  · rw [if_neg h, zero_add]
    have hz : β (Fin.last n) = 0 := by omega
    have he : liftExp (oldExp β) = β := by simpa [hz] using liftExp_oldExp_add β
    calc
      MvPowerSeries.coeff β F = MvPowerSeries.coeff (liftExp (oldExp β)) F := by rw [he]
      _ = MvPowerSeries.coeff (liftExp (oldExp β))
          (MvPowerSeries.rename (Fin.castAdd 1) (sliceSeries 0 F)) := by
            rw [coeff_rename_liftExp, coeff_sliceSeries, Finsupp.single_zero, add_zero]
      _ = _ := by rw [he]

/-- Putting the new degree-one normal equation first confines every inherited
multiplier to the zero slice and preserves the original owned support. -/
theorem historicalWholeSupportedDivision_closedNormal
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (h : HistoricalWholeSupportedDivision w g) :
    HistoricalWholeSupportedDivision (normalWords w) (normalFamily g) := by
  intro F hF
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hF
  have hslice : sliceSeries 0 F ∈ Ideal.span (range g) := by
    have hzero : sliceSeries 0 (c 0 * MvPowerSeries.X (Fin.last n)) = 0 := by
      ext α
      rw [coeff_sliceSeries, coeff_mul_normal, split_apply_last, if_neg (by omega), map_zero]
    have hadd (A B : MvPowerSeries (Fin (n+1)) ℂ) :
        sliceSeries 0 (A+B) = sliceSeries 0 A + sliceSeries 0 B := by
      ext α
      simp only [coeff_sliceSeries, map_add]
    rw [← hc, Fin.sum_univ_succ, hadd]
    change sliceSeries 0 (c 0 * MvPowerSeries.X (Fin.last n)) +
      sliceSeries 0 (∑ j : Fin k, c j.succ * MvPowerSeries.rename (Fin.castAdd 1) (g j)) ∈ _
    rw [hzero, zero_add, sliceSeries_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [sliceSeries_mul_rename]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)
  obtain ⟨Q, hQ, hSupport⟩ := h (sliceSeries 0 F) hslice
  let R : Fin (k+1) → MvPowerSeries (Fin (n+1)) ℂ := Fin.cons (assembleSeries (fun t => sliceSeries (t+1) F))
    (fun j => MvPowerSeries.rename (Fin.castAdd 1) (Q j))
  refine ⟨R, ?_, ?_⟩
  · rw [Fin.sum_univ_succ]
    change F = assembleSeries (fun t => sliceSeries (t+1) F) * MvPowerSeries.X (Fin.last n) +
      ∑ j : Fin k, MvPowerSeries.rename (Fin.castAdd 1) (Q j) *
        MvPowerSeries.rename (Fin.castAdd 1) (g j)
    conv_lhs => rw [normal_division_decompose F, hQ, map_sum]
    simp only [map_mul]
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · intro β hβ
      exact (hβ (by simp [AvoidsCones])).elim
    · intro β hβ
      change MvPowerSeries.coeff β (MvPowerSeries.rename (Fin.castAdd 1) (Q i)) = 0
      by_cases hb : ∃ α, liftExp α = β
      · obtain ⟨α,rfl⟩ := hb
        rw [coeff_rename_liftExp]
        apply hSupport i α
        intro hAvoid
        apply hβ
        change AvoidsCones ((List.ofFn (normalWords w)).take i.succ.val)
          (liftExp α + wordExponent (liftWord (w i)))
        rw [wordExponent_liftWord, ← liftExp_add, avoids_normalWords_succ_iff]
        exact hAvoid
      · exact coeff_rename_of_notMem _ (fun α he => hb ⟨α,he⟩)

#print axioms historicalWholeSupportedDivision_closedNormal

end
end Hironaka.HironakaG1ClosedNormalDivision
