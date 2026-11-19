import Hironaka.Resolution.HironakaG11PresLineFormal

/-!
# Adding a variable to the native five-law data: the whole jet maps (goal G11, step (3a-lines), part L1, law 2)

The whole jet map of a family `g` of formal power series with words `w` (`HironakaActualHistoricalWholeJetFrames`) is the
matrix of the historical columns `X^{β − w_j} g_j` (or `X^β` for unowned `β`) truncated at degree `q`. For the renamed family in
`n + 1` variables (no exponent in the new variable `s`) the columns of `(β, m)` are `s^m` times the renamed columns of `β`, so
the matrix at level `q` is block diagonal along the powers of `s`, with blocks the `n`-variable matrices at levels `q − m`.

* `oldExp`, `liftExp_oldExp_add`, `normalExponentDegree_split` (every exponent is `liftExp β + single (last n) m`);
* `historicalOwner_split`, `historicalWholeColumn_split`, `coeff_split_mul_rename`;
* **`historicalWholeJetMap_lift_bijective`**: law 2 (whole jet bijectivity at every level) passes to the lifted family.

Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-line-state.tex`.
-/

set_option autoImplicit false

open Set Classical

namespace Hironaka.HironakaG11PresLineJet

noncomputable section

open HironakaActualHistoricalWholeJetFrames HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaG11PresLineFormal

variable {n k : ℕ}

/-- The old part of an exponent in `n + 1` variables. -/
def oldExp (β : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => β (Fin.castSucc i)

@[simp] theorem oldExp_apply (β : Fin (n + 1) →₀ ℕ) (i : Fin n) : oldExp β i = β (Fin.castSucc i) := rfl

/-- Every exponent is a lifted exponent plus a power of the new variable. -/
theorem liftExp_oldExp_add (β : Fin (n + 1) →₀ ℕ) :
    liftExp (oldExp β) + Finsupp.single (Fin.last n) (β (Fin.last n)) = β := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp

theorem split_apply_castSucc (α : Fin n →₀ ℕ) (m : ℕ) (i : Fin n) :
    (liftExp α + Finsupp.single (Fin.last n) m) (Fin.castSucc i) = α i := by
  simp

theorem split_apply_last (α : Fin n →₀ ℕ) (m : ℕ) :
    (liftExp α + Finsupp.single (Fin.last n) m) (Fin.last n) = m := by
  simp

theorem normalExponentDegree_split (α : Fin n →₀ ℕ) (m : ℕ) :
    normalExponentDegree (liftExp α + Finsupp.single (Fin.last n) m) = normalExponentDegree α + m := by
  unfold normalExponentDegree
  rw [Fin.sum_univ_castSucc]
  simp only [split_apply_castSucc, split_apply_last]

theorem split_injective {α β : Fin n →₀ ℕ} {m p : ℕ}
    (h : liftExp α + Finsupp.single (Fin.last n) m = liftExp β + Finsupp.single (Fin.last n) p) : α = β ∧ m = p := by
  refine ⟨?_, ?_⟩
  · ext i
    have := congrArg (fun γ : Fin (n + 1) →₀ ℕ => γ (Fin.castSucc i)) h
    simpa only [split_apply_castSucc] using this
  · have := congrArg (fun γ : Fin (n + 1) →₀ ℕ => γ (Fin.last n)) h
    simpa only [split_apply_last] using this

theorem liftWord_le_split (u : CoordinateWord n) (β : Fin n →₀ ℕ) (m : ℕ) :
    wordExponent (liftWord u) ≤ liftExp β + Finsupp.single (Fin.last n) m ↔ wordExponent u ≤ β := by
  rw [wordExponent_liftWord, liftExp_le_iff]
  simp only [split_apply_castSucc]
  exact ⟨fun h i => h i, fun h i => h i⟩

/-- **The owner of `(β, m)` for the lifted words is the owner of `β`.** -/
theorem historicalOwner_split (w : Fin k → CoordinateWord n) (β : Fin n →₀ ℕ) (m : ℕ) :
    historicalOwner (fun i => liftWord (w i)) (liftExp β + Finsupp.single (Fin.last n) m) = historicalOwner w β := by
  unfold historicalOwner
  simp only [liftWord_le_split]

theorem rename_monomial_one (β : Fin n →₀ ℕ) :
    MvPowerSeries.rename (Fin.castAdd 1) (MvPowerSeries.monomial β (1 : ℂ)) = MvPowerSeries.monomial (liftExp β) 1 := by
  rw [MvPowerSeries.rename_monomial]
  have h : Finsupp.mapDomain (Fin.castAdd 1) β = liftExp β := (Finsupp.embDomain_eq_mapDomain (Fin.castAddEmb 1) β).symm
  rw [h]

/-- **The lifted column of `(β, m)` is `s^m` times the renamed column of `β`.** -/
theorem historicalWholeColumn_split (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (β : Fin n →₀ ℕ) (m : ℕ) :
    historicalWholeColumn (fun i => liftWord (w i)) (fun i => MvPowerSeries.rename (Fin.castAdd 1) (g i))
        (liftExp β + Finsupp.single (Fin.last n) m) =
      MvPowerSeries.monomial (Finsupp.single (Fin.last n) m) 1 *
        MvPowerSeries.rename (Fin.castAdd 1) (historicalWholeColumn w g β) := by
  unfold historicalWholeColumn
  rw [historicalOwner_split]
  cases ho : historicalOwner w β with
  | none =>
    simp only
    rw [rename_monomial_one, MvPowerSeries.monomial_mul_monomial, one_mul,
      add_comm (Finsupp.single (Fin.last n) m) (liftExp β)]
  | some j =>
    simp only
    have hle : wordExponent (w j) ≤ β := ((historicalOwner_eq_some_iff w β j).mp ho).1
    have hexp : liftExp β + Finsupp.single (Fin.last n) m - liftExp (wordExponent (w j)) =
        Finsupp.single (Fin.last n) m + liftExp (β - wordExponent (w j)) := by
      ext l
      refine Fin.lastCases ?_ (fun i => ?_) l
      · simp
      · simp only [Finsupp.tsub_apply, Finsupp.add_apply, liftExp_apply_castSucc, Finsupp.single_apply,
          (Fin.castSucc_lt_last i).ne', if_false, add_zero, zero_add]
    rw [map_mul, rename_monomial_one, ← mul_assoc, MvPowerSeries.monomial_mul_monomial, one_mul,
      wordExponent_liftWord, hexp]

/-- **Coefficients of `s^m` times a renamed series.** -/
theorem coeff_split_mul_rename (F : MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ) (p m : ℕ) :
    MvPowerSeries.coeff (liftExp α + Finsupp.single (Fin.last n) p)
        (MvPowerSeries.monomial (Finsupp.single (Fin.last n) m) 1 * MvPowerSeries.rename (Fin.castAdd 1) F) =
      if p = m then MvPowerSeries.coeff α F else 0 := by
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases hmp : m ≤ p
  · have hle : Finsupp.single (Fin.last n) m ≤ liftExp α + Finsupp.single (Fin.last n) p := by
      intro l
      refine Fin.lastCases ?_ (fun i => ?_) l
      · simpa using hmp
      · simp
    have hsub : liftExp α + Finsupp.single (Fin.last n) p - Finsupp.single (Fin.last n) m =
        liftExp α + Finsupp.single (Fin.last n) (p - m) := by
      ext l
      refine Fin.lastCases ?_ (fun i => ?_) l
      · simp
      · simp
    rw [if_pos hle, one_mul, hsub]
    by_cases hpm : p = m
    · subst hpm
      rw [if_pos rfl, Nat.sub_self, Finsupp.single_zero, add_zero, coeff_rename_liftExp]
    · rw [if_neg hpm]
      apply coeff_rename_of_notMem
      intro γ hγ
      have := congrArg (fun δ : Fin (n + 1) →₀ ℕ => δ (Fin.last n)) hγ
      simp only [liftExp_apply_last, split_apply_last] at this
      omega
  · have hle : ¬ Finsupp.single (Fin.last n) m ≤ liftExp α + Finsupp.single (Fin.last n) p := by
      intro h
      have := h (Fin.last n)
      simp only [Finsupp.single_eq_same, split_apply_last] at this
      omega
    rw [if_neg hle, if_neg (by omega)]

/-- **Law 2 under a new variable**: if the whole jet maps of `(w, g)` are bijective at every level, so are those of the
lifted words and the renamed family. -/
theorem historicalWholeJetMap_lift_bijective (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (h : ∀ q, Function.Bijective (historicalWholeJetMap w g q)) (q : ℕ) :
    Function.Bijective (historicalWholeJetMap (fun i => liftWord (w i))
      (fun i => MvPowerSeries.rename (Fin.castAdd 1) (g i)) q) := by
  classical
  let := normalExponentFintype (n + 1) q
  set w' : Fin k → CoordinateWord (n + 1) := fun i => liftWord (w i) with hw'
  set g' : Fin k → MvPowerSeries (Fin (n + 1)) ℂ := fun i => MvPowerSeries.rename (Fin.castAdd 1) (g i) with hg'
  have hinj : Function.Injective (historicalWholeJetMap w' g' q) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
    funext β'
    set m := β'.val (Fin.last n) with hm
    have hdeg : normalExponentDegree (oldExp β'.val) + m < q := by
      rw [← normalExponentDegree_split, liftExp_oldExp_add]
      exact β'.property
    let := normalExponentFintype n (q - m)
    let e : normalExponentIndex n (q - m) → normalExponentIndex (n + 1) q := fun β =>
      ⟨liftExp β.val + Finsupp.single (Fin.last n) m, by
        rw [normalExponentDegree_split]
        have := β.property
        omega⟩
    have he : Function.Injective e := fun a b hab =>
      Subtype.ext (split_injective (congrArg Subtype.val hab)).1
    let cm : normalExponentIndex n (q - m) → ℂ := fun β => c (e β)
    have hcm : historicalWholeJetMap w g (q - m) cm = 0 := by
      funext α
      have hα : normalExponentDegree (liftExp α.val + Finsupp.single (Fin.last n) m) < q := by
        rw [normalExponentDegree_split]
        have := α.property
        omega
      have h0 := congrFun hc ⟨liftExp α.val + Finsupp.single (Fin.last n) m, hα⟩
      change (∑ β', c β' * MvPowerSeries.coeff (liftExp α.val + Finsupp.single (Fin.last n) m)
        (historicalWholeColumn w' g' β'.val)) = 0 at h0
      change (∑ β, cm β * MvPowerSeries.coeff α.val (historicalWholeColumn w g β.val)) = 0
      rw [← h0]
      apply Fintype.sum_of_injective e he
      · intro γ' hγ'
        have hsplit := liftExp_oldExp_add γ'.val
        have hne : γ'.val (Fin.last n) ≠ m := by
          intro hγm
          apply hγ'
          refine ⟨⟨oldExp γ'.val, ?_⟩, Subtype.ext ?_⟩
          · have := γ'.property
            rw [← hsplit, normalExponentDegree_split, hγm] at this
            omega
          · change liftExp (oldExp γ'.val) + Finsupp.single (Fin.last n) m = γ'.val
            rw [← hγm]
            exact hsplit
        rw [← hsplit, hw', hg', historicalWholeColumn_split, coeff_split_mul_rename, if_neg (Ne.symm hne), mul_zero]
      · intro β
        change cm β * _ = c (e β) * MvPowerSeries.coeff (liftExp α.val + Finsupp.single (Fin.last n) m)
          (historicalWholeColumn w' g' (liftExp β.val + Finsupp.single (Fin.last n) m))
        rw [hw', hg', historicalWholeColumn_split, coeff_split_mul_rename, if_pos rfl]
    have hzero := (h (q - m)).1 (hcm.trans (map_zero _).symm)
    have hβ : β' = e ⟨oldExp β'.val, by omega⟩ := Subtype.ext (liftExp_oldExp_add β'.val).symm
    rw [hβ]
    exact congrFun hzero _
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

end

end Hironaka.HironakaG11PresLineJet
