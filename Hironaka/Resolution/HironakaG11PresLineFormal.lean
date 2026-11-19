import Hironaka.Resolution.HironakaActualHistoricalNormalizedWeakPresentation
import Hironaka.Resolution.HironakaActualTaylorCoordinateNaturality

/-!
# Adding a variable to the native five-law data: the combinatorial lifts (goal G11, step (3a-lines), part L1)

Step (3a-lines) (`HironakaG11PresLineState.NativeLineStability`) asks that the native Hilbert–Samuel state survive the
product with a line: a standard basis of `I_{W,x}` (vertices `V ⊆ ℕ^n`, words, selector, five point laws) pulled back along the
projection `ℂ^{n+1} → ℂ^n` is one of `I_{W×ℂ,(x,t)}` with the lifted vertices (no exponent in the new variable). This module
provides the combinatorial lifts and the laws that are coefficient conditions.

* `liftExp α` (`α ∈ ℕ^n` as an exponent in `n + 1` variables, last entry `0`), `liftWord`, `liftVertices V`,
  `liftVertexEquiv V : V ≃ liftVertices V`, **`liftSelector S`** (the fixed inherited selector of `V` for `liftVertices V`);
* the data laws: `wordExponent_liftWord`, `normalExponentDegree_liftExp`, `liftExp_le_liftExp_iff`,
  **`historicalOwner_liftWord`**, `weightedCommonMark_liftVertices`;
* the coefficient laws for `rename (Fin.castAdd 1)` (the Taylor series of the pulled-back germs,
  `HironakaActualTaylorCoordinateNaturality.actualUnshiftedTaylor_tangentPullback`): **`rename_mem_genuineFormalVariables_pow_iff`**
  (law 1, orders) and **`historicalWholePrefixSupport_lift`** (law 6, prefix support).

Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-line-state.tex`.
-/

set_option autoImplicit false

open Set Classical

namespace Hironaka.HironakaG11PresLineFormal

noncomputable section

open HironakaActualFixedInheritedSelector HironakaActualHistoricalWholeJetFrames HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalMonomialBasis HironakaActualWeightedCoefficientCompression HironakaActualOriginalFormalHSTransfer
  HironakaActualHistoricalMovingPrefixSupport

variable {n : ℕ}

/-! ### Exponents and words -/

/-- An exponent in `n` variables as an exponent in `n + 1` variables (the new variable last, exponent `0`). -/
def liftExp (α : Fin n →₀ ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.embDomain (Fin.castAddEmb 1) α

@[simp] theorem liftExp_apply_castSucc (α : Fin n →₀ ℕ) (i : Fin n) : liftExp α (Fin.castSucc i) = α i :=
  Finsupp.embDomain_apply_self (Fin.castAddEmb 1) α i

@[simp] theorem liftExp_apply_last (α : Fin n →₀ ℕ) : liftExp α (Fin.last n) = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact (Fin.castSucc_lt_last i).ne hi

theorem liftExp_injective : Function.Injective (liftExp (n := n)) :=
  Finsupp.embDomain_injective _

theorem liftExp_single (i : Fin n) (d : ℕ) : liftExp (Finsupp.single i d) = Finsupp.single (Fin.castSucc i) d :=
  Finsupp.embDomain_single _ i d

theorem liftExp_add (α β : Fin n →₀ ℕ) : liftExp (α + β) = liftExp α + liftExp β := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp

theorem liftExp_le_liftExp_iff {α β : Fin n →₀ ℕ} : liftExp α ≤ liftExp β ↔ α ≤ β := by
  constructor
  · intro h i
    simpa using h (Fin.castSucc i)
  · intro h j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp
    · simpa using h i

/-- A lifted exponent lies below `β'` iff it lies below the old part of `β'`. -/
theorem liftExp_le_iff {α : Fin n →₀ ℕ} {β' : Fin (n + 1) →₀ ℕ} :
    liftExp α ≤ β' ↔ ∀ i, α i ≤ β' (Fin.castSucc i) := by
  constructor
  · intro h i
    simpa using h (Fin.castSucc i)
  · intro h j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp
    · simpa using h i

theorem normalExponentDegree_liftExp (α : Fin n →₀ ℕ) :
    normalExponentDegree (liftExp α) = normalExponentDegree α := by
  unfold normalExponentDegree
  rw [Fin.sum_univ_castSucc]
  simp

/-- A word in `n` variables as a word in `n + 1` variables. -/
def liftWord (w : CoordinateWord n) : CoordinateWord (n + 1) :=
  w.map fun p => (Fin.castSucc p.1, p.2)

theorem wordExponent_liftWord (w : CoordinateWord n) : wordExponent (liftWord w) = liftExp (wordExponent w) := by
  induction w with
  | nil => simp [liftWord, wordExponent, liftExp]
  | cons p w ih =>
    obtain ⟨i, d⟩ := p
    change Finsupp.single (Fin.castSucc i) d + wordExponent (liftWord w) =
      liftExp (Finsupp.single i d + wordExponent w)
    rw [ih, liftExp_add, liftExp_single]

/-- **The historical owner of a lifted exponent** (lifted words) is the owner of the exponent. -/
theorem historicalOwner_liftWord {k : ℕ} (w : Fin k → CoordinateWord n) (α : Fin n →₀ ℕ) :
    historicalOwner (fun i => liftWord (w i)) (liftExp α) = historicalOwner w α := by
  unfold historicalOwner
  simp only [wordExponent_liftWord, liftExp_le_liftExp_iff]

/-! ### Vertex sets and selectors -/

/-- The lifted vertex set. -/
def liftVertices (V : Finset (Fin n →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  V.map ⟨liftExp, liftExp_injective⟩

theorem mem_liftVertices {V : Finset (Fin n →₀ ℕ)} {v' : Fin (n + 1) →₀ ℕ} :
    v' ∈ liftVertices V ↔ ∃ v ∈ V, liftExp v = v' := by
  simp [liftVertices]

/-- The vertices of `V` and of its lift. -/
def liftVertexEquiv (V : Finset (Fin n →₀ ℕ)) : V ≃ liftVertices V :=
  Equiv.ofBijective (fun v => ⟨liftExp v.val, Finset.mem_map_of_mem _ v.property⟩)
    ⟨fun a b h => Subtype.ext (liftExp_injective (congrArg Subtype.val h)), fun v' => by
      obtain ⟨v, hv, he⟩ := mem_liftVertices.mp v'.property
      exact ⟨⟨v, hv⟩, Subtype.ext he⟩⟩

@[simp] theorem liftVertexEquiv_val {V : Finset (Fin n →₀ ℕ)} (v : V) :
    (liftVertexEquiv V v).val = liftExp v.val := rfl

theorem liftVertexEquiv_symm_val {V : Finset (Fin n →₀ ℕ)} (v' : liftVertices V) :
    liftExp ((liftVertexEquiv V).symm v').val = v'.val := by
  conv_rhs => rw [← (liftVertexEquiv V).apply_symm_apply v']
  rfl

/-- The common mark of the lifted vertex family is that of the family. -/
theorem weightedCommonMark_liftVertices (V : Finset (Fin n →₀ ℕ)) :
    weightedCommonMark (fun v' : liftVertices V => normalExponentDegree v'.val) =
      weightedCommonMark (fun v : V => normalExponentDegree v.val) := by
  unfold weightedCommonMark
  rw [← (liftVertexEquiv V).prod_comp]
  simp [normalExponentDegree_liftExp]

/-- An essential variable of the lifted family is an old variable. -/
theorem ne_last_of_mem_essential {V : Finset (Fin n →₀ ℕ)} (j : fixedSelectorEssential (liftVertices V)) :
    j.val ≠ Fin.last n := by
  obtain ⟨a, ha⟩ := j.property
  intro h
  rw [h, ← liftVertexEquiv_symm_val a, liftExp_apply_last] at ha
  exact ha rfl

/-- The old variable under an essential variable of the lifted family. -/
def essentialPred {V : Finset (Fin n →₀ ℕ)} (j : fixedSelectorEssential (liftVertices V)) : fixedSelectorEssential V :=
  ⟨(j.val).castPred (ne_last_of_mem_essential j), by
    obtain ⟨a, ha⟩ := j.property
    refine ⟨(liftVertexEquiv V).symm a, ?_⟩
    have h := liftVertexEquiv_symm_val a
    rw [← Fin.castSucc_castPred j.val (ne_last_of_mem_essential j), ← h, liftExp_apply_castSucc] at ha
    exact ha⟩

theorem castSucc_essentialPred {V : Finset (Fin n →₀ ℕ)} (j : fixedSelectorEssential (liftVertices V)) :
    Fin.castSucc (essentialPred j).val = j.val :=
  Fin.castSucc_castPred j.val (ne_last_of_mem_essential j)

/-- **The lifted fixed inherited selector.** -/
def liftSelector {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V) :
    ActualFixedInheritedSelector (liftVertices V) where
  selected j := liftVertexEquiv V (S.selected (essentialPred j))
  positive j := by
    rw [liftVertexEquiv_val, ← castSucc_essentialPred j, liftExp_apply_castSucc]
    exact S.positive (essentialPred j)
  least_degree j a ha := by
    rw [liftVertexEquiv_val, normalExponentDegree_liftExp, ← liftVertexEquiv_symm_val a, normalExponentDegree_liftExp]
    apply S.least_degree (essentialPred j)
    rw [← liftVertexEquiv_symm_val a, ← castSucc_essentialPred j, liftExp_apply_castSucc] at ha
    exact ha

/-! ### Coefficient laws for the renamed series -/

theorem coeff_rename_liftExp (F : MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (liftExp α) (MvPowerSeries.rename (Fin.castAdd 1) F) = MvPowerSeries.coeff α F :=
  MvPowerSeries.coeff_embDomain_rename (Fin.castAddEmb 1) F α

theorem coeff_rename_of_notMem (F : MvPowerSeries (Fin n) ℂ) {β : Fin (n + 1) →₀ ℕ} (h : ∀ α, liftExp α ≠ β) :
    MvPowerSeries.coeff β (MvPowerSeries.rename (Fin.castAdd 1) F) = 0 := by
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨α, rfl⟩
  apply h α
  change Finsupp.embDomain (Fin.castAddEmb 1) α = Finsupp.mapDomain (Fin.castAdd 1) α
  rw [Finsupp.embDomain_eq_mapDomain]
  rfl

/-- **Law 1 (orders) under the new variable**: `rename F ∈ 𝔪^q ↔ F ∈ 𝔪^q`. -/
theorem rename_mem_genuineFormalVariables_pow_iff (F : MvPowerSeries (Fin n) ℂ) (q : ℕ) :
    MvPowerSeries.rename (Fin.castAdd 1) F ∈ genuineFormalVariables (n + 1) ^ q ↔ F ∈ genuineFormalVariables n ^ q := by
  rw [mem_genuineFormalVariables_pow_iff_coefficients_zero, mem_genuineFormalVariables_pow_iff_coefficients_zero]
  constructor
  · intro h α hα
    rw [← coeff_rename_liftExp]
    exact h _ (by rwa [normalExponentDegree_liftExp])
  · intro h β hβ
    by_cases hex : ∃ α, liftExp α = β
    · obtain ⟨α, rfl⟩ := hex
      rw [coeff_rename_liftExp]
      exact h α (by rwa [normalExponentDegree_liftExp] at hβ)
    · exact coeff_rename_of_notMem F (fun α hα => hex ⟨α, hα⟩)

/-- **Law 6 (whole prefix support) under the new variable.** -/
theorem historicalWholePrefixSupport_lift {V : Finset (Fin n →₀ ℕ)} {g : V → MvPowerSeries (Fin n) ℂ}
    (h : HistoricalWholePrefixSupport V g) :
    HistoricalWholePrefixSupport (liftVertices V)
      (fun v' => MvPowerSeries.rename (Fin.castAdd 1) (g ((liftVertexEquiv V).symm v'))) := by
  intro k a' hka b' hbk β hβ
  by_cases hex : ∃ α, liftExp α = β
  · obtain ⟨α, rfl⟩ := hex
    rw [coeff_rename_liftExp]
    have ha : normalExponentDegree ((liftVertexEquiv V).symm a').val = normalExponentDegree a'.val := by
      rw [← normalExponentDegree_liftExp, liftVertexEquiv_symm_val]
    have hb : normalExponentDegree ((liftVertexEquiv V).symm b').val = normalExponentDegree b'.val := by
      rw [← normalExponentDegree_liftExp, liftVertexEquiv_symm_val]
    apply h k ((liftVertexEquiv V).symm a') (by rwa [ha]) ((liftVertexEquiv V).symm b') (by rwa [hb]) α
    rw [← liftExp_le_liftExp_iff, liftVertexEquiv_symm_val]
    exact hβ
  · exact coeff_rename_of_notMem _ (fun α hα => hex ⟨α, hα⟩)

end

end Hironaka.HironakaG11PresLineFormal
