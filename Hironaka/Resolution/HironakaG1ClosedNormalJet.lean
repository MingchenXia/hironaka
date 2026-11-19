import Hironaka.Resolution.HironakaG1ClosedNormalDivision
import Hironaka.Resolution.HironakaActualHistoricalPrefixJetFrames

/-! Whole finite jets for the closed normal equation. -/
set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaG1ClosedNormalJet

noncomputable section

open HironakaActualHistoricalWholeJetFrames HironakaActualCauchyMonomialDivision
  HironakaActualCauchyDiagramPartition HironakaG11PresLineFormal HironakaG11PresLineJet
  HironakaG1ClosedNormalDivision HironakaRelativeNormalMonomialBasis
  HironakaActualHistoricalPrefixJetFrames HironakaActualOriginalFormalHSTransfer

variable {n k : ℕ}

/-- On the graph, the historical columns are the genuine extensions of the inherited columns. -/
theorem wholeColumn_closedNormal_liftExp (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (β : Fin n →₀ ℕ) :
    historicalWholeColumn (normalWords w) (normalFamily g) (liftExp β) =
      MvPowerSeries.rename (Fin.castAdd 1) (historicalWholeColumn w g β) := by
  unfold historicalWholeColumn
  cases h : historicalOwner w β with
  | none =>
    have hNone : historicalOwner (normalWords w) (liftExp β) = none := by
      cases hNew : historicalOwner (normalWords w) (liftExp β) with
      | none => rfl
      | some j =>
        exfalso
        refine Fin.cases ?_ (fun j hj => ?_) j hNew
        · intro hz
          have hle := ((historicalOwner_eq_some_iff _ _ _).mp hz).1
          change wordExponent (normalWord n) ≤ liftExp β at hle
          rw [normalWord, wordExponent_wordOfExponent, Finsupp.single_le_iff, liftExp_apply_last] at hle
          omega
        · have hOld := (normalOwner_liftExp_iff w β j).mp hj
          rw [h] at hOld
          cases hOld
    rw [hNone]
    exact (rename_monomial_one β).symm
  | some j =>
    rw [(normalOwner_liftExp_iff w β j).mpr h]
    change MvPowerSeries.monomial (liftExp β - wordExponent (liftWord (w j))) 1 *
      MvPowerSeries.rename (Fin.castAdd 1) (g j) =
        MvPowerSeries.rename (Fin.castAdd 1)
          (MvPowerSeries.monomial (β - wordExponent (w j)) 1 * g j)
    rw [map_mul, rename_monomial_one, wordExponent_liftWord]
    have hexp : liftExp β - liftExp (wordExponent (w j)) = liftExp (β-wordExponent (w j)) := by
      ext i
      refine Fin.lastCases ?_ (fun l => ?_) i <;> simp [Finsupp.tsub_apply]
    rw [hexp]

/-- All positive normal monomials give the original identity columns. -/
theorem wholeColumn_closedNormal_positive (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (β : Fin (n+1) →₀ ℕ)
    (hβ : 1 ≤ β (Fin.last n)) :
    historicalWholeColumn (normalWords w) (normalFamily g) β = MvPowerSeries.monomial β 1 := by
  unfold historicalWholeColumn
  rw [normalOwner_of_one_le w β hβ]
  change MvPowerSeries.monomial (β - wordExponent (normalWord n)) 1 *
    MvPowerSeries.X (Fin.last n) = _
  rw [normalWord, wordExponent_wordOfExponent, MvPowerSeries.X,
    MvPowerSeries.monomial_mul_monomial, one_mul,
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hβ)]

/-- Adjoining the actual degree-one equation preserves every whole finite historical jet frame. -/
theorem historicalWholeJetMap_closedNormal_bijective (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (q : ℕ)
    (h : Function.Bijective (historicalWholeJetMap w g q)) :
    Function.Bijective (historicalWholeJetMap (normalWords w) (normalFamily g) q) := by
  let := normalExponentFintype (n+1) q
  let := normalExponentFintype n q
  let e : normalExponentIndex n q → normalExponentIndex (n+1) q := fun β =>
    ⟨liftExp β.val, by simpa only [normalExponentDegree_liftExp] using β.property⟩
  have he : Function.Injective e := fun a b h => Subtype.ext (liftExp_injective (congrArg Subtype.val h))
  have e_onto {β : normalExponentIndex (n+1) q} (hβ : β.val (Fin.last n) = 0) :
      β ∈ range e := by
    have hval : liftExp (oldExp β.val) = β.val := by simpa [hβ] using liftExp_oldExp_add β.val
    refine ⟨⟨oldExp β.val, ?_⟩, Subtype.ext hval⟩
    simpa [← normalExponentDegree_liftExp (oldExp β.val), hval] using β.property
  have hinj : Function.Injective (historicalWholeJetMap (normalWords w) (normalFamily g) q) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
    have hOld : historicalWholeJetMap w g q (c ∘ e) = 0 := by
      funext α
      have h0 := congrFun hc (e α)
      change (∑ β, c β * MvPowerSeries.coeff (liftExp α.val)
        (historicalWholeColumn (normalWords w) (normalFamily g) β.val)) = 0 at h0
      change (∑ β, c (e β) * MvPowerSeries.coeff α.val (historicalWholeColumn w g β.val)) = 0
      rw [← h0]
      apply Fintype.sum_of_injective e he
      · intro β hb
        have hβ : 1 ≤ β.val (Fin.last n) := by
          by_contra h
          exact hb (e_onto (by omega))
        have hne : β.val ≠ liftExp α.val := by
          intro eq
          rw [eq, liftExp_apply_last] at hβ
          omega
        rw [wholeColumn_closedNormal_positive _ _ _ hβ, MvPowerSeries.coeff_monomial,
          if_neg (Ne.symm hne), mul_zero]
      · intro β
        change _ = c (e β) * MvPowerSeries.coeff (liftExp α.val)
          (historicalWholeColumn (normalWords w) (normalFamily g) (liftExp β.val))
        rw [wholeColumn_closedNormal_liftExp, coeff_rename_liftExp]
    have hOldZero := h.injective (hOld.trans (map_zero _).symm)
    funext β
    by_cases hβ : β.val (Fin.last n) = 0
    · obtain ⟨γ,rfl⟩ := e_onto hβ
      exact congrFun hOldZero γ
    · have h0 := congrFun hc β
      change (∑ γ, c γ * MvPowerSeries.coeff β.val
        (historicalWholeColumn (normalWords w) (normalFamily g) γ.val)) = 0 at h0
      rw [Finset.sum_eq_single β] at h0
      · rw [wholeColumn_closedNormal_positive _ _ _ (by omega), MvPowerSeries.coeff_monomial,
          if_pos rfl, mul_one] at h0
        exact h0
      · intro γ _ hne
        by_cases hγ : γ.val (Fin.last n) = 0
        · obtain ⟨δ,rfl⟩ := e_onto hγ
          change c (e δ) * _ = 0
          rw [show c (e δ) = 0 from congrFun hOldZero δ, zero_mul]
        · rw [wholeColumn_closedNormal_positive _ _ _ (by omega), MvPowerSeries.coeff_monomial,
            if_neg (fun heq => hne (Subtype.ext heq.symm)), mul_zero]
      · simp
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Original degree orders are retained and the new normal equation has degree one. -/
theorem normalFamily_mem_degree (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hg : ∀ j, g j ∈ genuineFormalVariables n ^ normalExponentDegree (wordExponent (w j))) :
    ∀ j, normalFamily g j ∈ genuineFormalVariables (n+1) ^
      normalExponentDegree (wordExponent (normalWords w j)) := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · change MvPowerSeries.X (Fin.last n) ∈ genuineFormalVariables (n+1) ^
      normalExponentDegree (wordExponent (normalWord n))
    have hDegree : normalExponentDegree (wordExponent (normalWord n)) = 1 := by
      rw [normalWord, wordExponent_wordOfExponent]
      simp [normalExponentDegree]
    rw [hDegree, pow_one]
    exact Ideal.subset_span ⟨Fin.last n, rfl⟩
  · change MvPowerSeries.rename (Fin.castAdd 1) (g i) ∈ genuineFormalVariables (n+1) ^
      normalExponentDegree (wordExponent (liftWord (w i)))
    simpa only [wordExponent_liftWord, normalExponentDegree_liftExp,
      rename_mem_genuineFormalVariables_pow_iff] using hg i

/-- For the inherited ordered degree prefix with the normal equation first,
the whole and the actual homogeneous coefficient frames are both bijective. -/
theorem historicalDegreePrefix_adjoinNormal (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (m : ℕ)
    (hg : ∀ j, g j ∈ genuineFormalVariables n ^ normalExponentDegree (wordExponent (w j)))
    (h : HistoricalDegreePrefixFrames w g m) :
    let v := historicalDegreePrefixWords w m
    let G := fun j => g (historicalDegreePrefixLabel w m j)
    (∀ q, Function.Bijective (historicalWholeJetMap (normalWords v) (normalFamily G) q)) ∧
    ∀ d, Function.Bijective (historicalHomogeneousColumnMap (normalWords v) (normalFamily G) d) := by
  dsimp only
  have hWhole q := historicalWholeJetMap_closedNormal_bijective _ _ q (h.1 q)
  refine ⟨hWhole, fun d => ?_⟩
  rw [historicalHomogeneousColumnMap_eq_operator]
  exact historicalHomogeneousOperator_bijective _ _
    (normalFamily_mem_degree _ _ (fun j => hg (historicalDegreePrefixLabel w m j))) hWhole d

private theorem normalWord_degree (n : ℕ) :
    normalExponentDegree (wordExponent (normalWord n)) = 1 := by
  rw [normalWord, wordExponent_wordOfExponent]
  simp [normalExponentDegree]

private theorem degree_normalWords_succ (w : Fin k → CoordinateWord n) (j : Fin k) :
    normalExponentDegree (wordExponent (normalWords w j.succ)) =
      normalExponentDegree (wordExponent (w j)) := by
  change normalExponentDegree (wordExponent (liftWord (w j))) = _
  rw [wordExponent_liftWord, normalExponentDegree_liftExp]

private theorem sortedPrefix_normalLabels (w : Fin k → CoordinateWord n)
    (hPos : ∀ j, 0 < normalExponentDegree (wordExponent (w j))) {m : ℕ} (hm : 1 ≤ m) :
    ∃ hCount : historicalDegreePrefixCount (normalWords w) m =
        historicalDegreePrefixCount w m + 1,
      ∀ j : Fin (historicalDegreePrefixCount w m + 1),
        historicalDegreePrefixLabel (normalWords w) m (Fin.cast hCount.symm j) =
          Fin.cons (α := fun _ => Fin (k+1)) 0 (fun i => (historicalDegreePrefixLabel w m i).succ) j := by
  let lab := historicalDegreePrefixLabel w m
  let newLab : Fin (historicalDegreePrefixCount w m + 1) → Fin (k+1) :=
    Fin.cons (α := fun _ => Fin (k+1)) 0 (fun i => (lab i).succ)
  have hMem (j) : normalExponentDegree (wordExponent (normalWords w (newLab j))) ≤ m := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa only [newLab, Fin.cons_zero, normalWords, normalWord_degree] using hm
    · simpa only [newLab, Fin.cons_succ, degree_normalWords_succ] using historicalDegreePrefixLabel_mem w m i
  let mapLabel (j) : {i : Fin (k+1) // normalExponentDegree (wordExponent (normalWords w i)) ≤ m} :=
    ⟨newLab j, hMem j⟩
  have hSur : Function.Surjective mapLabel := by
    rintro ⟨j,hj⟩
    refine Fin.cases ?_ (fun i hi => ?_) j hj
    · intro _
      exact ⟨0, Subtype.ext rfl⟩
    · rw [degree_normalWords_succ] at hi
      obtain ⟨l,hl⟩ := (historicalDegreePrefixLabelEquiv w m).surjective ⟨i,hi⟩
      exact ⟨l.succ, Subtype.ext (congrArg Fin.succ (congrArg Subtype.val hl))⟩
  have hMono : StrictMono (fun j => historicalDegreeKey (normalWords w) (newLab j)) := by
    intro i j hij
    revert j
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j h0j
      refine Fin.cases (fun h => (lt_irrefl _ h).elim) (fun j _ => ?_) j h0j
      change toLex (normalExponentDegree (wordExponent (normalWord n)), (0 : Fin (k+1))) <
        toLex (normalExponentDegree (wordExponent (normalWords w (lab j).succ)), (lab j).succ)
      rw [normalWord_degree, degree_normalWords_succ, Prod.Lex.toLex_lt_toLex']
      refine ⟨hPos _, fun _ => ?_⟩
      exact Nat.zero_lt_succ _
    · intro j hij
      refine Fin.cases (fun h => (Fin.not_lt_zero _ h).elim) (fun j hij => ?_) j hij
      change toLex (normalExponentDegree (wordExponent (normalWords w (lab i).succ)), (lab i).succ) <
        toLex (normalExponentDegree (wordExponent (normalWords w (lab j).succ)), (lab j).succ)
      rw [degree_normalWords_succ, degree_normalWords_succ, Prod.Lex.toLex_lt_toLex]
      have h := historicalDegreePrefixLabel_strictMono w m (Fin.succ_lt_succ_iff.mp hij)
      exact ((Prod.Lex.toLex_lt_toLex.mp h).imp id
        (fun ⟨hd,hl⟩ => ⟨hd, Fin.succ_lt_succ_iff.mpr hl⟩))
  have hInj : Function.Injective mapLabel := by
    intro x y h
    exact hMono.injective (congrArg (fun j => historicalDegreeKey (normalWords w) j.val) h)
  let e := (historicalDegreePrefixLabelEquiv (normalWords w) m).trans
    (Equiv.ofBijective mapLabel ⟨hInj,hSur⟩).symm
  have hCount : historicalDegreePrefixCount (normalWords w) m =
      historicalDegreePrefixCount w m + 1 := by simpa using Fintype.card_congr e
  have hKey := Finset.orderEmbOfFin_unique hCount (f := fun j =>
    historicalDegreeKey (normalWords w) (newLab j))
    (fun j => Finset.mem_image.mpr ⟨newLab j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMem j⟩, rfl⟩)
    hMono
  refine ⟨hCount, fun j => ?_⟩
  have hp := historicalDegreePrefixLabel_key (normalWords w) m (Fin.cast hCount.symm j)
  have hSame : ((historicalDegreePrefixKeys (normalWords w) m).orderIsoOfFin rfl
      (Fin.cast hCount.symm j)).val =
        (historicalDegreePrefixKeys (normalWords w) m).orderEmbOfFin hCount j := by
    rfl
  exact congrArg (fun key => (ofLex key).2) (hp.trans (hSame.trans (congrFun hKey j).symm))

private theorem frame_of_empty_labels {j : ℕ} (v : Fin j → CoordinateWord n)
    (G : Fin j → MvPowerSeries (Fin n) ℂ) (hv : IsEmpty (Fin j)) :
    (∀ q, Function.Bijective (historicalWholeJetMap v G q)) ∧
      ∀ d, Function.Bijective (historicalHomogeneousColumnMap v G d) := by
  have hWhole (q : ℕ) : historicalWholeJetMap v G q = LinearMap.id := by
    let := normalExponentFintype n q
    apply LinearMap.ext
    intro a
    funext b
    change (∑ β, a β * MvPowerSeries.coeff b.val (historicalWholeColumn v G β.val)) = a b
    have col (β) : historicalWholeColumn v G β = MvPowerSeries.monomial β 1 := by
      unfold historicalWholeColumn
      cases h : historicalOwner v β with
      | none => rfl
      | some i => exact (isEmptyElim i)
    simp only [col, MvPowerSeries.coeff_monomial, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      rw [if_neg (fun h => hc (Subtype.ext h.symm))]
    · simp
  refine ⟨fun q => hWhole q ▸ Function.bijective_id, fun d => ?_⟩
  rw [historicalHomogeneousColumnMap_eq_operator]
  exact historicalHomogeneousOperator_bijective v G (fun j => isEmptyElim j)
    (fun q => hWhole q ▸ Function.bijective_id) d

/-- The literal degree-sorted prefixes of the closed normal family preserve both
frames, including the cutoff zero where no positive-degree member is selected. -/
theorem historicalDegreePrefixFrames_closedNormal (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hPos : ∀ j, 0 < normalExponentDegree (wordExponent (w j)))
    (hg : ∀ j, g j ∈ genuineFormalVariables n ^ normalExponentDegree (wordExponent (w j)))
    (h : ∀ m, HistoricalDegreePrefixFrames w g m) (m : ℕ) :
    HistoricalDegreePrefixFrames (normalWords w) (normalFamily g) m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hEmpty : IsEmpty (Fin (historicalDegreePrefixCount (normalWords w) 0)) := by
      constructor
      intro i
      have hi := historicalDegreePrefixLabel_mem (normalWords w) 0 i
      generalize historicalDegreePrefixLabel (normalWords w) 0 i = l at hi
      refine Fin.cases ?_ (fun j h => ?_) l hi
      · change normalExponentDegree (wordExponent (normalWord n)) ≤ 0 → False
        rw [normalWord_degree]
        omega
      · rw [degree_normalWords_succ] at h
        exact (not_le_of_gt (hPos j)) h
    exact frame_of_empty_labels _ _ hEmpty
  · obtain ⟨hCount,hLabels⟩ := sortedPrefix_normalLabels w hPos hm
    let v := historicalDegreePrefixWords w m
    let G := fun j => g (historicalDegreePrefixLabel w m j)
    let v' := historicalDegreePrefixWords (normalWords w) m
    let G' := fun j => normalFamily g (historicalDegreePrefixLabel (normalWords w) m j)
    have hv : HEq (normalWords v) v' := by
      apply (Fin.heq_fun_iff hCount.symm).mpr
      intro j
      have hj := hLabels j
      change normalWords v j = normalWords w (historicalDegreePrefixLabel (normalWords w) m
        (Fin.cast hCount.symm j))
      rw [hj]
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl
    have hG : HEq (normalFamily G) G' := by
      apply (Fin.heq_fun_iff hCount.symm).mpr
      intro j
      have hj := hLabels j
      change normalFamily G j = normalFamily g (historicalDegreePrefixLabel (normalWords w) m
        (Fin.cast hCount.symm j))
      rw [hj]
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl
    have hFrames := historicalDegreePrefix_adjoinNormal w g m hg (h m)
    have transport {a b : ℕ} {A : Fin a → CoordinateWord (n+1)}
        {B : Fin b → CoordinateWord (n+1)}
        {I : Fin a → MvPowerSeries (Fin (n+1)) ℂ}
        {J : Fin b → MvPowerSeries (Fin (n+1)) ℂ}
        (he : a = b) (hA : HEq A B) (hI : HEq I J)
        (hAB : (∀ q, Function.Bijective (historicalWholeJetMap A I q)) ∧
          ∀ d, Function.Bijective (historicalHomogeneousColumnMap A I d)) :
        (∀ q, Function.Bijective (historicalWholeJetMap B J q)) ∧
          ∀ d, Function.Bijective (historicalHomogeneousColumnMap B J d) := by
      subst b
      cases hA
      cases hI
      exact hAB
    exact transport hCount.symm hv hG hFrames

#print axioms historicalWholeJetMap_closedNormal_bijective
#print axioms historicalDegreePrefixFrames_closedNormal

end
end Hironaka.HironakaG1ClosedNormalJet
