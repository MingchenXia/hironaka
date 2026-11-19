import Hironaka.Resolution.HironakaActualRelativeStandardnessPivotPriority
import Hironaka.Resolution.HironakaActualFormalCoordinatePowerDivision
import Mathlib.GroupTheory.Perm.Fin

/-! A genuine stable move INSIDE the normal block, derived by a finite word of
accepted zero-vertex global pivots. The tangent block is fixed coordinate by
coordinate. Whole diagrams and the SAME canonical members are outputs. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualRelativeStandardnessNormalPivotPriority
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualRelativeStandardnessPivotPriority
variable {n : ℕ}

/-- q is the first normal coordinate; the shorter prefix consists of tangents. -/
def normalPivotEquiv (q f : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) :=
  (pivotFirstEquiv f).trans (pivotFirstEquiv q).symm

/-- The actual finite word repeatedly moves the SAME prefix endpoint to zero. -/
def prefixPivotWord (q : Fin (n + 1)) : ℕ → (Fin (n + 1) ≃ Fin (n + 1))
  | 0 => Equiv.refl _
  | k + 1 => (prefixPivotWord q k).trans (pivotFirstEquiv q)

private theorem pivotFirstEquiv_eq_cycleRange (f : Fin (n + 1)) :
    pivotFirstEquiv f = Fin.cycleRange f := by
  ext i
  by_cases hi : i = f
  · subst i
    simp only [pivotFirstEquiv, Equiv.trans_apply, finSuccEquiv'_at,
      finSuccEquiv_symm_none, Fin.cycleRange_self]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    simp only [pivotFirstEquiv, Equiv.trans_apply, finSuccEquiv'_succAbove,
      finSuccEquiv_symm_some, Fin.cycleRange_succAbove]

private theorem pivot_val (q i : Fin (n + 1)) :
    (pivotFirstEquiv q i).val = if i ≤ q then (i.val + 1) % (q.val + 1) else i.val := by
  rw [pivotFirstEquiv_eq_cycleRange]
  by_cases hi : i ≤ q
  · rw [if_pos hi, Fin.coe_cycleRange_of_le hi]
    by_cases hie : i = q
    · simp only [hie, ite_true, Nat.mod_self]
    · rw [if_neg hie, Nat.mod_eq_of_lt]
      have hlt : i.val < q.val := Fin.lt_def.mp (lt_of_le_of_ne hi hie)
      omega
  · rw [if_neg hi, Fin.cycleRange_of_gt (lt_of_not_ge hi)]

private theorem pivot_symm_val (q i : Fin (n + 1)) :
    ((pivotFirstEquiv q).symm i).val =
      if i = 0 then q.val else if i ≤ q then i.val - 1 else i.val := by
  rw [pivotFirstEquiv_eq_cycleRange]
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · simp only [Fin.cycleRange_symm_zero, if_true]
  · rw [Fin.cycleRange_symm_succ, if_neg (Fin.succ_ne_zero j)]
    by_cases hi : j.succ ≤ q
    · have hj : j.castSucc < q := by
        change j.val < q.val
        have h : j.val + 1 ≤ q.val := hi
        omega
      rw [if_pos hi, Fin.succAbove_of_castSucc_lt _ _ hj]
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_sub_cancel]
    · have hj : q ≤ j.castSucc := by
        change q.val ≤ j.val
        have h : q.val < j.val + 1 := lt_of_not_ge hi
        omega
      rw [if_neg hi, Fin.succAbove_of_le_castSucc _ _ hj]

private theorem prefixPivotWord_val (q : Fin (n + 1)) (k : ℕ) (i : Fin (n + 1)) :
    (prefixPivotWord q k i).val = if i ≤ q then (i.val + k) % (q.val + 1) else i.val := by
  induction k with
  | zero =>
    by_cases hi : i ≤ q
    · simp only [prefixPivotWord, Equiv.refl_apply, if_pos hi, add_zero]
      exact (Nat.mod_eq_of_lt (by have h := Fin.le_iff_val_le_val.mp hi; omega)).symm
    · simp only [prefixPivotWord, Equiv.refl_apply, if_neg hi]
  | succ k ih =>
    change (pivotFirstEquiv q (prefixPivotWord q k i)).val = _
    rw [pivot_val]
    by_cases hi : i ≤ q
    · have hcur : prefixPivotWord q k i ≤ q := by
        apply Fin.le_iff_val_le_val.mpr
        rw [ih, if_pos hi]
        exact Nat.lt_succ_iff.mp (Nat.mod_lt (i.val + k) (Nat.succ_pos q.val))
      rw [if_pos hcur, ih, if_pos hi, if_pos hi]
      simpa only [Nat.add_assoc] using (Nat.mod_add_mod (i.val + k) (q.val + 1) 1)
    · have hcur : ¬ prefixPivotWord q k i ≤ q := by
        intro h
        have hle := Fin.le_iff_val_le_val.mp h
        rw [ih, if_neg hi] at hle
        exact hi (Fin.le_iff_val_le_val.mpr hle)
      rw [if_neg hcur, ih, if_neg hi, if_neg hi]

private theorem prefixPivotWord_eq_inverse (q : Fin (n + 1)) :
    prefixPivotWord q q.val = (pivotFirstEquiv q).symm := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [prefixPivotWord_val, pivot_symm_val]
  by_cases hi0 : i = 0
  · subst i
    simp only [Fin.zero_le, if_true, Fin.val_zero, zero_add]
    exact Nat.mod_eq_of_lt (Nat.lt_succ_self _)
  · rw [if_neg hi0]
    by_cases hi : i ≤ q
    · simp only [if_pos hi]
      have hip : 0 < i.val := Fin.val_pos_iff.mpr (Fin.pos_of_ne_zero hi0)
      have he : i.val + q.val = (i.val - 1) + (q.val + 1) := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt]
      have hle := Fin.le_iff_val_le_val.mp hi
      omega
    · simp only [if_neg hi]

/-- Exactly q.val repeated actual zero-prefix pivots restore all tangents. -/
theorem normalPivotEquiv_eq_pivot_word (q f : Fin (n + 1)) :
    normalPivotEquiv q f = (pivotFirstEquiv f).trans (prefixPivotWord q q.val) := by
  rw [prefixPivotWord_eq_inverse]
  rfl

private theorem normalPivotEquiv_val (q f : Fin (n + 1)) (hqf : q ≤ f) (i : Fin (n + 1)) :
    (normalPivotEquiv q f i).val =
      if i < q then i.val else if i = f then q.val else if i < f then i.val + 1 else i.val := by
  change ((pivotFirstEquiv q).symm (pivotFirstEquiv f i)).val = _
  rw [pivot_symm_val, pivotFirstEquiv_eq_cycleRange]
  by_cases hif : i = f
  · subst i
    simp only [Fin.cycleRange_self, if_true, lt_irrefl, if_false,
      not_lt_of_ge hqf, Fin.val_zero]
  · have hnot0 : Fin.cycleRange f i ≠ 0 := by
      intro h
      exact hif ((Fin.cycleRange f).injective (h.trans (Fin.cycleRange_self f).symm))
    rw [if_neg hnot0, if_neg hif]
    by_cases hiq : i < q
    · have hiflt : i < f := hiq.trans_le hqf
      have hc : (Fin.cycleRange f i).val = i.val + 1 := Fin.coe_cycleRange_of_lt hiflt
      have hle : Fin.cycleRange f i ≤ q := Fin.le_iff_val_le_val.mpr (by
        rw [hc]; have h := Fin.lt_def.mp hiq; omega)
      rw [if_pos hiq, if_pos hle, hc, Nat.add_sub_cancel]
    · rw [if_neg hiq]
      by_cases hiflt : i < f
      · have hc : (Fin.cycleRange f i).val = i.val + 1 := Fin.coe_cycleRange_of_lt hiflt
        have hle : ¬ Fin.cycleRange f i ≤ q := by
          intro h
          have h1 := Fin.le_iff_val_le_val.mp h
          have h2 := Fin.le_iff_val_le_val.mp (le_of_not_gt hiq)
          rw [hc] at h1
          omega
        rw [if_neg hle, if_pos hiflt, hc]
      · have hfi : f < i := lt_of_le_of_ne (le_of_not_gt hiflt) (Ne.symm hif)
        have hqi : q < i := hqf.trans_lt hfi
        rw [Fin.cycleRange_of_gt hfi, if_neg (not_le_of_gt hqi), if_neg hiflt]

/-- EVERY tangent coordinate is literally fixed. -/
theorem normalPivotEquiv_tangent (q f : Fin (n + 1)) (hqf : q ≤ f)
    (i : Fin (n + 1)) (hi : i < q) : normalPivotEquiv q f i = i := by
  apply Fin.ext
  rw [normalPivotEquiv_val q f hqf, if_pos hi]

/-- The selected normal pivot goes to the first NORMAL coordinate, q. -/
theorem normalPivotEquiv_pivot (q f : Fin (n + 1)) (hqf : q ≤ f) :
    normalPivotEquiv q f f = q := by
  apply Fin.ext
  rw [normalPivotEquiv_val q f hqf, if_neg (not_lt_of_ge hqf), if_pos rfl]

/-- All other normal coordinates keep their actual relative order. -/
theorem normalPivotEquiv_normal_order (q f : Fin (n + 1)) (hqf : q ≤ f)
    (i j : Fin (n + 1)) (hi : q ≤ i) (hj : q ≤ j) (hif : i ≠ f) (hjf : j ≠ f)
    (hij : i < j) : normalPivotEquiv q f i < normalPivotEquiv q f j := by
  apply Fin.lt_def.mpr
  rw [normalPivotEquiv_val q f hqf, normalPivotEquiv_val q f hqf,
    if_neg (not_lt_of_ge hi), if_neg (not_lt_of_ge hj), if_neg hif, if_neg hjf]
  have hi' := Fin.le_iff_val_le_val.mp hi
  have hj' := Fin.le_iff_val_le_val.mp hj
  have hij' := Fin.lt_def.mp hij
  have hif' : i.val ≠ f.val := by intro h; exact hif (Fin.ext h)
  have hjf' : j.val ≠ f.val := by intro h; exact hjf (Fin.ext h)
  split_ifs <;> simp_all only [Fin.lt_def] <;> omega

private theorem permute_apply (p : Fin (n + 1) ≃ Fin (n + 1))
    (α : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) : Finsupp.domCongr p α i = α (p.symm i) := by
  simp only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_equiv_apply]

private theorem permute_trans (p r : Fin (n + 1) ≃ Fin (n + 1)) (α : Fin (n + 1) →₀ ℕ) :
    Finsupp.domCongr (p.trans r) α = Finsupp.domCongr r (Finsupp.domCongr p α) := by
  exact congrArg (fun E : (Fin (n + 1) →₀ ℕ) ≃+ _ => E α) (Finsupp.domCongr_trans p r).symm

private theorem map_rename_trans (p r : Fin (n + 1) ≃ Fin (n + 1))
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) :
    Ideal.map (MvPowerSeries.rename (p.trans r)).toRingHom K =
      Ideal.map (MvPowerSeries.rename r).toRingHom (Ideal.map (MvPowerSeries.rename p).toRingHom K) := by
  rw [Ideal.map_map]
  apply congrArg (fun h => Ideal.map h K)
  apply RingHom.ext
  intro F
  exact (MvPowerSeries.rename_rename p r F).symm

private theorem rename_refl_map (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) :
    Ideal.map (MvPowerSeries.rename (Equiv.refl (Fin (n + 1)))).toRingHom K = K := by
  have h : (MvPowerSeries.rename (R := ℂ) (Equiv.refl (Fin (n + 1)))).toRingHom = RingHom.id _ := by
    apply RingHom.ext
    intro F
    exact MvPowerSeries.rename_id_apply F
  rw [h, Ideal.map_id]

private theorem prefix_zero_after_pivot
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q : Fin (n + 1))
    (hP : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i ≤ q, a.val i = 0) :
    ∀ a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (pivotFirstRename q).toRingHom K), ∀ i ≤ q, a.val i = 0 := by
  intro a i hi
  have hq : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val q = 0 := fun a => hP a q le_rfl
  obtain ⟨a, rfl⟩ := pivotFirstVertex_surjective K q hq a
  change Finsupp.domCongr (pivotFirstEquiv q) a.val i = 0
  rw [permute_apply]
  apply hP a
  apply Fin.le_iff_val_le_val.mpr
  rw [pivot_symm_val]
  by_cases hi0 : i = 0
  · rw [if_pos hi0]
  · rw [if_neg hi0, if_pos hi]
    have h := Fin.le_iff_val_le_val.mp hi
    omega

private theorem prefix_word_zero
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q : Fin (n + 1))
    (hP : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i ≤ q, a.val i = 0) (k : ℕ) :
    ∀ a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (MvPowerSeries.rename (prefixPivotWord q k)).toRingHom K), ∀ i ≤ q, a.val i = 0 := by
  induction k with
  | zero =>
    change ∀ a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (MvPowerSeries.rename (Equiv.refl (Fin (n + 1)))).toRingHom K), ∀ i ≤ q, a.val i = 0
    rw [rename_refl_map]
    exact hP
  | succ k ih =>
    rw [prefixPivotWord, map_rename_trans]
    exact prefix_zero_after_pivot _ q ih

private theorem prefix_word_diagram
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q : Fin (n + 1))
    (hP : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i ≤ q, a.val i = 0) (k : ℕ) :
    actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (MvPowerSeries.rename (prefixPivotWord q k)).toRingHom K) =
      Finsupp.domCongr (prefixPivotWord q k) '' actualInitialDiagram MonomialOrder.degLex K := by
  induction k with
  | zero =>
    rw [prefixPivotWord, rename_refl_map, Finsupp.domCongr_refl]
    change actualInitialDiagram MonomialOrder.degLex K = id '' actualInitialDiagram MonomialOrder.degLex K
    exact (Set.image_id _).symm
  | succ k ih =>
    have hz : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (MvPowerSeries.rename (prefixPivotWord q k)).toRingHom K), a.val q = 0 :=
      fun a => prefix_word_zero K q hP k a q le_rfl
    rw [prefixPivotWord, map_rename_trans]
    change actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (pivotFirstRename q).toRingHom
        (Ideal.map (MvPowerSeries.rename (prefixPivotWord q k)).toRingHom K)) = _
    rw [actualInitialDiagram_pivotFirst _ q hz, ih, Set.image_image]
    apply congrArg (fun E => E '' actualInitialDiagram MonomialOrder.degLex K)
    funext α
    exact (permute_trans (prefixPivotWord q k) (pivotFirstEquiv q) α).symm

/-- Actual entire normal coordinate renaming, with tangents fixed. -/
def normalPivotRename (q f : Fin (n + 1)) :
    MvPowerSeries (Fin (n + 1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (n + 1)) ℂ :=
  MvPowerSeries.rename (normalPivotEquiv q f)

/-- Only original tangent-zero and pivot-zero vertices are inputs. EVERY
intermediate zero-pivot premise and the final WHOLE diagram are produced. -/
theorem actualInitialDiagram_normalPivot
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q f : Fin (n + 1)) (hqf : q ≤ f)
    (hT : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i < q, a.val i = 0)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0) :
    actualInitialDiagram MonomialOrder.degLex (Ideal.map (normalPivotRename q f).toRingHom K) =
      Finsupp.domCongr (normalPivotEquiv q f) '' actualInitialDiagram MonomialOrder.degLex K := by
  let K1 := Ideal.map (pivotFirstRename f).toRingHom K
  have hP : ∀ a : actualInitialVertices MonomialOrder.degLex K1, ∀ i ≤ q, a.val i = 0 := by
    intro a i hi
    obtain ⟨a, rfl⟩ := pivotFirstVertex_surjective K f hf a
    change Finsupp.domCongr (pivotFirstEquiv f) a.val i = 0
    rw [permute_apply]
    obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · rw [pivotFirstEquiv_eq_cycleRange, Fin.cycleRange_symm_zero]
      exact hf a
    · rw [pivotFirstEquiv_eq_cycleRange, Fin.cycleRange_symm_succ]
      have hjq : j.castSucc < q := by
        change j.val < q.val
        have h : j.val + 1 ≤ q.val := hi
        omega
      have hjf : j.castSucc < f := hjq.trans_le hqf
      rw [Fin.succAbove_of_castSucc_lt _ _ hjf]
      exact hT a j.castSucc hjq
  have hm : Ideal.map (normalPivotRename q f).toRingHom K =
      Ideal.map (MvPowerSeries.rename (prefixPivotWord q q.val)).toRingHom K1 := by
    change Ideal.map (MvPowerSeries.rename (normalPivotEquiv q f)).toRingHom K = _
    rw [normalPivotEquiv_eq_pivot_word, map_rename_trans]
    rfl
  rw [hm, prefix_word_diagram K1 q hP q.val,
    actualInitialDiagram_pivotFirst K f hf, Set.image_image]
  apply congrArg (fun E => E '' actualInitialDiagram MonomialOrder.degLex K)
  funext α
  rw [normalPivotEquiv_eq_pivot_word]
  exact (permute_trans (pivotFirstEquiv f) (prefixPivotWord q q.val) α).symm

private theorem permute_le_iff (p : Fin (n + 1) ≃ Fin (n + 1))
    (α β : Fin (n + 1) →₀ ℕ) : Finsupp.domCongr p α ≤ Finsupp.domCongr p β ↔ α ≤ β := by
  constructor
  · intro h i
    have hi := h (p i)
    simpa only [permute_apply, Equiv.symm_apply_apply] using hi
  · intro h i
    simp only [permute_apply]
    exact h (p.symm i)

/-- The SAME literal exponent label, with minimality proved from the produced
whole diagram equality rather than a target monicness assumption. -/
def normalPivotVertex
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q f : Fin (n + 1)) (hqf : q ≤ f)
    (hT : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i < q, a.val i = 0)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualInitialVertices MonomialOrder.degLex (Ideal.map (normalPivotRename q f).toRingHom K) :=
  ⟨Finsupp.domCongr (normalPivotEquiv q f) a.val, by
    have ha : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) a.val := by
      simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.property
    have hm : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (normalPivotRename q f).toRingHom K))
          (Finsupp.domCongr (normalPivotEquiv q f) a.val) := by
      constructor
      · rw [actualInitialDiagram_normalPivot K q f hqf hT hf]
        exact ⟨a.val, ha.prop, rfl⟩
      · intro γ hγ hle
        rw [actualInitialDiagram_normalPivot K q f hqf hT hf] at hγ
        obtain ⟨β, hβ, rfl⟩ := hγ
        have hβa := (permute_le_iff (normalPivotEquiv q f) β a.val).mp hle
        exact (permute_le_iff (normalPivotEquiv q f) a.val β).mpr (ha.2 hβ hβa)
    simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hm⟩

/-- No new canonical labels are lost. -/
theorem normalPivotVertex_surjective
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q f : Fin (n + 1)) (hqf : q ≤ f)
    (hT : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i < q, a.val i = 0)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0) :
    Function.Surjective (normalPivotVertex K q f hqf hT hf) := by
  intro b
  have hb : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (normalPivotRename q f).toRingHom K)) b.val := by
    simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using b.property
  have hbD := hb.prop
  rw [actualInitialDiagram_normalPivot K q f hqf hT hf] at hbD
  obtain ⟨α, hα, hαb⟩ := hbD
  have hm : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) α := by
    refine ⟨hα, ?_⟩
    intro β hβ hβα
    have hEβ : Finsupp.domCongr (normalPivotEquiv q f) β ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (normalPivotRename q f).toRingHom K) := by
      rw [actualInitialDiagram_normalPivot K q f hqf hT hf]
      exact ⟨β, hβ, rfl⟩
    have hle : Finsupp.domCongr (normalPivotEquiv q f) β ≤ b.val := by
      rw [← hαb]
      exact (permute_le_iff (normalPivotEquiv q f) β α).mpr hβα
    have hback := hb.2 hEβ hle
    rw [← hαb] at hback
    exact (permute_le_iff (normalPivotEquiv q f) α β).mp hback
  let a : actualInitialVertices MonomialOrder.degLex K :=
    ⟨α, by simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hm⟩
  exact ⟨a, Subtype.ext hαb⟩

private theorem coeff_rename_permuted (p : Fin (n + 1) ≃ Fin (n + 1))
    (F : MvPowerSeries (Fin (n + 1)) ℂ) (α : Fin (n + 1) →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.domCongr p α) (MvPowerSeries.rename p F) = MvPowerSeries.coeff α F := by
  simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding] using
    MvPowerSeries.coeff_embDomain_rename p.toEmbedding F α

/-- Whole canonical uniqueness identifies the SAME old member after the real
normal-only coordinate permutation. -/
theorem normalPivot_actualReducedVertexSeries
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q f : Fin (n + 1)) (hqf : q ≤ f)
    (hT : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i < q, a.val i = 0)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    normalPivotRename q f (actualReducedVertexSeries MonomialOrder.degLex K a) =
      actualReducedVertexSeries MonomialOrder.degLex (Ideal.map (normalPivotRename q f).toRingHom K)
        (normalPivotVertex K q f hqf hT hf a) := by
  apply actualReducedVertexSeries_unique MonomialOrder.degLex
    (Ideal.map (normalPivotRename q f).toRingHom K) (normalPivotVertex K q f hqf hT hf a) _
    (Ideal.mem_map_of_mem _ (actualReducedVertexSeries_mem MonomialOrder.degLex K a))
  intro γ hγ
  rw [actualInitialDiagram_normalPivot K q f hqf hT hf] at hγ
  obtain ⟨β, hβ, rfl⟩ := hγ
  change MvPowerSeries.coeff (Finsupp.domCongr (normalPivotEquiv q f) β)
      (MvPowerSeries.rename (normalPivotEquiv q f) (actualReducedVertexSeries MonomialOrder.degLex K a)) =
        if Finsupp.domCongr (normalPivotEquiv q f) β = Finsupp.domCongr (normalPivotEquiv q f) a.val then 1 else 0
  rw [coeff_rename_permuted, actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex K a β hβ]
  simp only [EquivLike.apply_eq_iff_eq]

/-- The literal normal tail of the finite coordinate set. -/
def normalPivotVariables (q : Fin (n + 1)) : Set (Fin (n + 1)) := {i | q ≤ i}

private theorem normal_mem_iff (q f : Fin (n + 1)) (hqf : q ≤ f) (i : Fin (n + 1)) :
    q ≤ normalPivotEquiv q f i ↔ q ≤ i := by
  constructor
  · intro hi
    by_contra h
    have ht := normalPivotEquiv_tangent q f hqf i (lt_of_not_ge h)
    rw [ht] at hi
    exact h hi
  · intro hi
    apply Fin.le_iff_val_le_val.mpr
    rw [normalPivotEquiv_val q f hqf, if_neg (not_lt_of_ge hi)]
    have hiv := Fin.le_iff_val_le_val.mp hi
    split_ifs <;> omega

/-- The entire selected normal centre is fixed; every tangent is fixed as an
individual coordinate, not scaled as in a point chart. -/
theorem map_normalIdeal_normalPivot (q f : Fin (n + 1)) (hqf : q ≤ f) :
    Ideal.map (normalPivotRename q f).toRingHom (actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q)) =
      actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) := by
  apply le_antisymm
  · rw [actualFormalCoordinateIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro F ⟨G, ⟨i, hi, rfl⟩, rfl⟩
    change MvPowerSeries.rename (normalPivotEquiv q f) (MvPowerSeries.X i) ∈ _
    rw [MvPowerSeries.rename_X]
    exact Ideal.subset_span ⟨normalPivotEquiv q f i, (normal_mem_iff q f hqf i).mpr hi, rfl⟩
  · apply Ideal.span_le.mpr
    rintro F ⟨i, hi, rfl⟩
    let j := (normalPivotEquiv q f).symm i
    have hj : j ∈ normalPivotVariables q := (normal_mem_iff q f hqf j).mp (by
      change q ≤ i at hi
      simpa only [j, Equiv.apply_symm_apply] using hi)
    have hm := Ideal.mem_map_of_mem (normalPivotRename q f).toRingHom
      (Ideal.subset_span (show MvPowerSeries.X j ∈ MvPowerSeries.X '' normalPivotVariables q from ⟨j, hj, rfl⟩))
    change MvPowerSeries.rename (normalPivotEquiv q f) (MvPowerSeries.X j) ∈ _ at hm
    change MvPowerSeries.X i ∈ Ideal.map (normalPivotRename q f).toRingHom
      (actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q))
    simpa only [actualFormalCoordinateIdeal, MvPowerSeries.rename_X, j,
      Equiv.apply_symm_apply] using hm

private theorem mem_power_iff_rename (p : Fin (n + 1) ≃ Fin (n + 1))
    (I : Ideal (MvPowerSeries (Fin (n + 1)) ℂ))
    (hI : Ideal.map (MvPowerSeries.rename p).toRingHom I = I)
    (k : ℕ) (F : MvPowerSeries (Fin (n + 1)) ℂ) :
    F ∈ I ^ k ↔ MvPowerSeries.rename p F ∈ I ^ k := by
  have hPow : Ideal.map (MvPowerSeries.rename p).toRingHom (I ^ k) = I ^ k := by
    rw [Ideal.map_pow, hI]
  constructor
  · intro hF
    have hm := Ideal.mem_map_of_mem (MvPowerSeries.rename p).toRingHom hF
    rwa [hPow] at hm
  · intro hF
    rw [← hPow] at hF
    obtain ⟨G, hG, he⟩ := (Ideal.mem_map_iff_of_surjective (MvPowerSeries.rename p).toRingHom
      (MvPowerSeries.renameEquiv ℂ p).surjective).mp hF
    have hGF : G = F := (MvPowerSeries.renameEquiv ℂ p).injective he
    rwa [hGF] at hG

/-- Both whole actual normal-power directions, including power zero. -/
theorem mem_normal_power_iff_normalPivot (q f : Fin (n + 1)) (hqf : q ≤ f)
    (k : ℕ) (F : MvPowerSeries (Fin (n + 1)) ℂ) :
    F ∈ actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^ k ↔
      normalPivotRename q f F ∈ actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^ k :=
  mem_power_iff_rename (normalPivotEquiv q f) _ (map_normalIdeal_normalPivot q f hqf) k F

/-- Every SAME entire series retains all its actual total-order bounds. -/
theorem mem_variables_power_iff_normalPivot (q f : Fin (n + 1))
    (k : ℕ) (F : MvPowerSeries (Fin (n + 1)) ℂ) :
    F ∈ genuineFormalVariables (n + 1) ^ k ↔ normalPivotRename q f F ∈ genuineFormalVariables (n + 1) ^ k :=
  mem_power_iff_rename (normalPivotEquiv q f) _ (map_genuineFormalVariables_rename (normalPivotEquiv q f)) k F

/-- Every actual renamed vertex retains the unchanged tangent-zero block. -/
theorem normalPivotVertex_tangent
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q f : Fin (n + 1)) (hqf : q ≤ f)
    (hT : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i < q, a.val i = 0)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) (i : Fin (n + 1)) (hi : i < q) :
    (normalPivotVertex K q f hqf hT hf a).val i = 0 := by
  change Finsupp.domCongr (normalPivotEquiv q f) a.val i = 0
  rw [permute_apply]
  have hs : (normalPivotEquiv q f).symm i = i := by
    have h := congrArg (normalPivotEquiv q f).symm (normalPivotEquiv_tangent q f hqf i hi)
    have he : i = (normalPivotEquiv q f).symm i := by simpa only [Equiv.symm_apply_apply] using h
    exact he.symm
  rw [hs]
  exact hT a i hi

/-- The SAME actual renamed vertex is transverse to the first normal pivot. -/
theorem normalPivotVertex_pivot
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q f : Fin (n + 1)) (hqf : q ≤ f)
    (hT : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i < q, a.val i = 0)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    (normalPivotVertex K q f hqf hT hf a).val q = 0 := by
  change Finsupp.domCongr (normalPivotEquiv q f) a.val q = 0
  rw [permute_apply]
  have hs : (normalPivotEquiv q f).symm q = f := by
    apply (normalPivotEquiv q f).injective
    rw [Equiv.apply_symm_apply, normalPivotEquiv_pivot q f hqf]
  rw [hs]
  exact hf a

private theorem normal_weight_eq_degree (q : Fin (n + 1)) (α : Fin (n + 1) →₀ ℕ)
    (hα : ∀ i < q, α i = 0) :
    Finsupp.weight (actualCoordinateWeight (normalPivotVariables q)) α = normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q ≤ i
  · have hmem : i ∈ normalPivotVariables q := hi
    rw [actualCoordinateWeight, if_pos hmem, smul_eq_mul, mul_one]
  · rw [hα i (lt_of_not_ge hi)]
    exact zero_smul _ _

private theorem permute_degree (p : Fin (n + 1) ≃ Fin (n + 1)) (α : Fin (n + 1) →₀ ℕ) :
    normalExponentDegree (Finsupp.domCongr p α) = normalExponentDegree α := by
  simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    normalExponentDegree, ← Finsupp.degree_eq_sum] using Finsupp.degree_mapDomain p α

/-- Source canonical normal powers transfer to EVERY new actual vertex of the
SAME permuted family with its original mark. No target power is assumed. -/
theorem normalPivot_reduced_vertex_normal_powers
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q f : Fin (n + 1)) (hqf : q ≤ f)
    (hT : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i < q, a.val i = 0)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈
        actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^
          Finsupp.weight (actualCoordinateWeight (normalPivotVariables q)) a.val) :
    ∀ b : actualInitialVertices MonomialOrder.degLex (Ideal.map (normalPivotRename q f).toRingHom K),
      actualReducedVertexSeries MonomialOrder.degLex (Ideal.map (normalPivotRename q f).toRingHom K) b ∈
        actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^
          Finsupp.weight (actualCoordinateWeight (normalPivotVariables q)) b.val := by
  intro b
  obtain ⟨a, rfl⟩ := normalPivotVertex_surjective K q f hqf hT hf b
  have hmark : Finsupp.weight (actualCoordinateWeight (normalPivotVariables q))
      (normalPivotVertex K q f hqf hT hf a).val =
        Finsupp.weight (actualCoordinateWeight (normalPivotVariables q)) a.val := by
    rw [normal_weight_eq_degree q _ (normalPivotVertex_tangent K q f hqf hT hf a),
      normal_weight_eq_degree q a.val (hT a)]
    exact permute_degree (normalPivotEquiv q f) a.val
  rw [hmark, ← normalPivot_actualReducedVertexSeries K q f hqf hT hf a]
  exact (mem_normal_power_iff_normalPivot q f hqf _ _).mp (hV a)

end
end Hironaka.HironakaActualRelativeStandardnessNormalPivotPriority
