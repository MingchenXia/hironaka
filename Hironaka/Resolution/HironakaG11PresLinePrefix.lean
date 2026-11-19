import Hironaka.Resolution.HironakaG11PresLineJet

/-!
# Adding a variable to the native five-law data: the degree-prefix frames (goal G11, step (3a-lines), part L1, law 3)

Law 3 of the native point presentation (`HironakaActualHistoricalPrefixJetFrames.HistoricalDegreePrefixFrames`): for every
degree cut-off `m`, the subfamily of members of degree `≤ m` has bijective whole jet maps at every level and bijective
homogeneous column maps in every degree. Under a new variable the subfamilies are the lifted subfamilies (degrees of words
are unchanged, so the degree keys are unchanged), the whole jet maps are handled by `HironakaG11PresLineJet`, and the
homogeneous column maps are block diagonal along the powers of the new variable exactly as the whole jet maps.

* `historicalDegreeKey_lift`, `historicalDegreePrefixKeys_lift`;
* **`historicalHomogeneousColumnMap_lift_bijective`**;
* **`historicalDegreePrefixFrames_lift`**: law 3 passes to the lifted words and the renamed family.

Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-line-state.tex`.
-/

set_option autoImplicit false

open Set Classical

namespace Hironaka.HironakaG11PresLinePrefix

noncomputable section

open HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalMonomialBasis HironakaG11PresLineFormal HironakaG11PresLineJet

variable {n k : ℕ}

/-- **Law 3, homogeneous part, under a new variable.** -/
theorem historicalHomogeneousColumnMap_lift_bijective (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (h : ∀ d, Function.Bijective (historicalHomogeneousColumnMap w g d))
    (d : ℕ) :
    Function.Bijective (historicalHomogeneousColumnMap (fun i => liftWord (w i))
      (fun i => MvPowerSeries.rename (Fin.castAdd 1) (g i)) d) := by
  classical
  let := homogeneousExponentFintype (n + 1) d
  set w' : Fin k → CoordinateWord (n + 1) := fun i => liftWord (w i) with hw'
  set g' : Fin k → MvPowerSeries (Fin (n + 1)) ℂ := fun i => MvPowerSeries.rename (Fin.castAdd 1) (g i) with hg'
  have hinj : Function.Injective (historicalHomogeneousColumnMap w' g' d) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
    funext β'
    set m := β'.val (Fin.last n) with hm
    have hdeg : normalExponentDegree (oldExp β'.val) + m = d := by
      rw [← normalExponentDegree_split, liftExp_oldExp_add]
      exact β'.property
    let := homogeneousExponentFintype n (d - m)
    let e : homogeneousExponentIndex n (d - m) → homogeneousExponentIndex (n + 1) d := fun β =>
      ⟨liftExp β.val + Finsupp.single (Fin.last n) m, by
        rw [normalExponentDegree_split]
        have := β.property
        omega⟩
    have he : Function.Injective e := fun a b hab =>
      Subtype.ext (split_injective (congrArg Subtype.val hab)).1
    let cm : homogeneousExponentIndex n (d - m) → ℂ := fun β => c (e β)
    have hcm : historicalHomogeneousColumnMap w g (d - m) cm = 0 := by
      funext α
      have hα : normalExponentDegree (liftExp α.val + Finsupp.single (Fin.last n) m) = d := by
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
            change normalExponentDegree (oldExp γ'.val) = d - m
            omega
          · change liftExp (oldExp γ'.val) + Finsupp.single (Fin.last n) m = γ'.val
            rw [← hγm]
            exact hsplit
        rw [← hsplit, hw', hg', historicalWholeColumn_split, coeff_split_mul_rename, if_neg (Ne.symm hne), mul_zero]
      · intro β
        change cm β * _ = c (e β) * MvPowerSeries.coeff (liftExp α.val + Finsupp.single (Fin.last n) m)
          (historicalWholeColumn w' g' (liftExp β.val + Finsupp.single (Fin.last n) m))
        rw [hw', hg', historicalWholeColumn_split, coeff_split_mul_rename, if_pos rfl]
    have hzero := (h (d - m)).1 (hcm.trans (map_zero _).symm)
    have hβ : β' = e ⟨oldExp β'.val, by omega⟩ :=
      Subtype.ext (liftExp_oldExp_add β'.val).symm
    rw [hβ]
    exact congrFun hzero _
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

theorem historicalDegreeKey_lift (w : Fin k → CoordinateWord n) :
    historicalDegreeKey (fun i => liftWord (w i)) = historicalDegreeKey w := by
  funext j
  simp only [historicalDegreeKey, wordExponent_liftWord, normalExponentDegree_liftExp]

/-- The degree keys (hence counts and labels) of the lifted words are those of the words. -/
theorem historicalDegreePrefixKeys_lift (w : Fin k → CoordinateWord n) (m : ℕ) :
    historicalDegreePrefixKeys (fun i => liftWord (w i)) m = historicalDegreePrefixKeys w m := by
  unfold historicalDegreePrefixKeys
  rw [historicalDegreeKey_lift]
  simp only [wordExponent_liftWord, normalExponentDegree_liftExp]

/-- Transport of a property of the ordered label enumeration along an equality of key sets. -/
private theorem of_keys_eq {K K' : Finset (Lex (ℕ × Fin k))} (hK : K = K')
    (P : ∀ L : Finset (Lex (ℕ × Fin k)), (Fin L.card → Fin k) → Prop)
    (h : P K (fun j => (ofLex (K.orderIsoOfFin rfl j).val).2)) :
    P K' (fun j => (ofLex (K'.orderIsoOfFin rfl j).val).2) := by
  subst hK
  exact h

/-- **Law 3 (degree-prefix frames) under a new variable.** -/
theorem historicalDegreePrefixFrames_lift (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (m : ℕ) (h : HistoricalDegreePrefixFrames w g m) :
    HistoricalDegreePrefixFrames (fun i => liftWord (w i)) (fun i => MvPowerSeries.rename (Fin.castAdd 1) (g i)) m := by
  obtain ⟨h1, h2⟩ := h
  exact of_keys_eq (historicalDegreePrefixKeys_lift w m).symm
    (fun L lab => (∀ q, Function.Bijective (historicalWholeJetMap (fun j => liftWord (w (lab j)))
        (fun j => MvPowerSeries.rename (Fin.castAdd 1) (g (lab j))) q)) ∧
      ∀ d, Function.Bijective (historicalHomogeneousColumnMap (fun j => liftWord (w (lab j)))
        (fun j => MvPowerSeries.rename (Fin.castAdd 1) (g (lab j))) d))
    ⟨fun q => historicalWholeJetMap_lift_bijective _ _ h1 q,
      fun d => historicalHomogeneousColumnMap_lift_bijective _ _ h2 d⟩

end

end Hironaka.HironakaG11PresLinePrefix
