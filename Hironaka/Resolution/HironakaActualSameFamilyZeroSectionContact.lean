import Hironaka.Resolution.HironakaActualSameFamilyZeroSection
import Hironaka.Resolution.HironakaActualFixedInheritedSelector

/-! The same zero-section family retains the given selector and all selected contacts. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualSameFamilyZeroSectionContact
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualInheritedAnalyticBlockJacobian
  HironakaActualCanonicalBlockJacobian HironakaActualFixedInheritedSelector
  HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
  HironakaActualZeroSectionStabilization HironakaActualZeroSectionCanonicalFamily
  HironakaActualSameFamilyZeroSection HironakaActualRelativeNormalJetDivision
  HironakaActualAnalyticFormalNormalPowers HironakaActualRelativeTaylorCoefficients
  HironakaActualTaylorCoordinateNaturality HironakaActualAnalyticBlockGraphTranslation
  HironakaActualZeroSectionFormalBasis HironakaActualWeightedVertexSmallTails
  HironakaHolomorphicJetMonomialSpan

private theorem joined_add_tangent {n t : ℕ}
    (δ β : Fin n →₀ ℕ) (γ : Fin t →₀ ℕ) :
    actualJoinedExponent δ γ + actualJoinedExponent β (0 : Fin t →₀ ℕ) =
      actualJoinedExponent (δ + β) γ := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [actualJoinedExponent]

private theorem joined_factorial {n t : ℕ} (β : Fin n →₀ ℕ) (γ : Fin t →₀ ℕ) :
    actualExponentFactorial (actualJoinedExponent β γ) =
      actualExponentFactorial β * actualExponentFactorial γ := by
  simp [actualExponentFactorial, Fin.prod_univ_add, actualJoinedExponent]

private theorem formalMultiDerivative_tangent_rename (n t : ℕ)
    (β : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalMultiDerivative (actualJoinedExponent β (0 : Fin t →₀ ℕ))
        (MvPowerSeries.rename (Fin.castAdd t) F) =
      MvPowerSeries.rename (Fin.castAdd t) (actualFormalMultiDerivative β F) := by
  apply MvPowerSeries.ext
  intro a
  rw [← actualJoinedExponent_split a, coeff_actualFormalMultiDerivative,
    joined_add_tangent, coefficient_tangent_rename_joined,
    coefficient_tangent_rename_joined]
  by_cases h : actualNormalExponent a = 0
  · rw [if_pos h, if_pos h, h, joined_factorial, joined_factorial,
      coeff_actualFormalMultiDerivative]
    simp [actualExponentFactorial]
  · rw [if_neg h, if_neg h, zero_mul]

/-- Entire genuine higher derivatives commute with the dimension-changing tangent pullback. -/
theorem actualAnalyticMultiDerivative_tangentPullback (n t : ℕ)
    (β : Fin n →₀ ℕ) (F : HolGerm (ComplexModel n)) :
    actualAnalyticMultiDerivative (actualJoinedExponent β (0 : Fin t →₀ ℕ))
        (tangentPullback n t F) =
      tangentPullback n t (actualAnalyticMultiDerivative β F) := by
  apply actualUnshiftedTaylorAlgHom_injective (n+t)
  rw [actualTaylor_actualAnalyticMultiDerivative]
  have hleft := DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback n t) F
  have hright := DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback n t)
    (actualAnalyticMultiDerivative β F)
  change actualUnshiftedTaylorAlgHom (n+t) (tangentPullback n t F) =
    MvPowerSeries.rename (Fin.castAdd t) (actualUnshiftedTaylorAlgHom n F) at hleft
  change actualUnshiftedTaylorAlgHom (n+t)
      (tangentPullback n t (actualAnalyticMultiDerivative β F)) =
    MvPowerSeries.rename (Fin.castAdd t)
      (actualUnshiftedTaylorAlgHom n (actualAnalyticMultiDerivative β F)) at hright
  rw [hleft, hright, actualTaylor_actualAnalyticMultiDerivative,
    formalMultiDerivative_tangent_rename]

variable {n t : ℕ} (I : Ideal (HolGerm (ComplexModel n)))

private theorem old_label (a : ActualVertexIndex n I) :
    (originalZeroSectionVertexEquiv (t:=t) I (.inl a)).val =
      actualJoinedExponent a.val (0 : Fin t →₀ ℕ) := rfl

private theorem new_label (j : {_i : Fin t // analyticZeroTaylorIdeal n I ≠ ⊤}) :
    (originalZeroSectionVertexEquiv (t:=t) I (.inr j)).val =
      Finsupp.single (j.val.natAdd n) 1 := rfl

private theorem old_degree (a : ActualVertexIndex n I) :
    normalExponentDegree (originalZeroSectionVertexEquiv (t:=t) I (.inl a)).val =
      normalExponentDegree a.val := by
  rw [old_label]
  simp [normalExponentDegree, Fin.sum_univ_add, actualJoinedExponent]

private theorem new_degree (j : {_i : Fin t // analyticZeroTaylorIdeal n I ≠ ⊤}) :
    normalExponentDegree (originalZeroSectionVertexEquiv (t:=t) I (.inr j)).val = 1 := by
  rw [new_label]
  simp [normalExponentDegree]

private theorem cast_ne_normal (i : Fin n) (j : Fin t) : i.castAdd t ≠ j.natAdd n := by
  intro h
  have hv := congrArg (fun x : Fin (n+t) => x.val) h
  change i.val = n + j.val at hv
  omega

set_option backward.isDefEq.respectTransparency.types false in
private theorem essential_old_iff (i : Fin n) :
    i.castAdd t ∈ fixedSelectorEssential
        (actualInitialVertices MonomialOrder.degLex
          (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))) ↔
      i ∈ fixedSelectorEssential
        (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨a,rfl⟩ := (originalZeroSectionVertexEquiv (t:=t) I).surjective a
    cases a with
    | inl a =>
      refine ⟨a, ?_⟩
      change actualJoinedExponent a.val (0 : Fin t →₀ ℕ) (i.castAdd t) ≠ 0 at ha
      simpa [actualJoinedExponent] using ha
    | inr j =>
      exfalso
      apply ha
      change (Finsupp.single (j.val.natAdd n) 1 : Fin (n+t) →₀ ℕ) (i.castAdd t) = 0
      exact Finsupp.single_eq_of_ne (cast_ne_normal i j.val)
  · rintro ⟨a,ha⟩
    refine ⟨originalZeroSectionVertexEquiv (t:=t) I (.inl a), ?_⟩
    change actualJoinedExponent a.val (0 : Fin t →₀ ℕ) (i.castAdd t) ≠ 0
    simpa [actualJoinedExponent] using ha

set_option backward.isDefEq.respectTransparency.types false in
private theorem essential_new_iff (i : Fin t) :
    i.natAdd n ∈ fixedSelectorEssential
        (actualInitialVertices MonomialOrder.degLex
          (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))) ↔
      analyticZeroTaylorIdeal n I ≠ ⊤ := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨a,rfl⟩ := (originalZeroSectionVertexEquiv (t:=t) I).surjective a
    cases a with
    | inl a =>
      exfalso
      apply ha
      change actualJoinedExponent a.val (0 : Fin t →₀ ℕ) (i.natAdd n) = 0
      simp [actualJoinedExponent]
    | inr j => exact j.property
  · intro hK
    refine ⟨originalZeroSectionVertexEquiv (t:=t) I (.inr ⟨i,hK⟩), ?_⟩
    rw [new_label]
    simp

set_option backward.isDefEq.respectTransparency.types false in
private theorem block_old_iff (k : ℕ) (i : Fin n) :
    i.castAdd t ∈ fixedSelectorBlock
        (actualInitialVertices MonomialOrder.degLex
          (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))) k ↔
      i ∈ fixedSelectorBlock
        (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) k := by
  constructor
  · rintro ⟨a,hk,ha⟩
    obtain ⟨a,rfl⟩ := (originalZeroSectionVertexEquiv (t:=t) I).surjective a
    cases a with
    | inl a =>
      refine ⟨a, ?_, ?_⟩
      · rwa [old_degree] at hk
      · change actualJoinedExponent a.val (0 : Fin t →₀ ℕ) (i.castAdd t) ≠ 0 at ha
        simpa [actualJoinedExponent] using ha
    | inr j =>
      exfalso
      apply ha
      change (Finsupp.single (j.val.natAdd n) 1 : Fin (n+t) →₀ ℕ) (i.castAdd t) = 0
      exact Finsupp.single_eq_of_ne (cast_ne_normal i j.val)
  · rintro ⟨a,hk,ha⟩
    refine ⟨originalZeroSectionVertexEquiv (t:=t) I (.inl a), ?_, ?_⟩
    · rwa [old_degree]
    · change actualJoinedExponent a.val (0 : Fin t →₀ ℕ) (i.castAdd t) ≠ 0
      simpa [actualJoinedExponent] using ha

set_option backward.isDefEq.respectTransparency.types false in
private theorem block_new_iff (k : ℕ) (i : Fin t) :
    i.natAdd n ∈ fixedSelectorBlock
        (actualInitialVertices MonomialOrder.degLex
          (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))) k ↔
      analyticZeroTaylorIdeal n I ≠ ⊤ ∧ 1 ≤ k := by
  constructor
  · rintro ⟨a,hk,ha⟩
    obtain ⟨a,rfl⟩ := (originalZeroSectionVertexEquiv (t:=t) I).surjective a
    cases a with
    | inl a =>
      exfalso
      apply ha
      change actualJoinedExponent a.val (0 : Fin t →₀ ℕ) (i.natAdd n) = 0
      simp [actualJoinedExponent]
    | inr j => exact ⟨j.property, by rwa [new_degree] at hk⟩
  · rintro ⟨hK,hk⟩
    refine ⟨originalZeroSectionVertexEquiv (t:=t) I (.inr ⟨i,hK⟩), ?_, ?_⟩
    · rwa [new_degree]
    · rw [new_label]
      simp

private def liftedSelected
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (j : fixedSelectorEssential
      (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I)))) :
    actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I)) :=
  Fin.addCases
    (fun i hi => originalZeroSectionVertexEquiv (t:=t) I
      (.inl (S.selected ⟨i, (essential_old_iff I i).mp hi⟩)))
    (fun i hi => originalZeroSectionVertexEquiv (t:=t) I
      (.inr ⟨i, (essential_new_iff I i).mp hi⟩)) j.val j.property

set_option backward.isDefEq.respectTransparency.types false in
private def liftedSelector
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))) :
    ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))) where
  selected := liftedSelected I S
  positive := by
    rintro ⟨q,hq⟩
    revert hq
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) q
    · simp only [liftedSelected, Fin.addCases_left]
      change (originalZeroSectionVertexEquiv (t:=t) I
        (.inl (S.selected ⟨i,(essential_old_iff I i).mp hi⟩))).val (i.castAdd t) ≠ 0
      rw [old_label]
      simpa [actualJoinedExponent] using S.positive ⟨i,(essential_old_iff I i).mp hi⟩
    · simp only [liftedSelected, Fin.addCases_right]
      change (originalZeroSectionVertexEquiv (t:=t) I
        (.inr ⟨i,(essential_new_iff I i).mp hi⟩)).val (i.natAdd n) ≠ 0
      rw [new_label]
      simp
  least_degree := by
    rintro ⟨q,hq⟩ a ha
    obtain ⟨a,rfl⟩ := (originalZeroSectionVertexEquiv (t:=t) I).surjective a
    revert hq ha
    refine Fin.addCases (fun i hi ha => ?_) (fun i hi ha => ?_) q
    · simp only [liftedSelected, Fin.addCases_left]
      change normalExponentDegree
        (originalZeroSectionVertexEquiv (t:=t) I
          (.inl (S.selected ⟨i,(essential_old_iff I i).mp hi⟩))).val ≤ _
      rw [old_degree]
      cases a with
      | inl a =>
        rw [old_degree]
        apply S.least_degree ⟨i,(essential_old_iff I i).mp hi⟩ a
        change actualJoinedExponent a.val (0 : Fin t →₀ ℕ) (i.castAdd t) ≠ 0 at ha
        simpa [actualJoinedExponent] using ha
      | inr j =>
        exfalso
        apply ha
        change (Finsupp.single (j.val.natAdd n) 1 : Fin (n+t) →₀ ℕ) (i.castAdd t) = 0
        exact Finsupp.single_eq_of_ne (cast_ne_normal i j.val)
    · simp only [liftedSelected, Fin.addCases_right]
      change normalExponentDegree
        (originalZeroSectionVertexEquiv (t:=t) I
          (.inr ⟨i,(essential_new_iff I i).mp hi⟩)).val ≤ _
      rw [new_degree]
      cases a with
      | inl a =>
        exfalso
        apply ha
        change actualJoinedExponent a.val (0 : Fin t →₀ ℕ) (i.natAdd n) = 0
        simp [actualJoinedExponent]
      | inr j => rw [new_degree]

set_option backward.isDefEq.respectTransparency.types false in
private theorem liftedSelector_old
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (i : fixedSelectorEssential
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (j : fixedSelectorEssential
      (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))))
    (hj : j.val = i.val.castAdd t) :
    (liftedSelector I S).selected j =
      originalZeroSectionVertexEquiv (t:=t) I (.inl (S.selected i)) := by
  have he : j = ⟨i.val.castAdd t, (essential_old_iff I i.val).mpr i.property⟩ :=
    Subtype.ext hj
  subst j
  simp only [liftedSelector, liftedSelected, Fin.addCases_left]

set_option backward.isDefEq.respectTransparency.types false in
private theorem liftedSelector_new
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (j : fixedSelectorEssential
      (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))))
    (i : Fin t) (hj : j.val = i.natAdd n) :
    ∃ hK : analyticZeroTaylorIdeal n I ≠ ⊤,
      (liftedSelector I S).selected j =
        originalZeroSectionVertexEquiv (t:=t) I (.inr ⟨i,hK⟩) := by
  have hK : analyticZeroTaylorIdeal n I ≠ ⊤ :=
    (essential_new_iff I i).mp (hj ▸ j.property)
  refine ⟨hK, ?_⟩
  have he : j = ⟨i.natAdd n, (essential_new_iff I i).mpr hK⟩ := Subtype.ext hj
  subst j
  simp only [liftedSelector, liftedSelected, Fin.addCases_right]

set_option backward.isDefEq.respectTransparency.types false in
private theorem derivative_old
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (i : fixedSelectorEssential
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (j : fixedSelectorEssential
      (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))))
    (hj : j.val = i.val.castAdd t) :
    actualFixedSelectorDerivative (liftedSelector I S) (augmentedFamily (t:=t) I G).germs j =
      tangentPullback n t (actualFixedSelectorDerivative S G.germs i) := by
  have hb : fixedSelectorBeta (liftedSelector I S) j =
      actualJoinedExponent (fixedSelectorBeta S i) (0 : Fin t →₀ ℕ) := by
    unfold fixedSelectorBeta
    rw [liftedSelector_old I S i j hj, old_label, hj]
    ext q
    refine Fin.addCases (fun a => ?_) (fun a => ?_) q
    · by_cases ha : a = i.val
      · subst a
        simp [actualJoinedExponent, Finsupp.tsub_apply]
      · have he : a.castAdd t ≠ i.val.castAdd t := by
          intro h
          exact ha (Fin.ext (congrArg (fun x : Fin (n+t) => x.val) h))
        simp [actualJoinedExponent, Finsupp.tsub_apply,
          Finsupp.single_eq_of_ne ha, Finsupp.single_eq_of_ne he]
    · simp [actualJoinedExponent, Finsupp.tsub_apply]
  rw [actualFixedSelectorDerivative, hb, liftedSelector_old I S i j hj,
    augmentedFamily_lift I G (S.selected i), actualAnalyticMultiDerivative_tangentPullback]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem derivative_new
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (j : fixedSelectorEssential
      (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))))
    (i : Fin t) (hj : j.val = i.natAdd n) :
    ∃ hK : analyticZeroTaylorIdeal n I ≠ ⊤,
      (liftedSelector I S).selected j =
        originalZeroSectionVertexEquiv (t:=t) I (.inr ⟨i,hK⟩) ∧
      actualFixedSelectorDerivative (liftedSelector I S) (augmentedFamily (t:=t) I G).germs j =
        normalCoordinate n t i := by
  obtain ⟨hK,hs⟩ := liftedSelector_new I S j i hj
  refine ⟨hK, hs, ?_⟩
  have hb : fixedSelectorBeta (liftedSelector I S) j = 0 := by
    unfold fixedSelectorBeta
    rw [hs, new_label, hj, tsub_self]
  rw [actualFixedSelectorDerivative, hb, hs, augmentedFamily_normal I G hK i]
  apply actualUnshiftedTaylorAlgHom_injective (n+t)
  rw [actualTaylor_actualAnalyticMultiDerivative, actualFormalMultiDerivative_zero]

private theorem map_coordinateBlock_le (B : Set (Fin n)) (C : Set (Fin (n+t)))
    (hBC : ∀ i ∈ B, i.castAdd t ∈ C) :
    Ideal.map (tangentPullback n t).toRingHom (actualAnalyticCoordinateBlockIdeal B) ≤
      actualAnalyticCoordinateBlockIdeal C := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro g ⟨i,hi,rfl⟩
  change tangentPullback n t (coordinateGerm i) ∈ actualAnalyticCoordinateBlockIdeal C
  rw [tangentPullback_coordinateGerm]
  exact Ideal.subset_span ⟨i.castAdd t, hBC i hi, rfl⟩

private theorem liftedSelector_contact
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hContact : ∀ k, actualFixedSelectorContactAt S G.germs k) (k : ℕ) :
    actualFixedSelectorContactAt (liftedSelector (t:=t) I S)
      (augmentedFamily (t:=t) I G).germs k := by
  rintro ⟨q,hq⟩
  revert hq
  refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) q
  · let a : fixedSelectorBlock
        (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) k :=
      ⟨i,(block_old_iff I k i).mp hi⟩
    rw [derivative_old I G S (fixedSelectorBlockEssential k a) _ rfl]
    exact map_coordinateBlock_le _ _ (fun j hj => (block_old_iff I k j).mpr hj)
      (Ideal.mem_map_of_mem (tangentPullback n t).toRingHom (hContact k a))
  · obtain ⟨_,_,hd⟩ := derivative_new I G S
      (fixedSelectorBlockEssential k ⟨i.natAdd n,hi⟩) i rfl
    rw [hd]
    exact Ideal.subset_span ⟨i.natAdd n,hi,rfl⟩

/-- One transported selector retains every selected contact of the same augmented family. -/
theorem exists_augmentedFamily_selected_contact (n t : ℕ)
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hContact : ∀ k, actualFixedSelectorContactAt S G.germs k) :
    let V := actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)
    let Vplus := actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (n+t) (actualZeroSectionIdeal n t I))
    let e := originalZeroSectionVertexEquiv (t := t) I
    let Gplus := augmentedFamily (t := t) I G
    ∃ T : ActualFixedInheritedSelector Vplus,
      fixedSelectorEssential Vplus =
        {q | Fin.addCases (fun i => i ∈ fixedSelectorEssential V)
          (fun _ => analyticZeroTaylorIdeal n I ≠ ⊤) q} ∧
      (∀ k, fixedSelectorBlock Vplus k =
        {q | Fin.addCases (fun i => i ∈ fixedSelectorBlock V k)
          (fun _ => analyticZeroTaylorIdeal n I ≠ ⊤ ∧ 1 ≤ k) q}) ∧
      (∀ (i : fixedSelectorEssential V) (j : fixedSelectorEssential Vplus),
        j.val = i.val.castAdd t →
          T.selected j = e (.inl (S.selected i)) ∧
          actualFixedSelectorDerivative T Gplus.germs j =
            tangentPullback n t (actualFixedSelectorDerivative S G.germs i)) ∧
      (∀ (j : fixedSelectorEssential Vplus) (i : Fin t),
        j.val = i.natAdd n →
          ∃ hK : analyticZeroTaylorIdeal n I ≠ ⊤,
            T.selected j = e (.inr ⟨i,hK⟩) ∧
            actualFixedSelectorDerivative T Gplus.germs j = normalCoordinate n t i) ∧
      ∀ k, actualFixedSelectorContactAt T Gplus.germs k ∧
        (actualFixedSelectorJacobian T Gplus.germs k).det ≠ 0 := by
  dsimp only
  refine ⟨liftedSelector (t:=t) I S, ?_, ?_, ?_, ?_, ?_⟩
  · ext q
    refine Fin.addCases (fun i => ?_) (fun i => ?_) q
    · simpa only [Set.mem_ofPred_eq, Fin.addCases_left] using essential_old_iff (t:=t) I i
    · simpa only [Set.mem_ofPred_eq, Fin.addCases_right] using essential_new_iff I i
  · intro k
    ext q
    refine Fin.addCases (fun i => ?_) (fun i => ?_) q
    · simpa only [Set.mem_ofPred_eq, Fin.addCases_left] using block_old_iff (t:=t) I k i
    · simpa only [Set.mem_ofPred_eq, Fin.addCases_right] using block_new_iff I k i
  · intro i j hj
    exact ⟨liftedSelector_old I S i j hj, derivative_old I G S i j hj⟩
  · intro j i hj
    exact derivative_new I G S j i hj
  · intro k
    exact ⟨liftedSelector_contact I G S hContact k,
      actualFixedSelectorJacobian_det_ne_zero _ _
        (augmentedFamily (t:=t) I G).monic (augmentedFamily (t:=t) I G).lower k⟩

end
end Hironaka.HironakaActualSameFamilyZeroSectionContact
