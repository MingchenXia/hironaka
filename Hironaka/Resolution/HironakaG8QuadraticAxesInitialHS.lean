import Hironaka.Resolution.HironakaG8QuadraticAxesRecoding
import Hironaka.Resolution.HironakaActualDiagramStrictHSDrop
import Hironaka.Resolution.HironakaActualPointGeometricBennett
import Hironaka.Resolution.HironakaActualHistoricalCentreFilteredDivision

/-! Exact first Hilbert--Samuel distinction at the original quadratic tie. -/
set_option autoImplicit false
open Set Filter
open scoped Topology MonomialOrder
namespace Hironaka.HironakaG8QuadraticAxesInitialHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HolGerm OkaRelationSheaf HironakaRelativeNormalCoherentSaturation HironakaG8QuadraticAxesRecoding HironakaHolomorphicJetMonomialSpan
  HironakaActualFormalInitialDiagram HironakaActualFormalStandardMonomialHS
  HironakaActualOriginalFormalHSTransfer HironakaActualUnshiftedInitialHSTransfer
  HironakaActualDiagramStrictHSDrop HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualHistoricalCentreFilteredDivision
  HironakaRelativeNormalActualBaseJetDimension HironakaHolomorphicPointJets
  HironakaRelativeNormalDeformationInitialRelations HironakaActualPointGeometricBennett
  HironakaActualPrincipalHSFormula HironakaHolomorphicJetChartInvariance
  HironakaActualCoherentWeightedCoefficientMarked RelativePrincipalizationSpan
  HironakaActualOriginalFormalTaylor

abbrev R := HolGerm (ComplexModel 3)
abbrev F := MvPowerSeries (Fin 3) ℂ
abbrev τ := actualUnshiftedTaylorAlgHom 3

def axisGerm (i : Fin 3) : R := coordinateGerm (axesI i) * coordinateGerm (axesJ i)
def quadGerm : R := coordinateGerm (0 : Fin 3) * coordinateGerm 1 +
  coordinateGerm 2 * coordinateGerm 2

private def cross (i j : Fin 3) : Fin 3 →₀ ℕ := Finsupp.single i 1 + Finsupp.single j 1

private theorem crossDegree (i j : Fin 3) : normalExponentDegree (cross i j) = 2 := by
  simp [cross,normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib,Finsupp.single_apply]

private theorem crossTaylor (i j : Fin 3) :
    τ (coordinateGerm i * coordinateGerm j) = MvPowerSeries.monomial (cross i j) 1 := by
  rw [map_mul,actualUnshiftedTaylor_coordinate,actualUnshiftedTaylor_coordinate]
  change MvPowerSeries.monomial (Finsupp.single i 1) (1 : ℂ) *
    MvPowerSeries.monomial (Finsupp.single j 1) 1 = _
  rw [MvPowerSeries.monomial_mul_monomial,one_mul]
  rfl

private theorem coordHol (i : Fin 3) : HolAt (coord i) 0 :=
  Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt

private theorem axisRep (i : Fin 3) :
    axisGerm i = HolGerm.mk (axesFunction i) ((coordHol (axesI i)).mul (coordHol (axesJ i))) :=
  (HolGerm.mk_mul _ _ (coordHol (axesI i)) (coordHol (axesJ i))).symm

private theorem quadRep :
    quadGerm = HolGerm.mk quadFunction (((coordHol 0).mul (coordHol 1)).add ((coordHol 2).mul (coordHol 2))) := by
  unfold quadGerm coordinateGerm
  rw [← HolGerm.mk_mul,← HolGerm.mk_mul,← HolGerm.mk_add]
  rfl

private theorem origin_eq_span {m : ℕ} (s : Fin m → ComplexModel 3 → ℂ)
    (hI : (finiteFunctionIdeal (n := 3) s).IsCoherent) (hS : ∀ i, HolAt (s i) 0) :
    originalCoherentOriginIdeal (finiteFunctionIdeal (n := 3) s) =
      Ideal.span (range (fun i => HolGerm.mk (s i) (hS i))) := by
  ext g
  obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
  rw [mk_mem_originalCoherentOriginIdeal_iff _ hI hf]
  exact EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span s hS hf

theorem axes_origin :
    originalCoherentOriginIdeal axesIdeal = Ideal.span (range axisGerm) := by
  unfold axesIdeal
  rw [origin_eq_span axesFunction axesCoherent
    (fun i => (coordHol (axesI i)).mul (coordHol (axesJ i)))]
  rfl

theorem quad_origin :
    originalCoherentOriginIdeal quadIdeal = Ideal.span {quadGerm} := by
  unfold quadIdeal
  rw [origin_eq_span (fun _ : Fin 1 => quadFunction) quadCoherent
    (fun _ => ((coordHol 0).mul (coordHol 1)).add ((coordHol 2).mul (coordHol 2)))]
  rw [← quadRep]
  simp

private theorem lowCross (i j : Fin 3) (a : Fin 3 →₀ ℕ) (ha : normalExponentDegree a < 2) :
    MvPowerSeries.coeff a (MvPowerSeries.monomial (cross i j) (1 : ℂ)) = 0 := by
  rw [MvPowerSeries.coeff_monomial]
  have hn : a ≠ cross i j := fun he => (Nat.ne_of_lt ha) (he ▸ crossDegree i j)
  simp [hn]

private theorem axis_mem_order_two (i : Fin 3) :
    axisGerm i ∈ IsLocalRing.maximalIdeal R ^ 2 := by
  apply (actual_maximal_power_iff_formal_coefficients_zero 3 2 _).mpr
  intro a ha
  rw [axisGerm,crossTaylor]
  exact lowCross _ _ _ ha

private theorem quad_mem_order_two :
    quadGerm ∈ IsLocalRing.maximalIdeal R ^ 2 ∧
      quadGerm ∉ IsLocalRing.maximalIdeal R ^ 3 := by
  have hτ : τ quadGerm = MvPowerSeries.monomial (cross 0 1) 1 +
      MvPowerSeries.monomial (cross 2 2) 1 := by
    rw [quadGerm,map_add,crossTaylor,crossTaylor]
  constructor
  · apply (actual_maximal_power_iff_formal_coefficients_zero 3 2 _).mpr
    intro a ha
    rw [hτ,map_add,lowCross 0 1 a ha,lowCross 2 2 a ha,zero_add]
  · intro h
    have hcoef := (actual_maximal_power_iff_formal_coefficients_zero 3 3 _).mp h (cross 0 1)
      (by rw [crossDegree]; decide)
    have hd : cross 0 1 ≠ cross 2 2 := by
      intro h
      have hh := congrArg (fun a : Fin 3 →₀ ℕ => a 0) h
      simp [cross,Finsupp.add_apply] at hh
    simp [hτ,map_add,MvPowerSeries.coeff_monomial,hd] at hcoef

private theorem axes_origin_le :
    originalCoherentOriginIdeal axesIdeal ≤ IsLocalRing.maximalIdeal R ^ 2 := by
  rw [axes_origin]
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact axis_mem_order_two i

private theorem axes_hs_two_le :
    hilbertSamuelAt axesIdeal 0 2 ≤ 8 := by
  let J := Ideal.map τ.toRingHom (originalCoherentOriginIdeal axesIdeal)
  rw [hilbertSamuelAt_model_zero,hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    genuineFormalHilbertSamuelValue_eq_card_standardIndex]
  let := normalExponentFintype 3 3
  let s : normalExponentIndex 3 3 → Prop := fun a =>
    a.val ∈ actualInitialDiagram MonomialOrder.degLex J
  change Fintype.card {a : normalExponentIndex 3 3 // ¬ s a} ≤ 8
  have hTotal : Fintype.card (normalExponentIndex 3 3) = 10 := by
    rw [actualNormalExponentIndex_card 3 2]
    decide
  have hMember (i : Fin 3) :
      cross (axesI i) (axesJ i) ∈ actualInitialDiagram MonomialOrder.degLex J := by
    have hS : axisGerm i ∈ originalCoherentOriginIdeal axesIdeal := by
      rw [axes_origin]
      exact Ideal.subset_span ⟨i,rfl⟩
    have hm := Ideal.mem_map_of_mem τ.toRingHom hS
    change τ (axisGerm i) ∈ J at hm
    rw [axisGerm,crossTaylor] at hm
    exact ⟨_,hm,actualMonomial_ne_zero _,actualInitialExponent_monomial _ _⟩
  let a : {a : normalExponentIndex 3 3 // s a} :=
    ⟨⟨cross 0 1,by rw [crossDegree]; decide⟩,hMember 0⟩
  let b : {a : normalExponentIndex 3 3 // s a} :=
    ⟨⟨cross 0 2,by rw [crossDegree]; decide⟩,hMember 1⟩
  have hne : a ≠ b := by
    intro h
    have he := congrArg (fun a : {a : normalExponentIndex 3 3 // s a} => a.val.val 1) h
    simp [a,b,cross,Finsupp.add_apply] at he
  let : Fintype {a : normalExponentIndex 3 3 // s a} := Fintype.ofFinite _
  have hCount : 2 ≤ Fintype.card {a : normalExponentIndex 3 3 // s a} := by
    classical
    let f : Fin 2 → {a : normalExponentIndex 3 3 // s a} := ![a,b]
    have hf : Function.Injective f := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [f,Ne.symm hne]
    simpa using Fintype.card_le_of_injective f hf
  rw [Fintype.card_subtype_compl,hTotal]
  omega

/-- Below degree two the whole records tie, and degree two strictly
selects the quadric by Hilbert--Samuel size. -/
theorem axes_quad_distinct_initial_HS :
    (∀ l < 2, hilbertSamuelAt axesIdeal 0 l = hilbertSamuelAt quadIdeal 0 l) ∧
    hilbertSamuelAt axesIdeal 0 2 < hilbertSamuelAt quadIdeal 0 2 := by
  have hQuad (l : ℕ) : hilbertSamuelAt quadIdeal 0 l =
      Nat.choose (3+l) 3 - (if 2 ≤ l then Nat.choose (3+(l-2)) 3 else 0) := by
    rw [hilbertSamuelAt_model_zero,quad_origin,
      hilbertSamuelValue_actual_principal _ 2 quad_mem_order_two.1 quad_mem_order_two.2]
  constructor
  · intro l hl
    have hle := axes_origin_le.trans (Ideal.pow_le_pow_right (by omega : l+1 ≤ 2))
    unfold hilbertSamuelAt
    rw [wholeChartStalkIdeal_model_zero,hilbertSamuelValue,sup_eq_right.mpr hle]
    have hB := actualBaseJetDimension 3 l
    change _ = hilbertSamuelAt quadIdeal 0 l
    rw [hB,hQuad,if_neg (Nat.not_le_of_lt hl),Nat.sub_zero]
  · have h := axes_hs_two_le
    rw [hQuad]
    exact lt_of_le_of_lt h (by decide)


open BlowupTowers MarkedIdeals CanonicalCentres
  HironakaG8QuadraticInitialTieCriterion

/-- Two actual whole coherent mark-one histories have a strict ordering by
their original HS profile and an exact tie by their original invariant. -/
theorem axes_quad_HS_orders_original_tie :
    toLex (hilbertSamuelAt axesIdeal 0) < toLex (hilbertSamuelAt quadIdeal 0) ∧
    (canonicalInvariant 3).inv (fullRecord (X := model) axesIdeal 1) .refl 0 =
      (canonicalInvariant 3).inv (fullRecord (X := model) quadIdeal 1) .refl 0 :=
  ⟨⟨2,axes_quad_distinct_initial_HS.1,axes_quad_distinct_initial_HS.2⟩,
    axes_quad_original_mark_one_initial_value_eq⟩


/-- The two genuine model anchors form a compact tagged candidate set.
HS-only selection drops the axis anchor, which is an exact original tie. -/
theorem axes_quad_compact_tagged_candidate_maxima :
    let h : Bool → Lex (ℕ → ℕ) := fun q =>
      toLex (hilbertSamuelAt (if q then quadIdeal else axesIdeal) 0)
    let v : Bool → ValTy 3 := fun q =>
      (canonicalInvariant 3).inv (fullRecord (X := model) (if q then quadIdeal else axesIdeal) 1) .refl 0
    IsCompact (univ : Set Bool) ∧
      ResolutionDriver.maxLocus h univ = {true} ∧
      ResolutionDriver.maxLocus v univ = univ := by
  intro h v
  have hlt : h false < h true := axes_quad_HS_orders_original_tie.1
  have he : v false = v true := axes_quad_HS_orders_original_tie.2
  refine ⟨Set.toFinite _ |>.isCompact, ?_, ?_⟩
  · ext q
    cases q
    · simp only [ResolutionDriver.maxLocus,mem_ofPred_eq,mem_univ,true_and,
        mem_singleton_iff,Bool.false_eq_true,iff_false]
      exact fun hM => (not_le_of_gt hlt) (hM true trivial)
    · simp only [ResolutionDriver.maxLocus,mem_ofPred_eq,mem_univ,true_and,
        mem_singleton_iff,iff_true]
      intro q _
      cases q
      · exact hlt.le
      · exact le_rfl
  · ext q
    simp only [ResolutionDriver.maxLocus,mem_ofPred_eq,mem_univ,true_and,iff_true]
    intro r _
    cases q <;> cases r <;> simp only [he,le_rfl]

end
end Hironaka.HironakaG8QuadraticAxesInitialHS
