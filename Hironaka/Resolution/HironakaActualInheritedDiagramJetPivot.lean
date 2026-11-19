import Hironaka.Resolution.HironakaActualInheritedNestedContactFlag
import Hironaka.Resolution.HironakaHolomorphicJetQuotientFrames

/-! The CURRENT source diagram detects the whole source ideal jet image.
Actual restricted rows internally produce a full-rank original Macaulay
pivot. Word coordinates remain redundant; no nearby diagram is identified
with the source diagram. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualInheritedDiagramJetPivot
noncomputable section
open HolGerm OkaRelationSheaf HolomorphicTaylorTail HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalTaylorCoefficients HironakaHolomorphicPointJets
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaActualCoefficientPresentationCentrePower
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualCanonicalBlockJacobian
  HironakaActualFormalInitialDiagram HironakaActualFormalStandardMonomialHS
  HironakaActualCauchyCoefficientLimits

variable {n : ℕ}

/-- The genuine exponent of a row in the unmodified word-jet array. -/
def actualJetWordExponent {q : ℕ} (w : monomialIndex n q) : Fin n →₀ ℕ :=
  actualCoordinateWordExponent (List.ofFn w.2)

private theorem coordinateWordExponent_degree (L : List (Fin n)) :
    normalExponentDegree (actualCoordinateWordExponent L) = L.length := by
  have h := Multiset.toFinsupp_sum_eq (L : Multiset (Fin n))
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h
  simpa only [actualCoordinateWordExponent, normalExponentDegree,
    id_eq, Multiset.coe_card] using h

/-- The row exponent has precisely its actual word length. -/
theorem actualJetWordExponent_degree {q : ℕ} (w : monomialIndex n q) :
    normalExponentDegree (actualJetWordExponent w) = w.1.val := by
  simpa only [actualJetWordExponent, List.length_ofFn] using
    coordinateWordExponent_degree (List.ofFn w.2)

/-- Every bounded genuine exponent has a real coordinate-word row. -/
theorem exists_actualJetWordExponent (q : ℕ) (α : Fin n →₀ ℕ)
    (hα : normalExponentDegree α < q) :
    ∃ w : monomialIndex n q, actualJetWordExponent w = α := by
  let L := actualCoordinateDerivativeWord α
  have hL : L.length = normalExponentDegree α := by
    have h := coordinateWordExponent_degree L
    rw [show actualCoordinateWordExponent L = α from
      actualCoordinateDerivativeWord_exponent α] at h
    exact h.symm
  refine ⟨⟨⟨L.length, by rwa [hL]⟩, L.get⟩, ?_⟩
  simpa only [actualJetWordExponent, List.ofFn_get] using
    actualCoordinateDerivativeWord_exponent α

/-- A scalar entry of the SAME translated whole germ is the genuine
iterated coordinate derivative of its original function at that point. -/
theorem scalarJet_translatedGerm_eq_iterDeriv (q : ℕ) (p : ComplexModel n)
    (f : ComplexModel n → ℂ) (hf : HolAt f p) (w : monomialIndex n q) :
    scalarJet q (translatedGerm p f hf) w =
      iterDeriv ((List.ofFn w.2).map (fun i => EuclideanSpace.single i (1 : ℂ))) f p := by
  obtain ⟨U, hUf, hU, hpU⟩ := eventually_nhds_iff.mp hf
  have hdiff : DifferentiableOn ℂ f U := fun z hz => (hUf z hz).differentiableWithinAt
  change finiteCoordinateArray q (finiteJet q (translatedGerm p f hf)) w = _
  rw [finiteCoordinateArray_translatedGerm]
  simp only [List.map_ofFn]
  rw [OrderMultiplicativity.iterDeriv_ofFn_eq_iteratedFDeriv hU hdiff _ _ hpU]
  congr 1
  funext k
  ext i
  simp [EuclideanSpace.basisFun_apply]

/-- Actual scalar word jets are the SAME Taylor coefficient with the
genuine exponent factorial. Repeated word coordinates are not a basis. -/
theorem scalarJet_eq_actualTaylor_coefficient (q : ℕ)
    (g : HolGerm (ComplexModel n)) (w : monomialIndex n q) :
    scalarJet q g w =
      MvPowerSeries.coeff (actualJetWordExponent w) (actualUnshiftedTaylorAlgHom n g) *
        actualExponentFactorial (actualJetWordExponent w) := by
  have hd : HolGerm.eval (actualAnalyticWordDerivative (List.ofFn w.2) g) =
      MvPowerSeries.coeff (actualJetWordExponent w) (actualUnshiftedTaylorAlgHom n g) *
        actualExponentFactorial (actualJetWordExponent w) := by
    rw [← actualTaylor_coeff_zero, actualTaylor_actualAnalyticWordDerivative]
    exact constantCoeff_actualFormalMultiDerivative _ _
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
  obtain ⟨U, hUf, hU, h0U⟩ := eventually_nhds_iff.mp hf
  have hdiff : DifferentiableOn ℂ f U := fun z hz => (hUf z hz).differentiableWithinAt
  rw [actualAnalyticWordDerivative, iteratedDerivativeGerm_mk, HolGerm.eval_mk] at hd
  simp only [List.map_ofFn] at hd
  rw [OrderMultiplicativity.iterDeriv_ofFn_eq_iteratedFDeriv hU hdiff _ _ h0U] at hd
  have hv : (fun k => EuclideanSpace.single (w.2 k) (1 : ℂ)) =
      (fun k => EuclideanSpace.basisFun (Fin n) ℂ (w.2 k)) := by
    funext k
    ext i
    simp [EuclideanSpace.basisFun_apply]
  simp only [Function.comp_def] at hd
  rw [hv] at hd
  exact hd

private theorem formal_coefficients_zero_of_diagram
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hFK : F ∈ K)
    (hD : ∀ α, α ∈ actualInitialDiagram MonomialOrder.degLex K →
      normalExponentDegree α < q → MvPowerSeries.coeff α F = 0) :
    ∀ α, normalExponentDegree α < q → MvPowerSeries.coeff α F = 0 := by
  intro α hα
  by_contra hne
  have hF : F ≠ 0 := by
    intro hz
    exact hne (by rw [hz, map_zero])
  let δ := actualInitialExponent MonomialOrder.degLex F hF
  have hδ : MvPowerSeries.coeff δ F ≠ 0 := (actualInitialExponent_spec _ F hF).1
  have hδD : δ ∈ actualInitialDiagram MonomialOrder.degLex K := ⟨F, hFK, hF, rfl⟩
  have hle := (actualInitialExponent_spec MonomialOrder.degLex F hF).2 α hne
  have hdegree : normalExponentDegree δ ≤ normalExponentDegree α := by
    have h := Finsupp.DegLex.monotone_degree (MonomialOrder.degLex_le_iff.mp hle)
    simpa only [ofDegLex_toDegLex, Finsupp.degree_eq_sum, normalExponentDegree] using h
  exact hδ (hD δ hδD (hdegree.trans_lt hα))

/-- Source diagram rows detect every genuine WHOLE source ideal jet. -/
theorem scalarJet_eq_zero_of_diagram_rows
    (I : Ideal (HolGerm (ComplexModel n))) (q : ℕ)
    (g : HolGerm (ComplexModel n)) (hg : g ∈ I)
    (hrows : ∀ w : monomialIndex n q,
      actualJetWordExponent w ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → scalarJet q g w = 0) :
    scalarJet q g = 0 := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  have hFK : actualUnshiftedTaylorAlgHom n g ∈ K := Ideal.mem_map_of_mem _ hg
  have hD (α : Fin n →₀ ℕ) (hαD : α ∈ actualInitialDiagram MonomialOrder.degLex K)
      (hα : normalExponentDegree α < q) :
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n g) = 0 := by
    obtain ⟨w, hw⟩ := exists_actualJetWordExponent q α hα
    have hz := hrows w (by rwa [hw])
    rw [scalarJet_eq_actualTaylor_coefficient, hw] at hz
    exact (mul_eq_zero.mp hz).resolve_right (actualExponentFactorial_ne_zero α)
  have hall := formal_coefficients_zero_of_diagram K q _ hFK hD
  funext w
  rw [Pi.zero_apply, scalarJet_eq_actualTaylor_coefficient,
    hall _ (by rw [actualJetWordExponent_degree]; exact w.1.isLt), zero_mul]

/-- The historical SOURCE diagram rows of the real finite derivative array. -/
abbrev ActualDiagramJetRow (K : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :=
  {w : monomialIndex n q //
    actualJetWordExponent w ∈ actualInitialDiagram MonomialOrder.degLex K}

instance actualDiagramJetRowFintype (K : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    Fintype (ActualDiagramJetRow K q) := Fintype.ofFinite _

/-- Literal restriction of an actual scalar array to its SOURCE diagram rows. -/
def actualDiagramJetRestriction (K : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    (monomialIndex n q → ℂ) →ₗ[ℂ] (ActualDiagramJetRow K q → ℂ) where
  toFun v w := v w.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem translatedIdeal_zero {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel n → ℂ) (hH : ∀ i, HolAt (H i) 0) :
    translatedIdeal H 0 hH = Ideal.span (range fun i => HolGerm.mk (H i) (hH i)) := by
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => congrArg (H i) (add_zero z)

/-- A true full-rank minor of the ORIGINAL source Macaulay matrix is
internally selected INSIDE its source-diagram rows. No rank or pivot
certificate, canonicality, or nearby diagram equality is an input. -/
theorem exists_actual_source_diagram_jet_pivot
    (I : Ideal (HolGerm (ComplexModel n))) (q : ℕ)
    {ι : Type*} [Fintype ι] (H : ι → ComplexModel n → ℂ)
    (hH : ∀ i, HolAt (H i) 0)
    (hspan : Ideal.span (range fun i => HolGerm.mk (H i) (hH i)) = I) :
    ∃ (r : ℕ) (rows : Fin r → monomialIndex n q)
      (cols : Fin r → monomialIndex n q × ι),
      (∀ i, actualJetWordExponent (rows i) ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)) ∧
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H 0)) = r ∧
      (pivotMatrix q H rows cols 0).det ≠ 0 := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  let L := originalMacaulayLinearMap q H 0
  let R := actualDiagramJetRestriction K q
  let S := LinearMap.range L
  have himage : S = (I.restrictScalars ℂ).map (scalarJet q) := by
    dsimp only [S, L]
    rw [range_originalMacaulay_eq_whole_scalar_image q H 0 hH,
      translatedIdeal_zero H hH, hspan]
  have hdetect (v : monomialIndex n q → ℂ) (hv : v ∈ S) (hz : R v = 0) : v = 0 := by
    rw [himage] at hv
    obtain ⟨g, hg, rfl⟩ := hv
    apply scalarJet_eq_zero_of_diagram_rows I q g hg
    intro w hw
    exact congrFun hz ⟨w, hw⟩
  let f := R.comp S.subtype
  have hf : Function.Injective f := by
    intro v w hvw
    have hzero : R (v.val-w.val) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hvw
    exact Subtype.ext (sub_eq_zero.mp (hdetect _ (S.sub_mem v.property w.property) hzero))
  have hrange : LinearMap.range f = LinearMap.range (R.comp L) := by
    rw [LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
  have hrank : Module.finrank ℂ (LinearMap.range (R.comp L)) = Module.finrank ℂ S := by
    rw [← hrange]
    exact LinearMap.finrank_range_of_inj hf
  let M : Matrix (ActualDiagramJetRow K q) (monomialIndex n q × ι) ℂ :=
    fun a b => originalMacaulayMatrix q H 0 a.val b
  have hM : Fintype.linearCombination ℂ (fun b a => M a b) = R.comp L := by
    ext c a
    simp [M, R, L, actualDiagramJetRestriction, originalMacaulayLinearMap,
      Fintype.linearCombination_apply]
  let r := Module.finrank ℂ S
  have hnot : ¬ ∀ (rows : Fin r → ActualDiagramJetRow K q)
      (cols : Fin r → monomialIndex n q × ι),
      (Matrix.of fun i j => M (rows i) (cols j)).det = 0 := by
    intro hz
    have hlt := (finite_column_rank_lt_iff_minors_eq_zero M r).mpr hz
    rw [hM, hrank] at hlt
    exact (lt_irrefl r) hlt
  push Not at hnot
  obtain ⟨rows, cols, hdet⟩ := hnot
  refine ⟨r, fun i => (rows i).val, cols, fun i => (rows i).property, rfl, ?_⟩
  simpa only [pivotMatrix, M, Matrix.of_apply] using hdet

end
end Hironaka.HironakaActualInheritedDiagramJetPivot
