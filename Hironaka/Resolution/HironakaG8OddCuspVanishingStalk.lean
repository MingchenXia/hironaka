import Hironaka.Resolution.HironakaG8NativeCuspDiagram
import Hironaka.Analytic.ActualHolomorphicGermFactoriality
import Hironaka.Analytic.RueckertNullstellensatz
import Hironaka.Resolution.HironakaActualPointGeometricBennett
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Literal whole vanishing stalk of the odd embedded cusp. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter Polynomial
open scoped Topology MonomialOrder
namespace Hironaka.HironakaG8OddCuspVanishingStalk
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticFormalNormalPowers HironakaActualFormalInitialDiagram
  HironakaG8SameHSCuspContact HironakaG8NativeCuspDiagram
  ActualHolomorphicGermFactoriality ActualWeierstrassGermQuotient OkaGermRelations

private abbrev R := HolGerm (ComplexModel 1)
private abbrev K := FractionRing R
private abbrev t : R := normalCoordinate 0 1 0

private theorem tTaylor : actualUnshiftedTaylorAlgHom 1 t = MvPowerSeries.X (0 : Fin 1) :=
  actualUnshiftedTaylor_coordinate 1 0

private theorem t_ne_zero : t ≠ 0 := by
  intro h
  have ht := tTaylor
  rw [h, map_zero] at ht
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 1)) ht
  simp [MvPowerSeries.coeff_X] at hc

private def germExponent (a : R) (ha : a ≠ 0) : Fin 1 →₀ ℕ :=
  actualInitialExponent MonomialOrder.degLex (actualUnshiftedTaylorAlgHom 1 a)
    (fun h => ha (actualUnshiftedTaylorAlgHom_injective 1 (h.trans (map_zero _).symm)))

private theorem germExponent_mul (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    germExponent (a*b) (mul_ne_zero ha hb) = germExponent a ha + germExponent b hb := by
  unfold germExponent
  have h := actualInitialExponent_mul MonomialOrder.degLex
    (actualUnshiftedTaylorAlgHom 1 a) (actualUnshiftedTaylorAlgHom 1 b)
    (fun h => ha (actualUnshiftedTaylorAlgHom_injective 1 (h.trans (map_zero _).symm)))
    (fun h => hb (actualUnshiftedTaylorAlgHom_injective 1 (h.trans (map_zero _).symm)))
  convert h using 1
  congr 1
  exact map_mul _ _ _

private theorem germExponent_t (p : ℕ) :
    germExponent (t ^ p) (pow_ne_zero _ t_ne_zero) = Finsupp.single (0 : Fin 1) p := by
  unfold germExponent
  apply actualInitialExponent_eq_of_coefficients
  · rw [map_pow, tTaylor, MvPowerSeries.coeff_X_pow, if_pos rfl]
    exact one_ne_zero
  · intro b hb
    rw [map_pow, tTaylor, MvPowerSeries.coeff_X_pow, if_neg]
    intro h
    subst b
    exact lt_irrefl _ hb

private theorem odd_t_not_square (p : ℕ) (hp : Odd p) (u : K) :
    u ^ 2 ≠ algebraMap R K (t^p) := by
  intro hu
  obtain ⟨a, b, hb₀, h⟩ := IsFractionRing.div_surjective R u
  rw [← h] at hu
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb₀
  have hb' : algebraMap R K b ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hb
  have hEq : a*a = (t^p)*(b*b) := by
    apply IsFractionRing.injective R K
    simp only [map_mul]
    rw [div_pow, div_eq_iff (pow_ne_zero _ hb'), pow_two, pow_two] at hu
    exact hu
  have ha : a ≠ 0 := by
    intro h
    have hz : (t^p)*(b*b) ≠ 0 := mul_ne_zero (pow_ne_zero _ t_ne_zero) (mul_ne_zero hb hb)
    apply hz
    rw [← hEq, h, zero_mul]
  have hExp : germExponent (a*a) (mul_ne_zero ha ha) =
      germExponent ((t^p)*(b*b)) (mul_ne_zero (pow_ne_zero _ t_ne_zero) (mul_ne_zero hb hb)) := by
    generalize_proofs
    congr 1
  rw [germExponent_mul _ _ ha ha, germExponent_mul _ _ (pow_ne_zero _ t_ne_zero)
    (mul_ne_zero hb hb), germExponent_mul _ _ hb hb, germExponent_t] at hExp
  have hAt := congrArg (fun a : Fin 1 →₀ ℕ => a 0) hExp
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hAt
  obtain ⟨k, hk⟩ := hp
  omega

private def cuspPolynomial (p : ℕ) : R[X] := X^2 - C (t^p)

private theorem cuspPolynomial_monic (p : ℕ) : (cuspPolynomial p).Monic :=
  monic_X_pow_sub_C (R := R) (n := 2) (t^p) (by decide)

private theorem cuspPolynomial_prime (p : ℕ) (hp : Odd p) : Prime (cuspPolynomial p) := by
  let := uniqueFactorizationMonoid_holGerm_euclidean 1
  apply Irreducible.prime
  apply ((cuspPolynomial_monic p).irreducible_iff_irreducible_map_fraction_map (K := K)).mpr
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_map_eq_of_injective (IsFractionRing.injective R K)]
    rw [cuspPolynomial, natDegree_X_pow_sub_C]
    decide
  · intro u hu
    exact odd_t_not_square p hp u (sub_eq_zero.mp (by
      simpa [cuspPolynomial, Polynomial.IsRoot] using hu))


private theorem t_eval_zero : HolGerm.eval t = 0 := by
  unfold t normalCoordinate coordinateGerm
  rw [HolGerm.eval_mk]
  rfl

/-- The plane cusp germ of odd exponent is prime in the actual convergent
germ ring. The Weierstrass quotient, rather than a formal completion, supplies
the comparison to the polynomial fraction field. -/
theorem odd_cusp_germ_prime (p : ℕ) (hp : Odd p) : Prime (cuspGerm p) := by
  have hp0 : p ≠ 0 := by obtain ⟨k, hk⟩ := hp; omega
  have hD : (cuspPolynomial p).natDegree = 2 := by
    rw [cuspPolynomial, natDegree_X_pow_sub_C]
  have hW0 : ∀ j < (cuspPolynomial p).natDegree,
      HolGerm.eval ((cuspPolynomial p).coeff j) = 0 := by
    intro j hj
    rw [hD] at hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · simp [cuspPolynomial, -map_pow, coeff_X_pow]
      rw [map_pow, t_eval_zero, zero_pow hp0]
    · simp [cuspPolynomial, -map_pow, coeff_X_pow]
  have hPrime := ((prime_shiftEval_iff (cuspPolynomial_monic p) hW0).mpr
    (cuspPolynomial_prime p hp))
  let E := comapEquiv (euclideanSnocCLE 1)
  have hId : E (shiftEval 0 (cuspPolynomial p)) = cuspGerm p := by
    have hx : projGerm 2 1 t = tangentPullback 1 1 t := by
      unfold t normalCoordinate tangentPullback coordinateGerm
      rw [projGerm_mk, compAlgHom_mk]
      exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => rfl)
    have hEval : shiftEval (E := ComplexModel 1) 0 (cuspPolynomial p) =
        (lastCoord : HolGerm (ComplexModel 1 × ℂ))^2 - (ofFst t)^p := by
      simp [cuspPolynomial, shiftEval, eval₂_pow]
    change comapEquiv (euclideanSnocCLE 1) (shiftEval 0 (cuspPolynomial p)) = _
    rw [hEval, map_sub, map_pow, map_pow, comapEquiv_euclideanSnocCLE_lastCoord,
      comapEquiv_euclideanSnocCLE_ofFst, hx]
    rfl
  rw [← hId]
  exact (MulEquiv.prime_iff E.toMulEquiv).mpr hPrime

/-- The actual zero-section ideal is prime for every odd cusp exponent. -/
theorem embedded_odd_cusp_ideal_prime (p : ℕ) (hp : Odd p) :
    (embeddedCuspIdeal p).IsPrime := by
  have hc : cuspGerm p ≠ 0 := (odd_cusp_germ_prime p hp).ne_zero
  let : (Ideal.span {cuspGerm p}).IsPrime :=
    (Ideal.span_singleton_prime hc).mpr (odd_cusp_germ_prime p hp)
  rw [embeddedCuspIdeal, ← HironakaActualZeroSectionStabilization.comap_planeTrace_eq_actualZeroSectionIdeal]
  infer_instance

open HironakaActualPointGeometricBennett HironakaRelativeNormalDeformationInitialRelations
  Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences

/-- Literal analytic defining functions of the embedded cusp in the original
three-dimensional chart. -/
def embeddedCuspEquations (p : ℕ) (i : Fin 2) (z : ComplexModel 3) : ℂ :=
  if i = 0 then z.ofLp 1 ^ 2 - z.ofLp 0 ^ p else z.ofLp 2

def embeddedCuspSet (p : ℕ) : Set (ComplexModel 3) :=
  {z | ∀ i, embeddedCuspEquations p i z = 0}

private theorem equations_differentiable (p : ℕ) (i : Fin 2) :
    Differentiable ℂ (embeddedCuspEquations p i) := by
  by_cases hi : i = 0
  · rw [show embeddedCuspEquations p i =
      fun z => z.ofLp 1 ^ 2 - z.ofLp 0 ^ p by funext z; exact if_pos hi]
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable.pow 2).sub
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiable.pow p)
  · rw [show embeddedCuspEquations p i =
      fun z => z.ofLp 2 by funext z; exact if_neg hi]
    exact (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable

private def equationGerm (p : ℕ) (i : Fin 2) : HolGerm (ComplexModel 3) :=
  HolGerm.mk (embeddedCuspEquations p i) (Eventually.of_forall (equations_differentiable p i))

private theorem first_equation_germ (p : ℕ) :
    equationGerm p 0 = tangentPullback 2 1 (cuspGerm p) := by
  change equationGerm p 0 = tangentPullback 2 1
    ((normalCoordinate 1 1 0)^2 - (tangentPullback 1 1 (normalCoordinate 0 1 0))^p)
  rw [map_sub, map_pow, map_pow]
  unfold tangentPullback normalCoordinate coordinateGerm
  rw [compAlgHom_mk, compAlgHom_mk, compAlgHom_mk, ← mk_pow, ← mk_pow, ← mk_sub]
  exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => rfl)

private theorem second_equation_germ (p : ℕ) :
    equationGerm p 1 = normalCoordinate 2 1 0 := by
  unfold equationGerm normalCoordinate coordinateGerm
  exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => rfl)

private theorem equation_span (p : ℕ) :
    Ideal.span (range (equationGerm p)) = embeddedCuspIdeal p := by
  have hRange : range (equationGerm p) = {tangentPullback 2 1 (cuspGerm p), normalCoordinate 2 1 0} := by
    ext g
    simp only [mem_range, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl (first_equation_germ p)
      · exact Or.inr (second_equation_germ p)
    · rintro (rfl | rfl)
      · exact ⟨0, first_equation_germ p⟩
      · exact ⟨1, second_equation_germ p⟩
  have hNormal : range (normalCoordinate 2 1) = {normalCoordinate 2 1 0} := by
    ext g
    simp only [mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨a,rfl⟩
      rw [Subsingleton.elim a 0]
    · rintro rfl
      exact ⟨0,rfl⟩
  rw [hRange, embeddedCuspIdeal, HironakaActualZeroSectionStabilization.actualZeroSectionIdeal,
    Ideal.map_span, Set.image_singleton, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    normalIdeal, hNormal, ← Ideal.span_union]
  congr 1

/-- Exact literal geometric vanishing stalk for the original embedded
analytic cusp, with no reduction hypothesis on its generators. -/
theorem embedded_odd_cusp_vanishing_stalk (p : ℕ) (hp : Odd p) :
    originalCoherentOriginIdeal (vanishingIdeal (n := 3) (embeddedCuspSet p)) =
      embeddedCuspIdeal p := by
  have hGeo : originalCoherentOriginIdeal (vanishingIdeal (n := 3) (embeddedCuspSet p)) =
      AnalyticGermDecomposition.vanishingIdeal (embeddedCuspSet p) := by
    ext g
    obtain ⟨H, hH, rfl⟩ := HolGerm.exists_eq_mk g
    rw [mk_mem_original_vanishing_origin_ideal_iff, AnalyticGermDecomposition.mem_vanishingIdeal_mk]
  rw [hGeo]
  have hPrime := embedded_odd_cusp_ideal_prime p hp
  apply le_antisymm
  · have h := RueckertNullstellensatz.vanishingIdeal_le_radical (embeddedCuspIdeal p)
      (embeddedCuspEquations p) (fun i => ⟨Eventually.of_forall (equations_differentiable p i),
        equation_span p ▸ Ideal.subset_span ⟨i,rfl⟩⟩)
    exact h.trans ((hPrime.isRadical.radical_le_iff).mpr le_rfl)
  · rw [← equation_span]
    apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
      (Eventually.of_forall fun _ hz => hz i)

end
end Hironaka.HironakaG8OddCuspVanishingStalk
