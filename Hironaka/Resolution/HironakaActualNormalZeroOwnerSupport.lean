import Hironaka.Resolution.HironakaActualFormalMonomialBlowupReflection
import Hironaka.Resolution.HironakaActualRelativeStandardnessInheritedDivision
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Literal source representatives for finite jets in a zero normal chart

This lower algebraic module uses the actual zero-chart substitution, its whole
coefficient embedding, and genuine normalized members. It does not replace the
source inherited family or assume a diagram for a target ideal. In particular,
only polynomial target coefficients are lifted with one exceptional denominator;
arbitrary formal coefficients are first truncated at the actual leading jet.

This source is an unverified draft accompanying the independent, unregistered
normal-zero-owner-converse blueprint. No kernel acceptance is asserted here.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalZeroOwnerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalMonomialBlowupReflection
  HironakaActualRelativeStandardnessInheritedDivision
variable {n : ℕ}

/-- No coefficient is created outside the image of the actual monomial chart. -/
theorem coeff_actualFormalBlowup_zero_eq_zero_of_not_image
    (A : Set (Fin n)) (e : Fin n) (Q : MvPowerSeries (Fin n) ℂ)
    (c : Fin n →₀ ℕ) (hc : c ∉ Set.range (actualMonomialBlowupExponent A e)) :
    MvPowerSeries.coeff c (actualFormalBlowup A e (fun _ => 0) Q) = 0 := by
  rw [actualFormalBlowup, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (actualFormalBlowupCoordinates_constant_zero A e (fun _ => 0))) Q c]
  apply finsum_eq_zero_of_forall_eq_zero
  intro β
  rw [actualFormalBlowup_zero_coordinate_product, MvPowerSeries.coeff_monomial,
    if_neg (fun h => hc ⟨β, h.symm⟩)]
  simp

/-- EVERY actual nonzero chart coefficient has its unique genuine source exponent. -/
theorem exists_source_coefficient_of_actualFormalBlowup_zero
    (A : Set (Fin n)) (e : Fin n) (Q : MvPowerSeries (Fin n) ℂ)
    (c : Fin n →₀ ℕ)
    (hc : MvPowerSeries.coeff c (actualFormalBlowup A e (fun _ => 0) Q) ≠ 0) :
    ∃ β : Fin n →₀ ℕ, actualMonomialBlowupExponent A e β = c ∧
      MvPowerSeries.coeff β Q ≠ 0 := by
  have himage : c ∈ Set.range (actualMonomialBlowupExponent A e) := by
    by_contra h
    exact hc (coeff_actualFormalBlowup_zero_eq_zero_of_not_image A e Q c h)
  obtain ⟨β, hβ⟩ := himage
  refine ⟨β, hβ, ?_⟩
  rw [← actualFormalBlowup_zero_coefficient A e Q β, hβ]
  exact hc

/-- The actual initial exponent of a blown-up quotient comes from its WHOLE support. -/
theorem exists_source_exponent_of_actualFormalBlowup_zero_initial
    (A : Set (Fin n)) (e : Fin n) (Q : MvPowerSeries (Fin n) ℂ)
    (hQ : Q ≠ 0) :
    ∃ hσ : actualFormalBlowup A e (fun _ => 0) Q ≠ 0,
      ∃ β : Fin n →₀ ℕ, MvPowerSeries.coeff β Q ≠ 0 ∧
        actualInitialExponent MonomialOrder.degLex
          (actualFormalBlowup A e (fun _ => 0) Q) hσ =
            actualMonomialBlowupExponent A e β := by
  have hσ : actualFormalBlowup A e (fun _ => 0) Q ≠ 0 := by
    intro h
    apply hQ
    apply actualFormalBlowup_zero_injective A e
    simpa only [map_zero] using h
  obtain ⟨β, hβ, hc⟩ := exists_source_coefficient_of_actualFormalBlowup_zero A e Q _
    (actualInitialExponent_spec MonomialOrder.degLex _ hσ).1
  exact ⟨hσ, β, hc, hβ.symm⟩

/-- A normalized coefficient is the SAME source coefficient when its exponent
is supported after the exceptional variable and has exactly the true mark. -/
theorem coeff_actualNormalizedFormalMember_zero_of_pure_exponent
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (μ : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ)
    (c : Fin n →₀ ℕ)
    (hc : Finsupp.weight (actualCoordinateWeight (A \ {e})) c = μ) :
    MvPowerSeries.coeff c (actualNormalizedFormalMember A e he (fun _ => 0) μ F hF) =
      MvPowerSeries.coeff c F := by
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single e μ + c))
    (actualNormalizedFormalMember_spec A e he (fun _ => 0) μ F hF)
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_add_monomial_mul, one_mul] at h
  have hE : Finsupp.single e μ + c = actualMonomialBlowupExponent A e c := by
    simp only [actualMonomialBlowupExponent, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hc]
    exact add_comm _ _
  rw [hE, actualFormalBlowup_zero_coefficient] at h
  exact h

private theorem pure_tail_weight (e : Fin n) (c : Fin n →₀ ℕ)
    (hc : ∀ i : Fin n, i ≤ e → c i = 0) :
    Finsupp.weight (actualCoordinateWeight (Set.Ici e \ {e})) c = normalExponentDegree c := by
  rw [Finsupp.weight_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ≤ e
  · simp only [hc i hi, zero_smul]
  · have hmem : i ∈ Set.Ici e \ {e} := ⟨le_of_lt (lt_of_not_ge hi), ne_of_gt (lt_of_not_ge hi)⟩
    simp only [actualCoordinateWeight, if_pos hmem, smul_eq_mul, mul_one]

private theorem pure_tail_of_lex_lt (e : Fin n) (a c : Fin n →₀ ℕ)
    (ha : ∀ i : Fin n, i ≤ e → a i = 0) (hc : toLex c < toLex a) :
    ∀ i : Fin n, i ≤ e → c i = 0 := by
  obtain ⟨j, hj, hja⟩ := Finsupp.Lex.lt_iff.mp hc
  simp only [ofLex_toLex] at hj hja
  have hej : e < j := by
    by_contra h
    have hj0 := ha j (le_of_not_gt h)
    rw [hj0] at hja
    exact Nat.not_lt_zero _ hja
  intro i hi
  exact (hj i (lt_of_le_of_lt hi hej)).trans (ha i hi)

/-- Genuine order retention and SOURCE heads internally give the SAME
normalized target head. No target diagram is supplied. -/
theorem actualNormalizedFormalMember_zero_head_of_order
    (e : Fin n) (a : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (ha : ∀ i : Fin n, i ≤ e → a i = 0)
    (hmonic : MvPowerSeries.coeff a F = 1)
    (hlower : ∀ c, MonomialOrder.degLex.toSyn c < MonomialOrder.degLex.toSyn a →
      MvPowerSeries.coeff c F = 0)
    (hF : F ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a)
    (horder : actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
      (fun _ => 0) (normalExponentDegree a) F hF ∈
        genuineFormalVariables n ^ normalExponentDegree a) :
    ∃ hne : actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
        (fun _ => 0) (normalExponentDegree a) F hF ≠ 0,
      actualInitialExponent MonomialOrder.degLex
        (actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
          (fun _ => 0) (normalExponentDegree a) F hF) hne = a := by
  let H := actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
    (fun _ => 0) (normalExponentDegree a) F hF
  have hcoeff : MvPowerSeries.coeff a H = 1 := by
    rw [coeff_actualNormalizedFormalMember_zero_of_pure_exponent
      (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) _ F hF a (pure_tail_weight e a ha)]
    exact hmonic
  have hne : H ≠ 0 := by
    intro h
    rw [h, map_zero] at hcoeff
    exact zero_ne_one hcoeff
  refine ⟨hne, actualInitialExponent_eq_of_coefficients MonomialOrder.degLex H hne a
    (by rw [hcoeff]; exact one_ne_zero) ?_⟩
  intro c hc
  change toDegLex c < toDegLex a at hc
  rcases Finsupp.DegLex.lt_iff.mp hc with hd | ⟨hd, hlex⟩
  · exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n _ H).mp horder c
      (by simpa only [ofDegLex_toDegLex, normalExponentDegree, Finsupp.degree_eq_sum] using hd)
  · simp only [ofDegLex_toDegLex] at hd hlex
    have hcpure := pure_tail_of_lex_lt e a c ha hlex
    have hw : Finsupp.weight (actualCoordinateWeight (Set.Ici e \ {e})) c =
        normalExponentDegree a := by
      rw [pure_tail_weight e c hcpure]
      simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using hd
    rw [coeff_actualNormalizedFormalMember_zero_of_pure_exponent
      (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) _ F hF c hw]
    exact hlower c hc

/-- The genuine marked product and retained order force ALL source exponents
up to and including the exceptional variable to vanish at a monic label. -/
theorem pure_tail_of_monic_normal_mark_and_normalized_order
    (e : Fin n) (a : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hmonic : MvPowerSeries.coeff a F = 1)
    (hF : F ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a)
    (horder : actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
      (fun _ => 0) (normalExponentDegree a) F hF ∈
        genuineFormalVariables n ^ normalExponentDegree a) :
    ∀ i : Fin n, i ≤ e → a i = 0 := by
  let E := actualMonomialBlowupExponent (Set.Ici e) e
  let μ := normalExponentDegree a
  let s := Finsupp.weight (actualCoordinateWeight (Set.Ici e \ {e})) a
  let H := actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
    (fun _ => 0) μ F hF
  have hN : μ ≤ E a e := by
    rw [actualMonomialBlowupExponent_exceptional (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)]
    by_contra h
    have hz := (mem_actualFormalCoordinateIdeal_pow_iff (Set.Ici e) μ F).mp hF a (lt_of_not_ge h)
    rw [hmonic] at hz
    exact one_ne_zero hz
  have hle : Finsupp.single e μ ≤ E a := by
    intro i
    by_cases hi : i = e
    · subst i
      simpa only [Finsupp.single_eq_same] using hN
    · simp only [Finsupp.single_eq_of_ne hi]
      exact Nat.zero_le _
  let c := E a - Finsupp.single e μ
  have hE : E a = Finsupp.single e μ + c := (add_tsub_cancel_of_le hle).symm
  have hc : MvPowerSeries.coeff c H = 1 := by
    have hprod := actualNormalizedFormalMember_spec (Set.Ici e) e
      (Set.mem_Ici.mpr le_rfl) (fun _ => 0) μ F hF
    have h := congrArg (MvPowerSeries.coeff (E a)) hprod
    rw [actualFormalBlowup_zero_coefficient, hmonic] at h
    rw [hE, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_add_monomial_mul, one_mul] at h
    exact h
  have hdegE : (E a).degree = a.degree + s := by
    change (a + Finsupp.single e s).degree = _
    rw [map_add, Finsupp.degree_single]
  have hdegree := congrArg Finsupp.degree hE
  rw [hdegE, map_add, Finsupp.degree_single] at hdegree
  have haμ : a.degree = μ := by
    simp only [μ, normalExponentDegree, Finsupp.degree_eq_sum]
  have hcs : normalExponentDegree c = s := by
    have hcdegree : c.degree = s := by omega
    simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using hcdegree
  have hs : μ ≤ s := by
    by_contra h
    have hz := (mem_genuineFormalVariables_pow_iff_coefficients_zero n μ H).mp horder c
      (by rw [hcs]; exact lt_of_not_ge h)
    rw [hc] at hz
    exact one_ne_zero hz
  have hsplit : μ = s + ∑ i : Fin n, if i ≤ e then a i else 0 := by
    dsimp only [μ, s, normalExponentDegree]
    rw [Finsupp.weight_eq_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ≤ e
    · have hnot : i ∉ Set.Ici e \ {e} := by
        rintro ⟨hie, hne⟩
        exact hne (le_antisymm hi hie)
      simp only [actualCoordinateWeight, if_neg hnot, smul_eq_mul, mul_zero, if_pos hi, zero_add]
    · have hmem : i ∈ Set.Ici e \ {e} := ⟨le_of_lt (lt_of_not_ge hi), ne_of_gt (lt_of_not_ge hi)⟩
      simp only [actualCoordinateWeight, if_pos hmem, smul_eq_mul, mul_one, if_neg hi, add_zero]
  have hzero : (∑ i : Fin n, if i ≤ e then a i else 0) = 0 := by omega
  intro i hi
  have hbound := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => Nat.zero_le (if j ≤ e then a j else 0))
    (Finset.mem_univ i)
  rw [if_pos hi, hzero] at hbound
  exact Nat.eq_zero_of_le_zero hbound

/-- A literal finite target monomial lift at a prescribed sufficient denominator. -/
def zeroChartCoefficientExponent (A : Set (Fin n)) (e : Fin n) (r : ℕ)
    (γ : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  γ + Finsupp.single e (r - Finsupp.weight (actualCoordinateWeight (A \ {e})) γ)

/-- The genuine exponent embedding sends the coefficient lift to the exact
exceptional multiple; the bound is only on the finite target exponent. -/
theorem actualMonomialBlowupExponent_zeroChartCoefficientExponent
    (A : Set (Fin n)) (e : Fin n) (r : ℕ) (γ : Fin n →₀ ℕ)
    (hγ : Finsupp.weight (actualCoordinateWeight (A \ {e})) γ ≤ r) :
    actualMonomialBlowupExponent A e (zeroChartCoefficientExponent A e r γ) =
      Finsupp.single e r + γ := by
  have hw : Finsupp.weight (actualCoordinateWeight (A \ {e}))
      (zeroChartCoefficientExponent A e r γ) =
        Finsupp.weight (actualCoordinateWeight (A \ {e})) γ := by
    rw [zeroChartCoefficientExponent, map_add, Finsupp.weight_single]
    have he0 : actualCoordinateWeight (A \ {e}) e = 0 := by simp [actualCoordinateWeight]
    rw [he0, smul_zero, add_zero]
  change zeroChartCoefficientExponent A e r γ + Finsupp.single e _ = _
  rw [hw, zeroChartCoefficientExponent, add_assoc, ← Finsupp.single_add,
    Nat.sub_add_cancel hγ, add_comm]

/-- Whole zero-chart substitution has the literal monomial image, with its
original complex coefficient. -/
theorem actualFormalBlowup_zero_monomial
    (A : Set (Fin n)) (e : Fin n) (β : Fin n →₀ ℕ) (c : ℂ) :
    actualFormalBlowup A e (fun _ => 0) (MvPowerSeries.monomial β c) =
      MvPowerSeries.monomial (actualMonomialBlowupExponent A e β) c := by
  rw [actualFormalBlowup, MvPowerSeries.substAlgHom_monomial,
    actualFormalBlowup_zero_coordinate_product]
  change MvPowerSeries.C c * MvPowerSeries.monomial _ 1 = _
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial,
    zero_add, mul_one]

/-- The actual polynomial, with unchanged coefficients, before any use of
normalization or of ideal membership. -/
def zeroChartPolynomialCoefficientLift (A : Set (Fin n)) (e : Fin n) (r : ℕ)
    (P : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ γ ∈ P.support,
    MvPolynomial.monomial (zeroChartCoefficientExponent A e r γ) (P.coeff γ)

/-- One finite polynomial target coefficient has a genuine source polynomial
lift after its explicit sufficient exceptional denominator. -/
theorem actualFormalBlowup_zero_polynomialCoefficientLift
    (A : Set (Fin n)) (e : Fin n) (r : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : ∀ γ ∈ P.support, Finsupp.weight (actualCoordinateWeight (A \ {e})) γ ≤ r) :
    actualFormalBlowup A e (fun _ => 0)
      (zeroChartPolynomialCoefficientLift A e r P : MvPowerSeries (Fin n) ℂ) =
        (MvPowerSeries.X e)^r * (P : MvPowerSeries (Fin n) ℂ) := by
  change actualFormalBlowup A e (fun _ => 0)
    (MvPolynomial.coeToMvPowerSeries.ringHom (zeroChartPolynomialCoefficientLift A e r P)) = _
  rw [zeroChartPolynomialCoefficientLift, map_sum]
  simp only [map_sum]
  have hcoe (β : Fin n →₀ ℕ) (c : ℂ) :
      MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.monomial β c) =
        MvPowerSeries.monomial β c := MvPolynomial.coe_monomial β c
  calc
    _ = ∑ γ ∈ P.support, (MvPowerSeries.X e)^r * MvPowerSeries.monomial γ (P.coeff γ) := by
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [hcoe, actualFormalBlowup_zero_monomial,
        actualMonomialBlowupExponent_zeroChartCoefficientExponent A e r γ (hP γ hγ),
        MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
    _ = (MvPowerSeries.X e)^r * (P : MvPowerSeries (Fin n) ℂ) := by
      rw [← Finset.mul_sum]
      congr 1
      have h := congrArg (MvPolynomial.coeToMvPowerSeries.ringHom)
        (MvPolynomial.as_sum P)
      change (∑ γ ∈ P.support, MvPowerSeries.monomial γ (P.coeff γ)) =
        MvPolynomial.coeToMvPowerSeries.ringHom P
      simpa only [map_sum, hcoe] using h.symm

/-- A single finite denominator works for ALL coefficients of a finite tuple.
The returned numerator is literally a normalized source member at that SAME M. -/
theorem exists_normalized_source_of_polynomial_combination
    {ι : Type*} [Fintype ι] (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (μ : ι → ℕ)
    (G H : ι → MvPowerSeries (Fin n) ℂ)
    (hmem : ∀ i, G i ∈ K)
    (hproduct : ∀ i, (MvPowerSeries.X e)^(μ i) * H i = actualFormalBlowup A e (fun _ => 0) (G i))
    (P : ι → MvPolynomial (Fin n) ℂ) :
    ∃ M : ℕ, ∃ F : MvPowerSeries (Fin n) ℂ, ∃ hF : F ∈ actualFormalCoordinateIdeal n A ^ M,
      F ∈ K ∧ actualNormalizedFormalMember A e he (fun _ => 0) M F hF =
        ∑ i, (P i : MvPowerSeries (Fin n) ℂ) * H i := by
  let s (γ : Fin n →₀ ℕ) := Finsupp.weight (actualCoordinateWeight (A \ {e})) γ
  let M := (Finset.univ : Finset ι).sup (fun i => μ i + (P i).support.sup s)
  have hM (i : ι) : μ i + (P i).support.sup s ≤ M :=
    Finset.le_sup (f := fun j => μ j + (P j).support.sup s) (Finset.mem_univ i)
  have hμ (i : ι) : μ i ≤ M := le_trans (Nat.le_add_right _ _) (hM i)
  have hbound (i : ι) (γ : Fin n →₀ ℕ) (hγ : γ ∈ (P i).support) : s γ ≤ M - μ i := by
    have hs : s γ ≤ (P i).support.sup s := Finset.le_sup hγ
    have hMi := hM i
    omega
  let B (i : ι) : MvPowerSeries (Fin n) ℂ :=
    (zeroChartPolynomialCoefficientLift A e (M - μ i) (P i) : MvPowerSeries (Fin n) ℂ)
  let F := ∑ i, B i * G i
  have hFK : F ∈ K := K.sum_mem (fun i _ => K.mul_mem_left _ (hmem i))
  have hB (i : ι) : actualFormalBlowup A e (fun _ => 0) (B i) =
      (MvPowerSeries.X e)^(M - μ i) * (P i : MvPowerSeries (Fin n) ℂ) :=
    actualFormalBlowup_zero_polynomialCoefficientLift A e (M - μ i) (P i) (hbound i)
  have hσ : actualFormalBlowup A e (fun _ => 0) F =
      (MvPowerSeries.X e)^M * ∑ i, (P i : MvPowerSeries (Fin n) ℂ) * H i := by
    simp only [F, map_sum, map_mul]
    calc
      _ = ∑ i, (MvPowerSeries.X e)^M * ((P i : MvPowerSeries (Fin n) ℂ) * H i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hB i, ← hproduct i]
        calc
          _ = (MvPowerSeries.X e)^((M - μ i) + μ i) *
              ((P i : MvPowerSeries (Fin n) ℂ) * H i) := by rw [pow_add]; ring
          _ = _ := by rw [Nat.sub_add_cancel (hμ i)]
      _ = _ := (Finset.mul_sum (Finset.univ : Finset ι)
        (fun i : ι => (P i : MvPowerSeries (Fin n) ℂ) * H i)
        ((MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)^M)).symm
  have hF : F ∈ actualFormalCoordinateIdeal n A ^ M :=
    (mem_coordinate_power_iff_blowup_zero_exceptional_dvd A e he M F).mpr
      ⟨∑ i, (P i : MvPowerSeries (Fin n) ℂ) * H i, hσ⟩
  refine ⟨M, F, hF, hFK, ?_⟩
  exact (actualNormalizedFormalMember_unique A e he (fun _ => 0) M F hF _ hσ.symm).symm

private theorem sub_truncTotal_mem_variable_power (Q : MvPowerSeries (Fin n) ℂ) (L : ℕ) :
    Q - (MvPowerSeries.truncTotal L Q : MvPowerSeries (Fin n) ℂ) ∈
      genuineFormalVariables n ^ L := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n L _).mpr
  intro β hβ
  have hdeg : β.degree < L := by
    simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using hβ
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal Q hdeg, sub_self]

/-- Every nonzero member of the whole finite target span has the SAME actual
leading exponent as one genuine normalized source member. This does not assume
a basis, target diagram, target flatness or target HS equality. -/
theorem exists_normalized_source_with_same_initial_of_mem_span
    {ι : Type*} [Fintype ι] (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (μ : ι → ℕ)
    (G H : ι → MvPowerSeries (Fin n) ℂ)
    (hmem : ∀ i, G i ∈ K)
    (hproduct : ∀ i, (MvPowerSeries.X e)^(μ i) * H i = actualFormalBlowup A e (fun _ => 0) (G i))
    (g : MvPowerSeries (Fin n) ℂ) (hg : g ∈ Ideal.span (Set.range H)) (hne : g ≠ 0) :
    ∃ M : ℕ, ∃ F : MvPowerSeries (Fin n) ℂ, ∃ hF : F ∈ actualFormalCoordinateIdeal n A ^ M,
      F ∈ K ∧ ∃ hn : actualNormalizedFormalMember A e he (fun _ => 0) M F hF ≠ 0,
        actualInitialExponent MonomialOrder.degLex g hne =
          actualInitialExponent MonomialOrder.degLex
            (actualNormalizedFormalMember A e he (fun _ => 0) M F hF) hn := by
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
  let α := actualInitialExponent MonomialOrder.degLex g hne
  let L := normalExponentDegree α + 1
  let P (i : ι) := MvPowerSeries.truncTotal L (Q i)
  let h := ∑ i, (P i : MvPowerSeries (Fin n) ℂ) * H i
  have hdiff : g - h ∈ genuineFormalVariables n ^ L := by
    rw [← hQ]
    change (∑ i, Q i * H i) - ∑ i, (P i : MvPowerSeries (Fin n) ℂ) * H i ∈ _
    rw [← Finset.sum_sub_distrib]
    apply Ideal.sum_mem
    intro i _
    rw [← sub_mul]
    exact Ideal.mul_mem_right _ _ (sub_truncTotal_mem_variable_power (Q i) L)
  have hcoeff (β : Fin n →₀ ℕ) (hβ : normalExponentDegree β < L) :
      MvPowerSeries.coeff β h = MvPowerSeries.coeff β g := by
    have hz := (mem_genuineFormalVariables_pow_iff_coefficients_zero n L _).mp hdiff β hβ
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm
  have ha : normalExponentDegree α < L := Nat.lt_succ_self _
  have hn : h ≠ 0 := by
    intro hz
    have hc := hcoeff α ha
    rw [hz, map_zero] at hc
    exact (actualInitialExponent_spec MonomialOrder.degLex g hne).1 hc.symm
  have hhead : actualInitialExponent MonomialOrder.degLex h hn = α := by
    apply actualInitialExponent_eq_of_coefficients
    · rw [hcoeff α ha]
      exact (actualInitialExponent_spec MonomialOrder.degLex g hne).1
    · intro β hβ
      have hd : β.degree ≤ α.degree := by
        rcases Finsupp.DegLex.lt_iff.mp hβ with hd | ⟨hd, _⟩
        · exact le_of_lt hd
        · exact le_of_eq hd
      have hβL : normalExponentDegree β < L := by
        simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using
          lt_of_le_of_lt hd (show α.degree < L from by simpa only [normalExponentDegree,
            Finsupp.degree_eq_sum] using ha)
      rw [hcoeff β hβL]
      exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex g hne β hβ
  obtain ⟨M, F, hF, hFK, hNF⟩ := exists_normalized_source_of_polynomial_combination
    A e he K μ G H hmem hproduct P
  have hnF : actualNormalizedFormalMember A e he (fun _ => 0) M F hF ≠ 0 := by
    rw [hNF]
    exact hn
  refine ⟨M, F, hF, hFK, hnF, ?_⟩
  simpa only [hNF] using hhead.symm

end
end Hironaka.HironakaActualNormalZeroOwnerSupport
