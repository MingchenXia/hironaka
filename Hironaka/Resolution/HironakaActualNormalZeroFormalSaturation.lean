import Hironaka.Resolution.HironakaActualNormalZeroOwnerConverse
import Hironaka.Resolution.HironakaActualReducedFormalStandardBasis

/-!
# Exceptional cancellation and one fixed colon in the adapted zero normal chart

The whole target diagram and exceptional regularity are produced from the SAME
source monic family and its actual marked orders. The target normal remainder
is used only to prove cancellation; it does not replace that source family.
The generic finite-products lemma also applies in the actual analytic ring.

Source-only draft. No kernel acceptance is asserted.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalZeroFormalSaturation
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualReducedFormalStandardBasis HironakaActualReducedBasisDivision
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualFormalFamilyStrictGenerators
  HironakaActualRelativeStandardnessInheritedDivision HironakaActualNormalZeroOwnerConverse
variable {n : ℕ}

/-- The actual whole diagram, rather than a target presentation, suffices for
exceptional cancellation. Its input is a generic lower lemma only. -/
theorem mem_of_X_mul_mem_of_diagram_cylinder
    (J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n)
    (hcyl : ∀ γ : Fin n →₀ ℕ,
      Finsupp.single e 1 + γ ∈ actualInitialDiagram MonomialOrder.degLex J →
        γ ∈ actualInitialDiagram MonomialOrder.degLex J)
    (F : MvPowerSeries (Fin n) ℂ) (hF : MvPowerSeries.X e * F ∈ J) : F ∈ J := by
  let S := actualFormalRemainder MonomialOrder.degLex J F
  have hsub : F - S ∈ J := sub_actualFormalRemainder_mem MonomialOrder.degLex J F
  have hxS : MvPowerSeries.X e * S ∈ J := by
    have he : MvPowerSeries.X e * S =
        MvPowerSeries.X e * F - MvPowerSeries.X e * (F-S) := by ring
    rw [he]
    exact J.sub_mem hF (J.mul_mem_left _ hsub)
  have hS : S = 0 := by
    by_contra hS
    have hx : MvPowerSeries.X e ≠ (0 : MvPowerSeries (Fin n) ℂ) := actualFormalExceptional_ne_zero e
    have hp : MvPowerSeries.X e * S ≠ 0 := mul_ne_zero hx hS
    have hhead : actualInitialExponent MonomialOrder.degLex (MvPowerSeries.X e * S) hp =
        Finsupp.single e 1 + actualInitialExponent MonomialOrder.degLex S hS := by
      simpa only [MvPowerSeries.X, actualInitialExponent_monomial] using
        actualInitialExponent_mul MonomialOrder.degLex (MvPowerSeries.X e) S hx hS
    have hD : Finsupp.single e 1 + actualInitialExponent MonomialOrder.degLex S hS ∈
        actualInitialDiagram MonomialOrder.degLex J :=
      hhead ▸ (show actualInitialExponent MonomialOrder.degLex
        (MvPowerSeries.X e * S) hp ∈ actualInitialDiagram MonomialOrder.degLex J from
          ⟨_, hxS, hp, rfl⟩)
    exact (actualInitialExponent_spec MonomialOrder.degLex S hS).1
      (actualFormalRemainder_coefficient_diagram MonomialOrder.degLex J F _ (hcyl _ hD))
  exact (actualFormalRemainder_eq_zero_iff MonomialOrder.degLex J F).mp hS

/-- One-step cancellation iterates at every power, including zero, in any ring. -/
theorem pow_mul_mem_iff_of_mul_mem {R : Type*} [CommRing R]
    (J : Ideal R) (x : R) (hreg : ∀ F : R, x * F ∈ J → F ∈ J)
    (q : ℕ) (F : R) : x^q * F ∈ J ↔ F ∈ J := by
  constructor
  · induction q with
    | zero =>
      intro h
      simpa only [pow_zero, one_mul] using h
    | succ q ih =>
      intro h
      apply ih
      apply hreg
      simpa only [pow_succ, mul_assoc, mul_left_comm] using h
  · exact J.mul_mem_left _

/-- A finite normalized family produces ONE common exceptional exponent on its
WHOLE ideal. This lower ring lemma does not postulate the desired colon equality. -/
theorem exists_fixed_power_colon_of_finite_products
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (T J : Ideal R) (x : R) (μ : ι → ℕ) (H : ι → R)
    (hspan : Ideal.span (Set.range H) = J) (hT : T ≤ J)
    (hprod : ∀ i, x^(μ i) * H i ∈ T)
    (hreg : ∀ F : R, x * F ∈ J → F ∈ J) :
    ∃ M : ℕ, (∀ i, μ i ≤ M) ∧ (∀ F ∈ J, x^M * F ∈ T) ∧
      J = T.colon {x^M} ∧ (∀ F : R, F ∈ J ↔ ∃ q : ℕ, x^q * F ∈ T) := by
  let M := (Finset.univ : Finset ι).sup μ
  have hM (i : ι) : μ i ≤ M := Finset.le_sup (f := μ) (Finset.mem_univ i)
  have hJ : J ≤ T.colon {x^M} := by
    rw [← hspan]
    apply Ideal.span_le.mpr
    rintro F ⟨i, rfl⟩
    apply Submodule.mem_colon_singleton.mpr
    change H i * x^M ∈ T
    rw [mul_comm]
    have he : x^M * H i = x^(M-μ i) * (x^(μ i) * H i) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hM i)]
    rw [he]
    exact T.mul_mem_left _ (hprod i)
  have hbound (F : R) (hF : F ∈ J) : x^M * F ∈ T := by
    have h := hJ hF
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using h
  have hcolon : J = T.colon {x^M} := by
    apply le_antisymm hJ
    intro F hF
    apply (pow_mul_mem_iff_of_mul_mem J x hreg M F).mp
    apply hT
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hF
  refine ⟨M, hM, hbound, hcolon, ?_⟩
  intro F
  constructor
  · intro hF
    exact ⟨M, hbound F hF⟩
  · rintro ⟨q, hq⟩
    exact (pow_mul_mem_iff_of_mul_mem J x hreg q F).mp (hT hq)

/-- Whole genuine source generation by a specified actual monic family. -/
theorem ideal_eq_span_same_monic_family
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex K) :
    Ideal.span (Set.range B.series) = K := by
  apply le_antisymm (Ideal.span_le.mpr (by rintro F ⟨a, rfl⟩; exact B.mem a))
  intro F hF
  rw [family_formal_ideal_member_division MonomialOrder.degLex K B F hF]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)

/-- The literal total-degree normalized members of the SAME monic source family. -/
def sameMonicZeroNormalizedVertex
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex K)
    (e : Fin n)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex K) : MvPowerSeries (Fin n) ℂ :=
  actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0)
    (normalExponentDegree a.val) (B.series a) (hpower a)

/-- Source normal marks and a nonzero monic coefficient identify the mark with
its normal weight. No target order is needed in this generation bridge. -/
theorem normal_weight_eq_degree_of_monic_mark
    (A : Set (Fin n)) (a : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hmonic : MvPowerSeries.coeff a F = 1)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ normalExponentDegree a) :
    Finsupp.weight (actualCoordinateWeight A) a = normalExponentDegree a := by
  apply le_antisymm
  · rw [Finsupp.weight_eq_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ∈ A
    · simp only [actualCoordinateWeight, if_pos hi, smul_eq_mul, mul_one]
      exact le_rfl
    · simp only [actualCoordinateWeight, if_neg hi, smul_eq_mul, mul_zero]
      exact Nat.zero_le _
  · by_contra h
    have hz := (mem_actualFormalCoordinateIdeal_pow_iff A (normalExponentDegree a) F).mp hF
      a (lt_of_not_ge h)
    rw [hmonic] at hz
    exact one_ne_zero hz

/-- Existing whole strict-generation, at the SAME literal total-degree marks.
This exposes a reusable dictionary, not a new strict-generation assertion. -/
theorem actual_normal_zero_strict_eq_same_monic_span
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex K)
    (e : Fin n)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val) :
    actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) =
      Ideal.span (Set.range (sameMonicZeroNormalizedVertex K B e hpower)) := by
  have hw (a : actualInitialVertices MonomialOrder.degLex K) :=
    normal_weight_eq_degree_of_monic_mark (Set.Ici e) a.val (B.series a) (B.monic a) (hpower a)
  have hv (a : actualInitialVertices MonomialOrder.degLex K) :
      familyVertexSeries MonomialOrder.degLex K B a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^
        Finsupp.weight (actualCoordinateWeight (Set.Ici e)) a.val := by
    rw [hw a]
    exact hpower a
  rw [actualFormalStrictTransform_eq_family_span MonomialOrder.degLex K B
    (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) hv]
  congr 1
  apply congrArg Set.range
  funext a
  apply actualNormalizedFormalMember_unique (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
    (fun _ => 0) (normalExponentDegree a.val) (B.series a) (hpower a)
  calc
    _ = (MvPowerSeries.X e)^(Finsupp.weight (actualCoordinateWeight (Set.Ici e)) a.val) *
        familyNormalizedFormalVertex MonomialOrder.degLex K B (Set.Ici e) e
          (Set.mem_Ici.mpr le_rfl) (fun _ => 0) hv a := by rw [hw a]
    _ = _ := actualNormalizedFormalMember_spec _ _ _ _ _ _ _

private def sameInheritedFamily
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex K) :
    InheritedMonicFamily MonomialOrder.degLex K := ⟨B.series, B.monic, B.lower⟩

/-- Actual marked orders internally produce exceptional regularity of the WHOLE
strict ideal. No caller target diagram, regularity or HS certificate is used. -/
theorem actual_normal_zero_Xpow_mul_mem_strict_iff_of_marked_orders
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex K)
    (e : Fin n)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameMonicZeroNormalizedVertex K B e hpower a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    (MvPowerSeries.X e)^q * F ∈
      actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) ↔
    F ∈ actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) := by
  obtain ⟨hpure, hD, _hhs⟩ :=
    actual_normal_zero_strict_diagram_and_hs_of_inherited_marked_orders K K
      (sameInheritedFamily K B) rfl B.mem e hpower horder
  apply pow_mul_mem_iff_of_mul_mem
  intro G hG
  apply mem_of_X_mul_mem_of_diagram_cylinder _ e _ G hG
  intro γ hγ
  rw [hD] at hγ ⊢
  obtain ⟨a, ha, hle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K _).mp hγ
  apply (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K _).mpr
  refine ⟨a, ha, ?_⟩
  intro i
  by_cases hie : i = e
  · subst i
    rw [hpure ⟨a, ha⟩ e le_rfl]
    exact Nat.zero_le _
  · have hi := hle i
    simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne hie, zero_add] using hi

/-- A concrete single finite exceptional exponent and WHOLE saturation are
produced from natural marked orders of the SAME source family. -/
theorem exists_actual_normal_zero_fixed_colon_of_marked_orders
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex K)
    (e : Fin n)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameMonicZeroNormalizedVertex K B e hpower a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val) :
    ∃ M : ℕ,
      (∀ F ∈ actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0),
        (MvPowerSeries.X e)^M * F ∈ Ideal.map (actualFormalBlowup (Set.Ici e) e (fun _ => 0)).toRingHom K) ∧
      actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) =
        (Ideal.map (actualFormalBlowup (Set.Ici e) e (fun _ => 0)).toRingHom K).colon {(MvPowerSeries.X e)^M} ∧
      (∀ F : MvPowerSeries (Fin n) ℂ,
        F ∈ actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) ↔
          ∃ q : ℕ, (MvPowerSeries.X e)^q * F ∈
            Ideal.map (actualFormalBlowup (Set.Ici e) e (fun _ => 0)).toRingHom K) := by
  let J := actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0)
  let T := Ideal.map (actualFormalBlowup (Set.Ici e) e (fun _ => 0)).toRingHom K
  let H := sameMonicZeroNormalizedVertex K B e hpower
  have hspan : Ideal.span (Set.range H) = J :=
    (actual_normal_zero_strict_eq_same_monic_span K B e hpower).symm
  have hprod (a : actualInitialVertices MonomialOrder.degLex K) :
      (MvPowerSeries.X e)^(normalExponentDegree a.val) * H a ∈ T := by
    change (MvPowerSeries.X e)^(normalExponentDegree a.val) *
      actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0)
        (normalExponentDegree a.val) (B.series a) (hpower a) ∈ T
    rw [actualNormalizedFormalMember_spec]
    exact Ideal.mem_map_of_mem _ (B.mem a)
  have hT : T ≤ J := by
    change Ideal.map (actualFormalBlowup (Set.Ici e) e (fun _ => 0)).toRingHom K ≤ J
    rw [← ideal_eq_span_same_monic_family K B, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro G ⟨F, ⟨a, rfl⟩, rfl⟩
    change actualFormalBlowup (Set.Ici e) e (fun _ => 0) (B.series a) ∈ J
    rw [← actualNormalizedFormalMember_spec (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
      (fun _ => 0) _ (B.series a) (hpower a)]
    exact J.mul_mem_left _ (hspan ▸ Ideal.subset_span ⟨a, rfl⟩)
  have hreg (F : MvPowerSeries (Fin n) ℂ) (hF : MvPowerSeries.X e * F ∈ J) : F ∈ J := by
    apply (actual_normal_zero_Xpow_mul_mem_strict_iff_of_marked_orders K B e hpower horder 1 F).mp
    simpa only [pow_one] using hF
  obtain ⟨M, _hM, hbound, hc, hs⟩ := exists_fixed_power_colon_of_finite_products T J
    (MvPowerSeries.X e) (fun a : actualInitialVertices MonomialOrder.degLex K => normalExponentDegree a.val)
    H hspan hT hprod hreg
  exact ⟨M, hbound, hc, hs⟩

end
end Hironaka.HironakaActualNormalZeroFormalSaturation
