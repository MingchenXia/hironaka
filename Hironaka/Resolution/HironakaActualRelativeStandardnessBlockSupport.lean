import Hironaka.Resolution.HironakaActualFormalBlowupMemberGeneration
import Hironaka.Resolution.HironakaActualReducedFormalStandardBasis
import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# The same inherited reduced block support through an actual chart

The block coordinates are scaled, with no translation in those coordinates.
The explicit hypotheses `B ⊆ A`, `e ∉ B`, and `b = 0` on `B` are geometric
chart inputs. No implication from unchanged HS to these inputs is asserted.

Normalization preserves arbitrary forbidden block exponents. In particular,
every higher canonical vertex retains the reduced support belonging to each
supplied lower-degree vertex block. The same generic theorem can be applied
to its inherited, possibly noncanonical, normalized family at a later step.
This does not construct a semicoherent HS presentation or a history driver.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualRelativeStandardnessBlockSupport

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualReducedFormalStandardBasis

variable {n : ℕ}

private theorem weightedHomogeneous_one (w : Fin n → ℕ) :
    (1 : MvPowerSeries (Fin n) ℂ).IsWeightedHomogeneous w 0 := by
  intro α hα
  by_cases hz : α = 0
  · simp only [hz, map_zero]
  · exact False.elim (hα (by simp only [MvPowerSeries.coeff_one, if_neg hz]))

private theorem weightedHomogeneous_pow (w : Fin n → ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (d : ℕ) (hF : F.IsWeightedHomogeneous w d)
    (k : ℕ) : (F ^ k).IsWeightedHomogeneous w (k * d) := by
  induction k with
  | zero =>
      rw [pow_zero, zero_mul]
      exact weightedHomogeneous_one w
  | succ k ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hF

private theorem weightedHomogeneous_finset_prod {ι : Type*} [DecidableEq ι]
    (w : Fin n → ℕ) (s : Finset ι) (F : ι → MvPowerSeries (Fin n) ℂ)
    (d : ι → ℕ) (hF : ∀ j ∈ s, (F j).IsWeightedHomogeneous w (d j)) :
    (∏ j ∈ s, F j).IsWeightedHomogeneous w (∑ j ∈ s, d j) := by
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro _
      rw [Finset.prod_empty, Finset.sum_empty]
      exact weightedHomogeneous_one w
  | @insert j s hjs ih =>
      intro hF
      rw [Finset.prod_insert hjs, Finset.sum_insert hjs]
      exact MvPowerSeries.IsWeightedHomogeneous.mul (hF j (Finset.mem_insert_self j s))
        (ih (fun l hl => hF l (Finset.mem_insert_of_mem hl)))

private theorem coordinate_homogeneous_C (i : Fin n) (z : ℂ) :
    (MvPowerSeries.C z : MvPowerSeries (Fin n) ℂ).IsWeightedHomogeneous
      (Pi.single i 1) 0 := by
  intro α hα
  have hz : α = 0 := by
    by_contra hz
    exact hα (MvPowerSeries.coeff_C_of_ne_zero hz z)
  simp only [hz, map_zero]

private theorem coordinate_homogeneous_X (i j : Fin n) :
    (MvPowerSeries.X j : MvPowerSeries (Fin n) ℂ).IsWeightedHomogeneous
      (Pi.single i 1) ((Pi.single i 1 : Fin n → ℕ) j) := by
  intro α hα
  have hαj : α = Finsupp.single j 1 := by
    by_contra hαj
    exact hα (by simp only [MvPowerSeries.coeff_X, if_neg hαj])
  simp only [hαj, Finsupp.weight_single, one_smul]

private theorem actualFormalBlowup_coordinate_homogeneous
    (A B : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (hBA : B ⊆ A) (heB : e ∉ B) (hb : ∀ i ∈ B, b i = 0)
    (i : Fin n) (hi : i ∈ B) (j : Fin n) :
    (actualFormalBlowupCoordinates A e b j).IsWeightedHomogeneous
      (Pi.single i 1) ((Pi.single i 1 : Fin n → ℕ) j) := by
  intro α hα
  have hie : i ≠ e := by
    intro h
    exact heB (h ▸ hi)
  have hXe : (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ).IsWeightedHomogeneous
      (Pi.single i 1) 0 := by
    intro δ hδ
    simpa only [Pi.single_eq_of_ne hie.symm] using coordinate_homogeneous_X i e hδ
  by_cases hji : j = i
  · subst j
    have hXi : (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ).IsWeightedHomogeneous
        (Pi.single i 1) 1 := by
      intro δ hδ
      simpa only [Pi.single_eq_same] using coordinate_homogeneous_X i i hδ
    have hmul : (MvPowerSeries.X e * MvPowerSeries.X i :
        MvPowerSeries (Fin n) ℂ).IsWeightedHomogeneous
        (Pi.single i 1) (0 + 1) :=
      MvPowerSeries.IsWeightedHomogeneous.mul hXe hXi
    have hα' : MvPowerSeries.coeff α (MvPowerSeries.X e * MvPowerSeries.X i :
        MvPowerSeries (Fin n) ℂ) ≠ 0 := by
      simpa only [actualFormalBlowupCoordinates, if_pos (hBA hi), if_neg hie,
        hb i hi, map_zero, zero_add] using hα
    simpa only [Pi.single_eq_same, zero_add] using hmul hα'
  · have hXj : (MvPowerSeries.X j : MvPowerSeries (Fin n) ℂ).IsWeightedHomogeneous
        (Pi.single i 1) 0 := by
      intro δ hδ
      simpa only [Pi.single_eq_of_ne hji] using coordinate_homogeneous_X i j hδ
    by_cases hj : j ∈ A
    · by_cases hje : j = e
      · subst j
        have hα' : MvPowerSeries.coeff α (MvPowerSeries.X e :
            MvPowerSeries (Fin n) ℂ) ≠ 0 := by
          simpa only [actualFormalBlowupCoordinates, if_pos hj, ite_true] using hα
        simpa only [Pi.single_eq_of_ne hie.symm] using hXe hα'
      · have hsum : (MvPowerSeries.C (b j) + MvPowerSeries.X j :
            MvPowerSeries (Fin n) ℂ).IsWeightedHomogeneous (Pi.single i 1) 0 :=
          MvPowerSeries.IsWeightedHomogeneous.add (coordinate_homogeneous_C i (b j)) hXj
        have h : (MvPowerSeries.X e * (MvPowerSeries.C (b j) + MvPowerSeries.X j) :
            MvPowerSeries (Fin n) ℂ).IsWeightedHomogeneous (Pi.single i 1) (0 + 0) :=
          MvPowerSeries.IsWeightedHomogeneous.mul hXe hsum
        have hα' : MvPowerSeries.coeff α
            (MvPowerSeries.X e * (MvPowerSeries.C (b j) + MvPowerSeries.X j) :
              MvPowerSeries (Fin n) ℂ) ≠ 0 := by
          simpa only [actualFormalBlowupCoordinates, if_pos hj, if_neg hje] using hα
        simpa only [Pi.single_eq_of_ne hji, zero_add] using h hα'
    · have hα' : MvPowerSeries.coeff α (MvPowerSeries.X j :
          MvPowerSeries (Fin n) ℂ) ≠ 0 := by
        simpa only [actualFormalBlowupCoordinates, if_neg hj] using hα
      simpa only [Pi.single_eq_of_ne hji] using hXj hα'

/-- Every nonzero actual coordinate-product coefficient has exactly the original
exponent on the unshifted block, not just the same total block degree. -/
theorem actualFormalBlowup_coordinate_product_block_exponents
    (A B : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (hBA : B ⊆ A) (heB : e ∉ B) (hb : ∀ i ∈ B, b i = 0)
    (α γ : Fin n →₀ ℕ)
    (hγ : MvPowerSeries.coeff γ
      (α.prod (fun j k => actualFormalBlowupCoordinates A e b j ^ k)) ≠ 0) :
    ∀ i ∈ B, γ i = α i := by
  intro i hi
  have hprod : (∏ j ∈ α.support, actualFormalBlowupCoordinates A e b j ^ α j).IsWeightedHomogeneous
      (Pi.single i 1)
      (∑ j ∈ α.support, α j * (Pi.single i 1 : Fin n → ℕ) j) :=
    weightedHomogeneous_finset_prod (Pi.single i 1) α.support
    (fun j => actualFormalBlowupCoordinates A e b j ^ α j)
    (fun j => α j * (Pi.single i 1 : Fin n → ℕ) j)
    (fun j _ => weightedHomogeneous_pow (Pi.single i 1) _ _
      (actualFormalBlowup_coordinate_homogeneous A B e b hBA heB hb i hi j) (α j))
  have hdegree : (∑ j ∈ α.support, α j * (Pi.single i 1 : Fin n → ℕ) j) = α i := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using
      Finsupp.weight_single_one_apply i α
  have hhom : (α.prod (fun j k => actualFormalBlowupCoordinates A e b j ^ k)).IsWeightedHomogeneous
      (Pi.single i 1) (α i) := by
    change (∏ j ∈ α.support, actualFormalBlowupCoordinates A e b j ^ α j).IsWeightedHomogeneous
      (Pi.single i 1) (α i)
    rw [← hdegree]
    exact hprod
  simpa only [Finsupp.weight_single_one_apply] using hhom hγ

/-- Actual substitution preserves any forbidden exponent predicate that depends
only on the selected, unshifted block coordinates. -/
theorem actualFormalBlowup_forbidden_block_support
    (A B : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (hBA : B ⊆ A) (heB : e ∉ B) (hb : ∀ i ∈ B, b i = 0)
    (D : (Fin n →₀ ℕ) → Prop)
    (hD : ∀ α γ : Fin n →₀ ℕ, (∀ i ∈ B, α i = γ i) → (D α ↔ D γ))
    (F : MvPowerSeries (Fin n) ℂ) (hF : ∀ α, D α → MvPowerSeries.coeff α F = 0) :
    ∀ γ, D γ → MvPowerSeries.coeff γ (actualFormalBlowup A e b F) = 0 := by
  intro γ hDγ
  rw [actualFormalBlowup, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (actualFormalBlowupCoordinates_constant_zero A e b)) F γ]
  apply finsum_eq_zero_of_forall_eq_zero
  intro α
  by_cases hz : MvPowerSeries.coeff γ
      (α.prod (fun j k => actualFormalBlowupCoordinates A e b j ^ k)) = 0
  · rw [hz, smul_zero]
  · have hαγ : ∀ i ∈ B, α i = γ i := fun i hi =>
        (actualFormalBlowup_coordinate_product_block_exponents A B e b hBA heB hb α γ hz i hi).symm
    rw [hF α ((hD α γ hαγ).mpr hDγ), zero_smul]

/-- The literal normalized member of the same original numerator retains all its
forbidden block exponents, including when the exceptional mark is zero. -/
theorem actualNormalizedFormalMember_forbidden_block_support
    (A B : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hBA : B ⊆ A) (heB : e ∉ B) (hb : ∀ i ∈ B, b i = 0)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ)
    (D : (Fin n →₀ ℕ) → Prop)
    (hD : ∀ α γ : Fin n →₀ ℕ, (∀ i ∈ B, α i = γ i) → (D α ↔ D γ))
    (hzero : ∀ α, D α → MvPowerSeries.coeff α F = 0) :
    ∀ γ, D γ → MvPowerSeries.coeff γ
      (actualNormalizedFormalMember A e he b μ F hF) = 0 := by
  intro γ hDγ
  have hshift : D (Finsupp.single e μ + γ) := by
    apply (hD γ (Finsupp.single e μ + γ) ?_).mp hDγ
    intro i hi
    have hie : i ≠ e := by
      intro h
      exact heB (h ▸ hi)
    simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hie, zero_add]
  have hcoeff := actualFormalBlowup_forbidden_block_support A B e b hBA heB hb
    D hD F hzero (Finsupp.single e μ + γ) hshift
  rw [← actualNormalizedFormalMember_spec A e he b μ F hF,
    MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_add_monomial_mul, one_mul] at hcoeff
  exact hcoeff

/-- The lower-degree vertices generate an actual block diagram. The exponent
outside the selected block is unrestricted. -/
def actualDegreePrefixBlockDiagram (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (B : Set (Fin n))
    (γ : Fin n →₀ ℕ) : Prop :=
  ∃ v : actualInitialVertices m K,
    normalExponentDegree v.val ≤ k ∧ ∀ i ∈ B, v.val i ≤ γ i

/-- The essential block of a degree prefix is constructed from the same actual
vertices, rather than supplied as a standardness certificate. -/
def actualDegreePrefixVariables (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) : Set (Fin n) :=
  {i | ∃ v : actualInitialVertices m K, normalExponentDegree v.val ≤ k ∧ v.val i ≠ 0}

/-- Every higher canonical vertex has zero coefficients on each actual lower
degree-prefix block diagram, provided that block contains the lower vertices. -/
theorem actualReducedVertexSeries_degree_prefix_block_support
    (m : MonomialOrder (Fin n)) (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (k : ℕ) (B : Set (Fin n))
    (hB : ∀ v : actualInitialVertices m K, normalExponentDegree v.val ≤ k →
      ∀ i : Fin n, i ∉ B → v.val i = 0)
    (a : actualInitialVertices m K) (ha : k < normalExponentDegree a.val) :
    ∀ γ, actualDegreePrefixBlockDiagram m K k B γ →
      MvPowerSeries.coeff γ (actualReducedVertexSeries m K a) = 0 := by
  intro γ hγ
  obtain ⟨v, hvk, hvγ⟩ := hγ
  have hvγ' : v.val ≤ γ := by
    intro i
    by_cases hi : i ∈ B
    · exact hvγ i hi
    · rw [hB v hvk i hi]
      exact Nat.zero_le _
  have hγD : γ ∈ actualInitialDiagram m K :=
    (mem_actualInitialDiagram_iff_vertex_le m K γ).mpr ⟨v.val, v.property, hvγ'⟩
  have hγa : γ ≠ a.val := by
    intro h
    have hvD : v.val ∈ actualInitialDiagram m K :=
      (mem_actualInitialDiagram_iff_vertex_le m K v.val).mpr ⟨v.val, v.property, le_rfl⟩
    have hmin : Minimal (· ∈ actualInitialDiagram m K) a.val := by
      simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.property
    have hva : v.val ≤ a.val := by simpa only [h] using hvγ'
    have hav : a.val ≤ v.val := hmin.2 hvD hva
    have heq : a.val = v.val := le_antisymm hav hva
    have hdeg := congrArg normalExponentDegree heq
    omega
  rw [actualReducedVertexSeries_coefficient_diagram m K a γ hγD, if_neg hγa]

/-- The literal actual degree-prefix block needs no caller-supplied support
premise to produce the canonical higher-member coefficient vanishing. -/
theorem actualReducedVertexSeries_actual_degree_prefix_support
    (m : MonomialOrder (Fin n)) (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (k : ℕ) (a : actualInitialVertices m K) (ha : k < normalExponentDegree a.val) :
    ∀ γ, actualDegreePrefixBlockDiagram m K k (actualDegreePrefixVariables m K k) γ →
      MvPowerSeries.coeff γ (actualReducedVertexSeries m K a) = 0 := by
  apply actualReducedVertexSeries_degree_prefix_block_support m K k
    (actualDegreePrefixVariables m K k) ?_ a ha
  intro v hv i hi
  by_contra hvi
  exact hi ⟨v, hv, hvi⟩

/-- Each inherited normalized higher vertex retains the same forbidden block
exponents. The actual vertex labels, prefix, marks, and normalized members are
unchanged; this is not an assertion about the entire HS phase. -/
theorem actualNormalizedReducedVertexSeries_degree_prefix_block_support
    (m : MonomialOrder (Fin n)) (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (k : ℕ) (B : Set (Fin n))
    (hB : ∀ v : actualInitialVertices m K, normalExponentDegree v.val ≤ k →
      ∀ i : Fin n, i ∉ B → v.val i = 0)
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hBA : B ⊆ A) (heB : e ∉ B) (hb : ∀ i ∈ B, b i = 0)
    (μ : actualInitialVertices m K → ℕ)
    (hV : ∀ a : actualInitialVertices m K,
      actualReducedVertexSeries m K a ∈ actualFormalCoordinateIdeal n A ^ μ a) :
    ∀ (a : actualInitialVertices m K), k < normalExponentDegree a.val →
      ∀ γ, actualDegreePrefixBlockDiagram m K k B γ →
        MvPowerSeries.coeff γ (actualNormalizedFormalMember A e he b (μ a)
          (actualReducedVertexSeries m K a) (hV a)) = 0 := by
  intro a ha
  apply actualNormalizedFormalMember_forbidden_block_support A B e he b hBA heB hb
    (μ a) (actualReducedVertexSeries m K a) (hV a) (actualDegreePrefixBlockDiagram m K k B)
  · intro α γ hαγ
    constructor
    · rintro ⟨v, hv, hvα⟩
      refine ⟨v, hv, fun i hi => ?_⟩
      rw [← hαγ i hi]
      exact hvα i hi
    · rintro ⟨v, hv, hvγ⟩
      refine ⟨v, hv, fun i hi => ?_⟩
      rw [hαγ i hi]
      exact hvγ i hi
  · exact actualReducedVertexSeries_degree_prefix_block_support m K k B hB a ha

end

end Hironaka.HironakaActualRelativeStandardnessBlockSupport
