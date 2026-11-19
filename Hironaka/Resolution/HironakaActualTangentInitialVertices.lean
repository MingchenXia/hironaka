import Hironaka.Resolution.HironakaActualHomogeneousInitialHS
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Pure normal vertices from tangent differential stability

A positive leading coordinate decreases by one under the corresponding formal
partial derivative. Stability of an entire ideal therefore forces that coordinate
to vanish in every actual diagram vertex. Applying the unchanged homogeneous
initial-diagram dictionary gives pure normal vertices of the original ideal.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualTangentInitialVertices

noncomputable section

open HironakaActualFormalInitialDiagram HironakaActualHomogeneousInitialHS
  HironakaRelativeNormalMonomialBasis

variable {n : ℕ}

/-- A positive coordinate in the actual initial exponent decreases by exactly one
under the same partial derivative, which remains nonzero. -/
theorem actualInitialExponent_pderiv_of_pos (m : MonomialOrder (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) (i : Fin n)
    (hi : 0 < actualInitialExponent m F hF i) :
    ∃ hD : MvPowerSeries.pderiv ℂ i F ≠ 0,
      actualInitialExponent m (MvPowerSeries.pderiv ℂ i F) hD =
        actualInitialExponent m F hF - Finsupp.single i 1 := by
  let a := actualInitialExponent m F hF
  let u := a - Finsupp.single i 1
  have hsingle : Finsupp.single i 1 ≤ a := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Finsupp.single_eq_same] using (Nat.succ_le_iff.mpr hi)
    · simp only [Finsupp.single_eq_of_ne hj, zero_le]
  have hu : u + Finsupp.single i 1 = a := tsub_add_cancel_of_le hsingle
  have hc : MvPowerSeries.coeff u (MvPowerSeries.pderiv ℂ i F) ≠ 0 := by
    rw [MvPowerSeries.coeff_pderiv, hu]
    apply mul_ne_zero (actualInitialExponent_spec m F hF).1
    exact_mod_cast Nat.succ_ne_zero (u i)
  have hD : MvPowerSeries.pderiv ℂ i F ≠ 0 := by
    intro hz
    exact hc (by rw [hz, map_zero])
  refine ⟨hD, ?_⟩
  apply actualInitialExponent_eq_of_coefficients m _ hD u hc
  intro b hb
  rw [MvPowerSeries.coeff_pderiv]
  have hba : m.toSyn (b + Finsupp.single i 1) < m.toSyn a := by
    rw [← hu, map_add, map_add]
    simpa only [add_comm] using
      (add_lt_add_right hb (m.toSyn (Finsupp.single i 1)))
  rw [coeff_eq_zero_of_lt_actualInitialExponent m F hF _ hba, zero_mul]

/-- An entire derivative-stable ideal has no positive vertex exponent in that
coordinate; the actual ideal and diagram are unchanged. -/
theorem actualInitialVertex_coordinate_eq_zero_of_pderiv_stable
    (m : MonomialOrder (Fin n)) (J : Ideal (MvPowerSeries (Fin n) ℂ)) (i : Fin n)
    (hD : ∀ F ∈ J, MvPowerSeries.pderiv ℂ i F ∈ J)
    (a : actualInitialVertices m J) : a.val i = 0 := by
  have ha : Minimal (· ∈ actualInitialDiagram m J) a.val := by
    simpa [actualInitialVertices] using a.property
  by_contra hi
  have hpos : 0 < a.val i := Nat.pos_of_ne_zero hi
  obtain ⟨F, hFJ, hF, hFa⟩ := ha.prop
  have hFi : 0 < actualInitialExponent m F hF i := by rwa [hFa]
  obtain ⟨hDF, hDFa⟩ := actualInitialExponent_pderiv_of_pos m F hF i hFi
  have hPred : a.val - Finsupp.single i 1 ∈ actualInitialDiagram m J := by
    refine ⟨MvPowerSeries.pderiv ℂ i F, hD F hFJ, hDF, ?_⟩
    simpa only [hFa] using hDFa
  have hle : a.val ≤ a.val - Finsupp.single i 1 := ha.2 hPred tsub_le_self
  have hcoord := hle i
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hcoord
  omega

/-- Tangent partial stability of the actual homogeneous initial ideal forces the
same original degree-first vertices to have zero tangent exponents. -/
theorem actualInitialVertex_tangent_eq_zero (d t : ℕ)
    (K : Ideal (MvPowerSeries (Fin (d + t)) ℂ))
    (hD : ∀ i : Fin d, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) (i : Fin d) :
    a.val (i.castAdd t) = 0 := by
  have ha : a.val ∈ actualInitialVertices MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) := by
    simpa [actualInitialVertices, actual_homogeneous_initial_ideal_diagram] using a.property
  exact actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
    (actualHomogeneousInitialIdeal K) (i.castAdd t) (hD i) ⟨a.val, ha⟩

/-- The original total degree equals the normal-coordinate degree at every vertex. -/
theorem actualInitialVertex_degree_eq_normal_sum (d t : ℕ)
    (K : Ideal (MvPowerSeries (Fin (d + t)) ℂ))
    (hD : ∀ i : Fin d, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    normalExponentDegree a.val = ∑ j : Fin t, a.val (j.natAdd d) := by
  rw [normalExponentDegree, Fin.sum_univ_add]
  have hz : (∑ i : Fin d, a.val (i.castAdd t)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact actualInitialVertex_tangent_eq_zero d t K hD a i
  rw [hz, zero_add]

end

end Hironaka.HironakaActualTangentInitialVertices
