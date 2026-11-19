import Hironaka.Resolution.HironakaActualReducedFormalStandardBasis
import Hironaka.Resolution.HironakaActualHomogeneousInitialHS
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Stable directions annihilate the unchanged canonical reduced vertices

The full reduced coefficient rule makes every partial supported off the
entire source diagram. Whole-ideal directional stability then forces zero.
This applies to arbitrary constant directions, without choosing a new basis.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualCanonicalVertexDirectionalInvariance

noncomputable section

open HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualHomogeneousInitialHS HironakaRelativeNormalMonomialBasis

variable {n : ℕ}

/-- Every coordinate derivative of the literal canonical member is normal on the ENTIRE source diagram. -/
theorem coeff_pderiv_actualReducedVertexSeries_diagram
    (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices m I) (i : Fin n)
    (c : Fin n →₀ ℕ) (hc : c ∈ actualInitialDiagram m I) :
    MvPowerSeries.coeff c (MvPowerSeries.pderiv ℂ i (actualReducedVertexSeries m I a)) = 0 := by
  have hcle : c ≤ c + Finsupp.single i 1 := by
    intro j
    simp only [Finsupp.add_apply]
    omega
  have hupper : c + Finsupp.single i 1 ∈ actualInitialDiagram m I :=
    actualInitialDiagram_upper m I c _ hc hcle
  have hne : c + Finsupp.single i 1 ≠ a.val := by
    intro he
    have hminimal : Minimal (· ∈ actualInitialDiagram m I) a.val := by
      simpa [actualInitialVertices] using a.property
    have hca : c ≤ a.val := by rwa [he] at hcle
    have hac := hminimal.2 hc hca
    have hi := hac i
    rw [← he] at hi
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hi
    omega
  rw [MvPowerSeries.coeff_pderiv,
    actualReducedVertexSeries_coefficient_diagram m I a _ hupper, if_neg hne, zero_mul]

/-- Actual stability in ANY constant direction annihilates each SAME canonical reduced vertex member. -/
theorem directional_pderiv_actualReducedVertexSeries_eq_zero
    (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (v : Fin n → ℂ)
    (hD : ∀ F ∈ I, (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ I)
    (a : actualInitialVertices m I) :
    (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i (actualReducedVertexSeries m I a)) = 0 := by
  apply eq_zero_of_mem_of_diagram_coefficients_zero m I
  · exact hD _ (actualReducedVertexSeries_mem m I a)
  · intro c hc
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _hi
    rw [map_smul, coeff_pderiv_actualReducedVertexSeries_diagram m I a i c hc, smul_zero]

/-- In particular a stable coordinate partial vanishes on every canonical reduced member. -/
theorem pderiv_actualReducedVertexSeries_eq_zero_of_stable
    (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (i : Fin n)
    (hD : ∀ F ∈ I, MvPowerSeries.pderiv ℂ i F ∈ I)
    (a : actualInitialVertices m I) :
    MvPowerSeries.pderiv ℂ i (actualReducedVertexSeries m I a) = 0 := by
  apply eq_zero_of_mem_of_diagram_coefficients_zero m I
  · exact hD _ (actualReducedVertexSeries_mem m I a)
  · exact coeff_pderiv_actualReducedVertexSeries_diagram m I a i

/-- The actual homogeneous initial ideal retains the literal original vertex exponent. -/
def actualHomogeneousInitialVertex
    (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex I) :
    actualInitialVertices MonomialOrder.degLex (actualHomogeneousInitialIdeal I) :=
  ⟨a.val, by
    simpa [actualInitialVertices, actual_homogeneous_initial_ideal_diagram] using a.property⟩

/-- The leading component of the source canonical member is the SAME canonical member of the whole homogeneous initial ideal. -/
theorem homogeneousComponent_actualReducedVertexSeries_eq_initial
    (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex I) :
    (MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex I a) : MvPowerSeries (Fin n) ℂ) =
        actualReducedVertexSeries MonomialOrder.degLex (actualHomogeneousInitialIdeal I)
          (actualHomogeneousInitialVertex I a) := by
  let G := actualReducedVertexSeries MonomialOrder.degLex I a
  have hne : G ≠ 0 := actualReducedVertexSeries_ne_zero MonomialOrder.degLex I a
  have hdegree : actualHomogeneousInitialDegree G hne = normalExponentDegree a.val := by
    rw [actualHomogeneousInitialDegree]
    exact congrArg normalExponentDegree (actualReducedVertexSeries_initialExponent MonomialOrder.degLex I a)
  have hmem : (MvPowerSeries.homogeneousComponent (normalExponentDegree a.val) G :
      MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal I := by
    have hinit : actualHomogeneousInitialForm G hne ∈ actualHomogeneousInitialIdeal I :=
      Ideal.subset_span ⟨⟨G, actualReducedVertexSeries_mem MonomialOrder.degLex I a, hne⟩, rfl⟩
    simpa only [actualHomogeneousInitialForm, hdegree] using hinit
  apply actualReducedVertexSeries_unique MonomialOrder.degLex (actualHomogeneousInitialIdeal I)
    (actualHomogeneousInitialVertex I a) _ hmem
  intro c hc
  have hcI : c ∈ actualInitialDiagram MonomialOrder.degLex I := by
    rwa [actual_homogeneous_initial_ideal_diagram] at hc
  rw [MvPowerSeries.coeff_homogeneousComponent,
    actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex I a c hcI]
  change (if Finsupp.degree c = normalExponentDegree a.val then
      if c = a.val then (1 : ℂ) else 0 else 0) = if c = a.val then 1 else 0
  by_cases he : c = a.val
  · subst c
    have hd : Finsupp.degree a.val = normalExponentDegree a.val := by
      simp only [Finsupp.degree_eq_sum, normalExponentDegree]
    simp only [hd, ite_true]
  · simp only [he, ite_false, ite_self]

/-- Stability of the homogeneous initial ideal ALONE annihilates each unchanged source leading component in that direction. -/
theorem directional_pderiv_homogeneousComponent_actualReducedVertexSeries_eq_zero
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (v : Fin n → ℂ)
    (hD : ∀ F ∈ actualHomogeneousInitialIdeal I,
      (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal I)
    (a : actualInitialVertices MonomialOrder.degLex I) :
    (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i
      (MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
        (actualReducedVertexSeries MonomialOrder.degLex I a))) = 0 := by
  rw [homogeneousComponent_actualReducedVertexSeries_eq_initial]
  exact directional_pderiv_actualReducedVertexSeries_eq_zero MonomialOrder.degLex
    (actualHomogeneousInitialIdeal I) v hD (actualHomogeneousInitialVertex I a)

/-- The coordinate form needs only stability of the whole homogeneous initial ideal. -/
theorem pderiv_homogeneousComponent_actualReducedVertexSeries_eq_zero_of_stable
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (i : Fin n)
    (hD : ∀ F ∈ actualHomogeneousInitialIdeal I,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal I)
    (a : actualInitialVertices MonomialOrder.degLex I) :
    MvPowerSeries.pderiv ℂ i
      (MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
        (actualReducedVertexSeries MonomialOrder.degLex I a)) = 0 := by
  rw [homogeneousComponent_actualReducedVertexSeries_eq_initial]
  exact pderiv_actualReducedVertexSeries_eq_zero_of_stable MonomialOrder.degLex
    (actualHomogeneousInitialIdeal I) i hD (actualHomogeneousInitialVertex I a)

end

end Hironaka.HironakaActualCanonicalVertexDirectionalInvariance
