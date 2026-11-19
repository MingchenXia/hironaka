import Hironaka.Resolution.HironakaActualAnalyticSubspaceResidue
import Mathlib.Algebra.Regular.Basic

/-!
# Nonzero coordinate denominators at actual singular Cartier stalks

The whole principal ideal is generated in the original quotient stalk.
Only its chosen Cartier generator is assumed regular: the stalk may have
zero divisors. Evaluation is the existing actualSubspaceStalkEval to ℂ.
This supplies a stalk denominator, not local representatives or global gluing.

Blueprint: `hironaka-singular-blowup-denominator.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaSingularBlowupDenominator

open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue

noncomputable section

/-- Cancellation by a regular generator suffices; the ring need not be a domain. -/
theorem exists_eval_ne_zero_of_mem_span_multiples
    {R : Type*} [CommRing R] {ι : Type*}
    (e : R →+* ℂ) {alpha : R} (halpha : IsRegular alpha) (q : ι → R)
    (hmem : alpha ∈ Ideal.span (Set.range fun i => alpha * q i)) :
    ∃ i, e (q i) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hprop : ∃ a : R, e a = 0 ∧ alpha = alpha * a := by
    refine Submodule.span_induction
      (p := fun x _ => ∃ a : R, e a = 0 ∧ x = alpha * a) ?_ ?_ ?_ ?_ hmem
    · rintro x ⟨i, rfl⟩
      exact ⟨q i, hn i, rfl⟩
    · exact ⟨0, by simp, by simp⟩
    · rintro x y _ _ ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
      refine ⟨a + b, by simp [ha, hb], ?_⟩
      rw [hxa, hyb, mul_add]
    · rintro r x _ ⟨a, ha, hxa⟩
      refine ⟨r * a, by simp [ha], ?_⟩
      simp only [smul_eq_mul, hxa]
      ring
  obtain ⟨a, ha, hea⟩ := hprop
  have ha1 : a = 1 := halpha.left (by simpa only [mul_one] using hea.symm)
  have h10 : (1 : ℂ) = 0 := by simpa only [ha1, map_one] using ha
  exact one_ne_zero h10

/-- The original whole principal ideal yields actual quotient-stalk ratios and
one nonzero actual point value, with no domain or desired denominator input. -/
theorem exists_actual_stalk_quotients_of_principal_span
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {ι : Type*} (C : Set M) (x : C)
    {alpha : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier}
    (halpha : IsRegular alpha)
    (g : ι → ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier)
    (hspan : Ideal.span (Set.range g) = Ideal.span {alpha}) :
    ∃ q : ι → ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier,
      (∀ i, g i = alpha * q i) ∧
      ∃ i, actualSubspaceStalkEval (n := n) C x (q i) ≠ 0 := by
  classical
  have hdiv : ∀ i, alpha ∣ g i := by
    intro i
    apply Ideal.mem_span_singleton.mp
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose q hq using hdiv
  have hmem : alpha ∈ Ideal.span (Set.range fun i => alpha * q i) := by
    have hm : alpha ∈ Ideal.span (Set.range g) := by
      rw [hspan]
      exact Ideal.subset_span (Set.mem_singleton _)
    have heq : g = (fun i => alpha * q i) := funext hq
    rwa [heq] at hm
  exact ⟨q, hq, exists_eval_ne_zero_of_mem_span_multiples
    (actualSubspaceStalkEval (n := n) C x) halpha q hmem⟩

end

end Hironaka.HironakaSingularBlowupDenominator
