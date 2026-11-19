import Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartN5

/-!
# N5 on a graph chart: the pulled centre is principal on the chart, and the off-centre case

Lane G10HT, run 0081 (N5, Hironaka 1975 p. 532).  Complements `HironakaG10HtGraphChartN5`:

* `map_chartMap_centre` — on the chart ring `H ⧸ (ev(L) : ev(X_j)^∞)` the pulled centre `(g)` is the principal ideal
  of the exceptional equation `ev(X_j)` (since `g_i ≡ X_j X_i`, `g_j ≡ X_j` there);
* `strictIdeal_eq_powerSat_of_graphChart'` — the graph-chart N5 with the generator hypothesis in the form used by
  the native N5 (`Ideal.map φ D = Ideal.span {G}`), i.e. without a separate comparison of `G` with `X_j`;
* `strictIdeal_eq_powerSat_of_isUnit` — off the centre (unit equation) the strict ideal is the total transform, for
  every ring map: the native N5 needs charts only at points of the exceptional divisor.

Pure algebra; no named input.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartCentre

open MvPolynomial Hironaka Hironaka
open Hironaka.HironakaG10ChowArtinReesCentre
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation Hironaka.Analytic.Unibranch.HironakaG10HtStrictSaturation
  Hironaka.Analytic.Unibranch.HironakaG10HtPolynomialGermFlat Hironaka.Analytic.Unibranch.HironakaG10HtChartSaturation
  Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartN5

noncomputable section

/-- **Off the centre**: if the equation `G` is a unit, the algebraic strict ideal is the whole saturation (both are
the total transform). -/
theorem strictIdeal_eq_powerSat_of_isUnit {A R : Type*} [CommRing A] [CommRing R] (φ : A →+* R)
    (I D : Ideal A) (G : R) (hG : IsUnit G) :
    strictIdeal φ I D G = powerSat (Ideal.map φ I) G := by
  refine le_antisymm (strictIdeal_le_powerSat φ I D G) ?_
  intro a ha
  obtain ⟨m, hm⟩ := mem_powerSat.mp ha
  have hmem : a ∈ Ideal.map φ I := by
    obtain ⟨u, hu⟩ := hG.pow m
    have := (Ideal.map φ I).mul_mem_left (↑u⁻¹ : R) hm
    rwa [← hu, ← mul_assoc, Units.inv_mul, one_mul] at this
  refine (Ideal.map_le_iff_le_comap.mpr ?_) hmem
  intro h hh
  refine Ideal.subset_span ⟨0, h, ⟨hh, by simp⟩, by simp⟩

section Chart

variable {B H : Type*} [CommRing B] [CommRing H] {n : ℕ} (ev : MvPolynomial (Fin n) B →+* H)

/-- On the chart ring, the pulled centre `(g)` is the principal ideal of `ev(X_j)`. -/
theorem map_chartMap_centre (j : Fin n) (g : Fin n → B) (IX : Ideal B) :
    Ideal.map (chartMap ev j g IX) (Ideal.map (Ideal.Quotient.mk IX) (Ideal.span (Set.range g))) =
      Ideal.span {Ideal.Quotient.mk (chartIdeal ev j g IX) (ev (X j))} := by
  set K := chartIdeal ev j g IX
  have hLK : Ideal.map ev (relIdeal j g IX) ≤ K := le_powerSat _ _
  -- `g_i ≡ X_j * (X_i or 1)` modulo `K`
  have hgi : ∀ i, Ideal.Quotient.mk K (ev (C (g i))) =
      Ideal.Quotient.mk K (ev (X j)) * Ideal.Quotient.mk K (ev (if i = j then 1 else X i)) := by
    intro i
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← map_sub]
    by_cases hij : i = j
    · subst hij
      have := hLK (Ideal.mem_map_of_mem ev (pivot_mem_relIdeal i g IX))
      rw [if_pos rfl, mul_one, ← neg_sub, map_neg]
      exact K.neg_mem this
    · have := hLK (Ideal.mem_map_of_mem ev (ratio_mem_relIdeal j g IX hij))
      rw [if_neg hij, ← neg_sub, map_neg]
      exact K.neg_mem this
  rw [Ideal.map_map, Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    change chartMap ev j g IX (Ideal.Quotient.mk IX (g i)) ∈ _
    rw [chartMap_mk]
    change Ideal.Quotient.mk K (ev (C (g i))) ∈ _
    rw [hgi i]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_singleton_le_iff_mem]
    have hj := hgi j
    rw [if_pos rfl, map_one, map_one, mul_one] at hj
    rw [← hj]
    refine Ideal.subset_span ⟨j, ?_⟩
    change chartMap ev j g IX (Ideal.Quotient.mk IX (g j)) = _
    rw [chartMap_mk]

end Chart

/-- **Graph-chart N5, native generator form**: as `strictIdeal_eq_powerSat_of_graphChart`, with the hypothesis on
`G` only that it is regular and generates the pulled centre. -/
theorem strictIdeal_eq_powerSat_of_graphChart' {A R : Type*} [CommRing A] [CommRing R] (φ : A →+* R)
    (d r : ℕ) (b : Fin (r + 1) → ℂ) (j : Fin (r + 1)) (g : Fin (r + 1) → HolGerm (ComplexModel d))
    (IX : Ideal (HolGerm (ComplexModel d)))
    (α : A ≃+* HolGerm (ComplexModel d) ⧸ IX)
    (ρ : R ≃+* HolGerm (ComplexModel (d + (r + 1))) ⧸ chartIdeal (evPoly d (r + 1) b) j g IX)
    (hsq : ∀ a, ρ (φ a) = chartMap (evPoly d (r + 1) b) j g IX (α a))
    (D : Ideal A)
    (hD : Ideal.map (α : A →+* HolGerm (ComplexModel d) ⧸ IX) D =
      Ideal.map (Ideal.Quotient.mk IX) (Ideal.span (Set.range g)))
    (G : R) (hG : IsRegular G) (hGD : Ideal.map φ D = Ideal.span {G}) (I : Ideal A) :
    strictIdeal φ I D G = powerSat (Ideal.map φ I) G := by
  refine strictIdeal_eq_powerSat_of_graphChart φ d r b j g IX α ρ hsq D hD G hG ?_ I
  have h1 : Ideal.map (ρ : R →+* _) (Ideal.map φ D) =
      Ideal.map (chartMap (evPoly d (r + 1) b) j g IX)
        (Ideal.map (α : A →+* HolGerm (ComplexModel d) ⧸ IX) D) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    exact hsq a
  rw [hGD, Ideal.map_span, Set.image_singleton, hD, map_chartMap_centre] at h1
  exact h1

end

end Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartCentre
