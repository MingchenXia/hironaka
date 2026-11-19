import Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartRank

/-!
# N5.b (P1): graph-chart presentations of a ring map and the N5 conclusion

Lane G10N5, run 0081 (N5.b of `G10HT/STATUS.md`, Hironaka 1975 p. 532).  A *graph-chart presentation* of a ring
map `φ : A → R` with an ideal `D ⊆ A` is an identification of `φ` with the analytic graph chart map
`chartMap (evPoly d r b) j g IX : H_d ⧸ IX → H_{d+r} ⧸ (evPoly(L) : X_j^∞)` (`HironakaG10HtChartSaturation`) under
which `D` corresponds to the centre `(g)`.

* `GraphChartPresentation φ D`;
* `GraphChartPresentation.strictIdeal_eq_powerSat` — N5 for a presented map
  (`HironakaG10HtGraphChartRank.strictIdeal_eq_powerSat_of_graphChart_pos`);
* `GraphChartPresentation.transport` — presentations transport along ring isomorphisms of both sides;
* `N5Holds φ D` — the N5 conclusion for all ideals and all regular generators of the pulled centre;
  `n5Holds_of_presentation`, `n5Holds_of_eq_top` (off the centre: the pulled centre is the unit ideal, so the
  generator is a unit — `HironakaG10HtGraphChartCentre.strictIdeal_eq_powerSat_of_isUnit`).

Pure algebra; no named input.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10NfPresentation

open MvPolynomial Hironaka Hironaka
open Hironaka.HironakaG10ChowArtinReesCentre
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation Hironaka.Analytic.Unibranch.HironakaG10HtPolynomialGermFlat
  Hironaka.Analytic.Unibranch.HironakaG10HtChartSaturation Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartCentre
  Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartRank

noncomputable section

variable {A R : Type*} [CommRing A] [CommRing R]

/-- A **graph-chart presentation** of `φ : A → R` with centre `D`: ring isomorphisms `A ≃ H_d ⧸ IX` and
`R ≃ H_{d+r} ⧸ chartIdeal (evPoly d r b) j g IX` (`r > 0`) intertwining `φ` with the analytic graph chart map, under
which `D` corresponds to `(g)`. -/
def GraphChartPresentation (φ : A →+* R) (D : Ideal A) : Prop :=
  ∃ (d r : ℕ) (_ : 0 < r) (b : Fin r → ℂ) (j : Fin r) (g : Fin r → HolGerm (ComplexModel d))
    (IX : Ideal (HolGerm (ComplexModel d)))
    (α : A ≃+* HolGerm (ComplexModel d) ⧸ IX)
    (ρ : R ≃+* HolGerm (ComplexModel (d + r)) ⧸ chartIdeal (evPoly d r b) j g IX),
    (∀ a, ρ (φ a) = chartMap (evPoly d r b) j g IX (α a)) ∧
    Ideal.map (α : A →+* HolGerm (ComplexModel d) ⧸ IX) D =
      Ideal.map (Ideal.Quotient.mk IX) (Ideal.span (Set.range g))

/-- **N5 for a presented ring map.** -/
theorem GraphChartPresentation.strictIdeal_eq_powerSat {φ : A →+* R} {D : Ideal A}
    (h : GraphChartPresentation φ D) (I : Ideal A) (G : R) (hG : IsRegular G)
    (hGD : Ideal.map φ D = Ideal.span {G}) :
    strictIdeal φ I D G = powerSat (Ideal.map φ I) G := by
  obtain ⟨d, r, hr, b, j, g, IX, α, ρ, hsq, hD⟩ := h
  exact strictIdeal_eq_powerSat_of_graphChart_pos φ d r hr b j g IX α ρ hsq D hD G hG hGD I

/-- **Transport** of a presentation along ring isomorphisms of source and target. -/
theorem GraphChartPresentation.transport {A₂ R₂ : Type*} [CommRing A₂] [CommRing R₂]
    {φ : A →+* R} {D : Ideal A} (h : GraphChartPresentation φ D) (φ₂ : A₂ →+* R₂)
    (e₁ : A ≃+* A₂) (e₂ : R ≃+* R₂) (hsq : ∀ a, φ₂ (e₁ a) = e₂ (φ a)) :
    GraphChartPresentation φ₂ (Ideal.map (e₁ : A →+* A₂) D) := by
  obtain ⟨d, r, hr, b, j, g, IX, α, ρ, hsq', hD⟩ := h
  refine ⟨d, r, hr, b, j, g, IX, e₁.symm.trans α, e₂.symm.trans ρ, ?_, ?_⟩
  · intro a₂
    obtain ⟨a, rfl⟩ := e₁.surjective a₂
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.symm_apply_apply, hsq,
      RingEquiv.symm_apply_apply, hsq']
  · rw [Ideal.map_map, ← hD]
    congr 1
    ext a
    simp

/-- The N5 conclusion for a ring map and a centre. -/
def N5Holds (φ : A →+* R) (D : Ideal A) : Prop :=
  ∀ (I : Ideal A) (G : R), IsRegular G → Ideal.map φ D = Ideal.span {G} →
    strictIdeal φ I D G = powerSat (Ideal.map φ I) G

theorem n5Holds_of_presentation {φ : A →+* R} {D : Ideal A} (h : GraphChartPresentation φ D) :
    N5Holds φ D :=
  fun I G hG hGD => h.strictIdeal_eq_powerSat I G hG hGD

/-- **Off the centre.**  If the centre is the unit ideal, every generator of the pulled centre is a unit. -/
theorem n5Holds_of_eq_top (φ : A →+* R) {D : Ideal A} (hD : D = ⊤) : N5Holds φ D := by
  intro I G _ hGD
  refine strictIdeal_eq_powerSat_of_isUnit φ I D G ?_
  rw [hD, Ideal.map_top, eq_comm, Ideal.span_singleton_eq_top] at hGD
  exact hGD

end

end Hironaka.Analytic.Unibranch.HironakaG10NfPresentation
