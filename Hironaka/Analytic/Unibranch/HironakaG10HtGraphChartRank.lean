import Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartCentre

/-!
# Graph-chart N5 for an arbitrary positive number of generators

Lane G10HT, run 0081.  The landed chart results are stated for `r + 1` generators (flatness is proved by induction
from one variable); the centres of the native blowups come with a rank `t.rank` that is only known to be positive
(`CanonicalTargetGraph.positive`).  This module restates them for any `r > 0`:

* `evPoly_flat_of_pos` — `HironakaG10HtPolynomialGermFlat.evPoly d r b` is flat for `0 < r`;
* `strictIdeal_eq_powerSat_of_graphChart_pos` — `HironakaG10HtGraphChartCentre.strictIdeal_eq_powerSat_of_graphChart'`
  for `0 < r`.

No named input.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartRank

open MvPolynomial Hironaka Hironaka
open Hironaka.HironakaG10ChowArtinReesCentre
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation Hironaka.Analytic.Unibranch.HironakaG10HtPolynomialGermFlat
  Hironaka.Analytic.Unibranch.HironakaG10HtChartSaturation Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartCentre

noncomputable section

theorem evPoly_flat_of_pos (d r : ℕ) (hr : 0 < r) (b : Fin r → ℂ) : (evPoly d r b).Flat := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  exact evPoly_flat d r' b

theorem strictIdeal_eq_powerSat_of_graphChart_pos {A R : Type*} [CommRing A] [CommRing R] (φ : A →+* R)
    (d r : ℕ) (hr : 0 < r) (b : Fin r → ℂ) (j : Fin r) (g : Fin r → HolGerm (ComplexModel d))
    (IX : Ideal (HolGerm (ComplexModel d)))
    (α : A ≃+* HolGerm (ComplexModel d) ⧸ IX)
    (ρ : R ≃+* HolGerm (ComplexModel (d + r)) ⧸ chartIdeal (evPoly d r b) j g IX)
    (hsq : ∀ a, ρ (φ a) = chartMap (evPoly d r b) j g IX (α a))
    (D : Ideal A)
    (hD : Ideal.map (α : A →+* HolGerm (ComplexModel d) ⧸ IX) D =
      Ideal.map (Ideal.Quotient.mk IX) (Ideal.span (Set.range g)))
    (G : R) (hG : IsRegular G) (hGD : Ideal.map φ D = Ideal.span {G}) (I : Ideal A) :
    strictIdeal φ I D G = powerSat (Ideal.map φ I) G := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  exact strictIdeal_eq_powerSat_of_graphChart' φ d r' b j g IX α ρ hsq D hD G hG hGD I

end

end Hironaka.Analytic.Unibranch.HironakaG10HtGraphChartRank
