import Hironaka.Geometry.QuotGrassmannPivotAffinePullbackProjectivity
import Hironaka.Geometry.QuotGrassmannPivotAffineSectionsRank

/-!
# Exact constant native rank for EVERY affine pullback of SAME original quotient

No rank condition is added. Every original native generator index remains the
same original finite row index, and the internally produced original section
frames calculate native stalk rank at EVERY actual original prime.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- At EVERY actual original affine prime, SAME original global quotient has the exact original row rank. -/
theorem originalGlobalAffinePullbackSections_rankAtStalk
    (R : Type u) [CommRing R] (ι ν : Type u)
    [Fintype ι] [Fintype ν] [DecidableEq ι] {A : CommRingCat.{u}}
    (f : Spec A ⟶ projectiveModel R ι ν) (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A)
      Γ((Scheme.Modules.pullback f).obj (originalGlobalImageQuotient R ι ν), ⊤) p =
        Fintype.card ι := by
  apply originalAffineLocalGeneratorsSections_rankAtStalk
    (originalGlobalAffinePullbackGenerators R ι ν f) (Fintype.card ι) ?_ p
  intro i
  change Nat.card ι = Fintype.card ι
  exact Nat.card_eq_fintype_card

end Hironaka.Geometry.QuotGrassmann
