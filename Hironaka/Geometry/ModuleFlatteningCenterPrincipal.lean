import Hironaka.Geometry.AffineBlowupBaseChange
import Hironaka.Geometry.PrincipalBlowup
import Hironaka.Geometry.ModificationCenter

/-!
# Actual blowup isomorphisms from exact original principal localization

The actual localization comparison and actual nonzero-principal blowup
isomorphism prove that the literal original blowup restriction is an
isomorphism. The whole ideal, original target principal open and actual
modification isomorphism locus are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ModuleFlatteningCenter

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The literal original blowup is an actual isomorphism over any original
principal open on which the same extended ideal is exactly nonzero principal. -/
theorem isIso_restrict_of_away_principal (I : Ideal R) (a q : R)
    (ha : a ≠ 0) (hq : q ≠ 0)
    (hI : I.map (algebraMap R (Localization.Away a)) =
      Ideal.span ({algebraMap R (Localization.Away a) q} : Set (Localization.Away a))) :
    IsIso (affineBlowupStructure I ∣_ PrimeSpectrum.basicOpen a) := by
  have hM : Submonoid.powers a ≤ nonZeroDivisors R := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n ha)
  let : IsDomain (Localization.Away a) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away a) hM
  have hq' : algebraMap R (Localization.Away a) q ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective (Localization.Away a) hM)).mpr hq
  have hiso : IsIso (affineBlowupStructure (I.map (algebraMap R (Localization.Away a)))) := by
    rw [hI]
    exact PrincipalBlowup.affineBlowupStructure_span_singleton_isIso _ hq'
  let e₁ := AffineBlowupBaseChange.affineBlowupLocalizationIso I a
  let e₂ := basicOpenIsoSpecAway (R := CommRingCat.of R) a
  let f := affineBlowupStructure I ∣_ PrimeSpectrum.basicOpen a
  have hcomp : IsIso (e₁.hom ≫ f ≫ e₂.hom) := by
    dsimp only [e₁, e₂, f]
    rw [AffineBlowupBaseChange.affineBlowupLocalizationIso_hom_structure]
    exact hiso
  let : IsIso ((e₁.hom ≫ f) ≫ e₂.hom) := by simpa only [Category.assoc] using hcomp
  let : IsIso (e₁.hom ≫ f) := IsIso.of_isIso_comp_right (e₁.hom ≫ f) e₂.hom
  exact IsIso.of_isIso_comp_left (f := e₁.hom) f

/-- The actual original principal open belongs to the original blowup's actual isomorphism locus. -/
theorem basicOpen_le_isomorphismOpen_of_away_principal (I : Ideal R) (a q : R)
    (ha : a ≠ 0) (hq : q ≠ 0)
    (hI : I.map (algebraMap R (Localization.Away a)) =
      Ideal.span ({algebraMap R (Localization.Away a) q} : Set (Localization.Away a))) :
    PrimeSpectrum.basicOpen a ≤ ModificationCenter.isomorphismOpen (affineBlowupStructure I) :=
  (ModificationCenter.le_isomorphismOpen_iff _ _).mpr
    (isIso_restrict_of_away_principal I a q ha hq hI)

end Hironaka.Geometry.ModuleFlatteningCenter
