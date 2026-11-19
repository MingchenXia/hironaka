import Hironaka.Geometry.QuotGrassmannPivotAffineProjectiveSections
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Exact native affine-section rank from SAME original generating indices

The original global section module is internally proved finite and projective.
Actual original principal restriction maps are module localizations/base changes.
Every original prime is covered and its rank is computed by the actual native
section frame. No stalk-rank or projectivity output is supplied as an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native rank of SAME original affine sections, calculated from their ORIGINAL finite generator cardinalities. -/
theorem originalAffineLocalGeneratorsSections_rankAtStalk
    {A : CommRingCat.{u}} {M : (Spec A).Modules} [M.IsQuasicoherent]
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType]
    (r : ℕ) (hr : ∀ i : q.I, Nat.card (q.generators i).I = r)
    (p : PrimeSpectrum A) : Module.rankAtStalk (R := A) Γ(M, ⊤) p = r := by
  have hfp := originalAffineLocalGeneratorsSections_finitePresentation_projective q
  let := hfp.1
  let := hfp.2
  let t := originalAffinePrincipalGeneratorElements q
  have hn : ¬ t ⊆ (p.asIdeal : Set A) := by
    intro hp
    have H : (⊤ : Ideal A) ≤ p.asIdeal := by
      rw [← originalAffinePrincipalGeneratorElements_span q]
      exact Ideal.span_le.mpr hp
    exact p.isPrime.ne_top (top_unique H)
  obtain ⟨g, hg, hgp⟩ := Set.not_subset.mp hn
  let gg : t := ⟨g, hg⟩
  let B := Γ(Spec A, PrimeSpectrum.basicOpen g)
  let φ : Γ(M, ⊤) →ₗ[A] Γ(M, PrimeSpectrum.basicOpen g) :=
    originalAffinePrincipalGeneratorRestriction q gg
  let : Algebra A B := inferInstance
  let : IsLocalization.Away g B := inferInstance
  let : IsScalarTower A B Γ(M, PrimeSpectrum.basicOpen g) := inferInstance
  let : IsLocalizedModule.Away g φ :=
    originalAffinePrincipalGeneratorRestriction_isLocalizedModule q gg
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
    rw [PrimeSpectrum.localization_away_comap_range B g]
    exact hgp
  obtain ⟨P, hP⟩ := hp
  have hbc : IsBaseChange B φ := IsLocalizedModule.isBaseChange (.powers g) B φ
  have hb := Module.rankAtStalk_isBaseChange hbc P
  obtain ⟨i, hi⟩ := hg
  calc
    _ = Module.rankAtStalk (R := A) Γ(M, ⊤) (P.comap (algebraMap A B)) :=
      congrArg (Module.rankAtStalk (R := A) Γ(M, ⊤)) hP.symm
    _ = Module.rankAtStalk (R := B) Γ(M, PrimeSpectrum.basicOpen g) P := hb.symm
    _ = Nat.card (q.generators i).I :=
      originalLocalGeneratorSubopenSections_rankAtStalk q i _ hi P
    _ = r := hr i

end Hironaka.Geometry.QuotGrassmann
