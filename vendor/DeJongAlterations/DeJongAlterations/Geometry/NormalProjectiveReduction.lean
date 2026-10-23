import DeJongAlterations.Geometry.NormalizationProjective
import DeJongAlterations.Geometry.ProjectiveReduction
import DeJongAlterations.Geometry.CartierDominantPullback

/-!
# Full conditional normal projective Cartier reduction, de Jong 4.10

The actual normalization and actual original ideal pullback are constructed.
Existence for normal projective Cartier pairs is an explicit remaining premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.NormalProjectiveReduction

open NormalizationGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The literal normalization retains every projective Cartier-pair hypothesis. -/
theorem normalization_preparation (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hp : IsProjectiveOver p) (D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hproper : D.support ≠ ⊤) :
    IsVariety (normalizationStructure X ≫ p) ∧
      IsProjectiveOver (normalizationStructure X ≫ p) ∧
      IsNormalScheme (normalization X) ∧ IsFinite (normalizationStructure X) ∧
      IsModification (normalizationStructure X) ∧
      IsGenericallyEtale (normalizationStructure X) ∧
      IsEffectiveCartierDivisor (D.comap (normalizationStructure X)) ∧
      (D.comap (normalizationStructure X)).support ≠ ⊤ := by
  let : IsIntegral (normalization X) := NormalizationFinite.isIntegral_normalization
  let : IsAlteration (normalizationStructure X) :=
    NormalizationFiniteArbitraryField.normalizationStructure_isAlteration p
  refine ⟨NormalizationFiniteArbitraryField.normalization_isVariety p,
    NormalizationProjective.normalization_isProjectiveOver p hp,
    normalization_isNormalScheme X,
    NormalizationFiniteArbitraryField.normalizationStructure_isFinite p,
    NormalizationFiniteArbitraryField.normalizationStructure_isModification p,
    NormalizationFiniteArbitraryField.normalizationStructure_isGenericallyEtale p,
    CartierDominantPullback.isEffectiveCartierDivisor_comap _ D hD, ?_⟩
  rw [Scheme.IdealSheafData.support_comap]
  exact ProjectiveReduction.alteration_preimage_ne_top _ D.support hproper

/-- Full boundary output reduces to the explicit normal projective Cartier-case premise. -/
theorem reduce_normal_projective_cartier_case (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hp : IsProjectiveOver p) (D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hproper : D.support ≠ ⊤)
    (hnormal : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)),
      IsVariety q → IsProjectiveOver q → IsNormalScheme Y →
        ∀ E : Y.IdealSheafData, IsEffectiveCartierDivisor E → E.support ≠ ⊤ →
          Nonempty (AlterationWithBoundary q (E.support : Set Y))) :
    Nonempty (AlterationWithBoundary p (D.support : Set X)) := by
  obtain ⟨hv, hproj, hn, -, hm, -, hE, hEp⟩ := normalization_preparation p hp D hD hproper
  let : IsModification (normalizationStructure X) := hm
  obtain ⟨d⟩ := hnormal (normalization X) (normalizationStructure X ≫ p)
    hv hproj hn (D.comap (normalizationStructure X)) hE hEp
  exact ⟨ProjectiveReduction.compOutput (normalizationStructure X)
    (by simp only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]) d⟩

/-- The same normalization reduction retains generic étaleness and the same smooth compactification. -/
theorem reduce_normal_projective_cartier_case_refined
    (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hp : IsProjectiveOver p) (D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hproper : D.support ≠ ⊤)
    (hnormal : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)),
      IsVariety q → IsProjectiveOver q → IsNormalScheme Y →
        ∀ E : Y.IdealSheafData, IsEffectiveCartierDivisor E → E.support ≠ ⊤ →
          ∃ d : AlterationWithBoundary q (E.support : Set Y),
            IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure) :
    ∃ d : AlterationWithBoundary p (D.support : Set X),
      IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure := by
  obtain ⟨hv, hproj, hn, -, hm, hge, hE, hEp⟩ := normalization_preparation p hp D hD hproper
  let : IsModification (normalizationStructure X) := hm
  obtain ⟨d, hd, hs⟩ := hnormal (normalization X) (normalizationStructure X ≫ p)
    hv hproj hn (D.comap (normalizationStructure X)) hE hEp
  have heq : ((D.comap (normalizationStructure X)).support : Set (normalization X)) =
      (normalizationStructure X) ⁻¹' (D.support : Set X) := by
    simp only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  exact ⟨ProjectiveReduction.compOutput (normalizationStructure X) heq d,
    ProjectiveReduction.compOutput_genericallyEtale _ heq d hge hd, by
      simpa only [ProjectiveReduction.compOutput_compactificationStructure] using hs⟩

end DeJongAlterations.Geometry.NormalProjectiveReduction
