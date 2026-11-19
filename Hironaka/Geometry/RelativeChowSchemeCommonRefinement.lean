import Hironaka.Geometry.RelativeChowScheme
import Hironaka.Geometry.AlterationCommonRefinement

/-!
# The full projective common-refinement lemma over integral Noetherian schemes

The actual reduced-component common alteration is refined by the genuine
nonaffine relative Chow construction. Its actual closed immersion into
native relative projective space proves relative projectivity over the
original scheme. No affine, field, separated-base, dominating-component,
or projectivity certificate is supplied.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.RelativeChow

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]

/-- De Jong 5.4 over the original arbitrary integral Noetherian scheme:
an actual projective common alteration with every actual alteration
comparison and exact triangle, including for the empty family. -/
theorem exists_projective_finite_common_refinement_over_scheme
    [IsIntegral S] (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i, Y i ⟶ S)
    (hf : ∀ i, IsAlteration (f i)) :
    ∃ (W : Scheme.{u}) (q : W ⟶ S) (a : ∀ i, W ⟶ Y i)
      (d : ℕ) (e : W ⟶ relativeSpace S d),
      IsAlteration q ∧ (∀ i, IsAlteration (a i)) ∧ (∀ i, a i ≫ f i = q) ∧
      IsClosedImmersion e ∧ e ≫ relativeStructure S d = q := by
  obtain ⟨V, r, b, hr, hb, htri⟩ :=
    AlterationCommonRefinement.exists_finite_common_refinement n Y f hf
  let := hr
  let := hr.sourceIntegral
  obtain ⟨W, π, d, e, hπ, he, heq⟩ := exists_scheme_projective_source_of_isProper r
  let := hπ
  refine ⟨W, π ≫ r, fun i => π ≫ b i, d, e,
    IsAlteration.comp π r, ?_, ?_, he, heq⟩
  · intro i
    let := hb i
    exact IsAlteration.comp π (b i)
  · intro i
    rw [Category.assoc, htri]

/-- The two-alteration form over an arbitrary Noetherian scheme; the
integrality of the base is obtained from the actual input alterations. -/
theorem exists_projective_common_refinement_over_scheme
    {Y₁ Y₂ : Scheme.{u}} (f : Y₁ ⟶ S) (g : Y₂ ⟶ S)
    [hf : IsAlteration f] [hg : IsAlteration g] :
    ∃ (W : Scheme.{u}) (a : W ⟶ Y₁) (b : W ⟶ Y₂)
      (d : ℕ) (e : W ⟶ relativeSpace S d),
      IsAlteration a ∧ IsAlteration b ∧ IsAlteration (a ≫ f) ∧
      a ≫ f = b ≫ g ∧ IsClosedImmersion e ∧ e ≫ relativeStructure S d = a ≫ f := by
  obtain ⟨V, r, s, hr, hs, hrs⟩ := AlterationCommonRefinement.exists_common_refinement f g
  let := hr
  let := hs
  let := hr.sourceIntegral
  let : IsAlteration (r ≫ f) := IsAlteration.comp r f
  obtain ⟨W, π, d, e, hπ, he, heq⟩ :=
    exists_scheme_projective_source_of_isProper (r ≫ f)
  let := hπ
  let : IsAlteration (π ≫ r) := IsAlteration.comp π r
  refine ⟨W, π ≫ r, π ≫ s, d, e, inferInstance, IsAlteration.comp π s,
    IsAlteration.comp (π ≫ r) f, ?_, he, ?_⟩
  · rw [Category.assoc, hrs, Category.assoc]
  · simpa only [Category.assoc] using heq

end Hironaka.Geometry.RelativeChow
