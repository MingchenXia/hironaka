import Hironaka.Analytic.Unibranch.HironakaG11SingularCentreModification
import Hironaka.Analytic.Unibranch.HironakaG10ChowFlatOpen

/-!
# Hironaka's Chow lemma for compact reduced complex spaces: the statement

Blueprint node `chow:general` (`hironaka-g10-chow.tex`), stated in the native category of reduced
complex spaces (`SourceReducedComplexSpace`): for a compact reduced complex space `X` and a proper
bimeromorphic morphism `f : Y ⟶ X` there are a finite composition `σ : X' ⟶ X` of blowups with
smooth (nowhere dense) centres (`SmoothCentreModification.IsModification`, the book's
modifications, the same predicate whose singular-centre refinement is goal G11) and a morphism
`g : X' ⟶ Y` with `g ≫ f = σ`.

Degenerate cases (checked here): the identity of `X` satisfies the conclusion for `f = 𝟙 X`, and
more generally whenever `f` has a section; the statement makes no dimension, irreducibility or
non-emptiness assumption.

Blueprint: `hironaka-g10-gen-chow-general.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GenStatement

open SourceReducedComplexSpace SmoothCentreModification

noncomputable section

/-- `f : Y ⟶ X` is dominated by a finite composition of smooth-centre blowups: there are
`σ : X' ⟶ X` with `IsModification σ` and `g : X' ⟶ Y` with `g ≫ f = σ`. -/
def IsDominatedByModification {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) : Prop :=
  ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ X) (g : X' ⟶ Y), IsModification σ ∧ g ≫ f = σ

/-- **Hironaka's Chow lemma** (`chow:general`, source `thm:HironakaChow`): every proper
bimeromorphic morphism to a compact reduced complex space is dominated by a finite composition of
blowups with smooth centres. -/
def HironakaChowLemmaGeneral : Prop :=
  ∀ (X Y : SourceReducedComplexSpace) (f : Y ⟶ X), CompactSpace X.obj.left →
    IsProperBimeromorphic f → IsDominatedByModification f

/-- A morphism with a section is dominated by the identity (zero blowups). -/
theorem isDominatedByModification_of_section {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}
    (s : X ⟶ Y) (hs : s ≫ f = 𝟙 X) : IsDominatedByModification f :=
  ⟨X, 𝟙 X, s, .id X, hs⟩

/-- The identity is dominated by the identity. -/
theorem isDominatedByModification_id (X : SourceReducedComplexSpace) :
    IsDominatedByModification (𝟙 X) :=
  isDominatedByModification_of_section (𝟙 X) (Category.comp_id _)

/-- Isomorphisms are dominated by the identity. -/
theorem isDominatedByModification_of_isIso {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    [IsIso f] : IsDominatedByModification f :=
  isDominatedByModification_of_section (inv f) (IsIso.inv_hom_id f)

/-- Domination is stable under composition with a modification `τ` of the base: if `σ`
dominates `f`, then `σ ≫ τ` dominates `f ≫ τ`. -/
theorem IsDominatedByModification.comp {X Y Z : SourceReducedComplexSpace} {f : Y ⟶ X}
    {τ : X ⟶ Z} (hf : IsDominatedByModification f) (hτ : IsModification τ) :
    IsDominatedByModification (f ≫ τ) := by
  obtain ⟨X', σ, g, hσ, hg⟩ := hf
  exact ⟨X', σ ≫ τ, g, hσ.comp hτ, by rw [← Category.assoc, hg]⟩

/-- A modification `σ` followed by `g` with `g ≫ f = σ ≫ τ` and `τ` a modification shows that `f`
is dominated by a modification. -/
theorem isDominatedByModification_of_comp {X X₁ X₂ Y : SourceReducedComplexSpace} {f : Y ⟶ X}
    {τ : X₁ ⟶ X} {ρ : X₂ ⟶ X₁} (g : X₂ ⟶ Y) (hτ : IsModification τ) (hρ : IsModification ρ)
    (h : g ≫ f = ρ ≫ τ) : IsDominatedByModification f :=
  ⟨X₂, ρ ≫ τ, g, hρ.comp hτ, h⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10GenStatement
