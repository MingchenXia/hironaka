import Hironaka.Analytic.Unibranch.HironakaG11NativeTowerRepresentation
import Hironaka.Analytic.Unibranch.HironakaG10ChowPairInjective

/-!
# Global flattening reduces to a smooth initial base

First construct actual strict-transform data along any literal native tower,
without any flatness hypothesis. The compact G11 resolution then reduces the
original global flattening endpoint to exactly that endpoint restricted to
compact smooth initial bases. The restricted flattening theorem remains an
explicit input; no flatness theorem or later-stage smoothness is asserted here.

Blueprint FIRST: `hironaka-g10-smooth-base-reduction.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseReduction

open SourceReducedComplexSpace HironakaG10ChowTowerDomination
  HironakaG10ChowFlatteningReduction HironakaG10ChowStrictTransformCalculus
  HironakaG10ChowOneStepStrictTransform HironakaG10ChowFlatBimeromorphicIso
  HironakaG11NativeTowerRepresentation

noncomputable section

/-- Any literal finite native tower has the actual proper strict transform of
every ordinary proper family, including all six strict-transform properties.
Flatness and caller-supplied stage certificates are not premises. -/
theorem exists_isFlatteningData_of_isNativeBlowupTower
    {X X' : SourceReducedComplexSpace} {σ : X' ⟶ X}
    (hσ : IsNativeBlowupTower X X' σ) {Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base) :
    ∃ (E : Set X'.obj.left) (Y' : SourceReducedComplexSpace)
      (p : Y' ⟶ X') (q : Y' ⟶ Y), IsFlatteningData f σ E p q := by
  induction hσ with
  | refl => exact ⟨∅, Y, f, 𝟙 Y, IsFlatteningData.refl f hf⟩
  | @step Z τ B b inst hDense hτ ih =>
    obtain ⟨E, Y₁, p₁, q₁, h₁⟩ := ih
    have h₂ := HironakaG10ChowPairInjective.isFlatteningData_step
      B b hDense p₁ h₁.strict.proper
    exact ⟨stepExcep B b hDense ∪ (stepProj B b hDense).hom.left.base ⁻¹' E,
      strictSource B b p₁, strictP B b hDense p₁, strictQ B b p₁ ≫ q₁, h₁.trans h₂⟩

/-- Exactly the original global flattening endpoint restricted to compact
smooth INITIAL bases. This is an explicit input, not a proved flattening claim;
the later objects of the native tower have no smoothness requirement. -/
def HironakaFlatteningOnSmoothBases : Prop :=
  ∀ (X Y : SourceReducedComplexSpace) (f : Y ⟶ X), CompactSpace X.obj.left →
    X.IsSmooth → IsProperMap f.hom.left.base →
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ X) (E : Set X'.obj.left),
      IsNativeBlowupTower X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ Y),
        IsStrictTransform f σ E p q ∧ IsFlatMorphism p

/-- The full original compact-base endpoint follows from its SAME endpoint
for compact smooth initial bases, using an actual native G11 resolution first. -/
theorem hironakaFlattening_of_smooth_initialBase
    (hSmooth : HironakaFlatteningOnSmoothBases) : HironakaFlattening := by
  intro X Y f hX hf
  obtain ⟨X₀, σ₀, hσ₀, hX₀smooth, hX₀compact⟩ := exists_compact_smooth_nativeTower X hX
  obtain ⟨E₀, Y₀, p₀, q₀, h₀⟩ :=
    exists_isFlatteningData_of_isNativeBlowupTower hσ₀ f hf
  obtain ⟨X₁, σ₁, E₁, hσ₁, hE₁closed, hE₁thin, hσ₁open,
    Y₁, p₁, q₁, hstrict₁, hflat₁⟩ :=
    hSmooth X₀ Y₀ p₀ hX₀compact hX₀smooth h₀.strict.proper
  have h₁ : IsFlatteningData p₀ σ₁ E₁ p₁ q₁ :=
    ⟨hσ₁, hE₁closed, hE₁thin, hσ₁open, hstrict₁⟩
  have h := h₀.trans h₁
  exact ⟨X₁, σ₁ ≫ σ₀, E₁ ∪ σ₁.hom.left.base ⁻¹' E₀,
    h.tower, h.closed, h.thin, h.openImmersion, Y₁, p₁, q₁ ≫ q₀, h.strict, hflat₁⟩

/-- Equivalence to the compact smooth-initial-base input. The nontrivial
direction uses unconditional resolution, never flattening-dependent domination. -/
theorem hironakaFlattening_iff_smooth_initialBase :
    HironakaFlattening ↔ HironakaFlatteningOnSmoothBases := by
  constructor
  · intro h X Y f hX _ hf
    exact h X Y f hX hf
  · exact hironakaFlattening_of_smooth_initialBase

end
end Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseReduction
