import Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction

/-!
# Towers of native ideal blowups and domination over a singular base

Calculus of towers of native ideal blowups (`IsNativeBlowupTower`) and the singular-base form
of the domination step of `chow:dominating-ideal-existence` (blueprint
`hironaka-g10-chowside-singular-tower-domination.tex`): from Hironaka's flattening theorem and
the two classical inputs, every proper bimeromorphic morphism to a COMPACT REDUCED complex space
(not necessarily smooth) is dominated by a finite tower of native ideal blowups.  This is the
tower form, without `chow:blowup-composite`, of the first half of the proof of `chow:general`.

Main declarations:

* `IsNativeBlowupTower.isProperMap`, `IsNativeBlowupTower.surjective`,
  `IsNativeBlowupTower.comp` — towers are proper, surjective and compose.
* `exists_nativeBlowupTower_domination_of_flattening` — domination of proper bimeromorphic
  morphisms of compact reduced spaces by towers.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowSingularTowerDomination

open Hironaka SourceReducedComplexSpace
  OriginalFiniteIdealBlowup OriginalFiniteIdealBlowupUniversal
  HironakaG10ChowFlatBimeromorphicIso HironakaG10ChowTowerDomination
  HironakaG10ChowFlatteningReduction

noncomputable section

/-- The composite of a tower is proper. -/
theorem IsNativeBlowupTower.isProperMap {X Z : SourceReducedComplexSpace} {p : Z ⟶ X}
    (hp : IsNativeBlowupTower X Z p) : IsProperMap p.hom.left.base := by
  induction hp with
  | refl => exact isProperMap_id
  | @step Z p B b _ hDense _ ih =>
    exact ih.comp (projection_isProperMap B b hDense)

/-- The composite of a tower is surjective. -/
theorem IsNativeBlowupTower.surjective {X Z : SourceReducedComplexSpace} {p : Z ⟶ X}
    (hp : IsNativeBlowupTower X Z p) : Function.Surjective p.hom.left.base := by
  induction hp with
  | refl => exact Function.surjective_id
  | @step Z p B b _ hDense _ ih =>
    exact ih.comp (projection_surjective B b hDense)

/-- A tower over a tower is a tower. -/
theorem IsNativeBlowupTower.comp {X Z Z' : SourceReducedComplexSpace} {p : Z ⟶ X}
    {p' : Z' ⟶ Z} (hp' : IsNativeBlowupTower Z Z' p') (hp : IsNativeBlowupTower X Z p) :
    IsNativeBlowupTower X Z' (p' ≫ p) := by
  induction hp' with
  | refl => simpa only [Category.id_comp] using hp
  | @step W q B b _ hDense _ ih =>
    rw [Category.assoc]
    exact IsNativeBlowupTower.step (q ≫ p) B b hDense ih

/-- **Domination over a compact reduced base.**  From Hironaka's flattening theorem and the two
classical inputs, every proper bimeromorphic morphism `f : Y ⟶ X` of reduced complex spaces with
`X` compact is dominated by a finite tower of native ideal blowups: there are a tower
`σ : X' ⟶ X` and `β : X' ⟶ Y` with `β ≫ f = σ`. -/
theorem exists_nativeBlowupTower_domination_of_flattening (H₀ : HironakaFlattening)
    (H₁ : FlatMorphismsAreOpen) (H₂ : FiniteMappingTheorem) {X Y : SourceReducedComplexSpace}
    (hX : CompactSpace X.obj.left) {f : Y ⟶ X} (hf : IsProperBimeromorphic f) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ X) (β : X' ⟶ Y),
      IsNativeBlowupTower X X' σ ∧ β ≫ f = σ := by
  obtain ⟨hFproper, T, -, hTi, -, hFiso⟩ := hf
  obtain ⟨X', σ, E, hσ, hEc, hEi, hσE, Y', p, q, hst, hflat⟩ := H₀ X Y f hX hFproper
  have hp : IsIso p := isIso_of_isStrictTransform_of_flat H₁ H₂ hst hEc hEi hσE hTi hFiso hflat
  refine ⟨X', σ, inv p ≫ q, hσ, ?_⟩
  rw [Category.assoc, hst.comm, IsIso.inv_hom_id_assoc]

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowSingularTowerDomination
