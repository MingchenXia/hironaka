import Hironaka.Analytic.Unibranch.ContainedCentreModificationSequence
import Hironaka.Analytic.Unibranch.OriginalNativeModification
import Hironaka.Blowup.BlowupTowerTransforms

/-!
# Manifold blowup sequences are native finite modifications

A finite composition of blowups of a complex manifold `W` along nowhere dense closed submanifolds
(`IsBlowupSequence n W W' ρ`) induces, on the whole models, a finite composition of native
smooth-centre blowups (`SmoothCentreModification.IsModification`) of the reduced complex space
`wholeModel W`.  This is the contained-centre construction of
`ContainedCentreModificationSequence` for the whole space `W = univ`, whose successive strict
transforms are the whole spaces.

Main declarations:

* `strictTransform_proj_univ` — the strict transform of the whole space along a tower is the whole
  space;
* `isModification_nativeMorphism` — the native morphism of a blowup sequence is a finite
  modification.

Blueprint: `hironaka-g10-gen-chow-general.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10GenBlowupBridge

open Hironaka Hironaka.BlowupSequences
  Hironaka BlowupTowers SourceReducedComplexSpace SmoothCentreModification
  OriginalNativeModification ContainedCentreModificationSequence

noncomputable section

variable {n : ℕ}

/-- The strict transform of the whole space along a tower of blowups is the whole space. -/
theorem strictTransform_proj_univ {X Y : CMfd.{0} n} (T : BlowupTower X Y) :
    strictTransform n T.proj (univ : Set X) = univ := by
  induction T with
  | refl =>
    change strictTransform n (id : X → X) univ = univ
    rw [strictTransform, exceptionalLocus_id, sdiff_empty, preimage_id, closure_univ]
  | step T C π hπ ih =>
    change strictTransform n (T.proj ∘ π) univ = univ
    rw [StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff, ih]
    exact BlowupTowerTransforms.strictTransform_univ hπ

/-- Every centre of a tower is contained in, and nowhere dense in, the strict transform of the
whole space. -/
theorem centresContainedDense_univ {X Y : CMfd.{0} n} (T : BlowupTower X Y) :
    CentresContainedDense (univ : Set X) T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    refine ⟨ih, ?_, ?_⟩
    · rw [strictTransform_proj_univ T]
      exact subset_univ C
    · rw [strictTransform_proj_univ T, ← compl_eq_univ_sdiff, closure_compl, hπ.2.1, compl_empty]

private theorem object_eq {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {A B : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B) (hAB : A = B) :
    ofClosedAnalytic A hA = ofClosedAnalytic B hB := by
  cases hAB
  rfl

private theorem object_eqToHom_base {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {A B : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B) (hAB : A = B) (a : A) :
    ((eqToHom (object_eq hA hB hAB)).hom.left.base a).val = a.val := by
  cases hAB
  rfl

private theorem modification_precomp_eq {A B X : SourceReducedComplexSpace}
    (hAB : A = B) {p : B ⟶ X} (hp : IsModification p) :
    IsModification (eqToHom hAB ≫ p) := by
  cases hAB
  simpa only [eqToHom_refl, Category.id_comp] using hp

/-- The native morphism of the projection of a tower is a finite modification. -/
theorem isModification_nativeMorphism_proj {X Y : CMfd.{0} n} (T : BlowupTower X Y) :
    IsModification (nativeMorphism (n := n) (m := n) T.contMDiff_proj) := by
  have hU : IsComplexAnalyticSubset (n := n) (univ : Set X) := isComplexAnalyticSubset_univ
  have hm := projectionMorphism_isModification hU T (centresContainedDense_univ T)
  have hN := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hU
  have hobj : ofClosedAnalytic (n := n) (univ : Set Y) isComplexAnalyticSubset_univ =
      ofClosedAnalytic (strictTransform n T.proj univ) hN :=
    object_eq _ hN (strictTransform_proj_univ T).symm
  have hfull : eqToHom hobj ≫ projectionMorphism hU T =
      nativeMorphism (n := n) (m := n) T.contMDiff_proj := by
    apply morphism_eq_of_pointwise_eq
    intro y
    apply Subtype.ext
    change T.proj ((eqToHom hobj).hom.left.base y).val = T.proj y.val
    exact congrArg T.proj (object_eqToHom_base _ hN (strictTransform_proj_univ T).symm y)
  rw [← hfull]
  exact modification_precomp_eq hobj hm

/-- **A blowup sequence of complex manifolds is a native finite modification**: the native
morphism `wholeModel W' ⟶ wholeModel W` of a finite composition of blowups along nowhere dense
closed submanifolds is a finite composition of native smooth-centre blowups. -/
theorem isModification_nativeMorphism {W W' : Type} [TopologicalSpace W]
    [ChartedSpace (ComplexModel n) W] [IsComplexManifold n W] [TopologicalSpace W']
    [ChartedSpace (ComplexModel n) W'] [IsComplexManifold n W'] {ρ : W' → W}
    (hρ : IsBlowupSequence n W W' ρ) :
    IsModification (nativeMorphism (n := n) (m := n) hρ.contMDiff) := by
  obtain ⟨T, hT⟩ := BlowupTower.exists_proj_eq_of_isBlowupSequence hρ
  have h := isModification_nativeMorphism_proj T
  have heq : nativeMorphism (n := n) (m := n) T.contMDiff_proj =
      nativeMorphism (n := n) (m := n) hρ.contMDiff :=
    morphism_eq_of_pointwise_eq _ _ (fun y => by
      apply Subtype.ext
      change T.proj y.val = ρ y.val
      rw [hT])
  rwa [heq] at h

end

end Hironaka.Analytic.Unibranch.HironakaG10GenBlowupBridge
