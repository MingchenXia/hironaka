/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperGeometricGlobalFunctionsBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Literal original infinitesimal pullbacks and full coefficient transitions

Closed native scheme-transition proof adapted from
`EnvelopeProperty/EnvelopeProperty/InfinitesimalSchemes.lean`,
SHA256 da479c8f806ea19d51008166afccdf1aad85b93c06fb4dc9d85dd19ed3717a6d.
The actual coefficient-square proof is adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreProjectiveFormalSections.lean`,
SHA256 b6662724f8141b2cd3617b1fb96bdc58669aae6d3854515b759c6d2b9e93fe8c,
retaining only Mathlib and accepted own helpers.
No nonflat H0 base-change or global-surjectivity input is used.
-/
open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.Infinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The original quotient ring at EVERY natural order, including zero and whole ideals. -/
abbrev ring (n : ℕ) := R ⧸ I^n

/-- The literal original coefficient morphism into the same base scheme. -/
abbrev coefficientScheme (n : ℕ) : Spec (.of (ring I n)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I^n)))

/-- The LITERAL original infinitesimal pullback, with every nilpotent retained. -/
abbrev model (n : ℕ) := pullback f (coefficientScheme I n)

/-- The original whole scheme projection to X. -/
abbrev projection (n : ℕ) : model I f n ⟶ X := pullback.fst _ _

/-- The original coefficient projection to Spec(R/I^n). -/
abbrev structureMap (n : ℕ) : model I f n ⟶ Spec (.of (ring I n)) := pullback.snd _ _

/-- The genuine original quotient factor retains the WHOLE R coefficient morphism. -/
theorem coefficientScheme_factor {n m : ℕ} (h : n≤m) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h)) ≫ coefficientScheme I m =
      coefficientScheme I n := by
  dsimp only [coefficientScheme]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.factorPow I h).comp (Ideal.Quotient.mk (I^m)))) = _
  rw [Ideal.Quotient.factor_comp_mk]

/-- The actual original whole map between original-order infinitesimal pullbacks. -/
def transition {n m : ℕ} (h : n≤m) : model I f n ⟶ model I f m :=
  pullback.lift (projection I f n)
    (structureMap I f n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h))) (by
      rw [Category.assoc,coefficientScheme_factor I h]
      exact pullback.condition)

/-- Every transition preserves the ENTIRE original projection to X. -/
@[reassoc] theorem transition_projection {n m : ℕ} (h : n≤m) :
    transition I f h ≫ projection I f m = projection I f n := pullback.lift_fst _ _ _

/-- Every transition preserves the WHOLE original quotient coefficient map. -/
@[reassoc] theorem transition_structureMap {n m : ℕ} (h : n≤m) :
    transition I f h ≫ structureMap I f m =
      structureMap I f n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h)) :=
  pullback.lift_snd _ _ _

/-- The literal same-order transition is the ENTIRE scheme identity. -/
theorem transition_self (n : ℕ) : transition I f (le_refl n) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [transition,projection]
  · simp [transition,structureMap,Ideal.Quotient.factorPow]

/-- All original-order transitions obey actual WHOLE scheme composition. -/
theorem transition_comp {l n m : ℕ} (hln : l≤n) (hnm : n≤m) :
    transition I f hln ≫ transition I f hnm = transition I f (hln.trans hnm) := by
  apply pullback.hom_ext
  · change (transition I f hln ≫ transition I f hnm) ≫ projection I f m =
      transition I f (hln.trans hnm) ≫ projection I f m
    simp only [Category.assoc,transition_projection]
  · change (transition I f hln ≫ transition I f hnm) ≫ structureMap I f m =
      transition I f (hln.trans hnm) ≫ structureMap I f m
    rw [Category.assoc,transition_structureMap,transition_structureMap_assoc,
      transition_structureMap]
    rw [← Spec.map_comp]
    change _ ≫ Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.factorPow I hln).comp (Ideal.Quotient.factorPow I hnm))) = _
    rw [Ideal.Quotient.factor_comp]

/-- Every ORIGINAL coefficient quotient projection is a genuine closed immersion, including order zero. -/
instance projection_isClosedImmersion (n : ℕ) : IsClosedImmersion (projection I f n) := by
  let : IsClosedImmersion (coefficientScheme I n) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I^n)))
      Ideal.Quotient.mk_surjective
  exact inferInstanceAs (IsClosedImmersion (CategoryTheory.Limits.pullback.fst f _))

/-- EVERY literal original projection preserves the whole ORIGINAL quotient coefficient square. -/
theorem projection_coefficient_quotient (n : ℕ) :
    (projection I f n).appTop.hom.comp (ProperGeometricGlobalFunctions.coefficientMap f) =
      (ProperGeometricGlobalFunctions.coefficientMap (structureMap I f n)).comp
        (Ideal.Quotient.mk (I^n)) := by
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ (projection I f n ≫ f).appTop).hom =
    (CommRingCat.ofHom (Ideal.Quotient.mk (I^n)) ≫
      (Scheme.ΓSpecIso (.of (ring I n))).inv ≫ (structureMap I f n).appTop).hom
  rw [pullback.condition, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

end Hironaka.Geometry.ProperSteinProjectiveCech.Infinitesimal
