/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Actual finite-extension points of finite-type scheme fibres

Actual affine maximal quotients and Zariski's lemma construct closed finite-field
points with their entire original structure triangle. True scheme-surjectivity
makes every provided field-valued fibre nonempty. No point, separability,
normalization or proper-extension certificate is assumed.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
noncomputable section
namespace Hironaka.Algebra.FiniteTypePoint
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The actual coefficient map of an affine neighbourhood over the given field. -/
def affineBaseMap (f : X ⟶ Spec (CommRingCat.of K)) {U : X.Opens}
    (hU : IsAffineOpen U) : K →+* Γ(X, U) :=
  (Spec.preimage (hU.fromSpec ≫ f)).hom

theorem affineBaseMap_spec (f : X ⟶ Spec (CommRingCat.of K)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Spec.map (CommRingCat.ofHom (affineBaseMap f hU)) = hU.fromSpec ≫ f :=
  Spec.map_preimage _

theorem affineBaseMap_finiteType (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    (affineBaseMap f hU).FiniteType := by
  have : LocallyOfFiniteType (hU.fromSpec ≫ f) := inferInstance
  rw [← affineBaseMap_spec f hU] at this
  exact HasRingHomProperty.Spec_iff.mp this

/-- A genuine maximal affine quotient yields a finite extension, with the original field action. -/
theorem maximalQuotient_finite (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    (m : Ideal Γ(X, U)) [m.IsMaximal] :
    ((Ideal.Quotient.mk m).comp (affineBaseMap f hU)).Finite := by
  let := Ideal.Quotient.field m
  apply RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr
  exact (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp
    (affineBaseMap_finiteType f hU)

/-- The actual affine maximal quotient defines a whole scheme point. -/
def maximalQuotientPoint {U : X.Opens} (hU : IsAffineOpen U)
    (m : Ideal Γ(X, U)) : Spec (CommRingCat.of (Γ(X, U) ⧸ m)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ hU.fromSpec

theorem maximalQuotientPoint_base (f : X ⟶ Spec (CommRingCat.of K))
    {U : X.Opens} (hU : IsAffineOpen U) (m : Ideal Γ(X, U)) :
    maximalQuotientPoint hU m ≫ f =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk m).comp (affineBaseMap f hU))) := by
  rw [maximalQuotientPoint, Category.assoc, ← affineBaseMap_spec f hU, ← Spec.map_comp]
  rfl

theorem maximalQuotientPoint_isClosedImmersion (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    (m : Ideal Γ(X, U)) [m.IsMaximal] : IsClosedImmersion (maximalQuotientPoint hU m) := by
  let := Ideal.Quotient.field m
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let p := maximalQuotientPoint hU m
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsImmersion p := by dsimp [p, maximalQuotientPoint]; infer_instance
  have hrange : Set.range p = {p (IsLocalRing.closedPoint (Γ(X, U) ⧸ m))} := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact congrArg p (Subsingleton.elim _ _)
    · rintro rfl
      exact ⟨_, rfl⟩
  apply IsClosedImmersion.of_isPreimmersion p
  rw [hrange]
  apply isClosed_singleton_of_isLocallyClosed_singleton
  rw [← hrange]
  exact p.isLocallyClosed_range

/-- A nonempty scheme locally of finite type over a field has an actual closed finite-extension point. -/
theorem exists_finite_field_point (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [Nonempty X] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), Module.Finite K L ∧
      ∃ p : Spec (CommRingCat.of L) ⟶ X,
        IsClosedImmersion p ∧ p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  let x : X := Classical.choice ‹Nonempty X›
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  have : Nontrivial Γ(X, U) := (X.evaluation U x hx).hom.domain_nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(X, U)
  let := hm
  let := Ideal.Quotient.field m
  let := ((Ideal.Quotient.mk m).comp (affineBaseMap f hU)).toAlgebra
  refine ⟨Γ(X, U) ⧸ m, inferInstance, inferInstance, maximalQuotient_finite f hU m,
    maximalQuotientPoint hU m, maximalQuotientPoint_isClosedImmersion f hU m, ?_⟩
  exact maximalQuotientPoint_base f hU m

/-- True scheme-surjectivity gives a closed finite-extension point in the actual fibre of every field-valued point. -/
theorem exists_finite_field_point_of_surjective {Y S : Scheme.{u}}
    (g : Y ⟶ S) [Surjective g] [LocallyOfFiniteType g]
    (x : Spec (CommRingCat.of K) ⟶ S) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), Module.Finite K L ∧
      ∃ p : Spec (CommRingCat.of L) ⟶ pullback g x,
        IsClosedImmersion p ∧
          p ≫ pullback.snd g x = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  have : Nonempty (pullback g x : Scheme.{u}) := by
    obtain ⟨z, _⟩ := (pullback.snd g x).surjective (IsLocalRing.closedPoint K)
    exact ⟨z⟩
  exact exists_finite_field_point (pullback.snd g x)

/-- The actual finite generic-fibre point yields a whole compatible point of the original scheme, without properness. -/
theorem exists_finite_field_lift {Y S : Scheme.{u}}
    (g : Y ⟶ S) [Surjective g] [LocallyOfFiniteType g]
    (x : Spec (CommRingCat.of K) ⟶ S) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), Module.Finite K L ∧
      ∃ q : Spec (CommRingCat.of L) ⟶ Y,
        q ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x := by
  obtain ⟨L, hL, aL, hfinite, p, _, hp⟩ := exists_finite_field_point_of_surjective g x
  exact ⟨L, hL, aL, hfinite, p ≫ pullback.fst g x, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp]⟩

end Hironaka.Algebra.FiniteTypePoint
