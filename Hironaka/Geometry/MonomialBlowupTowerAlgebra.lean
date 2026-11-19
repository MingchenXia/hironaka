import Hironaka.Geometry.MonomialBlowupIteration

/-!
# Actual ideal-image identities used in the global node-cover induction

The hypotheses specify actual coordinate substitutions of actual algebra
maps. The global induction constructs these maps and formulas internally.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTowerAlgebra

open Algebra.NodeBlowupChart Algebra.MonomialBlowupIteration MonomialBlowupIteration

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] {c q : A}

/-- The actual ideal image on any chart with the given actual continuation-coordinate formula. -/
theorem center_map_continuation (F : Node A c →ₐ[A] Node A q) (p s : A)
    (hu : F (coordinate c 0) = algebraMap A (Node A q) p * coordinate q 0) :
    (prefixCenter c (p * s)).map F.toRingHom =
      Algebra.ReesPrincipalFactor.scaledIdeal (algebraMap A (Node A q) p) (prefixCenter q s) := by
  rw [prefixCenter, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hu, AlgHom.commutes, map_mul]
  rw [Algebra.ReesPrincipalFactor.scaledIdeal, prefixCenter, Ideal.span_mul_span']
  congr 1
  simp only [Set.singleton_mul, Set.image_insert_eq, Set.image_singleton]

/-- Divisibility of the actual next original prefix makes its actual finished-chart image principal. -/
theorem center_map_finished (F : Node A c →ₐ[A] Node A q) (p s : A)
    (hu : F (coordinate c 0) = algebraMap A (Node A q) p * coordinate q 0)
    (hs : p * q ∣ s) :
    (prefixCenter c s).map F.toRingHom =
      Ideal.span {algebraMap A (Node A q) p * coordinate q 0} := by
  rw [prefixCenter, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hu, AlgHom.commutes]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  obtain ⟨r, rfl⟩ := hs
  refine ⟨coordinate q 1 * algebraMap A (Node A q) r, ?_⟩
  rw [map_mul, map_mul, ← coordinate_product]
  ring

variable [IsDomain A]

/-- The genuine native blowup of the exact finished-chart ideal image is the whole chart. -/
def finishedBlowupIso (F : Node A c →ₐ[A] Node A q) (p s : A)
    (hu : F (coordinate c 0) = algebraMap A (Node A q) p * coordinate q 0)
    (hs : p * q ∣ s) (hp : p ≠ 0) (hq : q ≠ 0) :
    affineBlowup ((prefixCenter c s).map F.toRingHom) ≅ Spec (CommRingCat.of (Node A q)) := by
  let : IsDomain (Node A q) := Algebra.NodeDomain.nodeQuotient_isDomain q hq
  exact (blowupCenterEqIso (center_map_finished F p s hu hs)).trans
    (PrincipalBlowup.principalBlowupIso
      (algebraMap A (Node A q) p * coordinate q 0)
      (mul_ne_zero (coefficient_ne_zero p q hp hq)
        (Algebra.NodeDomain.nodeCoordinate_ne_zero q hq 0)))

@[reassoc]
theorem finishedBlowupIso_hom_structure (F : Node A c →ₐ[A] Node A q) (p s : A)
    (hu : F (coordinate c 0) = algebraMap A (Node A q) p * coordinate q 0)
    (hs : p * q ∣ s) (hp : p ≠ 0) (hq : q ≠ 0) :
    (finishedBlowupIso F p s hu hs hp hq).hom =
      affineBlowupStructure ((prefixCenter c s).map F.toRingHom) := by
  let : IsDomain (Node A q) := Algebra.NodeDomain.nodeQuotient_isDomain q hq
  change (blowupCenterEqIso (center_map_finished F p s hu hs)).hom ≫
    affineBlowupStructure (Ideal.span {algebraMap A (Node A q) p * coordinate q 0}) = _
  exact blowupCenterEqIso_hom_structure _

/-- The actual next continuation-chart blowup is the next smaller node blowup. -/
def continuationBlowupIso (F : Node A c →ₐ[A] Node A q) (p s : A)
    (hu : F (coordinate c 0) = algebraMap A (Node A q) p * coordinate q 0)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    affineBlowup ((prefixCenter c (p * s)).map F.toRingHom) ≅
      affineBlowup (prefixCenter q s) := by
  let : IsDomain (Node A q) := Algebra.NodeDomain.nodeQuotient_isDomain q hq
  exact (blowupCenterEqIso (center_map_continuation F p s hu)).trans
    (BlowupPrincipalFactor.blowupPrincipalFactorIso
      (algebraMap A (Node A q) p) (prefixCenter q s) (coefficient_ne_zero p q hp hq))

@[reassoc]
theorem continuationBlowupIso_hom_structure (F : Node A c →ₐ[A] Node A q) (p s : A)
    (hu : F (coordinate c 0) = algebraMap A (Node A q) p * coordinate q 0)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (continuationBlowupIso F p s hu hp hq).hom ≫ affineBlowupStructure (prefixCenter q s) =
      affineBlowupStructure ((prefixCenter c (p * s)).map F.toRingHom) := by
  let : IsDomain (Node A q) := Algebra.NodeDomain.nodeQuotient_isDomain q hq
  simp only [continuationBlowupIso, Iso.trans_hom, Category.assoc,
    BlowupPrincipalFactor.blowupPrincipalFactorIso_hom_structure,
    blowupCenterEqIso_hom_structure]

end Hironaka.Geometry.MonomialBlowupTowerAlgebra
