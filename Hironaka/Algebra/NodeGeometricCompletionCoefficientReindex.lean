import Hironaka.Algebra.NodeGeometricCompletionOriginalCoefficientAgreement
import Hironaka.Algebra.NodeNonsplitPresentationFiber

/-! Reindex an actual closed-fibre quadratic model along the SAME original residue equivalence. -/

noncomputable section

open MvPowerSeries IsLocalRing

namespace Hironaka.Algebra.NodeGeometricCompletionCoefficientReindex

open NodeFormalMorse NodeNonsplit NodeGeometricCompletionOriginalFiberSection
  NodeGeometricCompletionDiagonalCoefficients CompletionRegularityBasics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

universe u v

/-- Coefficientwise transport is an actual ring equivalence, with both inverse identities proved coefficientwise. -/
def seriesEquiv {K : Type u} {L : Type v} [CommRing K] [CommRing L] (χ : K ≃+* L) :
    Series K ≃+* Series L :=
  RingEquiv.ofRingHom (MvPowerSeries.map χ.toRingHom) (MvPowerSeries.map χ.symm.toRingHom)
    (by
      ext f d
      simp only [RingHom.comp_apply, coeff_map, RingHom.id_apply]
      exact χ.apply_symm_apply _)
    (by
      ext f d
      simp only [RingHom.comp_apply, coeff_map, RingHom.id_apply]
      exact χ.symm_apply_apply _)

theorem seriesEquiv_apply {K : Type u} {L : Type v} [CommRing K] [CommRing L]
    (χ : K ≃+* L) (f : Series K) :
    seriesEquiv χ f = MvPowerSeries.map χ.toRingHom f := rfl

/-- The literal original quadratic quotient, with its actual coefficients reindexed and BOTH variables retained. -/
def quadraticReindex {K : Type u} {L : Type v} [CommRing K] [CommRing L]
    (χ : K ≃+* L) (Q : Quadratic L) :
    QuadraticNode (Q.map χ.symm.toRingHom) ≃+* QuadraticNode Q :=
  Ideal.quotientEquiv _ _ (seriesEquiv χ) (by
    rw [Ideal.map_span, Set.image_singleton]
    apply congrArg Ideal.span
    apply congrArg Set.singleton
    change Q.series = MvPowerSeries.map χ.toRingHom (Q.map χ.symm.toRingHom).series
    rw [← Quadratic.map_series]
    ext d
    simp only [coeff_map]
    exact (χ.apply_symm_apply _).symm)

/-- EVERY original series representative follows the actual coefficientwise field reindexing. -/
theorem quadraticReindex_mk {K : Type u} {L : Type v} [CommRing K] [CommRing L]
    (χ : K ≃+* L) (Q : Quadratic L) (f : Series K) :
    quadraticReindex χ Q (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (MvPowerSeries.map χ.toRingHom f) := rfl

/-- EVERY actual original coefficient is transported by the SAME residue equivalence. -/
theorem quadraticReindex_C {K : Type u} {L : Type v} [CommRing K] [CommRing L]
    (χ : K ≃+* L) (Q : Quadratic L) (a : K) :
    quadraticReindex χ Q (Ideal.Quotient.mk _ (MvPowerSeries.C a)) =
      Ideal.Quotient.mk _ (MvPowerSeries.C (χ a)) := by
  rw [quadraticReindex_mk, map_C]
  rfl

/-- BOTH original coordinates are preserved by the actual reindexing. -/
theorem quadraticReindex_X {K : Type u} {L : Type v} [CommRing K] [CommRing L]
    (χ : K ≃+* L) (Q : Quadratic L) (i : Fin 2) :
    quadraticReindex χ Q (Ideal.Quotient.mk _ (MvPowerSeries.X i)) =
      Ideal.Quotient.mk _ (MvPowerSeries.X i : Series L) := by
  rw [quadraticReindex_mk, map_X]

section Original

variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

local notation "k" => ResidueField A
local notation "R" => FiberRing A B
local notation "C" => Completion R
local notation "χ" => NodeGeometricCompletionFiberResidue.quotientResidueAlgEquiv A B

local instance actualFiberLocalRing : IsLocalRing R :=
  CompletionIdealQuotient.quotientLocalRing _
    (CompletionLocalMap.closedFiberIdeal_le_maximalIdeal (algebraMap A B))

attribute [local instance] baseResidueAlgebra
  NodeGeometricCompletionFiberResidue.quotientResidue_finite
  NodeGeometricCompletionFiberResidue.quotientResidue_separable

/-- An actual model over the closed-fibre residue becomes a model over the ORIGINAL point residue, with its SAME original Hensel coefficient action. -/
def originalQuadraticEquiv (Q : Quadratic (ResidueField R))
    (e : letI := pointCoefficientAlgebra k R
      QuadraticNode Q ≃ₐ[ResidueField R] C) :
    letI := pointFieldAlgebra A B
    QuadraticNode (Q.map (χ).symm.toRingHom) ≃ₐ[ResidueField B] C := by
  letI := pointCoefficientAlgebra k R
  letI := pointFieldAlgebra A B
  refine { (quadraticReindex (χ).toRingEquiv Q).trans e.toRingEquiv with commutes' := ?_ }
  intro a
  change e (quadraticReindex (χ).toRingEquiv Q (Ideal.Quotient.mk _ (MvPowerSeries.C a))) =
    pointFieldSection A B a
  rw [quadraticReindex_C]
  calc
    e (Ideal.Quotient.mk _ (MvPowerSeries.C (χ a))) = pointCoefficientMap k R (χ a) :=
      e.commutes (χ a)
    _ = pointFieldSection A B a :=
      NodeGeometricCompletionOriginalCoefficientAgreement.originalDiagonalSection_apply A B a

/-- EVERY original series representative retains exactly its original classified-model image after canonical coefficient reindexing. -/
theorem originalQuadraticEquiv_mk (Q : Quadratic (ResidueField R))
    (e : letI := pointCoefficientAlgebra k R
      QuadraticNode Q ≃ₐ[ResidueField R] C) (f : Series (ResidueField B)) :
    letI := pointFieldAlgebra A B
    originalQuadraticEquiv A B Q e (Ideal.Quotient.mk _ f) =
      e (Ideal.Quotient.mk _ (MvPowerSeries.map (χ).toRingHom f)) := rfl

/-- Every ORIGINAL point coefficient has precisely the SAME original Hensel section image. -/
theorem originalQuadraticEquiv_C (Q : Quadratic (ResidueField R))
    (e : letI := pointCoefficientAlgebra k R
      QuadraticNode Q ≃ₐ[ResidueField R] C) (a : ResidueField B) :
    letI := pointFieldAlgebra A B
    originalQuadraticEquiv A B Q e (Ideal.Quotient.mk _ (MvPowerSeries.C a)) =
      pointFieldSection A B a := by
  let := pointFieldAlgebra A B
  exact (originalQuadraticEquiv A B Q e).commutes a

/-- BOTH original coordinates have the SAME original model images. -/
theorem originalQuadraticEquiv_X (Q : Quadratic (ResidueField R))
    (e : letI := pointCoefficientAlgebra k R
      QuadraticNode Q ≃ₐ[ResidueField R] C) (i : Fin 2) :
    letI := pointFieldAlgebra A B
    originalQuadraticEquiv A B Q e (Ideal.Quotient.mk _ (MvPowerSeries.X i)) =
      e (Ideal.Quotient.mk _ (MvPowerSeries.X i : Series (ResidueField R))) := by
  let := pointFieldAlgebra A B
  rw [originalQuadraticEquiv_mk, map_X]

end Original

end Hironaka.Algebra.NodeGeometricCompletionCoefficientReindex
