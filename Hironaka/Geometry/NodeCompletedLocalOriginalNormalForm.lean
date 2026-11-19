import Hironaka.Geometry.NodeCompletedLocalOriginalNodeSupportClassification
import Hironaka.Geometry.NodeCompletedLocalCoefficients
import Hironaka.Algebra.NodeEtaleNonsplitNormalForm

/-! The original geometric singular point constructs its actual completed total-space normal form. -/

noncomputable section

open AlgebraicGeometry IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalOriginalNormalForm

open NodeCompletedLocalMap NodeCompletedLocalOriginalNodeSupportClassification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f] [IsLocallyNoetherian S]
  (x : X) (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support)

local notation "A" => S.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
local notation "T" => CompletedStalkCoefficientRing f x

attribute [local instance] originalAlgebra Algebra.CompletionFlatMap.completedAlgebra

local instance originalLocalMap : IsLocalHom (algebraMap A B) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

/-- The SAME actual finite-free etale coefficient ring has all native properties, derived ONLY from the original geometry. -/
theorem coefficientRing_properties :
    letI := (residue_finite_separable f x hx).1
    letI := (residue_finite_separable f x hx).2
    Module.Finite (S.completedLocalRing (f x)) T ∧
      Module.Free (S.completedLocalRing (f x)) T ∧
      Algebra.Etale (S.completedLocalRing (f x)) T ∧
      IsLocalRing T ∧ IsNoetherianRing T ∧
      IsAdicComplete (maximalIdeal T) T := by
  let := (residue_finite_separable f x hx).1
  let := (residue_finite_separable f x hx).2
  exact completedStalkCoefficientRing_properties f x

/-- Actual upper flatness comes from ORIGINAL scheme flatness and finite type, with no completed-flatness premise. -/
theorem upper_flat :
    letI := (residue_finite_separable f x hx).1
    letI := (residue_finite_separable f x hx).2
    letI := upperCompletedStalkAlgebra f x
    Module.Flat T (X.completedLocalRing x) := by
  let := (residue_finite_separable f x hx).1
  let := (residue_finite_separable f x hx).2
  exact upperCompletedStalkAlgebra_flat f x

/-- The ENTIRE original completed structural map factors through the SAME actual coefficient map. -/
theorem coefficient_completed_triangle :
    letI := (residue_finite_separable f x hx).1
    letI := (residue_finite_separable f x hx).2
    (completedStalkCoefficientMap f x).comp
      (algebraMap (S.completedLocalRing (f x)) T) = completedMap f x := by
  let := (residue_finite_separable f x hx).1
  let := (residue_finite_separable f x hx).2
  exact completedStalkCoefficientMap_triangle f x

/-- The scalar tower is for the SAME original scheme completed map and SAME constructed upper map. -/
theorem coefficient_scalarTower :
    letI := (residue_finite_separable f x hx).1
    letI := (residue_finite_separable f x hx).2
    letI := completedAlgebra f x
    letI := upperCompletedStalkAlgebra f x
    IsScalarTower (S.completedLocalRing (f x)) T (X.completedLocalRing x) := by
  let := (residue_finite_separable f x hx).1
  let := (residue_finite_separable f x hx).2
  let := originalTarget_isNoetherianRing f x
  let := completedAlgebra f x
  let := upperCompletedStalkAlgebra f x
  exact Algebra.NodeGeometricCompletion.upperCompletedAlgebra_isScalarTower A B

/-- The original geometric singular point produces the actual total-space normal form on its SAME native completion. -/
theorem exists_normalForm :
    letI := (residue_finite_separable f x hx).1
    letI := (residue_finite_separable f x hx).2
    letI := upperCompletedStalkAlgebra f x
    ∃ Q : Algebra.NodeNonsplit.Quadratic T, ∃ h : T,
      h ∈ maximalIdeal T ∧
        Nonempty (X.completedLocalRing x ≃ₐ[T] Algebra.NodeSingular.Node Q h) := by
  let := (residue_finite_separable f x hx).1
  let := (residue_finite_separable f x hx).2
  let := originalTarget_isNoetherianRing f x
  let := originalAlgebra_flat f x
  let := originalAlgebra_essFiniteType f x
  let := upperCompletedStalkAlgebra f x
  let := pointAlgebra f x hx
  let : IsLocalRing (Algebra.NodeGeometricCompletionOriginalFiberSection.FiberRing A B) :=
    Algebra.CompletionIdealQuotient.quotientLocalRing _
      (Algebra.CompletionLocalMap.closedFiberIdeal_le_maximalIdeal (algebraMap A B))
  let : Algebra (ResidueField B)
      (Algebra.CompletionRegularityBasics.Completion
        (Algebra.NodeGeometricCompletionOriginalFiberSection.FiberRing A B)) :=
    Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldAlgebra A B
  obtain ⟨q, ⟨e⟩⟩ := exists_quadratic_model f x hx
  let h := Algebra.NodeEtaleNonsplitNormalForm.normalFormParameter A B q e.symm
  let E := Algebra.NodeEtaleNonsplitNormalForm.normalFormEquiv A B q e.symm
  exact ⟨Algebra.NodeEtaleNonsplitNormalForm.liftedQuadratic A B q, h,
    Algebra.NodeEtaleNonsplitNormalForm.normalFormParameter_mem A B q e.symm, ⟨E⟩⟩

/-- EVERY upper coefficient, ALL completed original base coefficients, and EVERY original base germ follow their SAME actual forward maps. -/
theorem normalForm_coefficient_triangles :
    letI := (residue_finite_separable f x hx).1
    letI := (residue_finite_separable f x hx).2
    letI := upperCompletedStalkAlgebra f x
    ∀ (Q : Algebra.NodeNonsplit.Quadratic T) (h : T)
      (e : X.completedLocalRing x ≃ₐ[T] Algebra.NodeSingular.Node Q h),
      (∀ t : T, e (completedStalkCoefficientMap f x t) =
        Ideal.Quotient.mk _ (MvPowerSeries.C t)) ∧
      (∀ a : S.completedLocalRing (f x), e (completedMap f x a) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap (S.completedLocalRing (f x)) T a))) ∧
      (∀ a : A, e (X.toCompletedLocalRing x (f.stalkMap x a)) =
        Ideal.Quotient.mk _ (MvPowerSeries.C
          (algebraMap (S.completedLocalRing (f x)) T (S.toCompletedLocalRing (f x) a)))) := by
  let := (residue_finite_separable f x hx).1
  let := (residue_finite_separable f x hx).2
  let := upperCompletedStalkAlgebra f x
  intro Q h e
  have hc (t : T) : e (completedStalkCoefficientMap f x t) =
      Ideal.Quotient.mk _ (MvPowerSeries.C t) := e.commutes t
  have hb (a : S.completedLocalRing (f x)) : e (completedMap f x a) =
      Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap (S.completedLocalRing (f x)) T a)) := by
    have ht := hc (algebraMap (S.completedLocalRing (f x)) T a)
    have heq : completedStalkCoefficientMap f x
        (algebraMap (S.completedLocalRing (f x)) T a) = completedMap f x a :=
      RingHom.congr_fun (completedStalkCoefficientMap_triangle f x) a
    rw [heq] at ht
    exact ht
  refine ⟨hc, hb, ?_⟩
  intro a
  have ht := hb (S.toCompletedLocalRing (f x) a)
  rw [completedMap_coefficient] at ht
  exact ht

/-- The actual source-produced SAME-ring normal form retains EVERY original coefficient triangle without an output-map certificate. -/
theorem exists_normalForm_with_coefficients :
    letI := (residue_finite_separable f x hx).1
    letI := (residue_finite_separable f x hx).2
    letI := upperCompletedStalkAlgebra f x
    ∃ Q : Algebra.NodeNonsplit.Quadratic T, ∃ h : T,
      ∃ e : X.completedLocalRing x ≃ₐ[T] Algebra.NodeSingular.Node Q h,
        h ∈ maximalIdeal T ∧
        (∀ t : T, e (completedStalkCoefficientMap f x t) =
          Ideal.Quotient.mk _ (MvPowerSeries.C t)) ∧
        (∀ a : S.completedLocalRing (f x), e (completedMap f x a) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap (S.completedLocalRing (f x)) T a))) ∧
        (∀ a : A, e (X.toCompletedLocalRing x (f.stalkMap x a)) =
          Ideal.Quotient.mk _ (MvPowerSeries.C
            (algebraMap (S.completedLocalRing (f x)) T (S.toCompletedLocalRing (f x) a)))) := by
  let := (residue_finite_separable f x hx).1
  let := (residue_finite_separable f x hx).2
  let := upperCompletedStalkAlgebra f x
  obtain ⟨Q, h, hh, ⟨e⟩⟩ := exists_normalForm f x hx
  exact ⟨Q, h, e, hh, normalForm_coefficient_triangles f x hx Q h e⟩

end Hironaka.Geometry.NodeCompletedLocalOriginalNormalForm
