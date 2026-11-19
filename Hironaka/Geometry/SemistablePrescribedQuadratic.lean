import Hironaka.Geometry.NodeCompletedLocalOriginalNormalForm
import Hironaka.Algebra.NodeEtaleNonsplitPrescribedNormalForm

/-! Every prescribed residue quadratic lift at the original semistable singular point. -/

noncomputable section

open AlgebraicGeometry IsLocalRing

namespace Hironaka.Geometry.SemistablePrescribedQuadratic

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
local notation "Ah" => S.completedLocalRing (f x)
local notation "C" => X.completedLocalRing x

attribute [local instance] originalAlgebra Algebra.CompletionFlatMap.completedAlgebra

local instance originalLocalMap : IsLocalHom (algebraMap A B) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

local notation "T" => CompletedStalkCoefficientRing f x
local notation "F" => Algebra.NodeGeometricCompletionOriginalFiberSection.FiberRing A B
local notation "Cf" => Algebra.CompletionRegularityBasics.Completion F
local instance : IsLocalRing F := Algebra.CompletionIdealQuotient.quotientLocalRing _
  (Algebra.CompletionLocalMap.closedFiberIdeal_le_maximalIdeal (algebraMap A B))

/-- ONLY original geometry produces one actual residue quadratic and normal forms for
EVERY exact prescribed lift, preserving all original coefficients and base germs. -/
theorem exists_quadratic_with_all_prescribed_normal_forms :
    letI := originalTarget_isNoetherianRing f x
    letI := (residue_finite_separable f x hx).1
    letI := (residue_finite_separable f x hx).2
    letI := Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldAlgebra A B
    letI := upperCompletedStalkAlgebra f x
    ∃ q : Algebra.NodeNonsplit.Quadratic (ResidueField B),
      Nonempty (Cf ≃ₐ[ResidueField B] Algebra.NodeNonsplit.QuadraticNode q) ∧
      ∀ (a0 a1 a2 : T)
        (h0 : residue T a0 = (Algebra.NodeEtaleNonsplitNormalForm.residueQuadratic A B q).a0)
        (h1 : residue T a1 = (Algebra.NodeEtaleNonsplitNormalForm.residueQuadratic A B q).a1)
        (h2 : residue T a2 = (Algebra.NodeEtaleNonsplitNormalForm.residueQuadratic A B q).a2),
        let Q := Algebra.NodeEtaleNonsplitPrescribedNormalForm.prescribedQuadratic T
          (Algebra.NodeEtaleNonsplitNormalForm.residueQuadratic A B q) a0 a1 a2 h0 h1 h2
        ∃ h : T, ∃ e : C ≃ₐ[T] Algebra.NodeSingular.Node Q h,
          h ∈ maximalIdeal T ∧
          (∀ t : T, e (completedStalkCoefficientMap f x t) =
            Ideal.Quotient.mk _ (MvPowerSeries.C t)) ∧
          (∀ a : Ah, e (completedMap f x a) =
            Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap Ah T a))) ∧
          (∀ a : A, e (X.toCompletedLocalRing x (f.stalkMap x a)) =
            Ideal.Quotient.mk _ (MvPowerSeries.C
              (algebraMap Ah T (S.toCompletedLocalRing (f x) a)))) := by
  let := originalTarget_isNoetherianRing f x
  let := (residue_finite_separable f x hx).1
  let := (residue_finite_separable f x hx).2
  let := pointAlgebra f x hx
  let := Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldAlgebra A B
  let := upperCompletedStalkAlgebra f x
  let := originalAlgebra_flat f x
  let := originalAlgebra_essFiniteType f x
  obtain ⟨q, ⟨eq⟩⟩ := exists_quadratic_model f x hx
  refine ⟨q, ⟨eq⟩, ?_⟩
  intro a0 a1 a2 h0 h1 h2
  let h := Algebra.NodeEtaleNonsplitPrescribedNormalForm.normalFormParameter A B q
    a0 a1 a2 h0 h1 h2 eq.symm
  let e := Algebra.NodeEtaleNonsplitPrescribedNormalForm.normalFormEquiv A B q
    a0 a1 a2 h0 h1 h2 eq.symm
  exact ⟨h, e, Algebra.NodeEtaleNonsplitPrescribedNormalForm.normalFormParameter_mem A B q
    a0 a1 a2 h0 h1 h2 eq.symm,
    NodeCompletedLocalOriginalNormalForm.normalForm_coefficient_triangles f x hx _ h e⟩

end Hironaka.Geometry.SemistablePrescribedQuadratic
