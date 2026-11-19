import Hironaka.Geometry.NodeCompletedLocalOriginalNodePointClassification

/-! The actual original ambient point/support interface of the quadratic classification. -/

noncomputable section

open AlgebraicGeometry IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalOriginalNodeSupportClassification

open NodeCompletedLocalMap NodeCompletedLocalOriginalNodeJets

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f] (x : X)
  (hx : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).support)

local notation "I" => Algebra.NodeFittingOmegaGluing.idealSheaf f 1
local notation "A" => S.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
local notation "R" => OriginalFiberRing f x
local notation "C" => Algebra.CompletionRegularityBasics.Completion R

attribute [local instance] originalAlgebra

local instance originalLocalMap : IsLocalHom (algebraMap A B) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

local instance originalQuotientLocalRing : IsLocalRing R := originalFiberLocalRing f x

include hx in
/-- The actual ambient original singular-support condition INTERNALLY produces native original residue finite separability. -/
theorem residue_finite_separable :
    FiniteDimensional (ResidueField A) (ResidueField B) ∧
      Algebra.IsSeparable (ResidueField A) (ResidueField B) := by
  have hx' : x ∈ ((I).support : Set X) := hx
  rw [← (I).range_subschemeι] at hx'
  obtain ⟨z, hz⟩ := hx'
  subst x
  exact originalResidue_finite_separable f z

variable [IsLocallyNoetherian S]

/-- The coefficient action is the SAME original Hensel section on the SAME actual ambient-point closed-fibre completion. -/
@[instance_reducible]
def pointAlgebra : Algebra (ResidueField B) C := by
  letI := originalTarget_isNoetherianRing f x
  letI := (residue_finite_separable f x hx).1
  letI := (residue_finite_separable f x hx).2
  exact Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldAlgebra A B

/-- The literal original ambient point in the original singular support has an actual quadratic model, with no supplied singular-scheme lift or geometric-field parameter. -/
theorem exists_quadratic_model :
    letI := pointAlgebra f x hx
    ∃ q : Algebra.NodeNonsplit.Quadratic (ResidueField B),
      Nonempty (C ≃ₐ[ResidueField B] Algebra.NodeNonsplit.QuadraticNode q) := by
  have hx' : x ∈ ((I).support : Set X) := hx
  rw [← (I).range_subschemeι] at hx'
  obtain ⟨z, hz⟩ := hx'
  subst x
  exact NodeCompletedLocalOriginalNodePointClassification.exists_original_point_quadratic_model_native f z

/-- EVERY original ambient-point coefficient has its SAME original constant class in an actual source-produced model. -/
theorem exists_quadratic_model_with_coefficients :
    letI := pointAlgebra f x hx
    ∃ q : Algebra.NodeNonsplit.Quadratic (ResidueField B),
      ∃ e : C ≃ₐ[ResidueField B] Algebra.NodeNonsplit.QuadraticNode q,
        ∀ a : ResidueField B, e (algebraMap (ResidueField B) C a) =
          Ideal.Quotient.mk _ (MvPowerSeries.C a) := by
  let := pointAlgebra f x hx
  obtain ⟨q, ⟨e⟩⟩ := exists_quadratic_model f x hx
  exact ⟨q, e, fun a => e.commutes a⟩

end Hironaka.Geometry.NodeCompletedLocalOriginalNodeSupportClassification
