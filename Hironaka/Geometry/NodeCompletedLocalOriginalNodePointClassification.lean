import Hironaka.Geometry.NodeCompletedLocalOriginalNodeQuadraticClassification
import Hironaka.Algebra.NodeGeometricCompletionCoefficientReindex
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The actual original point-residue quadratic model, with its SAME original Hensel coefficients. -/

noncomputable section

open AlgebraicGeometry IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalOriginalNodePointClassification

open NodeCompletedLocalMap NodeCompletedLocalOriginalNodeJets

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f] [IsLocallyNoetherian S]
  (z : (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subscheme)

local notation "x" => (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z
local notation "A" => S.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
local notation "R" => OriginalFiberRing f x
local notation "C" => Algebra.CompletionRegularityBasics.Completion R

attribute [local instance] originalAlgebra originalFiberResidueAlgebra
  originalFiberResidue_finite originalFiberResidue_separable

local instance originalLocalMap : IsLocalHom (algebraMap A B) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

local instance originalQuotientLocalRing : IsLocalRing R := originalFiberLocalRing f x

local instance originalAlgebraicQuotientLocalRing :
    IsLocalRing (Algebra.NodeGeometricCompletionOriginalFiberSection.FiberRing A B) :=
  Algebra.CompletionIdealQuotient.quotientLocalRing _
    (Algebra.CompletionLocalMap.closedFiberIdeal_le_maximalIdeal (algebraMap A B))

local instance originalTargetNoetherian : IsNoetherianRing B := originalTarget_isNoetherianRing f x

local instance originalResidueFinite : FiniteDimensional (ResidueField A) (ResidueField B) :=
  (originalResidue_finite_separable f z).1

local instance originalResidueSeparable : Algebra.IsSeparable (ResidueField A) (ResidueField B) :=
  (originalResidue_finite_separable f z).2

/-- The actual ORIGINAL point field acts by the SAME original Hensel section; all its native hypotheses come from the original geometry. -/
@[instance_reducible]
def originalHenselPointAlgebra : Algebra (ResidueField B) C :=
  Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldAlgebra A B

variable (L : Type u) [Field L] [IsAlgClosed L]
  [Algebra (X.residueField ((Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z)) L]

include L in
/-- The ORIGINAL semistable geometry produces its genuine closed-fibre quadratic model over the ORIGINAL point residue, with no model or coefficient-compatibility premise. -/
theorem exists_original_point_quadratic_model :
    letI := originalHenselPointAlgebra f z
    ∃ q : Algebra.NodeNonsplit.Quadratic (ResidueField B),
      Nonempty (C ≃ₐ[ResidueField B] Algebra.NodeNonsplit.QuadraticNode q) := by
  let := originalHenselPointAlgebra f z
  let := originalPointAlgebra f z
  let : Algebra (ResidueField A)
      (Algebra.NodeGeometricCompletionOriginalFiberSection.FiberRing A B) :=
    Algebra.NodeGeometricCompletionOriginalFiberSection.baseResidueAlgebra A B
  let : Algebra (ResidueField B)
      (Algebra.CompletionRegularityBasics.Completion
        (Algebra.NodeGeometricCompletionOriginalFiberSection.FiberRing A B)) :=
    Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldAlgebra A B
  obtain ⟨q, ⟨e⟩⟩ :=
    NodeCompletedLocalOriginalNodeQuadraticClassification.exists_quadratic_model f z L
  let χ := (Algebra.NodeGeometricCompletionFiberResidue.quotientResidueAlgEquiv A B).toRingEquiv
  let e' : Algebra.NodeNonsplit.QuadraticNode (q.map χ.symm.toRingHom) ≃ₐ[ResidueField B] C :=
    Algebra.NodeGeometricCompletionCoefficientReindex.originalQuadraticEquiv A B q e.symm
  exact ⟨q.map χ.symm.toRingHom, ⟨e'.symm⟩⟩

include L in
/-- EVERY actual ORIGINAL point coefficient has exactly its original constant image in a genuine source-produced quadratic model. -/
theorem exists_original_point_quadratic_model_with_coefficients :
    letI := originalHenselPointAlgebra f z
    ∃ q : Algebra.NodeNonsplit.Quadratic (ResidueField B),
      ∃ e : C ≃ₐ[ResidueField B] Algebra.NodeNonsplit.QuadraticNode q,
        ∀ a : ResidueField B,
          e (Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldSection A B a) =
            Ideal.Quotient.mk _ (MvPowerSeries.C a) := by
  let := originalHenselPointAlgebra f z
  obtain ⟨q, ⟨e⟩⟩ := exists_original_point_quadratic_model f z L
  exact ⟨q, e, fun a => e.commutes a⟩

/-- Choosing the actual original point's algebraic closure INTERNALLY removes the final geometric-field parameter. -/
theorem exists_original_point_quadratic_model_native :
    letI := originalHenselPointAlgebra f z
    ∃ q : Algebra.NodeNonsplit.Quadratic (ResidueField B),
      Nonempty (C ≃ₐ[ResidueField B] Algebra.NodeNonsplit.QuadraticNode q) :=
  exists_original_point_quadratic_model f z (AlgebraicClosure (X.residueField x))

/-- The model and EVERY original coefficient formula require ONLY the actual original curve and original singular point. -/
theorem exists_original_point_quadratic_model_native_with_coefficients :
    letI := originalHenselPointAlgebra f z
    ∃ q : Algebra.NodeNonsplit.Quadratic (ResidueField B),
      ∃ e : C ≃ₐ[ResidueField B] Algebra.NodeNonsplit.QuadraticNode q,
        ∀ a : ResidueField B,
          e (Algebra.NodeGeometricCompletionOriginalFiberSection.pointFieldSection A B a) =
            Ideal.Quotient.mk _ (MvPowerSeries.C a) :=
  exists_original_point_quadratic_model_with_coefficients f z
    (AlgebraicClosure (X.residueField x))

end Hironaka.Geometry.NodeCompletedLocalOriginalNodePointClassification
