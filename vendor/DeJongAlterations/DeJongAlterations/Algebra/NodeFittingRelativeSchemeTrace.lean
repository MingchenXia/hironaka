import DeJongAlterations.Algebra.NodeFittingRelativeTrace
import DeJongAlterations.Algebra.NodeFittingOmegaGluing
import DeJongAlterations.Geometry.NodeCompletedLocalMap

/-! # The ENTIRE ORIGINAL global singular ideal at the SAME actual completed local model

The actual original scheme stalk map, its actual completion and the original
globally glued full ideal are used. Local Noetherianity and essential finite
type are internally derived; no singular-ideal comparison is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingRelativeSchemeTrace

open NodeFittingFormalDerivation NodeFittingIdealSheaf
  Geometry.NodeCompletedLocalMap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
  [IsLocallyNoetherian S] (x : X)

local notation "A" => S.presheaf.stalk (f x)
local notation "R" => X.presheaf.stalk x
local notation "Â" => S.completedLocalRing (f x)
local notation "C" => X.completedLocalRing x

local instance : Algebra A R := NodeFittingOmegaStalk.stalkAlgebra f x
local instance : IsLocalHom (algebraMap A R) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
local instance : Algebra.EssFiniteType A R := originalAlgebra_essFiniteType f x
local instance : Algebra Â C := completedAlgebra f x

/-- The ENTIRE actual original globally glued ideal equals the original native local differential Fitting ideal. -/
theorem originalGlobalStalkIdeal_eq (i : ℕ) :
    letI : IsNoetherianRing (X.presheaf.stalk x) := originalTarget_isNoetherianRing f x
    stalkIdeal (NodeFittingOmegaGluing.idealSheaf f i) x =
      NodeFittingRelativeTrace.originalFittingIdeal A R i := by
  let : IsNoetherianRing R := originalTarget_isNoetherianRing f x
  rw [NodeFittingOmegaGluing.idealSheaf_stalk]
  rfl

variable (T : Type u) [CommRing T] [IsLocalRing T]
  [Algebra (S.completedLocalRing (f x)) T]
  [Algebra T (X.completedLocalRing x)]
  [IsScalarTower (S.completedLocalRing (f x)) T (X.completedLocalRing x)]
  [Algebra.FormallyUnramified (S.completedLocalRing (f x)) T]

local instance : Algebra A T := NodeFittingRelativeTransport.originalCoefficientAlgebra A T

omit [LocallyOfFinitePresentation f] [IsLocallyNoetherian S] [IsLocalRing T]
  [Algebra.FormallyUnramified (S.completedLocalRing (f x)) T] in
/-- EVERY original base germ follows the SAME original stalk map and SAME actual coefficient lift. -/
theorem originalCoefficient_triangle (a : S.presheaf.stalk (f x)) :
    algebraMap T C (algebraMap A T a) = X.toCompletedLocalRing x (f.stalkMap x a) :=
  NodeFittingRelativeTransport.originalCoefficient_triangle A R T a

/-- The entire actual original global first Fitting trace is the SAME original formal gradient ideal. -/
theorem globalStalkIdeal_eq_gradient (F : Series T)
    (e : X.completedLocalRing x ≃ₐ[T] Hypersurface F) :
    (stalkIdeal (NodeFittingOmegaGluing.idealSheaf f 1) x).map
      (e.toRingHom.comp (X.toCompletedLocalRing x)) =
        Ideal.span {quotientMap F (MvPowerSeries.pderiv T 0 F),
          quotientMap F (MvPowerSeries.pderiv T 1 F)} := by
  let : IsNoetherianRing R := originalTarget_isNoetherianRing f x
  rw [originalGlobalStalkIdeal_eq]
  exact NodeFittingRelativeTrace.originalFittingIdeal_eq_gradient A R T F e

variable (Q : NodeNonsplit.Quadratic T) (h : T)
  (e : X.completedLocalRing x ≃ₐ[T] NodeSingular.Node Q h)

/-- The FULL original native global singular trace is the actual two-coordinate ideal, nonsplit and including characteristic two. -/
theorem globalStalkIdeal_eq_coordinateIdeal :
    (stalkIdeal (NodeFittingOmegaGluing.idealSheaf f 1) x).map
      (e.toRingHom.comp (X.toCompletedLocalRing x)) = NodeSingular.coordinateIdeal Q h := by
  let : IsNoetherianRing R := originalTarget_isNoetherianRing f x
  rw [originalGlobalStalkIdeal_eq]
  exact NodeFittingRelativeTrace.originalFittingIdeal_eq_coordinateIdeal A R T Q h e

/-- The SAME original completed singular scheme quotient, retaining the actual original T coefficient action. -/
def globalSingularQuotientEquiv :
    (C ⧸ (stalkIdeal (NodeFittingOmegaGluing.idealSheaf f 1) x).map
      (X.toCompletedLocalRing x)) ≃ₐ[T] T ⧸ Ideal.span {h} := by
  letI : IsNoetherianRing R := originalTarget_isNoetherianRing f x
  exact (Ideal.quotientEquivAlgOfEq T
    (congrArg (Ideal.map (X.toCompletedLocalRing x)) (originalGlobalStalkIdeal_eq f x 1))).trans
      (NodeFittingRelativeTrace.originalSingularQuotientEquiv A R T Q h e)

/-- EVERY actual original completed element follows the SAME actual normal form and parameter evaluation. -/
theorem globalSingularQuotientEquiv_mk (c : X.completedLocalRing x) :
    globalSingularQuotientEquiv f x T Q h e
      (Ideal.Quotient.mk ((stalkIdeal (NodeFittingOmegaGluing.idealSheaf f 1) x).map
        (X.toCompletedLocalRing x)) c) = NodeSingular.nodeEvaluation Q h (e c) := by
  let : IsNoetherianRing R := originalTarget_isNoetherianRing f x
  rw [globalSingularQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact NodeFittingRelativeTrace.originalSingularQuotientEquiv_mk A R T Q h e c

/-- EVERY original coefficient retains its native actual parameter-zero residue class. -/
theorem globalSingularQuotientEquiv_coefficient (t : T) :
    globalSingularQuotientEquiv f x T Q h e
      (Ideal.Quotient.mk ((stalkIdeal (NodeFittingOmegaGluing.idealSheaf f 1) x).map
        (X.toCompletedLocalRing x)) (algebraMap T C t)) =
          Ideal.Quotient.mk (Ideal.span {h}) t :=
  (globalSingularQuotientEquiv f x T Q h e).commutes t

end DeJongAlterations.Algebra.NodeFittingRelativeSchemeTrace
