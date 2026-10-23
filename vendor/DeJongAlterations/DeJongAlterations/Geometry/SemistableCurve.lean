import DeJongAlterations.Geometry.NodeCompletedLocalCoherentUV
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The geometric completed-local definition of a semi-stable curve

Source 2.21: ordinary double points are defined on actual algebraically
closed geometric fibres. No relative total-space normal form is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry

universe u

/-- The actual geometric completed local ring, with its canonical original field action. -/
def IsGeometricOrdinaryDoublePoint {K : Type u} [Field K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) (y : Y) : Prop :=
  letI := Scheme.completedLocalRingAlgebra q y
  Nonempty (Y.completedLocalRing y ≃ₐ[K] Algebra.NodeGeometricCompletionFormalUV.FormalUV K)

/-- Semi-stability via actual geometric curves and their geometric completed nodes (2.21). -/
class IsSemistableCurve {X S : Scheme.{u}} (f : X ⟶ S) : Prop
    extends Flat f, IsProper f, LocallyOfFinitePresentation f,
      GeometricallyConnected f, GeometricallyReduced f where
  pureGeometricFibers : ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (C : Set (pullback (C := Scheme.{u}) f a)),
    C ∈ irreducibleComponents (pullback (C := Scheme.{u}) f a) → topologicalKrullDim C = 1
  geometricNodes : ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (y : pullback (C := Scheme.{u}) f a),
    IsClosed ({y} : Set (pullback (C := Scheme.{u}) f a)) →
      y ∈ (pullback.snd f a).smoothLocus ∨
        IsGeometricOrdinaryDoublePoint (pullback.snd f a) y

end DeJongAlterations.Geometry
