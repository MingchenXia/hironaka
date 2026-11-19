import Hironaka.Algebra.RelativeUnramifiedMaximal
import Hironaka.Geometry.ProjectiveSecantProjectionLocalBridge
import Hironaka.Geometry.RelativeUnramifiedStalkCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Actual original closed stalks detect formal unramifiedness -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.RelativeUnramified

universe u

/-- All original closed points suffice when the actual source is Jacobson. -/
theorem formallyUnramified_of_closed_stalks {X S : Scheme.{u}} [JacobsonSpace X]
    (f : X ⟶ S)
    (h : ∀ x : X, IsClosed ({x} : Set X) → (f.stalkMap x).hom.FormallyUnramified) :
    FormallyUnramified f := by
  constructor
  intro U hU V hV e
  let β : Γ(S, U) ⟶ Γ(X, V) := f.appLE U V e
  let : Algebra Γ(S, U) Γ(X, V) := β.hom.toAlgebra
  change Algebra.FormallyUnramified Γ(S, U) Γ(X, V)
  apply Algebra.RelativeUnramified.formallyUnramified_of_maximal
  intro m hm
  let Q : PrimeSpectrum Γ(X, V) := ⟨m, inferInstance⟩
  have hQ : Q ∈ closedPoints (Spec Γ(X, V)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal Q).mpr hm
  have hx : IsClosed ({hV.fromSpec Q} : Set X) := by
    change Q ∈ hV.fromSpec ⁻¹' closedPoints X
    rw [hV.fromSpec.isOpenEmbedding.preimage_closedPoints]
    exact hQ
  have H := ProjectiveSecant.chart_stalkMap_formallyUnramified_of_original
    f hV.fromSpec hU.fromSpec β
    (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm Q (h _ hx)
  exact ProjectiveSecant.isUnramifiedAt_of_spec_stalkMap β Q H

/-- The Jacobson property of the actual original field-scheme is derived internally. -/
theorem formallyUnramified_overField_of_closed_stalks {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (h : ∀ x : X, IsClosed ({x} : Set X) → (f.stalkMap x).hom.FormallyUnramified) :
    FormallyUnramified f := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  exact formallyUnramified_of_closed_stalks f h

/-- Actual coefficient-valued closed stalks imply the SAME original morphism is unramified. -/
theorem formallyUnramified_overField_of_closed_stalk_equiv {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      letI := Scheme.stalkAlgebra f x
      Nonempty ((X.presheaf.stalk x) ≃ₐ[K] K)) :
    FormallyUnramified f := by
  apply formallyUnramified_overField_of_closed_stalks f
  intro x hx
  obtain ⟨e⟩ := h x hx
  exact stalkMap_formallyUnramified_of_coefficientEquiv K f x e

end Hironaka.Geometry.RelativeUnramified
