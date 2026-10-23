import DeJongAlterations.Algebra.NodeNormal
import DeJongAlterations.Geometry.RegularCurve

/-! Native normality of the actual node spectrum and Zariski descent on actual stalks. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.NodeNormal

open Algebra.NodeBlowupChart

universe u v

/-- Normality on genuine open charts descends to the actual local rings of a scheme. -/
theorem isNormalScheme_of_openCover (X : Scheme.{u}) (𝒰 : X.OpenCover.{v})
    (h : ∀ i, IsNormalScheme (𝒰.X i)) : IsNormalScheme X := by
  intro x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  let := (h (𝒰.idx x) y).1
  let := (h (𝒰.idx x) y).2
  let e := (asIso ((𝒰.f (𝒰.idx x)).stalkMap y)).commRingCatIsoToRingEquiv
  have hn : IsDomain (X.presheaf.stalk (𝒰.f (𝒰.idx x) y)) ∧
      IsIntegrallyClosed (X.presheaf.stalk (𝒰.f (𝒰.idx x) y)) :=
    ⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩
  rw [hy] at hn
  exact hn

/-- The genuine node spectrum over an integrally closed domain has normal actual local rings. -/
theorem node_isNormalScheme {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (t : A) (ht : t ≠ 0) : IsNormalScheme (Spec (CommRingCat.of (Node A t))) := by
  let := Algebra.NodeDomain.nodeQuotient_isDomain t ht
  let := Algebra.NodeNormal.node_isIntegrallyClosed t ht
  exact isNormalScheme_spec (Node A t)

end DeJongAlterations.Geometry.NodeNormal
