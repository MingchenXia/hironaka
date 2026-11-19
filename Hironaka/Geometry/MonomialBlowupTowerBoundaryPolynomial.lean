import Hironaka.Geometry.PolynomialNodeBoundary
import Hironaka.Geometry.SNCLocality

/-!
# Arbitrary coordinate-node polynomial charts for the finite tower boundary

The actual quotient is eliminated, preserving both node and coefficient maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.MonomialBlowupTowerBoundaryPolynomial

open Algebra.NodeBlowupChart SpecIdealSheaf CoordinateSNC ReducedClosedSubscheme

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type u) [Field K] {ι : Type u} [DecidableEq ι]

abbrev Base := MvPolynomial ι K
abbrev Chart (i : ι) := Node (Base K (ι := ι)) (X i)
abbrev Variables (i : ι) := Fin 2 ⊕ {j : ι // j ≠ i}
abbrev PolynomialChart (i : ι) := MvPolynomial (Variables i) K

/-- The actual coefficient substitution replacing precisely the node parameter. -/
def baseEvaluation (i : ι) : Base K (ι := ι) →ₐ[K] PolynomialChart K i :=
  aeval fun j ↦ if h : j = i then X (Sum.inl 0) * X (Sum.inl 1) else X (Sum.inr ⟨j, h⟩)

def polynomialEvaluation (i : ι) :
    MvPolynomial (Fin 2) (Base K (ι := ι)) →ₐ[K] PolynomialChart K i :=
  aevalTower (baseEvaluation K i) (fun j ↦ X (Sum.inl j))

private theorem evaluation_ideal (i : ι) :
    Algebra.NodeChart.uChartIdeal (Base K (ι := ι)) (X i) ≤
      RingHom.ker (polynomialEvaluation K i).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = _)
  change polynomialEvaluation K i (X 0 * X 1 - C (X i)) = 0
  simp [polynomialEvaluation, baseEvaluation]

/-- The actual quotient map to the polynomial chart. -/
def forward (i : ι) : Chart K i →ₐ[K] PolynomialChart K i :=
  Ideal.Quotient.liftₐ _ (polynomialEvaluation K i) (fun _ h ↦ evaluation_ideal K i h)

@[simp]
theorem forward_mk (i : ι) (F : MvPolynomial (Fin 2) (Base K (ι := ι))) :
    forward K i (Ideal.Quotient.mk _ F) = polynomialEvaluation K i F := rfl

@[simp]
theorem forward_coordinate (i : ι) (j : Fin 2) :
    forward K i (coordinate (X i : Base K (ι := ι)) j) = X (Sum.inl j) := by
  simp [coordinate, polynomialEvaluation]

@[simp]
theorem forward_base (i : ι) (a : Base K (ι := ι)) :
    forward K i (algebraMap (Base K (ι := ι)) (Chart K i) a) = baseEvaluation K i a := by
  change forward K i (Ideal.Quotient.mk _ (C a)) = _
  simp [polynomialEvaluation]

/-- The reverse substitution uses the two actual quotient coordinates. -/
def backward (i : ι) : PolynomialChart K i →ₐ[K] Chart K i :=
  aeval (Sum.elim (fun j ↦ coordinate (X i : Base K (ι := ι)) j)
    (fun j ↦ algebraMap (Base K (ι := ι)) (Chart K i) (X j.val)))

private theorem backward_baseEvaluation (i : ι) :
    (backward K i).comp (baseEvaluation K i) =
      IsScalarTower.toAlgHom K (Base K (ι := ι)) (Chart K i) := by
  ext j
  by_cases h : j = i
  · subst j
    simpa [baseEvaluation, backward, coordinate] using
      (Algebra.NodeDomain.nodeCoordinateProduct (X i : Base K (ι := ι)))
  · simp [baseEvaluation, backward, h]

private theorem forward_backward (i : ι) :
    (forward K i).comp (backward K i) = AlgHom.id K _ := by
  ext j
  cases j with
  | inl j => simp [backward]
  | inr j => simp [backward, baseEvaluation, j.property]

private theorem backward_forward (i : ι) :
    (backward K i).comp (forward K i) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.coe_toRingHom,
      Ideal.Quotient.mkₐ_eq_mk, forward_mk, polynomialEvaluation, aevalTower_C,
      RingHom.comp_apply, IsScalarTower.toAlgHom_apply, ← Ideal.Quotient.mk_algebraMap,
      MvPolynomial.algebraMap_eq] using AlgHom.congr_fun (backward_baseEvaluation K i) a
  · intro j
    simp [polynomialEvaluation, backward, coordinate]

/-- A genuine algebra isomorphism of the full arbitrary-coordinate node quotient. -/
def polynomialEquiv (i : ι) : Chart K i ≃ₐ[K] PolynomialChart K i :=
  AlgEquiv.ofAlgHom (forward K i) (backward K i) (forward_backward K i) (backward_forward K i)

@[simp]
theorem polynomialEquiv_coordinate (i : ι) (j : Fin 2) :
    polynomialEquiv K i (coordinate (X i : Base K (ι := ι)) j) = X (Sum.inl j) :=
  forward_coordinate K i j

@[simp]
theorem polynomialEquiv_base (i : ι) (a : Base K (ι := ι)) :
    polynomialEquiv K i (algebraMap (Base K (ι := ι)) (Chart K i) a) = baseEvaluation K i a :=
  forward_base K i a

/-- The native actual scheme isomorphism associated to coordinate elimination. -/
def polynomialIso (i : ι) :
    Spec (CommRingCat.of (Chart K i)) ≅ Spec (CommRingCat.of (PolynomialChart K i)) :=
  Scheme.Spec.mapIso (polynomialEquiv K i).toRingEquiv.toCommRingCatIso.symm.op

@[simp]
theorem polynomialIso_hom (i : ι) :
    (polynomialIso K i).hom =
      Spec.map (CommRingCat.ofHom (polynomialEquiv K i).symm.toRingHom) := rfl

@[simp]
theorem polynomialIso_inv (i : ι) :
    (polynomialIso K i).inv =
      Spec.map (CommRingCat.ofHom (polynomialEquiv K i).toRingHom) := rfl

/-- On actual open immersions, radicalization commutes with the actual ideal comap. -/
theorem radical_comap_open {X U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (D : X.IdealSheafData) : D.radical.comap f = (D.comap f).radical := by
  let : IsReduced D.radical.subscheme := isReduced_radical_subscheme D
  let : IsReduced (D.radical.comap f).subscheme := SNCLocality.isReduced_comap f _
  let : IsReduced (D.comap f).radical.subscheme := isReduced_radical_subscheme _
  apply idealSheaf_eq_of_isReduced_of_support_eq
  simp only [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_radical]

end Hironaka.Geometry.MonomialBlowupTowerBoundaryPolynomial
