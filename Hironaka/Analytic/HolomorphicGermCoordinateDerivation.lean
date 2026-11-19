import Hironaka.Resolution.HironakaActualPrincipalPartsCompatibility

/-!
# Actual coordinate derivatives along a complex algebra germ map

The existing whole holomorphic directional derivation is reused. Its actual
representative derivative and restriction to an original algebra retain the
original scalar action; no derivative comparison is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Hironaka.HolomorphicGermCoordinateDerivation

open Filter HolGerm HolomorphicTaylorTail
open HironakaActualPrincipalPartsCompatibility HironakaRelativeNormalTaylorCoefficients
open HironakaHolomorphicJetMonomialSpan
open scoped Topology

variable {n : ℕ}

/-- The actual analytic coordinate coordinatePartial on the entire holomorphic germ ring. -/
def coordinatePartial (j : Fin n) : Derivation ℂ (HolGerm (ComplexModel n)) (HolGerm (ComplexModel n)) :=
  actualDirectionalDerivation (EuclideanSpace.single j 1)

/-- Every original representative retains its entire actual derivative germ. -/
theorem coordinatePartial_mk (j : Fin n) (f : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    coordinatePartial j (HolGerm.mk f hf) =
      HolGerm.mk (fun z => fderiv ℂ f z (EuclideanSpace.single j 1))
        (eventually_holomorphic_iterDeriv hf [EuclideanSpace.single j 1]) := rfl

/-- Coordinate partials give the literal Kronecker values on the original coordinates. -/
theorem coordinatePartial_coordinate (i j : Fin n) :
    coordinatePartial j (coordinateGerm i) = if i = j then 1 else 0 := by
  unfold coordinateGerm
  rw [coordinatePartial_mk]
  have he : (fun z : ComplexModel n =>
      fderiv ℂ (fun w : ComplexModel n => w i) z (EuclideanSpace.single j 1)) =
        fun _ => if i = j then (1 : ℂ) else 0 := by
    funext z
    have hproj : fderiv ℂ (fun w : ComplexModel n => w i) z =
        (PiLp.proj 2 (fun _ : Fin n => ℂ) i) :=
      (PiLp.proj 2 (fun _ : Fin n => ℂ) i).fderiv
    rw [hproj]
    simp
  calc
    _ = HolGerm.mk (fun _ : ComplexModel n => if i = j then (1 : ℂ) else 0)
        (eventually_differentiableAt_const _) :=
      HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z => congrFun he z)
    _ = _ := by split_ifs <;> simp [HolGerm.mk_const]

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Restrict actual analytic differentiation along the original complex algebra map. -/
def along (φ : A →ₐ[ℂ] HolGerm (ComplexModel n)) (j : Fin n) :
    letI := φ.toAlgebra
    Derivation ℂ A (HolGerm (ComplexModel n)) := by
  let := φ.toAlgebra
  let : IsScalarTower ℂ A (HolGerm (ComplexModel n)) :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  exact (coordinatePartial j).compAlgebraMap A

/-- Restriction retains the entire actual derivative of the same original image germ. -/
theorem along_apply (φ : A →ₐ[ℂ] HolGerm (ComplexModel n)) (j : Fin n) (a : A) :
    along φ j a = coordinatePartial j (φ a) := rfl

/-- Actual normalized coordinate images internally derive the coordinate derivative values. -/
theorem along_coordinate (φ : A →ₐ[ℂ] HolGerm (ComplexModel n))
    (v : Fin n → A) (c : Fin n → ℂ)
    (hv : ∀ i, φ (v i) = coordinateGerm i + HolGerm.constHom (c i)) (i j : Fin n) :
    along φ j (v i) = if i = j then 1 else 0 := by
  rw [along_apply, hv i, map_add, coordinatePartial_coordinate]
  change (if i = j then (1 : HolGerm (ComplexModel n)) else 0) +
    coordinatePartial j (algebraMap ℂ (HolGerm (ComplexModel n)) (c i)) = _
  rw [Derivation.map_algebraMap, add_zero]

end Hironaka.HolomorphicGermCoordinateDerivation
