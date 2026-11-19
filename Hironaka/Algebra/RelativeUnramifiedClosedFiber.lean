import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The ORIGINAL local map is formally unramified if its actual closed fibre is

Only original localness and essential finite type are used. Neither a nodal
model nor Noetherianity, flatness, a domain or residue separability is assumed.
-/

noncomputable section
open IsLocalRing
open scoped TensorProduct
namespace Hironaka.Algebra.RelativeUnramified
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual closed-fibre tensor and original local residue maps detect unramifiedness. -/
theorem formallyUnramified_of_residueTensor
    (R T : Type*) [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] [Algebra R T]
    [IsLocalHom (algebraMap R T)] [Algebra.EssFiniteType R T]
    [Algebra.FormallyUnramified (ResidueField R) (ResidueField R ⊗[R] T)] :
    Algebra.FormallyUnramified R T := by
  let Q := ResidueField R ⊗[R] T
  let : Algebra T Q := Algebra.TensorProduct.rightAlgebra
  let Ω := KaehlerDifferential R T
  let ψ : Q →ₐ[ResidueField R] ResidueField T :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (IsScalarTower.toAlgHom R T (ResidueField T)) (fun _ _ ↦ .all _ _)
  let : Algebra Q (ResidueField T) := ψ.toRingHom.toAlgebra
  let : IsScalarTower T Q (ResidueField T) :=
    IsScalarTower.of_algebraMap_eq fun t ↦ by
      change residue T t = ψ (1 ⊗ₜ[R] t)
      rw [Algebra.TensorProduct.lift_tmul]
      simp only [map_one, one_mul]
      rfl
  let : Subsingleton (Q ⊗[T] Ω) :=
    (KaehlerDifferential.tensorKaehlerEquiv R (ResidueField R) T Q).subsingleton
  let : Subsingleton (ResidueField T ⊗[Q] (Q ⊗[T] Ω)) := inferInstance
  have h : Subsingleton (ResidueField T ⊗[T] Ω) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      T Q (ResidueField T) (ResidueField T) Ω).symm.subsingleton
  exact ⟨(IsLocalRing.subsingleton_tensorProduct (R := T) (M := Ω)).mp h⟩

end Hironaka.Algebra.RelativeUnramified
