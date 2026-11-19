import Hironaka.Algebra.ModuleFlatteningMinorsExistence
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The actual algebra image of the original finite-algebra pure transform

The coefficient-induced algebra tensor map has literally the canonical
module tensor map as its underlying linear map. Its native algebra range
therefore carries the already constructed pure-transform basis, preserving
the original multiplication, unit, coefficients and generator images.
-/

noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace Hironaka.Algebra.FiniteMorphismFlattening

open ModuleFlatteningMinors ModuleFlatteningMinorsPureTransform
  ModuleFlatteningMinorsExistence

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The actual original algebra tensor map induced by the fraction-chart inclusion. -/
def tensorAlgMap (S : Subalgebra R (FractionRing R)) :
    S ⊗[R] A →ₐ[S] FractionRing R ⊗[R] A :=
  Algebra.TensorProduct.map (Algebra.ofId S (FractionRing R)) (AlgHom.id R A)

/-- This actual algebra homomorphism has the original canonical module map. -/
theorem tensorAlgMap_toLinearMap (S : Subalgebra R (FractionRing R)) :
    (tensorAlgMap R A S).toLinearMap = tensorMap R A S := rfl

/-- The actual algebra pure transform, with multiplication inherited from the original generic algebra. -/
abbrev pureTransformAlgebra (S : Subalgebra R (FractionRing R)) :
    Subalgebra S (FractionRing R ⊗[R] A) := (tensorAlgMap R A S).range

/-- The original generator retains its literal original generic tensor image. -/
@[simp]
theorem tensorAlgMap_one_tmul (S : Subalgebra R (FractionRing R)) (a : A) :
    tensorAlgMap R A S ((1 : S) ⊗ₜ[R] a) = (1 : FractionRing R) ⊗ₜ[R] a := by
  simp [tensorAlgMap]

/-- Equality with the original module image uses the same actual preimage witnesses. -/
theorem pureTransformAlgebra_toSubmodule (S : Subalgebra R (FractionRing R)) :
    (pureTransformAlgebra R A S).toSubmodule = pureTransform R A S := rfl

/-- The actual algebra range and actual module range have the same original elements. -/
def pureTransformLinearEquiv (S : Subalgebra R (FractionRing R)) :
    pureTransformAlgebra R A S ≃ₗ[S] pureTransform R A S :=
  LinearEquiv.ofEq _ _ (pureTransformAlgebra_toSubmodule R A S)

/-- The range comparison preserves every original underlying generic algebra element. -/
@[simp]
theorem pureTransformLinearEquiv_coe (S : Subalgebra R (FractionRing R))
    (x : pureTransformAlgebra R A S) :
    (pureTransformLinearEquiv R A S x : FractionRing R ⊗[R] A) = x := rfl

/-- The actual original tensor algebra surjects onto its actual algebra pure transform. -/
theorem tensorAlgMap_rangeRestrict_surjective (S : Subalgebra R (FractionRing R)) :
    Function.Surjective (tensorAlgMap R A S).rangeRestrict :=
  AlgHom.rangeRestrict_surjective _

/-- The original finite algebra internally constructs a nonzero minor ideal with finite
free and flat actual algebra pure transforms on every nonzero original minor chart. -/
theorem exists_nonzero_minorIdeal_free_finite_flat_algebra [IsDomain R] [Module.Finite R A] :
    ∃ (n r : ℕ) (m : Fin n → A) (V : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal V).FG ∧ minorIdeal V ≠ ⊥ ∧
      ∀ (s : Fin r → Fin n), columnMinor V s ≠ 0 →
        let S := affineBlowupFractionChart (minorIdeal V) (columnMinor V s)
        Module.Free S (pureTransformAlgebra R A S) ∧
          Module.Finite S (pureTransformAlgebra R A S) ∧
          Module.Flat S (pureTransformAlgebra R A S) ∧
          Module.finrank S (pureTransformAlgebra R A S) = r := by
  obtain ⟨n, r, m, V, hm, hfg, hI, hB⟩ :=
    exists_nonzero_minorIdeal_free_pureTransform R A
  refine ⟨n, r, m, V, hm, hfg, hI, fun s hs ↦ ?_⟩
  obtain ⟨B, hBimage⟩ := hB s hs
  let S := affineBlowupFractionChart (minorIdeal V) (columnMinor V s)
  let C := B.map (pureTransformLinearEquiv R A S).symm
  let : Module.Free S (pureTransformAlgebra R A S) := Module.Free.of_basis C
  exact ⟨inferInstance, Module.Finite.of_basis C, inferInstance,
    (Module.finrank_eq_card_basis C).trans (Fintype.card_fin r)⟩

end Hironaka.Algebra.FiniteMorphismFlattening
