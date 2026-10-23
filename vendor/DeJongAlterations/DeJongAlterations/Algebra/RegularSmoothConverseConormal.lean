import DeJongAlterations.Algebra.RegularQuotient
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# The actual ideal tensor map into the maximal cotangent space

Actual ideal generators with independent maximal cotangent classes make this
map injective. No rank or conormal injectivity certificate is assumed.
-/

open IsLocalRing TensorProduct

namespace DeJongAlterations.Algebra.RegularSmoothConverseConormal

noncomputable section

variable {P : Type*} [CommRing P] [IsLocalRing P]

/-- Extend the actual ideal inclusion followed by the actual maximal cotangent quotient. -/
def toMaximalCotangent (I : Ideal P) (hI : I ≤ maximalIdeal P) :
    ResidueField P ⊗[P] I →ₗ[ResidueField P] CotangentSpace P :=
  ((maximalIdeal P).toCotangent.comp (Submodule.inclusion hI)).liftBaseChange (ResidueField P)

@[simp]
theorem toMaximalCotangent_tmul (I : Ideal P) (hI : I ≤ maximalIdeal P)
    (a : ResidueField P) (x : I) :
    toMaximalCotangent I hI (a ⊗ₜ[P] x) =
      a • (maximalIdeal P).toCotangent ⟨(x : P), hI x.property⟩ := rfl

/-- Ideal generation gives generation of the entire actual residue tensor product. -/
theorem span_one_tmul_generators {ι : Type*} (I : Ideal P) (t : ι → I)
    (hspan : Ideal.span (Set.range fun i => (t i : P)) = I) :
    Submodule.span (ResidueField P)
      (Set.range fun i => (1 : ResidueField P) ⊗ₜ[P] t i) = ⊤ := by
  have hmod : Submodule.span P (Set.range t) = ⊤ := by
    apply (Submodule.map_injective_of_injective (f := I.subtype) Subtype.val_injective)
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    exact hspan
  have h := congrArg (fun M : Submodule P I => M.baseChange (ResidueField P)) hmod
  rw [Submodule.baseChange_span, Submodule.baseChange_top] at h
  simpa only [← Set.range_comp, Function.comp_def, TensorProduct.mk_apply] using h

/-- Independent actual generator classes force injectivity of the actual residue conormal map. -/
theorem toMaximalCotangent_injective {ι : Type*} (I : Ideal P)
    (hI : I ≤ maximalIdeal P) (t : ι → I)
    (hspan : Ideal.span (Set.range fun i => (t i : P)) = I)
    (hli : LinearIndependent (ResidueField P)
      (fun i => (maximalIdeal P).toCotangent ⟨(t i : P), hI (t i).property⟩)) :
    Function.Injective (toMaximalCotangent I hI) := by
  let v : ι → ResidueField P ⊗[P] I := fun i => 1 ⊗ₜ[P] t i
  have hs : Function.Surjective (Finsupp.linearCombination (ResidueField P) v) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact span_one_tmul_generators I t hspan
  have hcomp : toMaximalCotangent I hI ∘ v =
      (fun i => (maximalIdeal P).toCotangent ⟨(t i : P), hI (t i).property⟩) := by
    funext i
    simp only [Function.comp_apply, v, toMaximalCotangent_tmul, one_smul]
  intro x y hxy
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  apply congrArg (Finsupp.linearCombination (ResidueField P) v)
  apply linearIndependent_iff_injective_finsuppLinearCombination.mp hli
  simpa only [Finsupp.apply_linearCombination, hcomp] using hxy

end

end DeJongAlterations.Algebra.RegularSmoothConverseConormal
