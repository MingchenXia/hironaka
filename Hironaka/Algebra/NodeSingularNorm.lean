import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # The actual finite-free norm annihilates the original parameter quotient -/

noncomputable section

namespace Hironaka.Algebra.NodeSingular

open scoped Matrix

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]


/-- The actual multiplication determinant is a multiple of the original element. -/
theorem algebraMap_norm_mem_span [Module.Free R S] [Module.Finite R S] (h : S) :
    algebraMap R S (Algebra.norm R h) ∈ Ideal.span {h} := by
  classical
  let b := Module.Free.chooseBasis R S
  let M := Algebra.leftMulMatrix b h
  let y : S := b.equivFun.symm (M.adjugate *ᵥ b.equivFun 1)
  have hy : h * y = algebraMap R S (Algebra.norm R h) := by
    apply b.equivFun.injective
    calc
      b.equivFun (h * y) = M *ᵥ b.equivFun y :=
        (Algebra.leftMulMatrix_mulVec_repr b h y).symm
      _ = M *ᵥ (M.adjugate *ᵥ b.equivFun 1) := by
        rw [show b.equivFun y = M.adjugate *ᵥ b.equivFun 1 from b.equivFun.apply_symm_apply _]
      _ = (M * M.adjugate) *ᵥ b.equivFun 1 := by rw [Matrix.mulVec_mulVec]
      _ = (M.det • (1 : Matrix _ _ R)) *ᵥ b.equivFun 1 := by rw [Matrix.mul_adjugate]
      _ = b.equivFun (algebraMap R S (Algebra.norm R h)) := by
        rw [Algebra.norm_eq_matrix_det b]
        simp [Algebra.algebraMap_eq_smul_one, M, Matrix.smul_mulVec]
  rw [← hy]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton h))

/-- The actual original norm vanishes in the original parameter quotient. -/
theorem norm_quotient_eq_zero [Module.Free R S] [Module.Finite R S] (h : S) :
    algebraMap R (S ⧸ Ideal.span {h}) (Algebra.norm R h) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (algebraMap_norm_mem_span h)

/-- The original coefficient map factors through the actual norm zero locus. -/
def normLocusMap [Module.Free R S] [Module.Finite R S] (h : S) :
    R ⧸ Ideal.span {Algebra.norm R h} →+* S ⧸ Ideal.span {h} :=
  Ideal.Quotient.lift _ (algebraMap R (S ⧸ Ideal.span {h})) (by
    change Ideal.span {Algebra.norm R h} ≤ RingHom.ker (algebraMap R (S ⧸ Ideal.span {h}))
    apply Ideal.span_le.mpr
    rintro a rfl
    exact norm_quotient_eq_zero h)

@[simp]
theorem normLocusMap_mk [Module.Free R S] [Module.Finite R S] (h : S) (r : R) :
    normLocusMap (R := R) h (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R S r) := rfl

/-- The actual norm-locus factor is finite, without a false etaleness assertion. -/
theorem normLocusMap_finite [Module.Free R S] [Module.Finite R S] (h : S) :
    (normLocusMap (R := R) h).Finite := by
  apply RingHom.Finite.of_comp_finite
    (f := Ideal.Quotient.mk (Ideal.span {Algebra.norm R h}))
  have he : (normLocusMap (R := R) h).comp (Ideal.Quotient.mk (Ideal.span {Algebra.norm R h})) =
      algebraMap R (S ⧸ Ideal.span {h}) := by
    ext r
    rfl
  rw [he, RingHom.finite_algebraMap]
  infer_instance

/-- The actual local coefficient norm of a smoothing parameter is in the original maximal ideal. -/
theorem norm_mem_maximalIdeal [Module.Free R S] [Module.Finite R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    (h : S) (hh : h ∈ IsLocalRing.maximalIdeal S) :
    Algebra.norm R h ∈ IsLocalRing.maximalIdeal R := by
  rw [← IsLocalRing.maximalIdeal_comap (algebraMap R S)]
  change algebraMap R S (Algebra.norm R h) ∈ IsLocalRing.maximalIdeal S
  have hle : Ideal.span {h} ≤ IsLocalRing.maximalIdeal S := by
    apply Ideal.span_le.mpr
    rintro a rfl
    exact hh
  exact hle (algebraMap_norm_mem_span h)

end Hironaka.Algebra.NodeSingular
