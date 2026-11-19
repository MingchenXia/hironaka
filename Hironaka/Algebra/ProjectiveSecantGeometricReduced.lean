import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Actual geometric reducedness internally produces a finite separating basis
-/

noncomputable section

open scoped TensorProduct
open TensorProduct

namespace Hironaka.Algebra.ProjectiveSecant

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual reduced scalar tensor products force finite original linear independence to survive Frobenius. -/
theorem linearIndependent_pow_of_reduced_tensor
    (k : Type u) (K : Type v) (L : Type w) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [IsAlgClosed L]
    [IsReduced (L ⊗[k] K)] (p : ℕ) (hp : p.Prime) [ExpChar k p]
    {ι : Type*} [Fintype ι] (v : ι → K) (hv : LinearIndependent k v) :
    LinearIndependent k (fun i => v i ^ p) := by
  classical
  let : Nontrivial (L ⊗[k] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k L K (algebraMap k K).injective
  let : ExpChar (L ⊗[k] K) p :=
    expChar_of_injective_algebraMap (algebraMap k (L ⊗[k] K)).injective p
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  choose b hb using (fun i => IsAlgClosed.exists_pow_nat_eq (algebraMap k L (a i)) hp.pos)
  let z : L ⊗[k] K := ∑ i, b i ⊗ₜ[k] v i
  have hzpow : z ^ p = 0 := by
    calc
      z ^ p = ∑ i, algebraMap k L (a i) ⊗ₜ[k] (v i ^ p) := by
        simp only [z, sum_pow_char, Algebra.TensorProduct.tmul_pow, hb]
      _ = (1 : L) ⊗ₜ[k] (∑ i, a i • (v i ^ p)) := by
        rw [TensorProduct.tmul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      _ = 0 := by rw [ha, TensorProduct.tmul_zero]
  have hz : z = 0 := IsNilpotent.eq_zero ⟨p, hzpow⟩
  have hli : LinearIndependent L (fun i => (1 : L) ⊗ₜ[k] v i) :=
    Module.Flat.linearIndependent_one_tmul hv
  have hbzero : ∀ i, b i = 0 := (Fintype.linearIndependent_iff.mp hli) b (by
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hz)
  intro i
  apply (algebraMap k L).injective
  rw [← hb i, hbzero i, zero_pow hp.ne_zero, map_zero]

/-- Actual original geometric reducedness supplies the finite Frobenius-independence hypothesis internally. -/
theorem linearIndepOn_pow_of_isGeometricallyReduced
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.IsGeometricallyReduced k K] (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) := by
  classical
  let : IsReduced (AlgebraicClosure k ⊗[k] K) :=
    (Algebra.isGeometricallyReduced_field_iff k K).mp inferInstance
  exact linearIndependent_pow_of_reduced_tensor k K (AlgebraicClosure k) p hp
    (fun x : s => (x : K)) hs

/-- The actual original geometrically reduced finitely generated field internally supplies a finite separating basis. -/
theorem exists_separating_basis_of_isGeometricallyReduced
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.IsGeometricallyReduced k K] [Algebra.EssFiniteType k K] :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  obtain _ | ⟨p, hp, _⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  · let : ExpChar k p := .prime hp.out
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hp.out
      (fun s hs => linearIndepOn_pow_of_isGeometricallyReduced k K p hp.out s hs)

/-- Formal smoothness is produced for the same actual original field algebra, without a supplied separating basis. -/
theorem formallySmooth_of_isGeometricallyReduced
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.IsGeometricallyReduced k K] [Algebra.EssFiniteType k K] :
    Algebra.FormallySmooth k K := by
  obtain ⟨s, hs, hsep⟩ := exists_separating_basis_of_isGeometricallyReduced k K
  let : Algebra.IsSeparable
      (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K := by
    convert! hsep <;> simp
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

end Hironaka.Algebra.ProjectiveSecant
