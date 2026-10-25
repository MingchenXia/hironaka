import DeJongAlterations.Algebra.SteinTensorConnected

/-!
# Actual finite scalar specialization preserving nonzero tensors

The coefficient subalgebra, its maximal ideal, the finite residue field
and both actual tensor lifts are constructed from basis coefficients.
-/

noncomputable section

open TensorProduct

namespace DeJongAlterations.Algebra.SteinTensorSpecialization

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]

/-- Produce the actual finite scalar residue field and actual nonvanishing lifts internally. -/
theorem exists_finite_specialization (x y : E ⊗[K] F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ B : Subalgebra K E, Algebra.FiniteType K B ∧
      ∃ q : Ideal B, q.IsMaximal ∧ Module.Finite K (B ⧸ q) ∧
        ∃ xB yB : B ⊗[K] F,
          Algebra.TensorProduct.map B.val (AlgHom.id K F) xB = x ∧
          Algebra.TensorProduct.map B.val (AlgHom.id K F) yB = y ∧
          Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K q) (AlgHom.id K F) xB ≠ 0 ∧
          Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K q) (AlgHom.id K F) yB ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis K F
  let c := TensorProduct.equivFinsuppOfBasisRight b x
  let d := TensorProduct.equivFinsuppOfBasisRight b y
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! hc
    apply hx
    apply (TensorProduct.equivFinsuppOfBasisRight b).injective
    ext i
    exact hc i
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra! hd
    apply hy
    apply (TensorProduct.equivFinsuppOfBasisRight b).injective
    ext j
    exact hd j
  let s := (c.support.image c ∪ d.support.image d) ∪ {(c i)⁻¹, (d j)⁻¹}
  let B := Algebra.adjoin K (s : Set E)
  have hcB (l) : c l ∈ B := by
    by_cases hl : l ∈ c.support
    · exact Algebra.subset_adjoin (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hl)))
    · rw [Finsupp.notMem_support_iff.mp hl]; exact B.zero_mem
  have hdB (l) : d l ∈ B := by
    by_cases hl : l ∈ d.support
    · exact Algebra.subset_adjoin (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hl)))
    · rw [Finsupp.notMem_support_iff.mp hl]; exact B.zero_mem
  have hiB : (c i)⁻¹ ∈ B := Algebra.subset_adjoin (by simp [s])
  have hjB : (d j)⁻¹ ∈ B := Algebra.subset_adjoin (by simp [s])
  let xB : B ⊗[K] F :=
    ∑ l ∈ c.support.attach, (⟨c l.1, hcB l.1⟩ : B) ⊗ₜ[K] b l.1
  let yB : B ⊗[K] F :=
    ∑ l ∈ d.support.attach, (⟨d l.1, hdB l.1⟩ : B) ⊗ₜ[K] b l.1
  let m := Algebra.TensorProduct.map B.val (AlgHom.id K F)
  have hmx : m xB = x := by
    simp only [xB, m, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change (∑ l ∈ c.support.attach, c l.1 ⊗ₜ[K] b l.1) = x
    rw [Finset.sum_attach c.support (fun l => c l ⊗ₜ[K] b l)]
    simpa only [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum] using
      (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply x
  have hmy : m yB = y := by
    simp only [yB, m, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change (∑ l ∈ d.support.attach, d l.1 ⊗ₜ[K] b l.1) = y
    rw [Finset.sum_attach d.support (fun l => d l ⊗ₜ[K] b l)]
    simpa only [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum] using
      (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply y
  have hu (z : B ⊗[K] F) (l) (hn : TensorProduct.equivFinsuppOfBasisRight b (m z) l ≠ 0)
      (hinv : (TensorProduct.equivFinsuppOfBasisRight b (m z) l)⁻¹ ∈ B) :
      IsUnit (TensorProduct.equivFinsuppOfBasisRight b z l) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    change B.val _ * _ = 1
    rw [← SteinTensorConnected.coefficient_map b l B.val]
    exact mul_inv_cancel₀ hn
  have hui : IsUnit (TensorProduct.equivFinsuppOfBasisRight b xB i) :=
    hu xB i (by simpa only [hmx] using hi) (by simpa only [hmx] using hiB)
  have huj : IsUnit (TensorProduct.equivFinsuppOfBasisRight b yB j) :=
    hu yB j (by simpa only [hmy] using hj) (by simpa only [hmy] using hjB)
  obtain ⟨q, hq⟩ := Ideal.exists_maximal B
  let := hq
  let L := B ⧸ q
  let : Field L := Ideal.Quotient.field q
  let hB : Algebra.FiniteType K B := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  let hL : Module.Finite K L := finite_of_finite_type_of_isJacobsonRing K L
  let φ : B →ₐ[K] L := Ideal.Quotient.mkₐ K q
  let n := Algebra.TensorProduct.map φ (AlgHom.id K F)
  have hn0 (z : B ⊗[K] F) (l)
      (hz : IsUnit (TensorProduct.equivFinsuppOfBasisRight b z l)) : n z ≠ 0 := by
    intro hn
    have H := SteinTensorConnected.coefficient_map b l φ z
    rw [show Algebra.TensorProduct.map φ (AlgHom.id K F) z = n z from rfl, hn] at H
    exact (hz.map φ).ne_zero (by simpa using H.symm)
  exact ⟨B, hB, q, hq, hL, xB, yB, hmx, hmy, hn0 xB i hui, hn0 yB j huj⟩

end DeJongAlterations.Algebra.SteinTensorSpecialization
