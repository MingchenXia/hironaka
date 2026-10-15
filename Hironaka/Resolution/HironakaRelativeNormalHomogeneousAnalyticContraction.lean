/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphCentralIdealEquality

/-! Three prior full mathematical proofs: whole homogeneous ideal contraction
from actual finite holomorphic multiplier jets, no flatness certificate. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalHomogeneousAnalyticContraction
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalGraphCentralAnalyticClosure HironakaRelativeNormalGraphCentralIdealEquality
attribute [local instance] MvPolynomial.gradedAlgebra

theorem normalPolynomialEval_mem_analytic_map_iff (d t : ℕ)
    (H : Ideal (MvPolynomial (Fin t) (HolGerm (ComplexModel d))))
    (hH : H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    let := tangentAlgebra d t
    normalPolynomialEval d t P ∈ Ideal.map (normalPolynomialEval d t).toRingHom H ↔ P ∈ H := by
  classical
  let := tangentAlgebra d t
  constructor
  · intro hP
    change normalPolynomialEval d t P ∈ Submodule.span (HolGerm (ComplexModel (d+t)))
      ((normalPolynomialEval d t).toRingHom '' (H : Set (MvPolynomial (Fin t) (HolGerm (ComplexModel d))))) at hP
    obtain ⟨m,a,v,hv⟩ := Submodule.mem_span_set'.mp hP
    have hr (i : Fin m) : ∃ R ∈ H, normalPolynomialEval d t R = (v i).val := (v i).property
    choose R hRH hRv using hr
    have heq : normalPolynomialEval d t P = ∑ i : Fin m, a i * normalPolynomialEval d t (R i) := by
      calc
        _ = ∑ i : Fin m, a i * (v i).val := by simpa only [smul_eq_mul] using hv.symm
        _ = _ := Finset.sum_congr rfl (fun i _ => by rw [hRv i])
    let q := P.support.sup normalExponentDegree + 1
    have hbound : ∀ α : Fin t →₀ ℕ, q ≤ normalExponentDegree α → P.coeff α = 0 := by
      intro α hα
      by_contra hn
      have hs : α ∈ P.support := MvPolynomial.mem_support_iff.mpr hn
      have hle : normalExponentDegree α ≤ P.support.sup normalExponentDegree := Finset.le_sup hs
      dsimp only [q] at hα
      omega
    choose Q hQ hQbound using fun i : Fin m => exists_actual_bounded_normal_polynomial_jet d t q (a i)
    let S := ∑ i : Fin m, Q i * R i
    have hSH : S ∈ H := H.sum_mem (fun i _ => H.mul_mem_left (Q i) (hRH i))
    have hPQ : normalPolynomialEval d t P-normalPolynomialEval d t S ∈ normalIdeal d t^q := by
      have hm := (normalIdeal d t^q).sum_mem (fun i (_hi : i ∈ Finset.univ) =>
        (normalIdeal d t^q).mul_mem_right (normalPolynomialEval d t (R i)) (hQ i))
      simp only [sub_mul,Finset.sum_sub_distrib,← heq] at hm
      simpa only [S,map_sum,map_mul] using hm
    have hparts : ∀ k : ℕ, MvPolynomial.homogeneousComponent k P ∈ H := by
      intro k
      by_cases hk : k < q
      · have hPQk := Ideal.pow_le_pow_right (by omega : k+1 ≤ q) hPQ
        have he := actual_homogeneous_part_eq_of_same_normal_jet d t k P S hPQk
        change MvPolynomial.homogeneousComponent k P = MvPolynomial.homogeneousComponent k S at he
        rw [he]
        exact (MvPolynomial.mem_iff_homogeneousComponent_mem hH S).mp hSH k
      · have hz : MvPolynomial.homogeneousComponent k P = 0 := by
          apply MvPolynomial.ext
          intro α
          change MvPolynomial.coeff α (MvPolynomial.weightedHomogeneousComponent
            (fun _ : Fin t => (1 : ℕ)) k P) = MvPolynomial.coeff α 0
          rw [MvPolynomial.coeff_weightedHomogeneousComponent,MvPolynomial.coeff_zero]
          split_ifs with hα
          · apply hbound
            rw [HironakaRelativeNormalGraphDiagonalCoefficients.actualGraph_unitWeight_degree] at hα
            omega
          · rfl
        rw [hz]
        exact H.zero_mem
    rw [← MvPolynomial.sum_homogeneousComponent P]
    apply H.sum_mem
    intro k _
    exact hparts k
  · intro hP
    exact Ideal.mem_map_of_mem (normalPolynomialEval d t).toRingHom hP

theorem whole_homogeneous_analytic_contraction (d t : ℕ)
    (H : Ideal (MvPolynomial (Fin t) (HolGerm (ComplexModel d))))
    (hH : H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d)))) :
    let := tangentAlgebra d t
    Ideal.comap (normalPolynomialEval d t).toRingHom
      (Ideal.map (normalPolynomialEval d t).toRingHom H) = H := by
  let := tangentAlgebra d t
  ext P
  exact normalPolynomialEval_mem_analytic_map_iff d t H hH P

theorem whole_homogeneous_analytic_images_equal (d t : ℕ)
    (H K : Ideal (MvPolynomial (Fin t) (HolGerm (ComplexModel d))))
    (hH : H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))))
    (hK : K.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d)))) :
    let := tangentAlgebra d t
    Ideal.map (normalPolynomialEval d t).toRingHom H =
      Ideal.map (normalPolynomialEval d t).toRingHom K → H = K := by
  let := tangentAlgebra d t
  dsimp only
  intro he
  rw [← whole_homogeneous_analytic_contraction d t H hH,
    ← whole_homogeneous_analytic_contraction d t K hK,he]

theorem exists_original_coherent_whole_central_polynomial_kernel (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      (originalDeformationColonIdeal d t I N).IsCoherent ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t I N).mem y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, OkaRelationSheaf.HolAt g y →
        ((originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^q) ↔
          (originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^N))) ∧
      (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem y g) ↔
        (originalDeformationColonIdeal d t I N).mem y g) ∧
      ∀ P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)),
        normalPolynomialEval d t P ∈
          originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) ↔
            P ∈ originalNormalInitialIdeal d t (originalCoherentOriginIdeal I) := by
  let := tangentAlgebra d t
  obtain ⟨N,U,hU,h0,hcol,hcent,hchain,hpow,hsat,heq⟩ :=
    exists_original_coherent_whole_graph_central_ideal_equality d t I hI
  refine ⟨N,U,hU,h0,hcol,hcent,hchain,hpow,hsat,?_⟩
  intro P
  rw [heq]
  exact normalPolynomialEval_mem_analytic_map_iff d t
    (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I))
    (originalNormalInitialIdeal_homogeneous d t (originalCoherentOriginIdeal I)) P

end
end Hironaka.HironakaRelativeNormalHomogeneousAnalyticContraction
