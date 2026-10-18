/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualTangentJetConnection

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualMacaulayAnnihilatorConnection
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicPointJets
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetMonomialSpan
  HironakaActualTangentJetConnection

/-- Every actual column annihilator annihilates finite jets of the ENTIRE SAME original translated ideal. -/
theorem actual_macaulay_annihilator_whole_ideal (n q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z)
    (η : monomialIndex n q → ℂ)
    (hη : ∀ col, ∑ row, η row*originalMacaulayMatrix q G p row col=0)
    (g : HolGerm (ComplexModel n)) (hg : g ∈ translatedIdeal G p hG) :
    ∑ row, η row*finiteCoordinateArray q (finiteJet q g) row=0 := by
  have hj : finiteJet q g ∈ LinearMap.range
      (macaulayMap q (fun i => translatedGerm p (G i) (hG i))) := by
    rw [range_macaulayMap]
    exact ⟨g,hg,rfl⟩
  obtain ⟨b,hb⟩ := hj
  have he : finiteCoordinateArray q (finiteJet q g)=originalMacaulayLinearMap q G p b := by
    rw [originalMacaulayLinearMap_eq q G p hG,LinearMap.comp_apply]
    exact (congrArg (finiteCoordinateArray q) hb).symm
  rw [he]
  calc
    _ = ∑ col, b col*(∑ row, η row*originalMacaulayMatrix q G p row col) := by
      change (∑ row, η row*(∑ col, b col •
        (fun r => originalMacaulayMatrix q G p r col)) row)=_
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro col _
      apply Finset.sum_congr rfl
      intro row _
      ring
    _ = 0 := by simp only [hη,mul_zero,Finset.sum_const_zero]

/-- The TRUE derivative of the SAME word multiplier gives a germ in the SAME original ideal and is killed. -/
theorem actual_macaulay_annihilator_correction_zero (d t : ℕ) {ι : Type*} [Fintype ι]
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    (G : ι → ComplexModel (d+t) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U) (q : ℕ)
    (col : monomialIndex (d+t) q × ι) (c a : ComplexModel d)
    (hc : tangentInclusion d t c ∈ U) (η : monomialIndex (d+t) q → ℂ)
    (hη : ∀ col, ∑ row, η row*originalMacaulayMatrix q G (tangentInclusion d t c) row col=0) :
    ∑ row : monomialIndex (d+t) q, η row*
      iteratedFDeriv ℂ row.1.val
        (fun z => fderiv ℂ (wordFunction col.1) z (tangentInclusion d t a)*
          G col.2 (z+tangentInclusion d t c)) 0
        (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k))=0 := by
  have hGp (i : ι) : ∀ᶠ z in 𝓝 (tangentInclusion d t c), DifferentiableAt ℂ (G i) z := by
    filter_upwards [hU.mem_nhds hc] with z hz
    exact (hG i).differentiableAt (hU.mem_nhds hz)
  have hφ : Differentiable ℂ (fun z : ComplexModel (d+t) =>
      fderiv ℂ (wordFunction col.1) z (tangentInclusion d t a)) := by
    simp only [actual_wordFunction_fderiv]
    fun_prop
  let H : HolGerm (ComplexModel (d+t)) := HolGerm.mk
    (fun z => fderiv ℂ (wordFunction col.1) z (tangentInclusion d t a)) (Eventually.of_forall hφ)
  have hmem : H*translatedGerm (tangentInclusion d t c) (G col.2) (hGp col.2) ∈
      translatedIdeal G (tangentInclusion d t c) hGp :=
    Ideal.mul_mem_left _ H (Ideal.subset_span ⟨col.2,rfl⟩)
  have hz := actual_macaulay_annihilator_whole_ideal (d+t) q G (tangentInclusion d t c)
    hGp η hη _ hmem
  convert hz using 1
  apply Finset.sum_congr rfl
  intro row _
  apply congrArg (fun x : ℂ => η row*x)
  dsimp only [H,translatedGerm]
  rw [← HolGerm.mk_mul]
  rfl

/-- Differentiating the actual moving whole-column annihilator kills the TRUE word correction and gives the successor relation. -/
theorem actual_moving_macaulay_annihilator_connection (d t : ℕ) {ι : Type*} [Fintype ι]
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    (G : ι → ComplexModel (d+t) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U) (q : ℕ)
    {V : Set (ComplexModel d)} (hV : IsOpen V)
    (hVU : ∀ c ∈ V,tangentInclusion d t c ∈ U)
    (η : monomialIndex (d+t) q → ComplexModel d → ℂ)
    (hη : ∀ row,DifferentiableOn ℂ (η row) V)
    (hker : ∀ c ∈ V,∀ col,∑ row,η row c*originalMacaulayMatrix q G (tangentInclusion d t c) row col=0)
    (col : monomialIndex (d+t) q × ι) (c a : ComplexModel d) (hc : c ∈ V) :
    ∑ row : monomialIndex (d+t) q,
      (fderiv ℂ (η row) c a*originalMacaulayMatrix q G (tangentInclusion d t c) row col+
        η row c*iteratedFDeriv ℂ (row.1.val+1)
          (fun z => wordFunction col.1 z*G col.2 (z+tangentInclusion d t c)) 0
          (Fin.cons (tangentInclusion d t a)
            (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k))))=0 := by
  have hM (row : monomialIndex (d+t) q) : DifferentiableAt ℂ
      (fun b : ComplexModel d => originalMacaulayMatrix q G (tangentInclusion d t b) row col) c :=
    ((differentiableOn_originalMacaulayMatrix_entry q G hU hG row col).differentiableAt
      (hU.mem_nhds (hVU c hc))).comp c (tangentInclusion d t).differentiableAt
  have hηAt (row : monomialIndex (d+t) q) : DifferentiableAt ℂ (η row) c :=
    (hη row).differentiableAt (hV.mem_nhds hc)
  have hs := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (monomialIndex (d+t) q)))
    (fun row _ => (hηAt row).hasFDerivAt.mul (hM row).hasFDerivAt)
  have hz : (fun b : ComplexModel d => ∑ row,η row b*
      originalMacaulayMatrix q G (tangentInclusion d t b) row col) =ᶠ[𝓝 c]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hV.mem_nhds hc] with b hb
    exact hker b hb col
  have he := congrArg (fun L : ComplexModel d →L[ℂ] ℂ => L a) hs.fderiv
  change fderiv ℂ (fun b : ComplexModel d => ∑ row,η row b*
    originalMacaulayMatrix q G (tangentInclusion d t b) row col) c a=_ at he
  rw [hz.fderiv_eq,fderiv_const_apply] at he
  have he0 : 0=∑ row : monomialIndex (d+t) q,
      (η row c*fderiv ℂ (fun b : ComplexModel d =>
        originalMacaulayMatrix q G (tangentInclusion d t b) row col) c a+
        originalMacaulayMatrix q G (tangentInclusion d t c) row col*fderiv ℂ (η row) c a) := by
    simpa [smul_eq_mul] using he
  let A (row : monomialIndex (d+t) q) := iteratedFDeriv ℂ (row.1.val+1)
    (fun z => wordFunction col.1 z*G col.2 (z+tangentInclusion d t c)) 0
    (Fin.cons (tangentInclusion d t a)
      (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k)))
  let B (row : monomialIndex (d+t) q) := iteratedFDeriv ℂ row.1.val
    (fun z => fderiv ℂ (wordFunction col.1) z (tangentInclusion d t a)*
      G col.2 (z+tangentInclusion d t c)) 0
    (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k))
  have hcon (row : monomialIndex (d+t) q) : fderiv ℂ (fun b : ComplexModel d =>
      originalMacaulayMatrix q G (tangentInclusion d t b) row col) c a=A row-B row :=
    actual_original_macaulay_tangent_fderiv d t hU G hG q row col c a (hVU c hc)
  have he1 : 0=∑ row : monomialIndex (d+t) q,
      (η row c*(A row-B row)+
        originalMacaulayMatrix q G (tangentInclusion d t c) row col*fderiv ℂ (η row) c a) := by
    simpa only [hcon] using he0
  have hcorr : ∑ row : monomialIndex (d+t) q,η row c*B row=0 :=
    actual_macaulay_annihilator_correction_zero d t hU G hG q col c a (hVU c hc)
      (fun row => η row c) (hker c hc)
  have hsplit : (∑ row : monomialIndex (d+t) q,
      (η row c*(A row-B row)+
        originalMacaulayMatrix q G (tangentInclusion d t c) row col*fderiv ℂ (η row) c a))=
      (∑ row : monomialIndex (d+t) q,
        (fderiv ℂ (η row) c a*originalMacaulayMatrix q G (tangentInclusion d t c) row col+
          η row c*A row))-(∑ row : monomialIndex (d+t) q,η row c*B row) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro row _
    ring
  rw [hsplit,hcorr,sub_zero] at he1
  exact he1.symm

end
end Hironaka.HironakaActualMacaulayAnnihilatorConnection
