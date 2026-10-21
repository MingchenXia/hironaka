/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualMacaulayAnnihilatorConnection
import Hironaka.Resolution.HironakaActualHSZeroCentreVanishing

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualDualJetProlongation
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicPointJets
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetMonomialSpan
  HironakaActualMacaulayAnnihilatorConnection HironakaActualHSZeroCentreVanishing

/-- The actual differential prolongation is linear on the UNCHANGED original next-order multilinear jet space. -/
def actualDualJetProlongation (d t q : ℕ)
    (η : monomialIndex (d+t) q → ComplexModel d → ℂ) (c a : ComplexModel d) :
    (∀ j : Fin (q+1),MultilinearMap ℂ (fun _ : Fin j.val => ComplexModel (d+t)) ℂ) →ₗ[ℂ] ℂ where
  toFun H := ∑ row : monomialIndex (d+t) q,
    (fderiv ℂ (η row) c a*
      H ⟨row.1.val,Nat.lt_succ_of_lt row.1.isLt⟩
        (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k))+
      η row c*H ⟨row.1.val+1,Nat.succ_lt_succ row.1.isLt⟩
        (Fin.cons (tangentInclusion d t a)
          (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k))))
  map_add' H K := by
    simp only [Pi.add_apply,add_apply,mul_add,Finset.sum_add_distrib]
    ring
  map_smul' b H := by
    simp only [Pi.smul_apply,smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row _
    ring

section ActualFamily
variable (d t q : ℕ) {ι : Type*} [Fintype ι]
  {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
  (G : ι → ComplexModel (d+t) → ℂ) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
  {V : Set (ComplexModel d)} (hV : IsOpen V)
  (hVU : ∀ c ∈ V,tangentInclusion d t c ∈ U)
  (η : monomialIndex (d+t) q → ComplexModel d → ℂ)
  (hη : ∀ row,DifferentiableOn ℂ (η row) V)
  (hker : ∀ c ∈ V,∀ col,∑ row,η row c*originalMacaulayMatrix q G (tangentInclusion d t c) row col=0)
  (c a : ComplexModel d) (hc : c ∈ V) (hzero : ∀ i,G i (tangentInclusion d t c)=0)
include hV hη hker hzero

/-- The constructed functional kills EVERY genuine next-order column, including the new maximal-length words. -/
theorem actualDualJetProlongation_macaulay_column_zero
    (w : monomialIndex (d+t) (q+1)) (i : ι) :
    actualDualJetProlongation d t q η c a
      (finiteJet (q+1) (wordMonomial w*translatedGerm (tangentInclusion d t c) (G i)
        (actual_family_holomorphicAt hU G hG _ (hVU c hc) i)))=0 := by
  by_cases hw : w.1.val<q
  · let w0 : monomialIndex (d+t) q := ⟨⟨w.1.val,hw⟩,w.2⟩
    have he := actual_moving_macaulay_annihilator_connection d t hU G hG q hV hVU η hη hker
      (w0,i) c a hc
    change actualDualJetProlongation d t q η c a
      (finiteJet (q+1) (wordMonomial w0*translatedGerm (tangentInclusion d t c) (G i)
        (actual_family_holomorphicAt hU G hG _ (hVU c hc) i)))=0
    rw [wordMonomial_eq_mk,translatedGerm,← HolGerm.mk_mul]
    exact he
  · have hwq : w.1.val=q := by have h:=w.1.isLt;omega
    rw [actual_new_maxword_generator_finiteJet_zero w hwq _ _ _ (hzero i),map_zero]

/-- No higher annihilator certificate: the produced original next-order functional kills the ENTIRE SAME translated ideal. -/
theorem actualDualJetProlongation_whole_ideal_zero
    (g : HolGerm (ComplexModel (d+t)))
    (hg : g ∈ translatedIdeal G (tangentInclusion d t c)
      (actual_family_holomorphicAt hU G hG _ (hVU c hc))) :
    actualDualJetProlongation d t q η c a (finiteJet (q+1) g)=0 := by
  have hj : finiteJet (q+1) g ∈ LinearMap.range
      (macaulayMap (q+1) (fun i => translatedGerm (tangentInclusion d t c) (G i)
        (actual_family_holomorphicAt hU G hG _ (hVU c hc) i))) := by
    rw [range_macaulayMap]
    exact ⟨g,hg,rfl⟩
  obtain ⟨b,hb⟩ := hj
  rw [← hb]
  change actualDualJetProlongation d t q η c a
    (∑ col : monomialIndex (d+t) (q+1) × ι,b col •
      finiteJet (q+1) (wordMonomial col.1*translatedGerm (tangentInclusion d t c) (G col.2)
        (actual_family_holomorphicAt hU G hG _ (hVU c hc) col.2)))=0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro col _
  rw [map_smul,actualDualJetProlongation_macaulay_column_zero d t q hU G hG hV hVU η hη hker c a hc hzero,
    smul_zero]

end ActualFamily
end
end Hironaka.HironakaActualDualJetProlongation
