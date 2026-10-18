/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCoefficientPresentationCentrePower
import Mathlib.RingTheory.MvPowerSeries.Rename

/-! Actual coordinate-local germ algebra maps are determined on the ENTIRE original ring.
This gives genuine tangent Taylor naturality, before the relative coefficient dictionary. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTaylorCoordinateNaturality
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
  HironakaHolomorphicJetChartInvariance

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- The true original Hadamard decomposition forces the WHOLE maximal-ideal image. -/
theorem map_actualGerm_maximalIdeal_le_formal_coordinates {d m : ℕ}
    (f : HolGerm (ComplexModel d) →ₐ[ℂ] MvPowerSeries (Fin m) ℂ)
    (hf : ∀ i : Fin d, f (coordinateGerm i) ∈ actualFormalCoordinateIdeal m univ) :
    Ideal.map f.toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) ≤
      actualFormalCoordinateIdeal m univ := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro g hg
  obtain ⟨H,he⟩ := exists_coordinate_decomposition g
  have hz := (HolGerm.mem_maximalIdeal_iff g).mp hg
  rw [hz,map_zero,zero_add] at he
  change f g ∈ actualFormalCoordinateIdeal m univ
  rw [he,map_sum]
  apply Ideal.sum_mem
  intro i _
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (hf i)

/-- Genuine entire maximal powers annihilate EVERY actual lower formal coefficient. -/
theorem actualGermAlgHom_coefficient_zero_of_mem_maximal_pow {d m : ℕ}
    (f : HolGerm (ComplexModel d) →ₐ[ℂ] MvPowerSeries (Fin m) ℂ)
    (hf : ∀ i : Fin d, f (coordinateGerm i) ∈ actualFormalCoordinateIdeal m univ)
    (q : ℕ) (g : HolGerm (ComplexModel d))
    (hg : g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ q)
    (a : Fin m →₀ ℕ) (ha : normalExponentDegree a < q) : MvPowerSeries.coeff a (f g)=0 := by
  have himage := Ideal.mem_map_of_mem f.toRingHom hg
  rw [Ideal.map_pow] at himage
  have hpower : f g ∈ actualFormalCoordinateIdeal m univ ^ q :=
    (pow_le_pow_left' (map_actualGerm_maximalIdeal_le_formal_coordinates f hf) q) himage
  apply (mem_actualFormalCoordinateIdeal_pow_iff univ q (f g)).mp hpower a
  have hw : Finsupp.weight (actualCoordinateWeight (univ : Set (Fin m))) a=normalExponentDegree a := by
    rw [Finsupp.weight_eq_sum]
    simp [actualCoordinateWeight,normalExponentDegree,smul_eq_mul]
  rwa [hw]

/-- Actual coordinate identities and locality determine the ENTIRE original germ algebra map. -/
theorem actualGermAlgHom_eq_of_coordinate_images {d m : ℕ}
    (f h : HolGerm (ComplexModel d) →ₐ[ℂ] MvPowerSeries (Fin m) ℂ)
    (hcoord : ∀ i : Fin d, f (coordinateGerm i)=h (coordinateGerm i))
    (hf : ∀ i : Fin d, f (coordinateGerm i) ∈ actualFormalCoordinateIdeal m univ) : f=h := by
  have hh : ∀ i : Fin d, h (coordinateGerm i) ∈ actualFormalCoordinateIdeal m univ := by
    intro i
    rw [← hcoord i]
    exact hf i
  have hspan (q : ℕ) (p : HolGerm (ComplexModel d)) (hp : p ∈ monomialSpan d q) : f p=h p := by
    apply Submodule.span_induction (p := fun p _ => f p=h p) ?_ ?_ ?_ ?_ hp
    · rintro p ⟨w,rfl⟩
      simp only [wordMonomial,map_prod]
      exact Finset.prod_congr rfl fun i _ => hcoord (w.2 i)
    · simp
    · intro p r _ _ hp hr
      rw [map_add,map_add,hp,hr]
    · intro c p _ hp
      rw [map_smul,map_smul,hp]
  apply AlgHom.ext
  intro g
  apply MvPowerSeries.ext
  intro a
  let q := normalExponentDegree a+1
  obtain ⟨p,hp,hrem⟩ := exists_monomial_representative q g
  have hfa := actualGermAlgHom_coefficient_zero_of_mem_maximal_pow f hf q (g-p) hrem a (by dsimp [q];omega)
  have hha := actualGermAlgHom_coefficient_zero_of_mem_maximal_pow h hh q (g-p) hrem a (by dsimp [q];omega)
  rw [map_sub,map_sub,sub_eq_zero] at hfa hha
  exact hfa.trans ((congrArg (MvPowerSeries.coeff a) (hspan q p hp)).trans hha.symm)

/-- The actual tangential coordinate pullback has the SAME literal ambient original coordinate. -/
theorem tangentPullback_coordinateGerm (d t : ℕ) (i : Fin d) :
    tangentPullback d t (coordinateGerm i)=coordinateGerm (i.castAdd t) := by
  unfold tangentPullback coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => rfl

/-- Genuine original Taylor expansion commutes with the ACTUAL independently defined tangent inclusion. -/
theorem actualUnshiftedTaylor_tangentPullback (d t : ℕ) :
    (actualUnshiftedTaylorAlgHom (d+t)).comp (tangentPullback d t)=
      (MvPowerSeries.rename (Fin.castAdd t)).comp (actualUnshiftedTaylorAlgHom d) := by
  apply actualGermAlgHom_eq_of_coordinate_images
  · intro i
    change actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t (coordinateGerm i))=
      MvPowerSeries.rename (Fin.castAdd t) (actualUnshiftedTaylorAlgHom d (coordinateGerm i))
    rw [tangentPullback_coordinateGerm,actualUnshiftedTaylor_coordinate,
      actualUnshiftedTaylor_coordinate,MvPowerSeries.rename_X]
  · intro i
    change actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t (coordinateGerm i)) ∈ _
    rw [tangentPullback_coordinateGerm,actualUnshiftedTaylor_coordinate]
    exact Ideal.subset_span ⟨i.castAdd t,mem_univ _,rfl⟩

end
end Hironaka.HironakaActualTaylorCoordinateNaturality
