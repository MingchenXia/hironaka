/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalMonomialBasis
import Hironaka.Analytic.HolomorphicGermPointTruncationClosure
import Mathlib.RingTheory.Ideal.Colon
set_option autoImplicit false
namespace Hironaka.HironakaSmoothSubmersionProjectionIdealColon
open HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
noncomputable section

def projectionJetCoefficients (d t q : ℕ) :
    let := tangentAlgebra d t
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)]
      (normalExponentIndex t q → HolGerm (ComplexModel d)) :=
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  (normalPowerLinearEquiv d t q).symm.toLinearMap.comp
    (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).toLinearMap

theorem projectionJetCoefficients_tangent_mul (d t q : ℕ)
    (a : HolGerm (ComplexModel d)) (g : HolGerm (ComplexModel (d+t))) :
    projectionJetCoefficients d t q (tangentPullback d t a*g) =
      a • projectionJetCoefficients d t q g := by
  let := tangentAlgebra d t
  exact (projectionJetCoefficients d t q).map_smul a g

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
theorem projectionJetCoefficients_eq_zero_iff (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    projectionJetCoefficients d t q g = 0 ↔ g ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  change (normalPowerLinearEquiv d t q).symm (Ideal.Quotient.mk (normalIdeal d t ^ q) g) = 0 ↔ _
  rw [← (normalPowerLinearEquiv d t q).symm.map_zero,
    (normalPowerLinearEquiv d t q).symm.injective.eq_iff,
    Ideal.Quotient.eq_zero_iff_mem]

theorem projectionJetCoefficients_reconstruction (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    let := normalExponentFintype t q
    g - ∑ α : normalExponentIndex t q,
      tangentPullback d t (projectionJetCoefficients d t q g α) *
        normalExponentMonomial d t α.val ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  apply Ideal.Quotient.eq.mp
  have he := (normalPowerLinearEquiv d t q).apply_symm_apply
    (Ideal.Quotient.mk (normalIdeal d t ^ q) g)
  change normalMonomialCombination d t q (projectionJetCoefficients d t q g) = _ at he
  rw [normalMonomialCombination,Fintype.linearCombination_apply] at he
  rw [map_sum]
  refine he.symm.trans ?_
  apply Finset.sum_congr rfl
  intro α _
  exact ((Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).toLinearMap.map_smul
    (projectionJetCoefficients d t q g α) (normalExponentMonomial d t α.val)).symm

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
theorem projection_extended_ideal_coefficients (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel d)))
    {g : HolGerm (ComplexModel (d+t))} (hg : g ∈ Ideal.map (tangentPullback d t).toRingHom I) :
    ∀ α, projectionJetCoefficients d t q g α ∈ I := by
  let := tangentAlgebra d t
  have hall : ∀ r : HolGerm (ComplexModel (d+t)),
      ∀ α, projectionJetCoefficients d t q (r*g) α ∈ I := by
    apply Submodule.span_induction (p := fun g _ => ∀ r, ∀ α,
      projectionJetCoefficients d t q (r*g) α ∈ I) ?_ ?_ ?_ ?_ hg
    · rintro g ⟨a,ha,rfl⟩ r α
      change projectionJetCoefficients d t q (r*tangentPullback d t a) α ∈ I
      rw [mul_comm,projectionJetCoefficients_tangent_mul]
      exact I.mul_mem_right _ ha
    · intro r α
      simp
    · intro x y _ _ hx hy r α
      rw [mul_add,map_add]
      exact I.add_mem (hx r α) (hy r α)
    · intro r x _ hx s α
      change projectionJetCoefficients d t q (s*(r*x)) α ∈ I
      rw [← mul_assoc]
      exact hx (s*r) α
  intro α
  simpa only [one_mul] using hall 1 α

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
theorem projection_extended_ideal_mod_normal_pow_iff (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (g : HolGerm (ComplexModel (d+t))) :
    g ∈ Ideal.map (tangentPullback d t).toRingHom I ⊔ normalIdeal d t ^ q ↔
      ∀ α, projectionJetCoefficients d t q g α ∈ I := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  constructor
  · intro hg
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hg
    have hzero := (projectionJetCoefficients_eq_zero_iff d t q b).mpr hb
    intro α
    rw [map_add,hzero,add_zero]
    exact projection_extended_ideal_coefficients d t q I ha α
  · intro hg
    let P := ∑ α : normalExponentIndex t q,
      tangentPullback d t (projectionJetCoefficients d t q g α) * normalExponentMonomial d t α.val
    have hP : P ∈ Ideal.map (tangentPullback d t).toRingHom I := by
      apply Ideal.sum_mem
      intro α _
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hg α))
    have hr := projectionJetCoefficients_reconstruction d t q g
    exact Submodule.mem_sup.mpr ⟨P,hP,g-P,hr,by abel⟩


theorem normalIdeal_le_actual_maximalIdeal (d t : ℕ) :
    normalIdeal d t ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) := by
  apply Ideal.span_le.mpr
  rintro g ⟨i,rfl⟩
  apply (HolGerm.mem_maximalIdeal_iff _).mpr
  simp [normalCoordinate,HironakaHolomorphicJetMonomialSpan.coordinateGerm]

theorem mem_iff_mem_all_normal_truncations (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (g : HolGerm (ComplexModel (d+t))) :
    g ∈ I ↔ ∀ q : ℕ, g ∈ I ⊔ normalIdeal d t ^ q := by
  constructor
  · intro hg q
    exact (show I ≤ I ⊔ normalIdeal d t ^ q from le_sup_left) hg
  · intro hg
    apply (HolomorphicGermPointTruncationClosure.mem_iff_mem_all_point_truncations (d+t) I g).mpr
    intro q
    exact (sup_le_sup_left (pow_le_pow_left' (normalIdeal_le_actual_maximalIdeal d t) q) I) (hg q)

theorem projection_map_colon_eq (d t : ℕ)
    (I L : Ideal (HolGerm (ComplexModel d))) :
    Ideal.map (tangentPullback d t).toRingHom (I.colon L) =
      (Ideal.map (tangentPullback d t).toRingHom I).colon
        (Ideal.map (tangentPullback d t).toRingHom L) := by
  let := tangentAlgebra d t
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change tangentPullback d t a ∈ (Ideal.map (tangentPullback d t).toRingHom I).colon
      (Ideal.map (tangentPullback d t).toRingHom L)
    apply Submodule.mem_colon.mpr
    intro b hb
    change tangentPullback d t a * b ∈ Ideal.map (tangentPullback d t).toRingHom I
    apply Submodule.span_induction (p := fun b _ =>
      tangentPullback d t a*b ∈ Ideal.map (tangentPullback d t).toRingHom I) ?_ ?_ ?_ ?_ hb
    · rintro b ⟨z,hz,rfl⟩
      change tangentPullback d t a * tangentPullback d t z ∈ _
      rw [← map_mul]
      exact Ideal.mem_map_of_mem _ (Submodule.mem_colon.mp ha z hz)
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact Ideal.add_mem _ hx hy
    · intro r x _ hx
      change tangentPullback d t a * (r*x) ∈ _
      rw [mul_left_comm]
      exact Ideal.mul_mem_left _ r hx
  · intro g hg
    apply (mem_iff_mem_all_normal_truncations d t _ g).mpr
    intro q
    apply (projection_extended_ideal_mod_normal_pow_iff d t q (I.colon L) g).mpr
    intro α
    apply Submodule.mem_colon.mpr
    intro a ha
    have hag : tangentPullback d t a*g ∈ Ideal.map (tangentPullback d t).toRingHom I := by
      have hp := Submodule.mem_colon.mp hg (tangentPullback d t a) (Ideal.mem_map_of_mem _ ha)
      simpa only [smul_eq_mul,mul_comm] using hp
    have hc := projection_extended_ideal_coefficients d t q I hag α
    rw [projectionJetCoefficients_tangent_mul] at hc
    simpa only [Pi.smul_apply,smul_eq_mul,mul_comm] using hc

end
end Hironaka.HironakaSmoothSubmersionProjectionIdealColon
