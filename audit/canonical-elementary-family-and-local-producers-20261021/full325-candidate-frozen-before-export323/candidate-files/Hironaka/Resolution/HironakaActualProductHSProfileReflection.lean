/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualProductMixedHS

/-! Genuine smooth products reflect finite prefixes and the entire ORIGINAL intrinsic HS profile. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaActualProductHSProfileReflection
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicPointJets HironakaActualProductMixedHS

/-- True original normal exponent degree zero identifies the WHOLE zero exponent. -/
theorem actualNormalExponentDegree_eq_zero_iff {t : ℕ} (α : Fin t →₀ ℕ) :
    normalExponentDegree α = 0 ↔ α=0 := by
  constructor
  · intro h
    apply Finsupp.ext
    intro i
    have hi : α i ≤ normalExponentDegree α :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h] at hi
    exact Nat.eq_zero_of_le_zero hi
  · rintro rfl
    simp [normalExponentDegree]

/-- The actual unique original degree-zero index in the genuine finite product convolution. -/
def actualProductZeroIndex (t ℓ : ℕ) : normalExponentIndex t (ℓ+1) :=
  ⟨0,by simp [normalExponentDegree]⟩

@[simp] theorem actualProductZeroIndex_degree (t ℓ : ℕ) :
    normalExponentDegree (actualProductZeroIndex t ℓ).val = 0 := by
  simp [actualProductZeroIndex,normalExponentDegree]

section ActualOrders
variable (d t ℓ : ℕ)
local instance : Fintype (normalExponentIndex t (ℓ+1)) := normalExponentFintype t (ℓ+1)

/-- The literal nonzero-original-monomial remainder of the actual smooth-product HS convolution. -/
def actualProductHSRemainder (I : Ideal (HolGerm (ComplexModel d))) : ℕ := by
  classical
  exact ∑ α ∈ (Finset.univ.erase (actualProductZeroIndex t ℓ)),
    hilbertSamuelValue I (ℓ-normalExponentDegree α.val)

/-- The genuine original zero monomial occurs exactly once in the true existing product HS. -/
theorem actualProductHS_zeroTerm_add_remainder (I : Ideal (HolGerm (ComplexModel d))) :
    hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I) ℓ =
      hilbertSamuelValue I ℓ + actualProductHSRemainder d t ℓ I := by
  classical
  rw [actualProductHilbertSamuel_convolution]
  unfold actualProductHSRemainder
  have h := Finset.sum_erase_add Finset.univ
    (fun α : normalExponentIndex t (ℓ+1) => hilbertSamuelValue I (ℓ-normalExponentDegree α.val))
      (Finset.mem_univ (actualProductZeroIndex t ℓ))
  simpa only [actualProductZeroIndex_degree,Nat.sub_zero,add_comm] using h.symm

/-- ALL genuine remaining product coordinates have strictly smaller ORIGINAL HS orders. -/
theorem actualProductHSRemainder_eq_of_lower_orders (I K : Ideal (HolGerm (ComplexModel d)))
    (hprefix : ∀ j < ℓ, hilbertSamuelValue I j = hilbertSamuelValue K j) :
    actualProductHSRemainder d t ℓ I = actualProductHSRemainder d t ℓ K := by
  classical
  unfold actualProductHSRemainder
  apply Finset.sum_congr rfl
  intro α hα
  have hne := (Finset.mem_erase.mp hα).1
  have hp : 0 < normalExponentDegree α.val := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hne
    apply Subtype.ext
    exact (actualNormalExponentDegree_eq_zero_iff α.val).mp hz
  exact hprefix _ (by have := α.property; omega)

/-- The first differing actual ORIGINAL order has the SAME comparison after the true smooth product. -/
theorem actualProductHS_comparison_of_lower_orders (I K : Ideal (HolGerm (ComplexModel d)))
    (hprefix : ∀ j < ℓ, hilbertSamuelValue I j = hilbertSamuelValue K j) :
    (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I) ℓ ≤
        hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom K) ℓ ↔
          hilbertSamuelValue I ℓ ≤ hilbertSamuelValue K ℓ) ∧
    (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I) ℓ <
        hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom K) ℓ ↔
          hilbertSamuelValue I ℓ < hilbertSamuelValue K ℓ) ∧
    (hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I) ℓ =
        hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom K) ℓ ↔
          hilbertSamuelValue I ℓ = hilbertSamuelValue K ℓ) := by
  rw [actualProductHS_zeroTerm_add_remainder,actualProductHS_zeroTerm_add_remainder,
    actualProductHSRemainder_eq_of_lower_orders d t ℓ I K hprefix]
  omega
end ActualOrders

/-- EVERY original finite HS prefix is faithfully reflected by the genuine original smooth product. -/
theorem actualProductHS_prefix_eq_iff (d t N : ℕ) (I K : Ideal (HolGerm (ComplexModel d))) :
    (∀ ℓ < N, hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I) ℓ =
      hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom K) ℓ) ↔
        ∀ ℓ < N, hilbertSamuelValue I ℓ = hilbertSamuelValue K ℓ := by
  constructor
  · intro h
    have he : ∀ ℓ, ℓ<N → hilbertSamuelValue I ℓ = hilbertSamuelValue K ℓ := by
      intro ℓ
      induction ℓ using Nat.strong_induction_on with
      | h ℓ ih =>
        intro hℓ
        exact ((actualProductHS_comparison_of_lower_orders d t ℓ I K
          (fun j hj => ih j hj (hj.trans hℓ))).2.2).mp (h ℓ hℓ)
    exact he
  · intro h ℓ hℓ
    rw [actualProductHilbertSamuel_convolution,actualProductHilbertSamuel_convolution]
    apply Finset.sum_congr rfl
    intro α _
    exact h _ (by omega)

/-- Equality of the ENTIRE existing product HS is equivalent to equality of the ENTIRE ORIGINAL profile. -/
theorem actualProductHS_entire_profile_eq_iff (d t : ℕ) (I K : Ideal (HolGerm (ComplexModel d))) :
    (∀ ℓ, hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I) ℓ =
      hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom K) ℓ) ↔
        ∀ ℓ, hilbertSamuelValue I ℓ = hilbertSamuelValue K ℓ := by
  constructor
  · intro h ℓ
    exact ((actualProductHS_prefix_eq_iff d t (ℓ+1) I K).mp (fun j _ => h j)) ℓ (Nat.lt_succ_self ℓ)
  · intro h ℓ
    exact ((actualProductHS_prefix_eq_iff d t (ℓ+1) I K).mpr (fun j _ => h j)) ℓ (Nat.lt_succ_self ℓ)
end
end Hironaka.HironakaActualProductHSProfileReflection
