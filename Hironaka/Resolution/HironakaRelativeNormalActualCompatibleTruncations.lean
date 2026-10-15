/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalActualPowerLifts
import Mathlib.LinearAlgebra.Isomorphisms

/-! One genuine whole power representative map gives every original normal
truncation, retaining the entire actual normal filtration. -/
set_option autoImplicit false

namespace Hironaka.HironakaRelativeNormalActualCompatibleTruncations
noncomputable section
open HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalActualPowerLifts
open scoped DirectSum

variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]
variable (I J : Ideal R) [∀ q, Module.Free B (idealPowerLayer B I J q)]

/-- The single whole map sums the true original power lifts, before any quotient. -/
def actualWholePowerLift : (⨁ q : ℕ, idealPowerLayer B I J q) →ₗ[B] R :=
  DirectSum.toModule B ℕ R (fun q =>
    (powerModule B J q).subtype.comp (actualFreeLayerPowerLift (B := B) I J q))

/-- Every truncation uses the SAME original whole representative map. -/
def actualNormalTruncationMap (s : ℕ) :
    (⨁ q : ℕ, idealPowerLayer B I J q) →ₗ[B] R ⧸ (I ⊔ J ^ s) :=
  (Ideal.Quotient.mkₐ B (I ⊔ J ^ s)).toLinearMap.comp (actualWholePowerLift (B := B) I J)

@[simp] theorem actualWholePowerLift_lof (q : ℕ) (x : idealPowerLayer B I J q) :
    actualWholePowerLift (B := B) I J (DirectSum.lof B ℕ (layerFamily B I J) q x) =
      (actualFreeLayerPowerLift (B := B) I J q x).val := by
  simp [actualWholePowerLift]

@[simp] theorem actualNormalTruncationMap_lof (s q : ℕ) (x : idealPowerLayer B I J q) :
    actualNormalTruncationMap (B := B) I J s (DirectSum.lof B ℕ (layerFamily B I J) q x) =
      Ideal.Quotient.mk (I ⊔ J ^ s) (actualFreeLayerPowerLift (B := B) I J q x).val := by
  simp [actualNormalTruncationMap]

/-- A true original high-degree vector has its whole representative in the same power. -/
theorem actualWholePowerLift_mem_power (r : ℕ)
    (v : ⨁ q : ℕ, idealPowerLayer B I J q) (hv : ∀ q < r, v q = 0) :
    actualWholePowerLift (B := B) I J v ∈ J ^ r := by
  classical
  rw [← DirectSum.sum_support_of v, map_sum]
  apply Ideal.sum_mem
  intro q hq
  by_cases hqr : q < r
  · rw [hv q hqr]
    simp
  · have hm := (actualFreeLayerPowerLift (B := B) I J q (v q)).property
    change actualWholePowerLift (B := B) I J
      (DirectSum.lof B ℕ (layerFamily B I J) q (v q)) ∈ J ^ r
    rw [actualWholePowerLift_lof]
    exact (Ideal.pow_le_pow_right (Nat.le_of_not_gt hqr)) hm

/-- Every actual power numerator is reached from its genuine graded tail. -/
theorem actualNormalTruncationMap_power_preimage (r n : ℕ) (g : R) (hg : g ∈ J ^ r) :
    ∃ v : ⨁ q : ℕ, idealPowerLayer B I J q,
      (∀ q < r, v q = 0) ∧
      actualNormalTruncationMap (B := B) I J (r+n) v = Ideal.Quotient.mk (I ⊔ J ^ (r+n)) g := by
  induction n generalizing r g with
  | zero =>
    refine ⟨0,fun q hq => rfl,?_⟩
    simpa only [Nat.add_zero, map_zero] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right hg)).symm
  | succ n ih =>
    let x := idealPowerLayerMap B I J r ⟨g,hg⟩
    let a := (actualFreeLayerPowerLift (B := B) I J r x).val
    have ha : g-a ∈ I ⊔ J ^ (r+1) := by
      apply Ideal.Quotient.eq.mp
      exact (actualFreeLayerPowerLift_class (B := B) I J r x).symm
    obtain ⟨i,hi,z,hz,hiz⟩ := Submodule.mem_sup.mp ha
    obtain ⟨v,hv,he⟩ := ih (r+1) z hz
    have horder : (r+1)+n = r+(n+1) := by omega
    refine ⟨DirectSum.lof B ℕ (layerFamily B I J) r x + v,?_,?_⟩
    · intro q hq
      rw [DFinsupp.add_apply, hv q (by omega)]
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne (β := layerFamily B I J) r q x (Nat.ne_of_lt hq), add_zero]
    · rw [map_add, actualNormalTruncationMap_lof, ← horder, he]
      rw [← map_add]
      apply Ideal.Quotient.eq.mpr
      have hsub : a+z-g = -i := by linear_combination hiz
      rw [hsub]
      exact Ideal.mem_sup_left (I.neg_mem hi)

/-- All true original quotient classes are reached by the one whole map. -/
theorem actualNormalTruncationMap_surjective (s : ℕ) :
    Function.Surjective (actualNormalTruncationMap (B := B) I J s) := by
  intro z
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨v,hv,he⟩ := actualNormalTruncationMap_power_preimage (B := B) I J 0 s g (by simp)
  rw [Nat.zero_add] at he
  exact ⟨v,he⟩

/-- The WHOLE kernel contains exactly the actual high-degree tail, without a splitting premise. -/
theorem actualNormalTruncationMap_eq_zero_iff (s : ℕ)
    (v : ⨁ q : ℕ, idealPowerLayer B I J q) :
    actualNormalTruncationMap (B := B) I J s v = 0 ↔ ∀ q < s, v q = 0 := by
  constructor
  · intro hzero
    have hwhole : actualWholePowerLift (B := B) I J v ∈ I ⊔ J ^ s :=
      Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hcoeff : ∀ q, q < s → v q = 0 := by
      intro q
      induction q using Nat.strong_induction_on with
      | h q ih =>
        intro hqs
        let w := v - DirectSum.lof B ℕ (layerFamily B I J) q (v q)
        have hw : ∀ j < q+1, w j = 0 := by
          intro j hj
          by_cases hje : j=q
          · subst j
            simp [w,DirectSum.sub_apply,DirectSum.lof_apply]
          · have hjq : j < q := by omega
            simp only [w,DirectSum.sub_apply, ih j hjq (by omega), DirectSum.lof_eq_of,
              DirectSum.of_eq_of_ne (β := layerFamily B I J) q j (v q) hje, sub_self]
        have hwm := actualWholePowerLift_mem_power (B := B) I J (q+1) w hw
        have hvsmall : actualWholePowerLift (B := B) I J v ∈ I ⊔ J ^ (q+1) :=
          (sup_le_sup_left (Ideal.pow_le_pow_right (by omega : q+1 ≤ s)) I) hwhole
        have hlift : (actualFreeLayerPowerLift (B := B) I J q (v q)).val ∈ I ⊔ J ^ (q+1) := by
          have hid : (actualFreeLayerPowerLift (B := B) I J q (v q)).val =
              actualWholePowerLift (B := B) I J v - actualWholePowerLift (B := B) I J w := by
            simp [w,map_sub,actualWholePowerLift_lof]
          rw [hid]
          exact (I ⊔ J ^ (q+1)).sub_mem hvsmall (Ideal.mem_sup_right hwm)
        apply Subtype.ext
        change (v q).val = 0
        rw [← actualFreeLayerPowerLift_class (B := B) I J q (v q)]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hlift
    exact hcoeff
  · intro hv
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_sup_right (actualWholePowerLift_mem_power (B := B) I J s v hv)

/-- The literal whole original direct-sum tail, defined by its actual coordinates. -/
def actualNormalTail (r : ℕ) : Submodule B (⨁ q : ℕ, idealPowerLayer B I J q) where
  carrier := {v | ∀ q < r, v q = 0}
  zero_mem' := by intro q hq; rfl
  add_mem' := by intro v w hv hw q hq; simp only [DirectSum.add_apply,hv q hq,hw q hq,add_zero]
  smul_mem' := by intro b v hv q hq; simp only [DirectSum.smul_apply,hv q hq,smul_zero]

/-- The true original normal-power image inside the actual whole truncation. -/
def actualNormalPowerImage (s r : ℕ) : Submodule B (R ⧸ (I ⊔ J ^ s)) :=
  (powerModule B J r).map (Ideal.Quotient.mkₐ B (I ⊔ J ^ s)).toLinearMap

/-- Every truncation, including orders smaller than the original power, has a true tail preimage. -/
theorem actualNormalTruncationMap_power_preimage_any (r s : ℕ) (g : R) (hg : g ∈ J ^ r) :
    ∃ v : ⨁ q : ℕ, idealPowerLayer B I J q,
      v ∈ actualNormalTail (B := B) I J r ∧
      actualNormalTruncationMap (B := B) I J s v = Ideal.Quotient.mk (I ⊔ J ^ s) g := by
  by_cases hrs : r ≤ s
  · have heq : r+(s-r)=s := Nat.add_sub_of_le hrs
    obtain ⟨v,hv,he⟩ := actualNormalTruncationMap_power_preimage (B := B) I J r (s-r) g hg
    rw [heq] at he
    exact ⟨v,hv,he⟩
  · refine ⟨0,?_,?_⟩
    · intro q hq; rfl
    · rw [map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right ((Ideal.pow_le_pow_right (by omega : s ≤ r)) hg))).symm

/-- The whole map preserves EVERY actual normal-filtration level. -/
theorem actualNormalTruncationMap_tail_image (s r : ℕ) :
    (actualNormalTail (B := B) I J r).map (actualNormalTruncationMap (B := B) I J s) =
      actualNormalPowerImage (B := B) I J s r := by
  apply le_antisymm
  · rintro z ⟨v,hv,rfl⟩
    exact ⟨actualWholePowerLift (B := B) I J v,actualWholePowerLift_mem_power (B := B) I J r v hv,rfl⟩
  · rintro z ⟨g,hg,rfl⟩
    obtain ⟨v,hv,he⟩ := actualNormalTruncationMap_power_preimage_any (B := B) I J r s g hg
    exact ⟨v,hv,he⟩

/-- The actual comparison quotient retains each ORIGINAL numerator. -/
def actualNormalTruncationComparison (s t : ℕ) (hst : s ≤ t) :
    R ⧸ (I ⊔ J ^ t) →ₐ[B] R ⧸ (I ⊔ J ^ s) :=
  Ideal.quotientMapₐ (I ⊔ J ^ s) (AlgHom.id B R)
    (by intro g hg; exact (sup_le_sup_left (Ideal.pow_le_pow_right hst) I) hg)

/-- Every pair of original truncations is compatible with the SAME whole map. -/
theorem actualNormalTruncationMap_comparison (s t : ℕ) (hst : s ≤ t) :
    (actualNormalTruncationComparison (B := B) I J s t hst).toLinearMap.comp
      (actualNormalTruncationMap (B := B) I J t) = actualNormalTruncationMap (B := B) I J s := by
  ext v
  rfl

/-- The complete actual kernel is precisely the same original degree tail. -/
theorem actualNormalTruncationMap_ker (s : ℕ) :
    LinearMap.ker (actualNormalTruncationMap (B := B) I J s) = actualNormalTail (B := B) I J s := by
  ext v
  exact actualNormalTruncationMap_eq_zero_iff (B := B) I J s v

-- Expose the genuine module quotient instance at this dependent direct-sum type.
local instance actualNormalDirectSumHasQuotient :
    HasQuotient (⨁ q : ℕ, idealPowerLayer B I J q)
      (Submodule B (⨁ q : ℕ, idealPowerLayer B I J q)) :=
  @Submodule.hasQuotient B (⨁ q : ℕ, idealPowerLayer B I J q) _ _ _

/-- The genuine quotient of the WHOLE original direct sum is the actual normal truncation. -/
def actualNormalTruncationQuotientEquiv (s : ℕ) :
    ((⨁ q : ℕ, idealPowerLayer B I J q) ⧸ actualNormalTail (B := B) I J s) ≃ₗ[B]
      R ⧸ (I ⊔ J ^ s) :=
  (Submodule.quotEquivOfEq _ _ (actualNormalTruncationMap_ker (B := B) I J s).symm).trans
    ((actualNormalTruncationMap (B := B) I J s).quotKerEquivOfSurjective
      (actualNormalTruncationMap_surjective (B := B) I J s))

/-- The quotient equivalence sends EVERY actual vector to its same original numerator class. -/
theorem actualNormalTruncationQuotientEquiv_mk (s : ℕ)
    (v : ⨁ q : ℕ, idealPowerLayer B I J q) :
    actualNormalTruncationQuotientEquiv (B := B) I J s (Submodule.Quotient.mk v) =
      actualNormalTruncationMap (B := B) I J s v := by
  simp only [actualNormalTruncationQuotientEquiv,LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk]

end

open Hironaka.HolomorphicIdealSheaves HolGerm Set Filter
  HironakaRelativeNormalGradedAlgebra
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalNearbyUniformRanks HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalCoherentTranslatedJets
open scoped Topology Manifold ContDiff

/-- ONLY original coherence constructs the entire compatible filtration on the SAME nearby open. -/
theorem exists_original_nearby_all_compatible_normal_truncations (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U,
        let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
        ∃ hfree : ∀ q, Module.Free (HolGerm (ComplexModel d))
          (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q),
          (∀ q, Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) ∧
            Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) = r q) ∧
          letI := hfree
          ∀ s : ℕ,
            Function.Surjective (actualNormalTruncationMap (B := HolGerm (ComplexModel d))
              Ia (normalIdeal d t) s) ∧
            LinearMap.ker (actualNormalTruncationMap (B := HolGerm (ComplexModel d))
              Ia (normalIdeal d t) s) = actualNormalTail (B := HolGerm (ComplexModel d))
                Ia (normalIdeal d t) s ∧
            (∀ j, (actualNormalTail (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) j).map
              (actualNormalTruncationMap (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) s) =
                actualNormalPowerImage (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) s j) ∧
            (∀ k (hsk : s ≤ k),
              (actualNormalTruncationComparison (B := HolGerm (ComplexModel d))
                Ia (normalIdeal d t) s k hsk).toLinearMap.comp
                  (actualNormalTruncationMap (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) k) =
                    actualNormalTruncationMap (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) s) := by
  let := tangentAlgebra d t
  obtain ⟨U,r,hU,hmeet,hdegree⟩ := exists_original_nearby_all_degree_uniform_rank_open d t I hI
  refine ⟨U,r,hU,hmeet,?_⟩
  intro a ha
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
  let hfree : ∀ q, Module.Free (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q) :=
    fun q => (hdegree a ha q).1
  refine ⟨hfree,fun q => (hdegree a ha q).2,?_⟩
  let := hfree
  intro s
  exact ⟨actualNormalTruncationMap_surjective (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) s,
    actualNormalTruncationMap_ker (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) s,
    fun j => actualNormalTruncationMap_tail_image (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) s j,
    fun k hsk => actualNormalTruncationMap_comparison (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t) s k hsk⟩

end Hironaka.HironakaRelativeNormalActualCompatibleTruncations
