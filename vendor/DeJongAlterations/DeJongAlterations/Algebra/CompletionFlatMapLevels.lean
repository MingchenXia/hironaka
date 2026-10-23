import DeJongAlterations.Algebra.CompletionLocalMap
import Mathlib.RingTheory.TensorProduct.Basic

/-! Actual finite-level tensor comparison for an original local homomorphism. -/

noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace DeJongAlterations.Algebra.CompletionFlatMap

open CompletionRegularityBasics CompletionLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- The original completed-base tensor ring. -/
abbrev TensorRing := Completion A ⊗[A] B

/-- The actual original target maximal ideal extended to the actual tensor ring. -/
def tensorIdeal : Ideal (TensorRing A B) :=
  (maximalIdeal B).map Algebra.TensorProduct.includeRight.toRingHom

/-- The actual finite-level map on completed coefficients. -/
def levelCoefficient (n : ℕ) : Completion A →ₐ[A] B ⧸ maximalIdeal B ^ n where
  toRingHom := completionMapLevel (algebraMap A B) n
  commutes' a := by
    change completionMapLevel (algebraMap A B) n (AdicCompletion.of (maximalIdeal A) A a) =
      Ideal.Quotient.mk _ (algebraMap A B a)
    simp [completionMapLevel]

/-- The actual tensor map to the original finite target quotient. -/
def tensorLevelMap (n : ℕ) : TensorRing A B →ₐ[A] B ⧸ maximalIdeal B ^ n :=
  Algebra.TensorProduct.lift (levelCoefficient A B n) (Ideal.Quotient.mkₐ A _)
    (fun _ _ ↦ Commute.all _ _)

/-- Literal values on the actual tensor generators. -/
theorem tensorLevelMap_tmul (n : ℕ) (x : Completion A) (b : B) :
    tensorLevelMap A B n (x ⊗ₜ[A] b) =
      levelCoefficient A B n x * Ideal.Quotient.mk _ b := by
  simp [tensorLevelMap]

/-- The actual tensor map kills the entire original target maximal-ideal power. -/
theorem tensorIdeal_pow_le_ker (n : ℕ) :
    tensorIdeal A B ^ n ≤ RingHom.ker (tensorLevelMap A B n).toRingHom := by
  rw [tensorIdeal, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro b hb
  change tensorLevelMap A B n (1 ⊗ₜ[A] b) = 0
  rw [tensorLevelMap_tmul, map_one, one_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hb

/-- The actual forward map on full original finite-level tensor quotients. -/
def levelForward (n : ℕ) :
    TensorRing A B ⧸ tensorIdeal A B ^ n →+* B ⧸ maximalIdeal B ^ n :=
  Ideal.Quotient.lift _ (tensorLevelMap A B n).toRingHom (tensorIdeal_pow_le_ker A B n)

/-- The inverse candidate is the literal original target inclusion on quotient classes. -/
def levelBackward (n : ℕ) :
    B ⧸ maximalIdeal B ^ n →+* TensorRing A B ⧸ tensorIdeal A B ^ n :=
  Ideal.quotientMap _ Algebra.TensorProduct.includeRight.toRingHom (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact le_rfl)

/-- Original target classes are retained literally by the forward comparison. -/
theorem levelForward_right (n : ℕ) (b : B) :
    levelForward A B n (Ideal.Quotient.mk _ (1 ⊗ₜ[A] b)) = Ideal.Quotient.mk _ b := by
  change tensorLevelMap A B n (1 ⊗ₜ[A] b) = _
  rw [tensorLevelMap_tmul, map_one, one_mul]

/-- The inverse candidate is actually a right inverse, on every original target quotient. -/
theorem levelForward_levelBackward (n : ℕ) (b : B ⧸ maximalIdeal B ^ n) :
    levelForward A B n (levelBackward A B n b) = b := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact levelForward_right A B n b

variable [IsNoetherianRing A]

/-- Every actual completed coefficient has an original representative modulo each
full original extended maximal-ideal power. -/
theorem exists_original_congr (n : ℕ) (x : Completion A) :
    ∃ a : A, x - algebraMap A (Completion A) a ∈
      (maximalIdeal A ^ n).map (algebraMap A (Completion A)) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  refine ⟨a, ?_⟩
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map]
  simpa [AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal A).fg_of_isNoetherianRing,
    AdicCompletion.eval, sub_eq_zero, AdicCompletion.algebraMap_apply,
    AdicCompletion.of_apply] using ha.symm

omit [IsNoetherianRing A] in
/-- Locality of the original map gives actual containment of the original base powers
inside the extended target powers in the actual tensor ring. -/
theorem basePower_le_tensorPower (n : ℕ) :
    ((maximalIdeal A ^ n).map (algebraMap A (Completion A))).map
      (algebraMap (Completion A) (TensorRing A B)) ≤ tensorIdeal A B ^ n := by
  rw [Ideal.map_map, tensorIdeal, ← Ideal.map_pow]
  have hcomp : (algebraMap (Completion A) (TensorRing A B)).comp
      (algebraMap A (Completion A)) =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap A B) :=
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  rw [hcomp, ← Ideal.map_map]
  exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr
    (maximalIdeal_pow_le_comap (algebraMap A B) n))

omit [IsNoetherianRing A] in
/-- The actual finite coefficient map kills the full original extended base power. -/
theorem basePower_le_ker_levelCoefficient (n : ℕ) :
    (maximalIdeal A ^ n).map (algebraMap A (Completion A)) ≤
      RingHom.ker (levelCoefficient A B n).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change levelCoefficient A B n (algebraMap A (Completion A) a) = 0
  rw [AlgHom.commutes]
  change Ideal.Quotient.mk (maximalIdeal B ^ n) (algebraMap A B a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (maximalIdeal_pow_le_comap (algebraMap A B) n ha)

/-- The literal inverse on quotients recovers every actual completed coefficient. -/
theorem levelBackward_levelCoefficient (n : ℕ) (x : Completion A) :
    levelBackward A B n (levelCoefficient A B n x) =
      Ideal.Quotient.mk (tensorIdeal A B ^ n) (x ⊗ₜ[A] 1) := by
  obtain ⟨a, ha⟩ := exists_original_congr A n x
  have hlevel : levelCoefficient A B n x =
      Ideal.Quotient.mk (maximalIdeal B ^ n) (algebraMap A B a) := by
    have hzero := basePower_le_ker_levelCoefficient A B n ha
    change levelCoefficient A B n (x - algebraMap A (Completion A) a) = 0 at hzero
    rw [map_sub, sub_eq_zero, AlgHom.commutes] at hzero
    exact hzero
  have hleft : Ideal.Quotient.mk (tensorIdeal A B ^ n) (x ⊗ₜ[A] 1) =
      Ideal.Quotient.mk (tensorIdeal A B ^ n)
        ((algebraMap A (Completion A) a) ⊗ₜ[A] 1) := by
    apply Ideal.Quotient.eq.mpr
    change (algebraMap (Completion A) (TensorRing A B)) x -
      (algebraMap (Completion A) (TensorRing A B)) (algebraMap A (Completion A) a) ∈ _
    rw [← map_sub]
    exact basePower_le_tensorPower A B n (Ideal.mem_map_of_mem _ ha)
  rw [hlevel]
  change Ideal.Quotient.mk _ (1 ⊗ₜ[A] algebraMap A B a) = _
  rw [hleft]
  exact congrArg (Ideal.Quotient.mk (tensorIdeal A B ^ n))
    (RingHom.congr_fun Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap a).symm

/-- Both original finite-level quotient maps are genuine inverses. -/
theorem levelBackward_levelForward (n : ℕ) (z : TensorRing A B ⧸ tensorIdeal A B ^ n) :
    levelBackward A B n (levelForward A B n z) = z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      change levelBackward A B n (tensorLevelMap A B n (x ⊗ₜ[A] b)) = _
      rw [tensorLevelMap_tmul, map_mul, levelBackward_levelCoefficient]
      change Ideal.Quotient.mk _ (x ⊗ₜ[A] 1) * Ideal.Quotient.mk _ (1 ⊗ₜ[A] b) = _
      rw [← map_mul]
      congr 1
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      rw [hx, hy]

/-- The actual finite-level tensor quotient equivalence, with no supplied comparison. -/
def levelEquiv (n : ℕ) :
    TensorRing A B ⧸ tensorIdeal A B ^ n ≃+* B ⧸ maximalIdeal B ^ n :=
  RingEquiv.ofRingHom (levelForward A B n) (levelBackward A B n)
    (RingHom.ext (levelForward_levelBackward A B n))
    (RingHom.ext (levelBackward_levelForward A B n))

end DeJongAlterations.Algebra.CompletionFlatMap
