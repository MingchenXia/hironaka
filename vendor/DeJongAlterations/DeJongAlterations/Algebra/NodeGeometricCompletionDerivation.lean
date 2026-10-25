import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Derivation.Basic

/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution); module-valued adaptation for de Jong alterations.

The construction adapts Hironaka/Algebra/Local/Completion.lean, SHA256
2c55e4e163c1f0921bae3f5cfad5d979d9cb9b428799b29d512b44b07dbff913.
-/

/-! Completion of an ORIGINAL module-valued derivation. In particular the target
of the completed universal differential is the completion of the original
coherent differential module, not the algebraic differential module of the
completed ring. No finite generation or Noetherian hypotheses are required here. -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeGeometricCompletionDerivation

open AdicCompletion

variable {K R M : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module R M] [Module K M]
  (I : Ideal R) (D : Derivation K R M)

/-- Every original derivation lowers the ideal filtration of its ORIGINAL target module by one. -/
theorem differential_mem_pow_smul (n : ℕ) {r : R} (hr : r ∈ I ^ (n + 1)) :
    D r ∈ (I ^ n • ⊤ : Submodule R M) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz]
      apply Submodule.add_mem
      · exact Submodule.smul_mem_smul ha Submodule.mem_top
      · rw [pow_succ', Submodule.mul_smul]
        exact Submodule.smul_mem_smul hb (ih ha)
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb

/-- The actual differential on the original finite quotient representatives. -/
def differentialLevel (n : ℕ) (q : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  Quotient.liftOn' q (fun r => Submodule.Quotient.mk (D r)) fun r s h => by
    apply (Submodule.Quotient.eq _).mpr
    rw [← map_sub]
    apply differential_mem_pow_smul I D n
    have h' := (Submodule.quotientRel_def _).mp h
    rwa [Ideal.smul_eq_mul, Ideal.mul_top] at h'

@[simp]
theorem differentialLevel_mk (n : ℕ) (r : R) :
    differentialLevel I D n (Submodule.Quotient.mk r) = Submodule.Quotient.mk (D r) := rfl

/-- The actual finite quotient differentials commute with all actual transition maps. -/
theorem transition_differentialLevel {m n : ℕ} (h : m ≤ n)
    (q : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    transitionMap I M h (differentialLevel I D n q) =
      differentialLevel I D m (transitionMap I R (Nat.succ_le_succ h) q) := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- The actual completed differential, before packaging its derivation laws. -/
def completedDifferentialFun (r : AdicCompletion I R) : AdicCompletion I M :=
  ⟨fun n => differentialLevel I D n (r.val (n + 1)), fun h => by
    rw [transition_differentialLevel, r.property (Nat.succ_le_succ h)]⟩

@[simp]
theorem completedDifferentialFun_val (r : AdicCompletion I R) (n : ℕ) :
    (completedDifferentialFun I D r).val n = differentialLevel I D n (r.val (n + 1)) := rfl

variable [IsScalarTower K R M]

/-- Completion of the ORIGINAL module-valued derivation, with the native completed-ring action
on the completion of its ORIGINAL target module. -/
def completedDifferential : Derivation K (AdicCompletion I R) (AdicCompletion I M) where
  toFun := completedDifferentialFun I D
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1))
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (y.val (n + 1))
    rw [val_add_apply, completedDifferentialFun_val, completedDifferentialFun_val,
      completedDifferentialFun_val, val_add_apply, ← hr, ← hs, ← Submodule.Quotient.mk_add,
      differentialLevel_mk, differentialLevel_mk, differentialLevel_mk, map_add,
      Submodule.Quotient.mk_add]
  map_smul' k x := by
    apply AdicCompletion.ext
    intro n
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1))
    rw [RingHom.id_apply, val_smul_apply, completedDifferentialFun_val,
      completedDifferentialFun_val, val_smul_apply, ← hr, ← Submodule.Quotient.mk_smul,
      differentialLevel_mk, differentialLevel_mk, Derivation.map_smul,
      Submodule.Quotient.mk_smul]
  map_one_eq_zero' := by
    apply AdicCompletion.ext
    intro n
    change differentialLevel I D n ((1 : AdicCompletion I R).val (n + 1)) =
      (0 : AdicCompletion I M).val n
    rw [val_one, val_zero_apply,
      show (1 : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) = Submodule.Quotient.mk 1 from
        (map_one (Ideal.Quotient.mk _)).symm,
      differentialLevel_mk, Derivation.map_one_eq_zero, Submodule.Quotient.mk_zero]
  leibniz' x y := by
    apply AdicCompletion.ext
    intro n
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1))
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (y.val (n + 1))
    have hxn : x.val n = Submodule.Quotient.mk r := by
      rw [← x.property (Nat.le_succ n), ← hr]
      exact transitionMap_ideal_mk I (Nat.le_succ n) r
    have hyn : y.val n = Submodule.Quotient.mk s := by
      rw [← y.property (Nat.le_succ n), ← hs]
      exact transitionMap_ideal_mk I (Nat.le_succ n) s
    have hDx : (completedDifferentialFun I D x).val n = Submodule.Quotient.mk (D r) := by
      rw [completedDifferentialFun_val, ← hr, differentialLevel_mk]
    have hDy : (completedDifferentialFun I D y).val n = Submodule.Quotient.mk (D s) := by
      rw [completedDifferentialFun_val, ← hs, differentialLevel_mk]
    have hxy : (x * y).val (n + 1) = Submodule.Quotient.mk (r * s) := by
      rw [val_mul, ← hr, ← hs]
      exact (map_mul (Ideal.Quotient.mk _) r s).symm
    change differentialLevel I D n ((x * y).val (n + 1)) =
      (x • completedDifferentialFun I D y + y • completedDifferentialFun I D x).val n
    rw [hxy, differentialLevel_mk, val_add_apply, smul_eval, smul_eval,
      hxn, hyn, hDx, hDy, Derivation.leibniz, Submodule.Quotient.mk_add]
    rfl

@[simp]
theorem completedDifferential_val (r : AdicCompletion I R) (n : ℕ) :
    (completedDifferential I D r).val n = differentialLevel I D n (r.val (n + 1)) := rfl

/-- The completed derivation retains EVERY original differential, through the actual canonical maps. -/
theorem completedDifferential_of (r : R) :
    completedDifferential I D (AdicCompletion.of I R r) = AdicCompletion.of I M (D r) := by
  apply AdicCompletion.ext
  intro n
  rfl

/-- The entire original coefficient square, not just its reduction modulo the maximal ideal. -/
theorem completedDifferential_algebraMap (r : R) :
    completedDifferential I D (algebraMap R (AdicCompletion I R) r) =
      AdicCompletion.of I M (D r) := by
  exact completedDifferential_of I D r

/-- Continuity at zero for the actual inverse-limit coordinate kernels: each target level
is killed by some source level. These kernels are the defining neighbourhoods of the
canonical adic inverse-limit topologies. -/
def IsCoordinateContinuous (F : AdicCompletion I R → AdicCompletion I M) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ∀ x : AdicCompletion I R, x.val m = 0 → (F x).val n = 0

/-- The constructed differential is continuous, with the explicit uniform one-level loss. -/
theorem completedDifferential_filtration (n : ℕ) (x : AdicCompletion I R)
    (hx : x.val (n + 1) = 0) : (completedDifferential I D x).val n = 0 := by
  rw [completedDifferential_val, hx]
  change Submodule.Quotient.mk (D 0) = 0
  rw [map_zero, Submodule.Quotient.mk_zero]

theorem completedDifferential_continuous :
    IsCoordinateContinuous I (completedDifferential I D) :=
  fun n => ⟨n + 1, completedDifferential_filtration I D n⟩

/-- The actual completed derivation is the UNIQUE continuous derivation extending the
ORIGINAL derivation, with continuity stated on the actual inverse-limit coordinate kernels. -/
theorem completedDifferential_unique
    (E : Derivation K (AdicCompletion I R) (AdicCompletion I M))
    (hE : IsCoordinateContinuous I E)
    (hOriginal : ∀ r : R, E (AdicCompletion.of I R r) = AdicCompletion.of I M (D r)) :
    E = completedDifferential I D := by
  apply DFunLike.ext
  intro x
  apply AdicCompletion.ext
  intro n
  obtain ⟨m, hm⟩ := hE n
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val (m + (n + 1)))
  have hzero (j : ℕ) (hj : j ≤ m + (n + 1)) :
      (x - AdicCompletion.of I R r).val j = 0 := by
    rw [val_sub_apply]
    apply sub_eq_zero.mpr
    rw [← x.property hj, ← hr]
    exact transitionMap_ideal_mk I hj r
  have hEzero := hm (x - AdicCompletion.of I R r) (hzero m (Nat.le_add_right _ _))
  have hDzero := completedDifferential_filtration I D n (x - AdicCompletion.of I R r)
    (hzero (n + 1) (Nat.le_add_left _ _))
  rw [map_sub, val_sub_apply, hOriginal] at hEzero
  rw [map_sub, val_sub_apply, completedDifferential_of] at hDzero
  exact (sub_eq_zero.mp hEzero).trans (sub_eq_zero.mp hDzero).symm

/-- Two actual continuous completed derivations agreeing on the ORIGINAL algebra agree
on the entire actual completion. No presentation or model of that completion is assumed. -/
theorem continuousDerivation_ext
    (E F : Derivation K (AdicCompletion I R) (AdicCompletion I M))
    (hE : IsCoordinateContinuous I E) (hF : IsCoordinateContinuous I F)
    (hOriginal : ∀ r : R, E (AdicCompletion.of I R r) = F (AdicCompletion.of I R r)) :
    E = F := by
  apply DFunLike.ext
  intro x
  apply AdicCompletion.ext
  intro n
  obtain ⟨m, hm⟩ := hE n
  obtain ⟨l, hl⟩ := hF n
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val (m + l))
  have hzero (j : ℕ) (hj : j ≤ m + l) :
      (x - AdicCompletion.of I R r).val j = 0 := by
    rw [val_sub_apply]
    apply sub_eq_zero.mpr
    rw [← x.property hj, ← hr]
    exact transitionMap_ideal_mk I hj r
  have hEzero := hm (x - AdicCompletion.of I R r) (hzero m (Nat.le_add_right _ _))
  have hFzero := hl (x - AdicCompletion.of I R r) (hzero l (Nat.le_add_left _ _))
  rw [map_sub, val_sub_apply, hOriginal] at hEzero
  rw [map_sub, val_sub_apply] at hFzero
  exact (sub_eq_zero.mp hEzero).trans (sub_eq_zero.mp hFzero).symm

end DeJongAlterations.Algebra.NodeGeometricCompletionDerivation
