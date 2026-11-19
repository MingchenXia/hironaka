/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.MonomialInvariant

/-! # Actual colex obstruction and intrinsic birth-block selections

The finite counterexample evaluates the ACTUAL MonomialInvariant inv/key API.
It does not assert a concrete analytic FULL canonicalInvariant counterexample.
Birth-preserving permutation invariance is characterized exactly by whole-block
selection; no new strict-progress or termination algorithm is claimed.
Blueprint: `hironaka-monomial-birth-block-obstruction-extension.tex`.
-/
set_option autoImplicit false
universe u v
namespace Hironaka.HironakaMonomialBirthBlockObstruction
open Finset MonomialInvariant

/-- The actual three-unit-branch, marking-two recipe selects the colex-largest
pair, which is changed by swapping two equal original branch labels.
`decide` is a small kernel computation of the actual finite definitions. -/
theorem actual_colex_three_branch_obstruction :
    inv 3 ({0,1,2} : Finset ℕ) (fun _ => 1) 2 =
        (key 3 (fun _ => 1) {1,2} : WithBot Val) ∧
    inv 3 ({1,2} : Finset ℕ) (fun _ => 1) 2 >
        inv 3 ({0,1} : Finset ℕ) (fun _ => 1) 2 ∧
    ({1,2} : Finset ℕ).image (Equiv.swap 0 2) = {0,1} ∧
    ({1,2} : Finset ℕ).image (Equiv.swap 0 2) ≠ {1,2} := by
  decide

/-- Intrinsic selected membership is constant on each assigned birth/colour block. -/
def BirthBlockClosed {ι : Type u} {κ : Type v} (birth : ι → κ) (K : Finset ι) : Prop :=
  ∀ i j, birth i = birth j → (i ∈ K ↔ j ∈ K)

/-- Invariance under ALL actual birth-preserving permutations holds exactly
for unions of WHOLE birth blocks. No invariant-value symmetry is assumed. -/
theorem birthBlockClosed_iff_permutation_invariant
    {ι : Type u} {κ : Type v} [DecidableEq ι] (birth : ι → κ) (K : Finset ι) :
    BirthBlockClosed birth K ↔
      ∀ e : Equiv.Perm ι, (∀ i, birth (e i) = birth i) → K.image e = K := by
  constructor
  · intro hblock e hbirth
    ext p
    constructor
    · intro hp
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
      exact (hblock q (e q) (hbirth q).symm).mp hq
    · intro hp
      refine mem_image.mpr ⟨e.symm p,?_,e.apply_symm_apply p⟩
      exact (hblock p (e.symm p) (by simpa only [e.apply_symm_apply] using hbirth (e.symm p))).mp hp
  · intro hinv i j hij
    have hbirth (a : ι) : birth ((Equiv.swap i j) a) = birth a := by
      by_cases hi : a = i
      · subst a
        simpa only [Equiv.swap_apply_left] using hij.symm
      · by_cases hj : a = j
        · subst a
          simpa only [Equiv.swap_apply_right] using hij
        · simp only [Equiv.swap_apply_def,if_neg hi,if_neg hj]
    have heq := hinv (Equiv.swap i j) hbirth
    constructor
    · intro hi
      have hj : j ∈ K.image (Equiv.swap i j) := mem_image.mpr ⟨i,hi,Equiv.swap_apply_left i j⟩
      exact heq ▸ hj
    · intro hj
      have hi : i ∈ K.image (Equiv.swap i j) := mem_image.mpr ⟨j,hj,Equiv.swap_apply_right i j⟩
      exact heq ▸ hi

/-- Three indistinguishable initial branches have no fully permutation-invariant
choice of one minimal feasible pair for the actual unit-weight marking-two case. -/
theorem no_permutation_invariant_two_of_three :
    ¬ ∃ K : Finset (Fin 3), K.card = 2 ∧ ∀ e : Equiv.Perm (Fin 3), K.image e = K := by
  rintro ⟨K,hcard,hinv⟩
  have hblock : BirthBlockClosed (fun _ : Fin 3 => ()) K :=
    (birthBlockClosed_iff_permutation_invariant (fun _ : Fin 3 => ()) K).mpr (fun e _ => hinv e)
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < K.card by omega)
  have hK : K = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun j => (hblock i j rfl).mp hi)
  rw [hK] at hcard
  exact (by decide : (Finset.univ : Finset (Fin 3)).card ≠ 2) hcard

end Hironaka.HironakaMonomialBirthBlockObstruction
