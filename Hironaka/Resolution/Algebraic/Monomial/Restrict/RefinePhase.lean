/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Restrict
public import Hironaka.Resolution.Algebraic.Monomial.Step3Phases
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Phase
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Refine

/-!
# Functoriality under refinement: the run on `Y` is the preimage of the run on `L`

Kollár's Step 3 on the monomial state commutes with refinement (`Refines ρ Y L` of
`Hironaka/Resolution/Algebraic/Monomial/Restrict.lean`), the first clause of [Kol07, 34.1],
commutation with smooth surjections, for the combinatorial procedure. The two runs advance in
lockstep: at every step Kollár's choice on `Y` is the `ρ`-preimage of the choice on `L`
(`Refines.choice_eq` of `Hironaka/Resolution/Algebraic/Monomial/Restrict/Refine.lean`), both are
nonempty or both empty, and the extended `ρ` keeps `Refines` (`Refines.blowUp`). `refineRun ρ' Y Ls`
is the preimage run, the centres of `L` pulled back to `Y` in order, each replaced by the faces of
the current nerve of `Y` whose image lies in it, and `step3_refine` says the run on `Y` is
`refineRun` of the run on `L` (read index by index through `refineRun_getElem?`), the run on `L` is
the image of the run on `Y`, and `Refines` holds between the final states. Not in the sources. The
geometric consequence is in `Hironaka/Resolution/Algebraic/Monomial/Geometric/ChainRun.lean` and
`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackRun.lean`.
-/

@[expose] public section

namespace Hironaka.Monomial.MonomialState

open Finset

/-- The `ρ`-preimage run: the centres of `L` pulled back to `Y` in order, each replaced by the
faces of the current nerve of `Y` whose image lies in it. -/
def refineRun (ρ : ℕ → ℕ) : MonomialState → List (Finset (Finset ℕ)) → List (Finset (Finset ℕ))
  | _, [] => []
  | st, S' :: Ls =>
    (st.nerve.filter fun Q => Q.image ρ ∈ S') ::
      refineRun ρ (st.blowUp (st.nerve.filter fun Q => Q.image ρ ∈ S')) Ls

theorem refineRun_nil (ρ : ℕ → ℕ) (st : MonomialState) : refineRun ρ st [] = [] := rfl

theorem refineRun_cons (ρ : ℕ → ℕ) (st : MonomialState) (S' : Finset (Finset ℕ))
    (Ls : List (Finset (Finset ℕ))) :
    refineRun ρ st (S' :: Ls) = (st.nerve.filter fun Q => Q.image ρ ∈ S') ::
      refineRun ρ (st.blowUp (st.nerve.filter fun Q => Q.image ρ ∈ S')) Ls := rfl

/-- The preimage run, index by index. -/
theorem refineRun_getElem? (ρ : ℕ → ℕ) (st : MonomialState) (Ls : List (Finset (Finset ℕ)))
    (k : ℕ) :
    (refineRun ρ st Ls)[k]? = (Ls[k]?).map fun S' : Finset (Finset ℕ) =>
      (((refineRun ρ st Ls).take k).foldl blowUp st).nerve.filter fun Q : Finset ℕ =>
        Q.image ρ ∈ S' := by
  induction Ls generalizing st k with
  | nil => simp [refineRun]
  | cons S' Ls ih =>
    cases k with
    | zero => simp [refineRun]
    | succ k =>
      rw [refineRun_cons, List.getElem?_cons_succ, List.getElem?_cons_succ, List.take_succ_cons,
        List.foldl_cons]
      exact ih _ k

theorem nextComp_le_foldl (st : MonomialState) (Ls : List (Finset (Finset ℕ))) :
    st.nextComp ≤ (Ls.foldl blowUp st).nextComp := by
  induction Ls generalizing st with
  | nil => exact le_rfl
  | cons S Ls ih => exact (nextComp_le_blowUp st S).trans (ih _)

/-- The preimage run depends on `ρ` only below the final counter of the run. -/
theorem refineRun_congr {ρ ρ' : ℕ → ℕ} : ∀ (st : MonomialState) (Ls : List (Finset (Finset ℕ))),
    (∀ c, c < ((refineRun ρ st Ls).foldl blowUp st).nextComp → ρ' c = ρ c) →
    refineRun ρ' st Ls = refineRun ρ st Ls
  | _, [], _ => rfl
  | st, S' :: Ls, hρ => by
    have hfil : (st.nerve.filter fun Q => Q.image ρ' ∈ S') =
        st.nerve.filter fun Q => Q.image ρ ∈ S' := by
      refine Finset.filter_congr fun Q hQ => ?_
      rw [Finset.image_congr fun c hc => hρ c ((st.lt_nextComp_of_mem hQ hc).trans_le
        ((nextComp_le_blowUp st _).trans (nextComp_le_foldl _ _)))]
    rw [refineRun_cons, refineRun_cons, hfil]
    congr 1
    refine refineRun_congr _ Ls fun c hc => hρ c ?_
    rw [refineRun_cons, List.foldl_cons]
    exact hc

theorem refineRun_append (ρ : ℕ → ℕ) (st : MonomialState) (L₁ L₂ : List (Finset (Finset ℕ))) :
    refineRun ρ st (L₁ ++ L₂) =
      refineRun ρ st L₁ ++ refineRun ρ ((refineRun ρ st L₁).foldl blowUp st) L₂ := by
  induction L₁ generalizing st with
  | nil => rfl
  | cons S' L₁ ih =>
    rw [List.cons_append, refineRun_cons, refineRun_cons, ih, List.cons_append, List.foldl_cons]

/-- The final state of a phase is the fold of its centres. -/
theorem phase_fst_eq_foldl {r : ℕ} (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    (phase r st hs).1 = (phase r st hs).2.foldl blowUp st := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih => rw [phase_of_nonempty st hs h]; exact ih
  | case2 st hs h => rw [phase_of_not_nonempty st hs h]; rfl

/-! ### The lockstep induction -/

theorem phase_refine (r : ℕ) : ∀ (L : MonomialState) (hsL : ∀ s < r, L.Star s) (Y : MonomialState)
    (ρ : ℕ → ℕ), Refines ρ Y L → ∀ hsY : ∀ s < r, Y.Star s,
    ∃ ρ' : ℕ → ℕ, (∀ c, c < Y.nextComp → ρ' c = ρ c) ∧
      Refines ρ' (phase r Y hsY).1 (phase r L hsL).1 ∧
      (phase r L hsL).2 = (phase r Y hsY).2.map (fun S => S.image (Finset.image ρ')) ∧
      (phase r Y hsY).2 = refineRun ρ' Y (phase r L hsL).2 := by
  intro L hsL
  induction L, hsL using phase.induct r with
  | case1 L hsL hne ih =>
    intro Y ρ href hsY
    have hYne : (Y.choice r).Nonempty := (href.choice_nonempty_iff r).mpr hne
    rw [phase_of_nonempty L hsL hne, phase_of_nonempty Y hsY hYne]
    simp only [List.map_cons]
    have hSY : Y.choice r ⊆ Y.nerve := (Y.isCenter_choice r).1
    have hSL : L.choice r = (Y.choice r).image (Finset.image ρ) := href.choice_image r
    have hpre : ∀ Q ∈ Y.nerve, Q.image ρ ∈ L.choice r → Q ∈ Y.choice r := fun Q hQ hQL => by
      rw [href.choice_eq]; exact Finset.mem_filter.mpr ⟨hQ, hQL⟩
    obtain ⟨ρ', hρ', href', hmapL, hmapY⟩ := ih (Y.blowUp (Y.choice r)) _
      (href.blowUp hSY hSL hpre) (fun _ hsr => Y.star_blowUp hsY hsr)
    have hρ'Y : ∀ c, c < Y.nextComp → ρ' c = ρ c := fun c hc => by
      rw [hρ' c (hc.trans_le (nextComp_le_blowUp Y _)), extendComp_of_lt ρ Y L _ _ hc]
    have hlt : ∀ Q ∈ Y.choice r, ∀ c ∈ Q, c < Y.nextComp := fun Q hQ c hc =>
      Y.lt_nextComp_of_mem (hSY hQ) hc
    refine ⟨ρ', hρ'Y, href', ?_, ?_⟩
    · rw [hmapL, hSL, image_image_congr hρ'Y hlt]
    · have hfil : (Y.nerve.filter fun Q => Q.image ρ' ∈ L.choice r) = Y.choice r := by
        rw [href.choice_eq]
        refine Finset.filter_congr fun Q hQ => ?_
        rw [Finset.image_congr fun c hc => hρ'Y c (Y.lt_nextComp_of_mem hQ hc)]
      rw [refineRun_cons, hfil, ← hmapY]
  | case2 L hsL hne =>
    intro Y ρ href hsY
    have hYe : ¬ (Y.choice r).Nonempty := fun hY => hne ((href.choice_nonempty_iff r).mp hY)
    rw [phase_of_not_nonempty L hsL hne, phase_of_not_nonempty Y hsY hYe]
    exact ⟨ρ, fun _ _ => rfl, href, rfl, rfl⟩

theorem phases_refine (k : ℕ) : ∀ (r : ℕ) (L : MonomialState) (hsL : ∀ s < r, L.Star s)
    (Y : MonomialState) (ρ : ℕ → ℕ), Refines ρ Y L → ∀ hsY : ∀ s < r, Y.Star s,
    ∃ ρ' : ℕ → ℕ, (∀ c, c < Y.nextComp → ρ' c = ρ c) ∧
      Refines ρ' (phases k r Y hsY).1 (phases k r L hsL).1 ∧
      (phases k r L hsL).2 = (phases k r Y hsY).2.map (fun S => S.image (Finset.image ρ')) ∧
      (phases k r Y hsY).2 = refineRun ρ' Y (phases k r L hsL).2 := by
  induction k with
  | zero =>
    intro r L hsL Y ρ href hsY
    exact ⟨ρ, fun _ _ => rfl, href, rfl, rfl⟩
  | succ k ih =>
    intro r L hsL Y ρ href hsY
    rw [phases_succ, phases_succ]
    simp only [List.map_append]
    obtain ⟨ρ₁, hρ₁, href₁, hmapL₁, hmapY₁⟩ := phase_refine r L hsL Y ρ href hsY
    obtain ⟨ρ', hρ', href', hmapL', hmapY'⟩ := ih (r + 1) _ (phase_star_succ L hsL) _ ρ₁ href₁
      (phase_star_succ Y hsY)
    have hfold : (phase r Y hsY).1 = (refineRun ρ₁ Y (phase r L hsL).2).foldl blowUp Y := by
      rw [← hmapY₁, phase_fst_eq_foldl]
    have hcongr : refineRun ρ' Y (phase r L hsL).2 = refineRun ρ₁ Y (phase r L hsL).2 :=
      refineRun_congr Y _ fun c hc => hρ' c (hfold ▸ hc)
    refine ⟨ρ', fun c hc => ?_, href', ?_, ?_⟩
    · rw [hρ' c (hc.trans_le (phase_nextComp_le Y hsY)), hρ₁ c hc]
    · rw [hmapL', hmapL₁]
      congr 1
      exact List.map_congr_left fun S hS =>
        (image_image_congr hρ' (phase_centers_lt Y hsY S hS)).symm
    · rw [refineRun_append, hcongr, ← hmapY₁, ← phase_fst_eq_foldl, ← hmapY']

theorem step3_refine_aux {ρ : ℕ → ℕ} {Y L : MonomialState} (h : Refines ρ Y L) :
    ∃ ρ' : ℕ → ℕ, (∀ c, c < Y.nextComp → ρ' c = ρ c) ∧
      Refines ρ' (step3 Y).1 (step3 L).1 ∧
      (step3 L).2 = (step3 Y).2.map (fun S => S.image (Finset.image ρ')) ∧
      (step3 Y).2 = refineRun ρ' Y (step3 L).2 := by
  have e : step3 Y = phases L.n 1 Y (star_of_lt_one Y) := by rw [step3, h.n_eq]
  rw [e, step3]
  exact phases_refine L.n 1 L (star_of_lt_one L) Y ρ h (star_of_lt_one Y)

/-- Functoriality of Step 3 under refinement, the first clause of [Kol07, 34.1] on the state:
the run on `Y` is the `ρ`-preimage of the run on `L`, with `ρ` extended to the new components
and `Refines` between the final states. -/
theorem step3_refine {ρ : ℕ → ℕ} {Y L : MonomialState} (h : Refines ρ Y L) :
    ∃ ρ' : ℕ → ℕ, (∀ c, c < Y.nextComp → ρ' c = ρ c) ∧
      Refines ρ' (step3 Y).1 (step3 L).1 ∧
      (∀ k : ℕ, (step3 L).2[k]? =
        ((step3 Y).2[k]?).map fun S : Finset (Finset ℕ) => S.image (Finset.image ρ')) ∧
      ∀ k : ℕ, (step3 Y).2[k]? = ((step3 L).2[k]?).map fun S' : Finset (Finset ℕ) =>
        (((step3 Y).2.take k).foldl blowUp Y).nerve.filter fun Q : Finset ℕ =>
          Q.image ρ' ∈ S' := by
  obtain ⟨ρ', hρ', href, hmapL, hmapY⟩ := step3_refine_aux h
  refine ⟨ρ', hρ', href, fun k => ?_, fun k => ?_⟩
  · rw [hmapL, List.getElem?_map]
  · rw [hmapY]
    exact refineRun_getElem? ρ' Y (step3 L).2 k

end Hironaka.Monomial.MonomialState
