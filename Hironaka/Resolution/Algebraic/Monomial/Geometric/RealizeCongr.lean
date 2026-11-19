/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Congruence
public import Hironaka.Resolution.Algebraic.Monomial.Restrict.Extend
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Phase
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The realise congruence

The geometric Step 3 `PieceFamily.realize` is invariant under a renumbering of the piece family
(`PieceFamily.Rel ρ σ Φ Φ'` of `Hironaka/Resolution/Algebraic/Monomial/Geometric/Congruence.lean`):
the same pieces and exponents, the components re-embedded by the strictly monotone `ρ`, the labels
by the strictly monotone `σ`. Not in the sources; Kollár's Step 3 reads label tuples
lexicographically and face sums, and puts the new divisor last, so an order-preserving renumbering
cannot change the run. The proof has a combinatorial half and a geometric half.

* *Combinatorial half, the lockstep of the two runs (`RunRel`).* The relation
  `MonomialState.Rel` is preserved by a blow-up (`Rel.blowUp` of
  `Hironaka/Resolution/Algebraic/Monomial/Restrict/Extend.lean`, with the renumbering extended by
  `extendComp`/`extendLabel`), and Kollár's choice is transported (`Rel.choice_eq`). The runs of
  Step 3 on two related states therefore proceed in lockstep: at each step the centre of the
  renumbered state is the image of the centre of the original one under the current
  renumbering, and the renumbering extends. `RunRel ρ σ D P L L' ρ' σ' D' P'` records this
  chain (the pattern of `phase_restrict` with the subnerve equal to the whole nerve);
  `step3_runRel` runs it along Step 3, and `step3_rel` is the summary: an order embedding `ρ'`
  extending `ρ` with `(step3 P).2 = (step3 D).2.map (image (image ρ'))` and `Rel ρ' σ'` between
  the final states.
* *Geometric half, the fold.* Along the lockstep the two piece families keep the same pieces
  (`PieceEq`): the old pieces become their strict transforms under the same centre (the centre
  of a finset of faces is the vanishing ideal of the union of their face sets,
  `PieceEq.centerOf`), the new pieces are the preimages of the same face sets, and the counters,
  labels and exponents of the families are those of the states (`Agrees`). The two folds then
  produce the same blow-up sequence (`realizeAux_runRel`). The two tails live over the blow-ups
  at the two centres, which are equal but not syntactically so; the transport along that
  equality is by the `cast*` lemmas below, each proved by `subst` (nothing about the schemes is
  used).

Nothing geometric enters: `realize` is a function of the state and of the pieces as closed sets,
so the congruence holds for piece families on any scheme. It is used in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothStep3.lean` for the deletion of empty
boundary members.
-/

@[expose] public section

universe u

open AlgebraicGeometry TopologicalSpace Scheme Finset

namespace Hironaka.Monomial

namespace MonomialState

/-! ### The lockstep of two runs related by a renumbering -/

/-- *The lockstep of two runs* (the pattern of `phase_restrict`): from the states `D`, `P`
related by `Rel ρ σ`, the lists `L` (on `D`) and `L'` (on `P`) proceed centre by centre, each
centre of `P` the image of the centre of `D` under the current renumbering, the renumbering
extended by `extendComp`/`extendLabel` at each blow-up, ending at the states `D'`, `P'` with the
renumbering `ρ'`, `σ'`. -/
inductive RunRel : (ρ σ : ℕ → ℕ) → MonomialState → MonomialState → List (Finset (Finset ℕ)) →
    List (Finset (Finset ℕ)) → (ρ' σ' : ℕ → ℕ) → MonomialState → MonomialState → Prop
  | nil (ρ σ : ℕ → ℕ) (D P : MonomialState) : RunRel ρ σ D P [] [] ρ σ D P
  | cons {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P) (S : Finset (Finset ℕ))
      (hSD : S ⊆ D.nerve) (hS0 : ∀ Q ∈ S, Q.Nonempty) {L L' : List (Finset (Finset ℕ))}
      {ρ' σ' : ℕ → ℕ} {D' P' : MonomialState}
      (hL : RunRel (extendComp ρ D P S (S.image (Finset.image ρ))) (extendLabel σ D P)
        (D.blowUp S) (P.blowUp (S.image (Finset.image ρ))) L L' ρ' σ' D' P') :
      RunRel ρ σ D P (S :: L) (S.image (Finset.image ρ) :: L') ρ' σ' D' P'

namespace RunRel

/-- `RunRel.cons` with the image centre given up to an equation. -/
theorem cons' {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P) (S : Finset (Finset ℕ))
    (hSD : S ⊆ D.nerve) (hS0 : ∀ Q ∈ S, Q.Nonempty) {S' : Finset (Finset ℕ)}
    (hS' : S' = S.image (Finset.image ρ)) {L L' : List (Finset (Finset ℕ))} {ρ' σ' : ℕ → ℕ}
    {D' P' : MonomialState}
    (hL : RunRel (extendComp ρ D P S S') (extendLabel σ D P) (D.blowUp S) (P.blowUp S') L L'
      ρ' σ' D' P') :
    RunRel ρ σ D P (S :: L) (S' :: L') ρ' σ' D' P' := by
  subst hS'
  exact .cons h S hSD hS0 hL

/-- The lockstep composes. -/
theorem append {ρ σ ρ₁ σ₁ ρ₂ σ₂ : ℕ → ℕ} {D P D₁ P₁ D₂ P₂ : MonomialState}
    {L₁ L₁' L₂ L₂' : List (Finset (Finset ℕ))} (h₁ : RunRel ρ σ D P L₁ L₁' ρ₁ σ₁ D₁ P₁)
    (h₂ : RunRel ρ₁ σ₁ D₁ P₁ L₂ L₂' ρ₂ σ₂ D₂ P₂) :
    RunRel ρ σ D P (L₁ ++ L₂) (L₁' ++ L₂') ρ₂ σ₂ D₂ P₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons h S hSD hS0 _ ih => exact .cons h S hSD hS0 (ih h₂)

/-- The faces of the image centre lie in the nerve of the renumbered state. -/
theorem filter_image_eq {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P)
    {S : Finset (Finset ℕ)} (hSD : S ⊆ D.nerve) :
    (S.image (Finset.image ρ)).filter (· ∈ P.nerve) = S.image (Finset.image ρ) :=
  Finset.filter_true_of_mem fun Q hQ => by
    obtain ⟨Q₀, hQ₀, rfl⟩ := Finset.mem_image.mp hQ
    exact h.image_mem_nerve (hSD hQ₀)

/-- The images of nonempty faces are nonempty. -/
theorem image_nonempty' {ρ : ℕ → ℕ} {S : Finset (Finset ℕ)} (hS0 : ∀ Q ∈ S, Q.Nonempty) :
    ∀ Q ∈ S.image (Finset.image ρ), Q.Nonempty := fun Q hQ => by
  obtain ⟨Q₀, hQ₀, rfl⟩ := Finset.mem_image.mp hQ
  exact (hS0 Q₀ hQ₀).image _

/-- The renumbering persists along the lockstep (`Rel.blowUp` at every step). -/
theorem rel_end {ρ σ ρ' σ' : ℕ → ℕ} {D P D' P' : MonomialState} {L L' : List (Finset (Finset ℕ))}
    (hr : RunRel ρ σ D P L L' ρ' σ' D' P') (h : Rel ρ σ D P) : Rel ρ' σ' D' P' := by
  induction hr with
  | nil => exact h
  | cons h S hSD hS0 _ ih =>
    exact ih (h.blowUp hSD (filter_image_eq h hSD) (image_nonempty' hS0))

/-- The final renumbering agrees with the initial one on the initial components. -/
theorem agree {ρ σ ρ' σ' : ℕ → ℕ} {D P D' P' : MonomialState} {L L' : List (Finset (Finset ℕ))}
    (hr : RunRel ρ σ D P L L' ρ' σ' D' P') : ∀ c, c < D.nextComp → ρ' c = ρ c := by
  induction hr with
  | nil => exact fun _ _ => rfl
  | cons h S hSD hS0 _ ih =>
    intro c hc
    rw [ih c (hc.trans_le (nextComp_le_blowUp _ _)), extendComp_of_lt _ _ _ _ _ hc]

/-- The final label renumbering agrees with the initial one on the initial labels. -/
theorem agree_label {ρ σ ρ' σ' : ℕ → ℕ} {D P D' P' : MonomialState}
    {L L' : List (Finset (Finset ℕ))} (hr : RunRel ρ σ D P L L' ρ' σ' D' P') :
    ∀ ℓ, ℓ < D.nextLabel → σ' ℓ = σ ℓ := by
  induction hr with
  | nil => exact fun _ _ => rfl
  | cons h S hSD hS0 _ ih =>
    intro ℓ hℓ
    rw [ih ℓ (hℓ.trans_le (nextLabel_le_blowUp _ _)), extendLabel_of_lt _ _ _ hℓ]

/-- The renumbered run is the image of the run under the final renumbering (which agrees with
every intermediate one on the components then present). -/
theorem map_eq {ρ σ ρ' σ' : ℕ → ℕ} {D P D' P' : MonomialState} {L L' : List (Finset (Finset ℕ))}
    (hr : RunRel ρ σ D P L L' ρ' σ' D' P') :
    L' = L.map fun S => S.image (Finset.image ρ') := by
  induction hr with
  | nil => rfl
  | cons h S hSD hS0 hL ih =>
    rw [List.map_cons, ← ih]
    congr 1
    have hlt : ∀ Q ∈ S, ∀ c ∈ Q, c < _ := fun Q hQ c hc =>
      MonomialState.lt_nextComp_of_mem _ (hSD hQ) hc
    exact ((image_image_congr hL.agree fun Q hQ c hc =>
      (hlt Q hQ c hc).trans_le (nextComp_le_blowUp _ _)).trans
      (image_image_congr (fun c hc => extendComp_of_lt _ _ _ _ _ hc) hlt)).symm

end RunRel

/-! ### The lockstep along a phase and along Step 3 -/

/-- A phase of Step 3 on two states related by a renumbering proceeds in lockstep
(`phase_restrict` with the subnerve the whole nerve). -/
theorem phase_runRel (r : ℕ) : ∀ (P : MonomialState) (hsP : ∀ s < r, P.Star s) (D : MonomialState)
    (ρ σ : ℕ → ℕ), Rel ρ σ D P → ∀ hsD : ∀ s < r, D.Star s,
    ∃ ρ' σ' : ℕ → ℕ, RunRel ρ σ D P (phase r D hsD).2 (phase r P hsP).2 ρ' σ'
      (phase r D hsD).1 (phase r P hsP).1 := by
  intro P hsP
  induction P, hsP using phase.induct r with
  | case1 P hsP hne ih =>
    intro D ρ σ hrel hsD
    have hPc : P.choice r = (D.choice r).image (Finset.image ρ) := hrel.choice_eq r
    have hDne : (D.choice r).Nonempty := by
      rw [← Finset.image_nonempty (f := Finset.image ρ), ← hPc]
      exact hne
    have hSD : D.choice r ⊆ D.nerve := (D.isCenter_choice r).1
    have hS0 : ∀ Q ∈ D.choice r, Q.Nonempty := fun Q hQ => D.nerve_nonempty Q (hSD hQ)
    have hfilter : (P.choice r).filter (· ∈ P.nerve) = (D.choice r).image (Finset.image ρ) := by
      rw [Finset.filter_true_of_mem fun Q hQ => P.mem_nerve_of_mem_choice hQ, hPc]
    have hS0' : ∀ Q ∈ P.choice r, Q.Nonempty := fun Q hQ =>
      P.nerve_nonempty Q (P.mem_nerve_of_mem_choice hQ)
    rw [phase_of_nonempty P hsP hne, phase_of_nonempty D hsD hDne]
    obtain ⟨ρ', σ', hrun⟩ := ih (D.blowUp (D.choice r)) _ _ (hrel.blowUp hSD hfilter hS0')
      (fun _ hsr => D.star_blowUp hsD hsr)
    exact ⟨ρ', σ', RunRel.cons' hrel (D.choice r) hSD hS0 hPc hrun⟩
  | case2 P hsP hne =>
    intro D ρ σ hrel hsD
    have hD : D.choice r = ∅ :=
      (hrel.choice_eq_empty_iff r).mp (Finset.not_nonempty_iff_eq_empty.mp hne)
    rw [phase_of_not_nonempty P hsP hne,
      phase_of_not_nonempty D hsD (Finset.not_nonempty_iff_eq_empty.mpr hD)]
    exact ⟨ρ, σ, RunRel.nil ρ σ D P⟩

/-- The phases `r, …, r + k − 1` in lockstep. -/
theorem phases_runRel (k : ℕ) : ∀ (r : ℕ) (P : MonomialState) (hsP : ∀ s < r, P.Star s)
    (D : MonomialState) (ρ σ : ℕ → ℕ), Rel ρ σ D P → ∀ hsD : ∀ s < r, D.Star s,
    ∃ ρ' σ' : ℕ → ℕ, RunRel ρ σ D P (phases k r D hsD).2 (phases k r P hsP).2 ρ' σ'
      (phases k r D hsD).1 (phases k r P hsP).1 := by
  induction k with
  | zero =>
    intro r P hsP D ρ σ hrel hsD
    exact ⟨ρ, σ, RunRel.nil ρ σ D P⟩
  | succ k ih =>
    intro r P hsP D ρ σ hrel hsD
    obtain ⟨ρ₁, σ₁, h₁⟩ := phase_runRel r P hsP D ρ σ hrel hsD
    obtain ⟨ρ', σ', h₂⟩ := ih (r + 1) _ (phase_star_succ P hsP) _ ρ₁ σ₁ (h₁.rel_end hrel)
      (phase_star_succ D hsD)
    rw [phases_succ, phases_succ]
    exact ⟨ρ', σ', h₁.append h₂⟩

/-- Step 3 on two states related by a renumbering proceeds in lockstep. -/
theorem step3_runRel {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P) :
    ∃ ρ' σ' : ℕ → ℕ, RunRel ρ σ D P (step3 D).2 (step3 P).2 ρ' σ' (step3 D).1 (step3 P).1 := by
  have e : step3 D = phases P.n 1 D (star_of_lt_one D) := by rw [step3, h.n_eq]
  rw [e, step3]
  exact phases_runRel P.n 1 P (star_of_lt_one P) D ρ σ h (star_of_lt_one D)

/-- *The run on a renumbered state is the image of the run*, under a renumbering `ρ'` extending
`ρ` (and `σ'` extending `σ`), with the final states again related. -/
theorem step3_rel {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P) :
    ∃ ρ' σ' : ℕ → ℕ, (∀ c, c < D.nextComp → ρ' c = ρ c) ∧ (∀ ℓ, ℓ < D.nextLabel → σ' ℓ = σ ℓ) ∧
      Rel ρ' σ' (step3 D).1 (step3 P).1 ∧
      (step3 P).2 = (step3 D).2.map fun S => S.image (Finset.image ρ') := by
  obtain ⟨ρ', σ', hr⟩ := step3_runRel h
  exact ⟨ρ', σ', hr.agree, hr.agree_label, hr.rel_end h, hr.map_eq⟩

end MonomialState

namespace PieceFamily

variable {X : Scheme.{u}}

/-! ### Families following states -/

/-- The counters, labels and exponents of a piece family are those of a state (with the mark
`m`): the invariant that lets the state-level renumbering drive the geometric fold. -/
structure Agrees (Φ : PieceFamily X) (D : MonomialState) (m : ℕ) : Prop where
  /-- The component counter. -/
  nextComp_eq : Φ.nextComp = D.nextComp
  /-- The label counter. -/
  nextLabel_eq : Φ.nextLabel = D.nextLabel
  /-- The labels. -/
  label_eq : Φ.label = D.label
  /-- The exponents. -/
  a_eq : Φ.a = D.a
  /-- The mark. -/
  m_eq : D.m = m

/-- A family agrees with its own state. -/
theorem agrees_toState (Φ : PieceFamily X) {n m : ℕ} (hV : Φ.IsValid n m) :
    Φ.Agrees (Φ.toState n m hV) m := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The agreement passes through a blow-up: `blowUpPieces` and `MonomialState.blowUp` use the
same formulas for the counters, labels and exponents. -/
theorem Agrees.blowUpPieces {Φ : PieceFamily X} {D : MonomialState} {m : ℕ}
    (h : Φ.Agrees D m) (S : Finset (Finset ℕ)) :
    (Φ.blowUpPieces S m).Agrees (D.blowUp S) m where
  nextComp_eq := by rw [blowUpPieces_nextComp, MonomialState.blowUp_nextComp, h.nextComp_eq]
  nextLabel_eq := by rw [blowUpPieces_nextLabel, MonomialState.blowUp_nextLabel, h.nextLabel_eq]
  label_eq := by
    funext c
    change (if c < Φ.nextComp then Φ.label c else Φ.nextLabel) =
      (if c < D.nextComp then D.label c else D.nextLabel)
    rw [h.nextComp_eq, h.nextLabel_eq, h.label_eq]
  a_eq := by
    funext c
    change (if c < Φ.nextComp then Φ.a c
        else (S.filter fun P => Φ.newComp S P = c).sup fun P => Φ.total P - m) =
      (if c < D.nextComp then D.a c
        else (S.filter fun P => D.newComp S P = c).sup fun P => D.total P - D.m)
    have hnew : Φ.newComp S = D.newComp S := by
      funext P
      simp only [PieceFamily.newComp, MonomialState.newComp, h.nextComp_eq]
    have htot : Φ.total = D.total := by
      funext P
      simp only [PieceFamily.total, MonomialState.total, h.a_eq]
    rw [h.nextComp_eq, h.a_eq, hnew, htot, h.m_eq]
  m_eq := h.m_eq

/-! ### Families with the same pieces along a renumbering -/

/-- The pieces of `Φ'` at the renumbered indices are the pieces of `Φ`. -/
def PieceEq (ρ : ℕ → ℕ) (Φ Φ' : PieceFamily X) : Prop :=
  ∀ c, c < Φ.nextComp → ρ c < Φ'.nextComp ∧ Φ'.piece (ρ c) = Φ.piece c

/-- The face set of the image of a set of live components is the face set of the set. -/
theorem PieceEq.faceSet {ρ : ℕ → ℕ} {Φ Φ' : PieceFamily X} (h : PieceEq ρ Φ Φ') {T : Finset ℕ}
    (hT : ∀ c ∈ T, c < Φ.nextComp) : Φ'.faceSet (T.image ρ) = Φ.faceSet T := by
  unfold PieceFamily.faceSet
  rw [Finset.inf_image]
  exact Finset.inf_congr rfl fun c hc => (h c (hT c hc)).2

/-- The face ideal of the image of a live face is the face ideal of the face. -/
theorem PieceEq.faceIdeal {ρ : ℕ → ℕ} {Φ Φ' : PieceFamily X} (h : PieceEq ρ Φ Φ') {T : Finset ℕ}
    (hT : ∀ c ∈ T, c < Φ.nextComp) : Φ'.faceIdeal (T.image ρ) = Φ.faceIdeal T := by
  unfold PieceFamily.faceIdeal
  rw [Finset.iSup_finset_image]
  exact iSup_congr fun c => iSup_congr fun hc => by rw [(h c (hT c hc)).2]

/-- The centre of the image of a finset of live faces is the centre of the finset. -/
theorem PieceEq.centerOf {ρ : ℕ → ℕ} {Φ Φ' : PieceFamily X} (h : PieceEq ρ Φ Φ')
    (hinj : Set.InjOn ρ (Set.Iio Φ.nextComp)) {S : Finset (Finset ℕ)}
    (hS : ∀ Q ∈ S, ∀ c ∈ Q, c < Φ.nextComp) :
    Φ'.centerOf (S.image (Finset.image ρ)) = Φ.centerOf S := by
  unfold PieceFamily.centerOf
  rw [Finset.prod_image]
  · exact Finset.prod_congr rfl fun Q hQ => h.faceIdeal (hS Q hQ)
  · intro Q₁ hQ₁ Q₂ hQ₂ hQ
    have h₁ : (Q₁ : Set ℕ) ⊆ Set.Iio Φ.nextComp := fun c hc => hS Q₁ hQ₁ c hc
    have h₂ : (Q₂ : Set ℕ) ⊆ Set.Iio Φ.nextComp := fun c hc => hS Q₂ hQ₂ c hc
    have := (hinj.image_eq_image_iff h₁ h₂).mp (by rw [← Finset.coe_image, ← Finset.coe_image, hQ])
    exact Finset.coe_injective this

/-! ### Transport along an equality of centres -/

section Cast

variable {Z Z' : X.IdealSheafData}

/-- A piece family on the blow-up at `Z`, read on the blow-up at `Z' = Z`. -/
def castFamily (hZ : Z = Z') (Ψ : PieceFamily Z.blowUp) : PieceFamily Z'.blowUp :=
  hZ ▸ Ψ

/-- A closed set of the blow-up at `Z`, read on the blow-up at `Z' = Z`. -/
def castCloseds (hZ : Z = Z') (C : Closeds Z.blowUp) : Closeds Z'.blowUp := hZ ▸ C

/-- A blow-up sequence of the blow-up at `Z`, read on the blow-up at `Z' = Z`. -/
def castSeq (hZ : Z = Z') (T : BlowUpSequence Z.blowUp) : BlowUpSequence Z'.blowUp :=
  hZ ▸ T

theorem cons_castSeq (hZ : Z = Z') (T : BlowUpSequence Z.blowUp) :
    BlowUpSequence.cons X Z' (castSeq hZ T) = BlowUpSequence.cons X Z T := by
  subst hZ
  rfl

theorem realizeAux_castFamily (hZ : Z = Z') (Ψ : PieceFamily Z.blowUp) (m : ℕ)
    (L : List (Finset (Finset ℕ))) :
    realizeAux (castFamily hZ Ψ) m L = castSeq hZ (realizeAux Ψ m L) := by
  subst hZ
  rfl

theorem castFamily_nextComp (hZ : Z = Z') (Ψ : PieceFamily Z.blowUp) :
    (castFamily hZ Ψ).nextComp = Ψ.nextComp := by
  subst hZ
  rfl

theorem castFamily_nextLabel (hZ : Z = Z') (Ψ : PieceFamily Z.blowUp) :
    (castFamily hZ Ψ).nextLabel = Ψ.nextLabel := by
  subst hZ
  rfl

theorem castFamily_label (hZ : Z = Z') (Ψ : PieceFamily Z.blowUp) :
    (castFamily hZ Ψ).label = Ψ.label := by
  subst hZ
  rfl

theorem castFamily_a (hZ : Z = Z') (Ψ : PieceFamily Z.blowUp) :
    (castFamily hZ Ψ).a = Ψ.a := by
  subst hZ
  rfl

theorem castFamily_piece (hZ : Z = Z') (Ψ : PieceFamily Z.blowUp) (c : ℕ) :
    (castFamily hZ Ψ).piece c = castCloseds hZ (Ψ.piece c) := by
  subst hZ
  rfl

theorem castCloseds_strictTransformCloseds (hZ : Z = Z') (C : Closeds X) :
    castCloseds hZ (strictTransformCloseds Z C) = strictTransformCloseds Z' C := by
  subst hZ
  rfl

theorem castCloseds_preimage (hZ : Z = Z') (C : Closeds X) :
    castCloseds hZ (C.preimage Z.blowUpπ.continuous) =
      C.preimage Z'.blowUpπ.continuous := by
  subst hZ
  rfl

/-- The transported family agrees with the same state. -/
theorem Agrees.castFamily (hZ : Z = Z') {Ψ : PieceFamily Z.blowUp} {D : MonomialState}
    {m : ℕ} (h : Ψ.Agrees D m) : (PieceFamily.castFamily hZ Ψ).Agrees D m := by
  subst hZ
  exact h

end Cast

/-! ### The piece correspondence passes through a blow-up -/

/-- Along the lockstep, the two transported families keep the same pieces: the old pieces are
the strict transforms of the same pieces under the same centre, the new pieces the preimages of
the same face sets, at the indices matched by `extendComp`. -/
theorem PieceEq.blowUpPieces {ρ : ℕ → ℕ} {Φ Φ' : PieceFamily X} {D P : MonomialState} {m : ℕ}
    (hpe : PieceEq ρ Φ Φ') (hΦ : Φ.Agrees D m) (hΦ' : Φ'.Agrees P m)
    {S : Finset (Finset ℕ)} (hS : ∀ Q ∈ S, ∀ c ∈ Q, c < Φ.nextComp)
    (hZ : Φ'.centerOf (S.image (Finset.image ρ)) = Φ.centerOf S) :
    PieceEq (MonomialState.extendComp ρ D P S (S.image (Finset.image ρ))) (Φ.blowUpPieces S m)
      (castFamily hZ (Φ'.blowUpPieces (S.image (Finset.image ρ)) m)) := by
  intro c hc
  rw [blowUpPieces_nextComp] at hc
  rw [castFamily_nextComp, blowUpPieces_nextComp, castFamily_piece]
  have hnew : Φ.newComp S = D.newComp S := by
    funext Q
    simp only [PieceFamily.newComp, MonomialState.newComp, hΦ.nextComp_eq]
  have hnew' : Φ'.newComp (S.image (Finset.image ρ)) = P.newComp (S.image (Finset.image ρ)) := by
    funext Q
    simp only [PieceFamily.newComp, MonomialState.newComp, hΦ'.nextComp_eq]
  rcases MonomialState.lt_or_exists_newComp D S (hΦ.nextComp_eq ▸ hc) with hlt | ⟨Q, hQ, hQc⟩
  · -- an old component: its strict transform
    have hlt' : c < Φ.nextComp := hΦ.nextComp_eq ▸ hlt
    rw [MonomialState.extendComp_of_lt ρ D P _ _ hlt]
    obtain ⟨hρc, hpiece⟩ := hpe c hlt'
    refine ⟨hρc.trans_le (Nat.le_add_right _ _), ?_⟩
    rw [blowUpPieces_piece_of_lt _ _ hρc, castCloseds_strictTransformCloseds,
      blowUpPieces_piece_of_lt _ _ hlt', hpiece]
  · -- a new component: the preimage of the face set of its face
    have hQc' : c = Φ.newComp S Q := by rw [hnew, hQc]
    subst hQc'
    rw [hnew, MonomialState.extendComp_newComp ρ D P S _ hQ, ← hnew', ← hnew]
    have hQ' : Q.image ρ ∈ S.image (Finset.image ρ) := Finset.mem_image_of_mem _ hQ
    refine ⟨?_, ?_⟩
    · simp only [PieceFamily.newComp, hΦ'.nextComp_eq]
      exact Nat.add_lt_add_left (MonomialState.rank_lt_card hQ') _
    · rw [blowUpPieces_piece_newComp _ _ hQ', castCloseds_preimage,
        blowUpPieces_piece_newComp _ _ hQ, hpe.faceSet (hS Q hQ)]

/-! ### The fold -/

/-- *Along the lockstep, the two folds produce the same blow-up sequence*, by one induction on
`RunRel`: the centres agree (`PieceEq.centerOf`), the transported families keep the same pieces
(`PieceEq.blowUpPieces`) and follow the blown-up states (`Agrees.blowUpPieces`), and the tails
are identified through the equality of the centres. -/
theorem realizeAux_runRel {ρ σ ρ' σ' : ℕ → ℕ} {D P D' P' : MonomialState}
    {L L' : List (Finset (Finset ℕ))} (hr : MonomialState.RunRel ρ σ D P L L' ρ' σ' D' P') :
    ∀ {X : Scheme.{u}} (Φ Φ' : PieceFamily X) (m : ℕ), Φ.Agrees D m → Φ'.Agrees P m →
      PieceEq ρ Φ Φ' → realizeAux Φ m L = realizeAux Φ' m L' := by
  induction hr with
  | nil => intros; rfl
  | @cons ρ σ D P h S hSD hS0 _ _ _ _ _ _ _ ih =>
    intro X Φ Φ' m hΦ hΦ' hpe
    have hS : ∀ Q ∈ S, ∀ c ∈ Q, c < Φ.nextComp := fun Q hQ c hc =>
      hΦ.nextComp_eq ▸ MonomialState.lt_nextComp_of_mem _ (hSD hQ) hc
    have hinj : Set.InjOn ρ (Set.Iio Φ.nextComp) := by
      rw [hΦ.nextComp_eq]
      exact h.mono.injOn
    have hZ := hpe.centerOf hinj hS
    rw [realizeAux_cons, realizeAux_cons, ← cons_castSeq hZ, ← realizeAux_castFamily]
    exact congrArg _ (ih (Φ.blowUpPieces S m) _ m (hΦ.blowUpPieces S)
      ((hΦ'.blowUpPieces _).castFamily hZ) (hpe.blowUpPieces hΦ hΦ' hS hZ))

/-- *The geometric Step 3 is invariant under a renumbering of the piece family.* The states are
related by `MonomialState.Rel`, Step 3 runs in lockstep (`step3_runRel`), and the fold follows
(`realizeAux_runRel`). -/
theorem realize_congr_of_rel {Φ Φ' : PieceFamily X} {ρ σ : ℕ → ℕ} {n m : ℕ} (h : Φ.Rel ρ σ Φ')
    (hV : Φ.IsValid n m) (hV' : Φ'.IsValid n m) : Φ.realize n m hV = Φ'.realize n m hV' := by
  have hrel : MonomialState.Rel ρ σ (Φ.toState n m hV) (Φ'.toState n m hV') :=
    ⟨rfl, rfl, h.mono, h.lt, h.a_eq, h.label_eq, h.σmono, h.σlt, h.nerve_eq⟩
  obtain ⟨ρ', σ', hr⟩ := MonomialState.step3_runRel hrel
  exact realizeAux_runRel hr Φ Φ' m (Φ.agrees_toState hV) (Φ'.agrees_toState hV')
    fun c hc => ⟨h.lt c hc, h.piece_eq c hc⟩

end PieceFamily

end Hironaka.Monomial
