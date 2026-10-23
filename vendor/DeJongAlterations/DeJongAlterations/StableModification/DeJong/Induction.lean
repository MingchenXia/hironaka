import DeJongAlterations.StableModification.DeJong.Reductions
import DeJongAlterations.Geometry.CurveBoundaryAlteration

/-!
# The induction on the dimension, conditional on the producers

de Jong 4.3 (`dejong96-alterations:page-0017`): Theorem 4.1 is proved by induction on
`d = dim X`. For `d ≤ 1` the normalization and its regular projective compactification
solve the problem (Codex's `Geometry.CurveBoundary.exists_alterationWithBoundary_curve`).
For `d ≥ 2` the inductive step 4.22 (`BaseStep k`, with Temkin's stable modification in
place of 4.17–4.21) gives the normal projective Cartier case in dimension `d` from the
theorem in dimension `d - 1`, and the reductions 4.4–4.10 (`Reductions.lean`) give the
theorem in dimension `d`.

## Main results

* `theoremUpTo_of_le_one`: the base case `d ≤ 1`.
* `deJongAlterationTheorem_iff_forall_theoremUpTo`: 4.1 is the conjunction of its
  dimension-indexed forms (varieties have finite dimension).
* `deJongAlterationTheorem_of_producers` (IF-4, `thm:sm-dj-main-of-producers`): over an
  algebraically closed field, the four producer propositions and `BaseStep k` imply
  `DeJongAlterationTheorem k`. This is a conditional theorem; it does not prove 4.1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

variable {k : Type u} [Field k]

/-- de Jong 4.3, the case `dim X ≤ 1`. -/
theorem theoremUpTo_of_le_one {d : ℕ} (hd : d ≤ 1) : TheoremUpTo k d := by
  intro X p hp hdim Z hZ
  let := hp
  have h1 : topologicalKrullDim X ≤ 1 := hdim.trans (by exact_mod_cast hd)
  obtain ⟨e, -⟩ := Geometry.CurveBoundary.exists_alterationWithBoundary_curve p h1 Z hZ
  exact ⟨e⟩

/-- Theorem 4.1 over `k` is equivalent to its dimension-indexed forms in all dimensions. -/
theorem deJongAlterationTheorem_iff_forall_theoremUpTo :
    DeJongAlterationTheorem k ↔ ∀ d : ℕ, TheoremUpTo k d := by
  constructor
  · intro h d X p hp _ Z hZ
    exact h X p hp Z hZ
  · intro h X p hp Z hZ
    let := hp
    obtain ⟨n, hn⟩ := exists_nat_topologicalKrullDim_eq p
    exact h n X p hp hn.le Z hZ

/-- The induction of de Jong 4.3 from the inductive step: if the inductive step holds in
every dimension `d ≥ 2`, then Theorem 4.1 holds in every dimension. -/
theorem forall_theoremUpTo_of_step
    (hstep : ∀ d : ℕ, 2 ≤ d → TheoremUpTo k (d - 1) → CartierCaseUpTo k d) :
    ∀ d : ℕ, TheoremUpTo k d := by
  have key : ∀ n : ℕ, TheoremUpTo k (n + 1) := by
    intro n
    induction n with
    | zero => exact theoremUpTo_of_le_one le_rfl
    | succ n ih =>
      apply theoremUpTo_of_cartierCaseUpTo
      exact hstep (n + 2) (by omega) (by simpa using ih)
  intro d
  exact (key d).mono (Nat.le_succ d)

/-- **IF-4** (`thm:sm-dj-main-of-producers`). Over an algebraically closed field, the
producer propositions `TemkinReadyFibration k`, `FlatteningAfterGEAlteration k`,
`TemkinStableModification k`, `SemistableResolution k` and the inductive step `BaseStep k`
imply de Jong's Theorem 4.1, `DeJongAlterationTheorem k`. -/
theorem deJongAlterationTheorem_of_producers [IsAlgClosed k]
    (hFIB : TemkinReadyFibration k) (hFLAT : FlatteningAfterGEAlteration k)
    (hTSM : TemkinStableModification k) (hEND : SemistableResolution k)
    (hSTEP : BaseStep k) : DeJongAlterationTheorem k :=
  deJongAlterationTheorem_iff_forall_theoremUpTo.mpr
    (forall_theoremUpTo_of_step (hSTEP hFIB hFLAT hTSM hEND))

end DeJongAlterations.StableModification.DeJong
