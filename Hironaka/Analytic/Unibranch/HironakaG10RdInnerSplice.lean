import Hironaka.Analytic.Unibranch.HironakaG10RdPermRun

/-!
# The finite recursion of Theorem `I_n` at fixed dimension (lane G10RD)

Plan item G10-03-12 (finite recursion splice at fixed dimension), in the form of
`work/hironaka-run0081-20261117/G10RD/G10-03-01-double-induction-contract.md` §3.2.  Source: H. Hironaka,
*Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), end of the proof of
`II_{n-1} ⇒ I_n`, printed pp. 543–544: "The proof of the implication will be done by induction on i. …
Now take the case in which i = 0 … the conclusion of (4.5.4) is exactly what is claimed in Theorem I_n.
For the case of i > 0, … (4.5.5) implies that the assumption of (4.5.1) is satisfied by an integer smaller
than i for the transform R' of R."

* `exists_openTracked_of_macroStep` — for any invariant `P` of data and any `ℕ`-valued measure `μ` (in the
  application: the stratification contract and Hironaka's index `i` = `HironakaG10RdTopIndex.topIndex`), if
  every datum satisfying `P` admits a permissible run (one macro-step: the lower-dimensional run of
  `II_{n-1}` on `C_i` followed by the `D_β` step) preserving `P`, ending with open tracked supports when
  `μ = 0` and strictly lowering `μ` otherwise, then every datum satisfying `P` admits a permissible run
  ending with open tracked supports (the conclusion of Theorem `I_n`).  The concatenation keeps the
  actual centres and the final datum (`PermRun.append`, `PermRun.final_append`).

The macro-step itself (Hironaka Lemmas 4.5.1–4.5.5, plan items G10-03-05 … 11) is the hypothesis; nothing
about rounds or `RoundData` is assumed.  No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace Hironaka.Analytic.Unibranch.HironakaG10RdInnerSplice

open Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver Hironaka.Analytic.Unibranch.HironakaG10RdPermRun

/-- **Theorem `I_n` from the macro-step by induction on Hironaka's index** (pp. 543–544). -/
theorem exists_openTracked_of_macroStep
    (P : ∀ (s : Stage) (q : ℕ), FDatum s q → Prop)
    (μ : ∀ (s : Stage) (q : ℕ), FDatum s q → ℕ)
    (hmacro : ∀ (s : Stage) (q : ℕ) (R : FDatum s q), P s q R →
      ∃ l : PermRun s R, P l.final.1 q l.final.2 ∧
        (μ s q R = 0 → OpenTracked l.final.2) ∧
        (0 < μ s q R → μ l.final.1 q l.final.2 < μ s q R)) :
    ∀ (s : Stage) (q : ℕ) (R : FDatum s q), P s q R →
      ∃ l : PermRun s R, OpenTracked l.final.2 := by
  suffices h : ∀ m, ∀ (s : Stage) (q : ℕ) (R : FDatum s q), μ s q R = m → P s q R →
      ∃ l : PermRun s R, OpenTracked l.final.2 from
    fun s q R hP => h _ s q R rfl hP
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s q R hm hP
    obtain ⟨l, hPl, h0, hlt⟩ := hmacro s q R hP
    rcases Nat.eq_zero_or_pos (μ s q R) with hz | hpos
    · exact ⟨l, h0 hz⟩
    · obtain ⟨l', hl'⟩ := ih (μ l.final.1 q l.final.2) (by rw [← hm]; exact hlt hpos)
        l.final.1 q l.final.2 rfl hPl
      refine ⟨l.append l', ?_⟩
      rw [PermRun.final_append]
      exact hl'

end Hironaka.Analytic.Unibranch.HironakaG10RdInnerSplice
