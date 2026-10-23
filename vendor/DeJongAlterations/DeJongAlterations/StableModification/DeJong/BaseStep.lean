import DeJongAlterations.StableModification.DeJong.BaseStepFlatDimension

/-!
# The base step 4.22 with Temkin's stable modification

de Jong, *Smoothness, semi-stability and alterations* (1996), 4.22
(`dejong96-alterations:page-0025`, `page-0026`), with Temkin's stable modification theorem
(Temkin, *Stable modification of relative curves*, Thm 1.5 and Thm 1.1,
`semi-stable.tex` l.1713–1716, l.1771–1775) in place of the moduli argument 4.17–4.21.

Let `X` be a normal projective variety of dimension `d ≥ 2` over an algebraically closed
field `k` and `D` an effective Cartier divisor with `Supp D ≠ X` (the situation (i)–(v) of
4.5–4.10). The proof (PLAN-DJ-MAIN §3.4) runs:

* S1: a Temkin-ready fibration `f : X' → Y` (`TemkinReadyFibration k`);
* S2: flattening of `X'` and of the horizontal boundary after a generically étale alteration
  of `Y` (`FlatteningAfterGEAlteration k`), giving the input of Temkin's theorem
  (`temkinInput_of_fibration`);
* S3–S5: Temkin's theorem (`TemkinStableModification k`), Chow's lemma and splitting of the
  marks into disjoint sections, with the boundary bookkeeping (`preparedFamily_of_temkinInput`);
* S6–S8: the induction hypothesis on the base, pulling back, the semi-stable resolution
  (`SemistableResolution k`), shrinking the boundary and composing
  (`nonempty_alterationWithBoundary_of_preparedFamily`).

## Main results

* `baseStep_of_flatFamilyPureFiberDimension`: `FlatFamilyPureFiberDimension → BaseStep k`.
* `baseStep`: `BaseStep k` over an algebraically closed field.

The statement `FlatFamilyPureFiberDimension` (the dimension theory of flat families, EGA IV
6.1.2) is used only to show that the flat strict transforms have pure relative dimension one
and zero, as Temkin's notion of a multipointed curve asks (`IsMultipointedCurve`); it is
proved in `BaseStepFlatDimension` (`flatFamilyPureFiberDimension`). Nothing else is assumed:
the four producer propositions are the hypotheses of `BaseStep k` itself.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

variable {k : Type u} [Field k]

/-- **The base step 4.22 with Temkin's theorem plugged in** (`thm:sm-dj-base-step`), up to
the dimension theory of flat families `FlatFamilyPureFiberDimension`. Over an algebraically
closed field, given the fibration, flattening, stable modification and semi-stable resolution
statements, Theorem 4.1 in dimension at most `d - 1` implies the Cartier case in dimension at
most `d`, for every `d ≥ 2`. -/
theorem baseStep_of_flatFamilyPureFiberDimension [IsAlgClosed k]
    (hFD : FlatFamilyPureFiberDimension.{u}) : BaseStep k := by
  intro hFIB hFLAT hTSM hEND d hd IH X p hp hproj hn hdim D hD hsupp
  let := hp
  obtain ⟨e, he⟩ := exists_nat_topologicalKrullDim_eq p
  by_cases hle : e ≤ d - 1
  · exact IH X p hp (by rw [he]; exact_mod_cast hle) D.support hsupp
  have hed : e = d := by
    have : (e : WithBot ℕ∞) ≤ d := he ▸ hdim
    have : e ≤ d := by exact_mod_cast this
    omega
  subst hed
  obtain ⟨X', φ, Y, pY, hvY, f, Dh, T, hφ, hX'proj, hYn, hYproj, hYdim, hfY, hfdom, hsm, hgi,
    hss, -, hT, hcov⟩ := hFIB e hd X p hp hproj hn he D hD hsupp
  let := hvY
  obtain ⟨I⟩ := temkinInput_of_fibration hFD hFLAT hd he D φ pY f Dh T hφ hX'proj hYn hYproj hYdim
    hfY hfdom hsm hgi hss hT hcov
  obtain ⟨F⟩ := preparedFamily_of_temkinInput hTSM I
  exact nonempty_alterationWithBoundary_of_preparedFamily hEND IH D hD F

/-- **The base step 4.22 with Temkin's theorem plugged in** (`thm:sm-dj-base-step`). Over an
algebraically closed field, given the fibration, flattening, stable modification and
semi-stable resolution statements, Theorem 4.1 in dimension at most `d - 1` implies the
Cartier case in dimension at most `d`, for every `d ≥ 2`. -/
theorem baseStep [IsAlgClosed k] : BaseStep k :=
  baseStep_of_flatFamilyPureFiberDimension FlatDimension.flatFamilyPureFiberDimension

end DeJongAlterations.StableModification.DeJong
