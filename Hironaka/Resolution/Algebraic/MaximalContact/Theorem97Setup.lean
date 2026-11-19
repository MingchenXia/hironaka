/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquiv
public import Hironaka.Scheme.BlowUpSequence.Pullback
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Theorem 97: the marked datum carried along the induction

[Kol07, Theorem 97]: for `X` a smooth variety over a field of characteristic zero, `I` an
MC-invariant ideal sheaf and `B`, `B'` two blow-up sequences of order `m = max-ord I` which are
étale equivalent, `B = B'`. Its proof is an induction on the stage `i` along the common pull-back
`B^U := ψ^*B = ψ'^*B'` carrying three assertions: (1) `(X_i, I_i) = (X'_i, I'_i)`, (2) the lifts
`ψ_i, ψ'_i : U_i ⇉ X_i` satisfy `im(ψ_i^* − ψ'^*_i) ⊂ (Π^U_i)^{-1}_*(MC(I^U_0), 1)`,
(3) `Z_{i−1} = Z'_{i−1}`, with `W_i = cosupp((Π^U_i)^{-1}_*(MC(I^U_0), 1))` and the remark that
`Z^U_i ⊂ W_i` by Corollary 77.

The proof in this library (`Hironaka/Resolution/Algebraic/MaximalContact/Theorem97Induction.lean`)
recasts the induction in a **marked form** that carries the marked ideal `(M, 1)`, `M := MC(ψ^*I)`,
instead of `I`: the transforms `I_i` are in general neither D-balanced nor MC-invariant (the Warning
in [Kol07, 104]), and the proof uses of `I` only that `M_i := (Π^U_i)^{-1}_*(M, 1)` is contained in
the ideal of every centre `Z^U_i` ([Kol07, Corollary 77] with `j = m − 1`, together with the
reducedness of the smooth centres). This file holds the definition of that datum:

* `IsMarkedOneSeq C M`: the sequence `C` on `U` is **a blow-up sequence of order `≥ 1` for the
  marked ideal `(M, 1)`** in the containment form, `M_i ≤ 𝒪(Z^U_i)` for every `i`, where
  `M_i = C.markedTransformSeq M 1 i` is the recursion `M_0 = M`,
  `M_{i+1} = (π^U_i)^{-1}_*(M_i, 1) = (π^{U*}_i M_i : 𝒪(F^U_{i+1}))` (the condition (1′) of
  [Kol07, Definition 66]). The containment is one of ideals, not of supports: for a non-reduced
  centre `J = (x², y²)` and `M = (x, y)` have equal zero sets but `M ⊄ J`, and it is the
  containment that makes `M_{i+1}` an ideal. `isMarkedOneSeq_cons_iff` is the recursive reading
  (`nil ↦ True`; `cons Z rest, M ↦ M ≤ Z ∧ IsMarkedOneSeq rest (markedTransform Z M 1)`).
* `AgreeOn.mono`: agreement on `V(M)` gives agreement on the smaller closed subscheme `V(J)` for
  `M ≤ J` (the closed immersion `V(J) ⟶ V(M)`, Mathlib's `IdealSheafData.inclusion`); needed for
  the descent of the centres in the induction and in the one-step descent
  (`Hironaka/Resolution/Algebraic/MaximalContact/AgreeOnBlowUp.lean`).
* `centersInRange_cons_iff`, `centersInRange_eqToHom_comp`: the recursive reading of
  `CentersInRange` and its invariance under the transport of the source along an equality of
  schemes.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.BlowUpSequence

namespace AlgebraicGeometry.Scheme.BlowUpSequence


variable {U : Scheme.{u}}

/-- The blow-up sequence `C` on `U` is **of order `≥ 1` for the marked ideal `(M, 1)`**, in the
containment form: the marked transform `M_i = (Π^U_i)^{-1}_*(M, 1)` (`markedTransformSeq M 1`) is
contained in the ideal sheaf of the centre `Z^U_i` at every stage. This is Kollár's `Z^U_i ⊂ W_i`
in the proof of [Kol07, Theorem 97], strengthened from supports to ideals. -/
def IsMarkedOneSeq (C : BlowUpSequence U) (M : U.IdealSheafData) : Prop :=
  ∀ i : Fin C.length, C.markedTransformSeq M 1 i.castSucc ≤ C.center i

/-- The empty sequence is of order `≥ 1` for every `(M, 1)`. -/
theorem isMarkedOneSeq_nil (M : U.IdealSheafData) : (nil U).IsMarkedOneSeq M := fun i => i.elim0

/-- The recursive reading: on the `cons` shape the containment at stage `0` is `M ≤ Z`, and the
tail is of order `≥ 1` for `(π^{-1}_*(M, 1), 1)`. -/
theorem isMarkedOneSeq_cons_iff (Z : U.IdealSheafData) (rest : BlowUpSequence Z.blowUp)
    (M : U.IdealSheafData) :
    (cons U Z rest).IsMarkedOneSeq M ↔ M ≤ Z ∧ rest.IsMarkedOneSeq
        (M.markedTransform Z 1) := by
  constructor
  · intro h
    refine ⟨h ⟨0, Nat.succ_pos _⟩, fun i => ?_⟩
    obtain ⟨j, hj⟩ := i
    exact h ⟨j + 1, Nat.succ_lt_succ hj⟩
  · rintro ⟨h0, hr⟩ ⟨_ | j, hi⟩
    · exact h0
    · exact hr ⟨j, Nat.lt_of_succ_lt_succ hi⟩

variable {X : Scheme.{u}}

/-- `CentersInRange` read recursively: on the `cons` shape the condition at stage `0` is
`|Z| ⊆ im ψ`, and the tail's condition is along the lift `blowUpMap ψ Z`
(`pullbackStageHom_cons_zero`, `pullbackStageHom_cons_succ`, both definitional). -/
theorem centersInRange_cons_iff (Z : X.IdealSheafData) (rest : BlowUpSequence Z.blowUp)
    (ψ : U ⟶ X) :
    (cons X Z rest).CentersInRange ψ ↔
      (Z.support : Set X) ⊆ Set.range ψ ∧ rest.CentersInRange (Scheme.Hom.blowUpMap ψ Z) := by
  constructor
  · intro h
    refine ⟨h ⟨0, Nat.succ_pos _⟩, fun i => ?_⟩
    obtain ⟨j, hj⟩ := i
    exact h ⟨j + 1, Nat.succ_lt_succ hj⟩
  · rintro ⟨h0, hr⟩ ⟨_ | j, hi⟩
    · exact h0
    · exact hr ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- The covering condition on the centres is unchanged when the source of the map is transported
along an equality of schemes. -/
theorem centersInRange_eqToHom_comp (S : BlowUpSequence X) {U' : Scheme.{u}} (e : U' = U)
    (ψ : U ⟶ X) : S.CentersInRange (eqToHom e ≫ ψ) ↔ S.CentersInRange ψ := by
  subst e
  rw [eqToHom_refl, Category.id_comp]

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {U X : Scheme.{u}}

/-- Kollár's use of the inductive assumption (2) on the centre `Z^U_i ⊆ W_i` (proof of
[Kol07, Theorem 97]): two morphisms agreeing on `V(M)` agree on every closed subscheme `V(J)` with
`M ≤ J`, since `V(J) ⟶ V(M)` is the closed immersion `inclusion h` and `ι_J = inclusion h ≫ ι_M`. -/
theorem AgreeOn.mono {f g : U ⟶ X} {M J : U.IdealSheafData} (h : M ≤ J) (hfg : AgreeOn f g M) :
    AgreeOn f g J := by
  unfold AgreeOn at hfg ⊢
  rw [← inclusion_subschemeι h, Category.assoc, Category.assoc, hfg]

end AlgebraicGeometry.Scheme.IdealSheafData
