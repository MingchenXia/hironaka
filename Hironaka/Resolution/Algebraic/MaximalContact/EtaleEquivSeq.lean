/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquiv
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Étale equivalence of blow-up sequences

[Kol07, Definition 96] calls two blow-up sequences `B` and `B'` of order `m = max-ord I` starting
with `(X, I)`, `X` a smooth variety over a field of characteristic zero, **étale equivalent** when
there are étale surjections `ψ, ψ' : U ⇉ X` with (1) `ψ^*(I) = ψ'^*(I)`,
(2) `ψ^*(h) − ψ'^*(h) ∈ MC ψ^*(I)` for every function `h` on `X`, and (3) `ψ^* B = ψ'^* B'`.

**Conventions.** As for [Kol07, Definition 91]
(`Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquiv.lean`), the definition is stated for étale
maps whose images each contain the cosupport `cosupp(I, m) = {x | ord_x I ≥ m}` (`EtaleImagePair`).
Every centre of an order-`m` sequence lies over the cosupport, so the surjective form is recovered
by adjoining `X ∖ cosupp(I, m)` with both maps the inclusion; the image form is what Theorem 92 and
the functoriality argument of [Kol07, Theorem 103, Step 2.3] produce. Condition (2) is stated as the
agreement of morphisms on the closed subscheme `V(MC(ψ^*I))` (`AgreeOn`); condition (3) is an
equality of terms of `BlowUpSequence U`, `B.pullback ψ = B'.pullback ψ'`, for the pull-back of a
blow-up sequence of [Kol07, 30.1]. Kollár's `ψ, ψ'` are morphisms of `k`-varieties: the field
`comp_eq` (`ψ ≫ f = ψ' ≫ f`) records it, and it is what makes `MC(ψ^*I)` in (2) independent of which
of the two maps induces the `k`-structure of `U`.

* `EtaleEquivSeq f I m B B'`: the étale equivalence datum for two blow-up sequences, an
  `EtaleImagePair X (cosupp I m)` with (1)–(3) and `ψ ≫ f = ψ' ≫ f`. Kollár's standing hypothesis
  "`B, B'` are blow-up sequences of order `m = max-ord I`" is a hypothesis of the theorems that use
  the relation (Theorem 97), not a field.
* `EtaleEquivSeq.refl`: `B` is étale equivalent to itself through `U = X`, `ψ = ψ' = 𝟙 X`.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory Scheme AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- [Kol07, Definition 96], with images containing the cosupport in place of surjections: the
blow-up sequences `B` and `B'` on `X` are **étale equivalent** for `(X, I)` and the mark `m`
through the étale pair `ψ, ψ' : U ⟶ X` whose images each contain `cosupp(I, m) = {x | ord_x I ≥ m}`
(`EtaleImagePair`), when (1) `ψ^*I = ψ'^*I`, (2) `ψ` and `ψ'` agree on `V(MC(ψ^*I))` (Kollár's
"`ψ^*(h) − ψ'^*(h) ∈ MC ψ^*(I)` for every `h`", `AgreeOn`), and (3) `ψ^*B = ψ'^*B'` as terms of
`BlowUpSequence U` (the `pullback` of [Kol07, 30.1]); `ψ` and `ψ'` are morphisms of `k`-schemes
(`ψ ≫ f = ψ' ≫ f`, Kollár's varieties over `k`). -/
structure EtaleEquivSeq (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (m : ℕ)
    (B B' : BlowUpSequence X) extends EtaleImagePair X {x | (m : ℕ∞) ≤ I.ord x} where
  /-- Kollár's `ψ, ψ' : U ⇉ X` are morphisms of varieties over `k`. -/
  comp_eq : ψ ≫ f = ψ' ≫ f
  /-- (1) `ψ^*(I) = ψ'^*(I)`. -/
  h1 : I.comap ψ = I.comap ψ'
  /-- (2) `ψ^*(h) − ψ'^*(h) ∈ MC ψ^*(I)` for every `h ∈ 𝒪_X`: `ψ`, `ψ'` agree on `V(MC(ψ^*I))`. -/
  h2 : AgreeOn ψ ψ' (MC (ψ ≫ f) (I.comap ψ) m)
  /-- (3) `ψ^* B = ψ'^* B'`. -/
  h3 : B.pullback ψ = B'.pullback ψ'

namespace EtaleEquivSeq

variable {f : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {m : ℕ} {B B' : BlowUpSequence X}

/-- The three conditions (1)–(3) of [Kol07, Definition 96], bundled. -/
theorem conditions (Q : EtaleEquivSeq f I m B B') :
    I.comap Q.ψ = I.comap Q.ψ' ∧ AgreeOn Q.ψ Q.ψ' (MC (Q.ψ ≫ f) (I.comap Q.ψ) m) ∧
      B.pullback Q.ψ = B'.pullback Q.ψ' :=
  ⟨Q.h1, Q.h2, Q.h3⟩

/-- In place of Kollár's "étale surjections": the images of `ψ` and `ψ'` each contain the
cosupport `cosupp(I, m)`. -/
theorem covers_covers' (Q : EtaleEquivSeq f I m B B') :
    {x | (m : ℕ∞) ≤ I.ord x} ⊆ Set.range Q.ψ.base ∧
      {x | (m : ℕ∞) ≤ I.ord x} ⊆ Set.range Q.ψ'.base :=
  ⟨Q.covers, Q.covers'⟩

/-- Kollár's `ψ, ψ' : U ⇉ X` are morphisms of varieties over `k`: the field `comp_eq` restated. -/
theorem ψ_comp_eq (Q : EtaleEquivSeq f I m B B') : Q.ψ ≫ f = Q.ψ' ≫ f :=
  Q.comp_eq

end EtaleEquivSeq

/-- The trivial instance: `B` is étale equivalent to itself through `U = X`, `ψ = ψ' = 𝟙 X`
(`pullback_id`). -/
def EtaleEquivSeq.refl (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (m : ℕ)
    (B : BlowUpSequence X) : EtaleEquivSeq f I m B B where
  U := X
  ψ := 𝟙 X
  ψ' := 𝟙 X
  etale_ψ := inferInstance
  etale_ψ' := inferInstance
  covers := fun _ _ => ⟨_, rfl⟩
  covers' := fun _ _ => ⟨_, rfl⟩
  comp_eq := rfl
  h1 := rfl
  h2 := rfl
  h3 := rfl

/-- Kollár's `ψ, ψ' : U ⇉ X` are morphisms of `k`-varieties: when `U` is over `Spec k` and `ψ` is
over `Spec k`, so is `ψ'`, by `comp_eq`; the second map of an étale equivalence commutes with the
structure morphisms. -/
theorem EtaleEquiv.isOver_ψ' [X.Over (Spec (.of k))] {I : X.IdealSheafData} {m : ℕ}
    {E : DivisorFamily X} {H H' : X.IdealSheafData}
    (Q : EtaleEquiv (X ↘ Spec (.of k)) I m E H H') [Q.U.Over (Spec (.of k))]
    [Q.ψ.IsOver (Spec (.of k))] : Q.ψ'.IsOver (Spec (.of k)) :=
  ⟨by rw [← Q.comp_eq]; exact comp_over (f := Q.ψ) (S := Spec (.of k))⟩

end AlgebraicGeometry.Scheme.IdealSheafData
