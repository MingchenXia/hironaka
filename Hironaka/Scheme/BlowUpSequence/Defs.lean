/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.ClosedImmersionLift
public import Hironaka.Scheme.Defs
public import Hironaka.Scheme.Snc.Defs
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite successions of monoidal transformations

A finite succession of monoidal transformations `X_r → ⋯ → X_1 → X_0 = X` with centres
`D_i ⊆ X_i`, `X_{i+1} = D_i.blowUp` [Hir64, Main Theorem I, p. 132]; [Kol07, Definition 29], as an
inductive type `BlowUpSequence X`: a list of centres, each living on the blow-up of the previous
stage. Empty and trivial centres are allowed [Kol07, Warning 20]. Everything attached to a
succession is a recursive function of its list of centres:

* its length `r`, stages `X_i`, centres `D_i`, partial composites `Π_i : X_i ⟶ X` and composite
  `Π : X_r ⟶ X` (Hironaka's `f`);
* Hironaka's weak transforms `J_i` and boundaries `E_i`, `E_{i+1} = red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`
  [Hir64, Main Theorem II (ii), (iii)]; Kollár's total transforms of a divisor family and the strict
  transforms of a closed subscheme [Kol07, Definitions 25 and 30];
* the pull-back along a morphism and the push-forward along a closed immersion
  [Kol07, Definition 30], and the deletion of the blow-ups with empty centre
  [Kol07, 32 and 34.1].

The functorial theorems assert the existence of blow-up sequence functors on their inputs
[Kol07, Definition 31, Theorems 35 and 36]; [Wlo05, Theorem 1.0.2]
(`AlgebraicGeometry.BlowUpSequenceFunctor`, `Hironaka.Scheme.Resolution.Defs`). Every scheme is
over `Spec k` through a structure morphism that is separated and of finite type (`FiniteType`;
Kollár's schemes of finite type over a field, made separated); smoothness over `k` is Mathlib's
`Smooth` of the structure morphism.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

open IdealSheafData Scheme.Hom

variable {X : Scheme.{u}}

/-! ### Finite successions of monoidal transformations -/

/-- A finite succession of monoidal transformations starting at `X` [Hir64, Main Theorem I,
p. 132]; [Kol07, Definition 29]: `nil X` is the empty succession, and `cons X D S'` is the
blow-up of `X` with centre `D` followed by the succession `S'` starting at `D.blowUp`. Stages,
centres and composites are recovered by `BlowUpSequence.stage`, `center`, `stageMap`,
`composite`. Empty and trivial centres are allowed [Kol07, Warning 20]. -/
inductive BlowUpSequence : Scheme.{u} → Type (u + 1)
  | nil (X : Scheme.{u}) : BlowUpSequence X
  | cons (X : Scheme.{u}) (D : X.IdealSheafData) (rest : BlowUpSequence
      D.blowUp) :
      BlowUpSequence X

namespace BlowUpSequence

open IdealSheafData

/-- The number `r` of monoidal transformations in the succession. -/
def length : {X : Scheme.{u}} → BlowUpSequence X → ℕ
  | _, nil _ => 0
  | _, cons _ _ rest => rest.length + 1

/-- The stage `X_i`, `0 ≤ i ≤ r`, with `X_0 = X`. -/
def stage : {X : Scheme.{u}} → (S : BlowUpSequence X) → Fin (S.length + 1) → Scheme.{u}
  | X, nil _, _ => X
  | _, cons X _ _, ⟨0, _⟩ => X
  | _, cons _ _ rest, ⟨j + 1, h⟩ => rest.stage ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The centre `D_i ⊆ X_i` of the `i`-th monoidal transformation, `0 ≤ i < r`. -/
def center : {X : Scheme.{u}} → (S : BlowUpSequence X) → (i : Fin S.length) →
    (S.stage i.castSucc).IdealSheafData
  | _, nil _, i => i.elim0
  | _, cons _ D _, ⟨0, _⟩ => D
  | _, cons _ _ rest, ⟨j + 1, h⟩ => rest.center ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The partial composite `Π_i = f_0 ∘ ⋯ ∘ f_{i-1} : X_i ⟶ X` (Kollár's `Π_{i0}`). -/
def stageMap : {X : Scheme.{u}} → (S : BlowUpSequence X) → (i : Fin (S.length + 1)) →
    (S.stage i ⟶ X)
  | X, nil _, _ => 𝟙 X
  | _, cons X _ _, ⟨0, _⟩ => 𝟙 X
  | _, cons X D rest, ⟨j + 1, h⟩ => rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ h⟩ ≫
      D.blowUpπ

/-- The final stage `X_r`. -/
def last {X : Scheme.{u}} (S : BlowUpSequence X) : Scheme.{u} :=
  S.stage (Fin.last S.length)

/-- The composite `Π = f_0 ∘ ⋯ ∘ f_{r-1} : X_r ⟶ X` of the whole succession (Hironaka's `f`). -/
def composite {X : Scheme.{u}} (S : BlowUpSequence X) : S.last ⟶ X :=
  S.stageMap (Fin.last S.length)

/-! ### Transforms along a succession -/

/-- Hironaka's sequence of weak transforms: `J_0 = J` and `J_{i+1}` the weak transform of `J_i`
by `f_i` [Hir64, Main Theorem II (ii)]. -/
def weakTransformSeq : {X : Scheme.{u}} → (S : BlowUpSequence X) → X.IdealSheafData →
    (i : Fin (S.length + 1)) → (S.stage i).IdealSheafData
  | _, nil _, J, _ => J
  | _, cons _ _ _, J, ⟨0, _⟩ => J
  | _, cons _ D rest, J, ⟨j + 1, h⟩ =>
    rest.weakTransformSeq (J.weakTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- Hironaka's sequence of boundaries: `E_0 = E` and `E_{i+1} = red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`
[Hir64, Main Theorem II (iii); Main Theorem II(N) (3)] (II(N) writes `red(f_i⁻¹(E_i ∪ D_i))`,
the same reduced subscheme: both are the reduced structure on `f_i⁻¹(|E_i| ∪ |D_i|)`). -/
def boundarySeq : {X : Scheme.{u}} → (S : BlowUpSequence X) → X.IdealSheafData →
    (i : Fin (S.length + 1)) → (S.stage i).IdealSheafData
  | _, nil _, E, _ => E
  | _, cons _ _ _, E, ⟨0, _⟩ => E
  | _, cons _ D rest, E, ⟨j + 1, h⟩ =>
    rest.boundarySeq (E.reducedTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- Kollár's total transform `E_i = (π_0 ⋯ π_{i-1})⁻¹_*(E) + Ex_tot(π_0 ⋯ π_{i-1})` of a divisor
family at stage `i` of the succession [Kol07, Definition 25]. -/
def totalTransformSeq : {X : Scheme.{u}} → (S : BlowUpSequence X) → DivisorFamily X →
    (i : Fin (S.length + 1)) → DivisorFamily (S.stage i)
  | _, nil _, E, _ => E
  | _, cons _ _ _, E, ⟨0, _⟩ => E
  | _, cons _ D rest, E, ⟨j + 1, h⟩ =>
    rest.totalTransformSeq (E.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The strict transform `Y_i ⊆ X_i` of a closed subscheme `Y ⊆ X` along the succession
[Kol07, Definition 30.2]; Włodarczyk's `Y_i` [Wlo05, Theorem 1.0.2 (b)]. -/
def strictTransformSeq : {X : Scheme.{u}} → (S : BlowUpSequence X) → X.IdealSheafData →
    (i : Fin (S.length + 1)) → (S.stage i).IdealSheafData
  | _, nil _, Y, _ => Y
  | _, cons _ _ _, Y, ⟨0, _⟩ => Y
  | _, cons _ D rest, Y, ⟨j + 1, h⟩ =>
    rest.strictTransformSeq (Y.strictTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩

end BlowUpSequence

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Scheme

variable {X Y : Scheme.{u}}

/-! ### Pull-back, push-forward, and the deletion of empty blow-ups -/

namespace Scheme.BlowUpSequence

/-- The pull-back `h^* B` of a succession along `h : Y ⟶ X` [Kol07, Definition 30.1]: blow up the
inverse image centres `h⁻¹(Z_i)`; for smooth (more generally flat) `h` the stages are `X_i ×_X Y`.
-/
def pullback : {X : Scheme.{u}} → BlowUpSequence X → {Y : Scheme.{u}} → (Y ⟶ X) →
    BlowUpSequence Y
  | _, nil _, Y, _ => nil Y
  | _, cons _ D rest, Y, h => cons Y (D.comap h) (rest.pullback (Scheme.Hom.blowUpMap h D))

/-- The push-forward `j_* B(S)` of a succession on a closed subscheme `S ⊆ X` along the closed
immersion `j : S ⟶ X` [Kol07, Definition 30.3]: the centres `Z_i^S` viewed in `X_i`,
`Z_i^X := (j_i)_* Z_i^S` along the inclusions `j_i : S_i ↪ X_i` (`pushforwardBlowUp`). The instance
argument `[IsClosedImmersion j]` is what makes the recursion well defined: `pushforwardBlowUp`
exists only for closed immersions. -/
def pushforward : {Y : Scheme.{u}} → BlowUpSequence Y → {X : Scheme.{u}} → (j : Y ⟶ X) →
    [IsClosedImmersion j] → BlowUpSequence X
  | _, nil _, X, _, _ => nil X
  | _, cons _ Z rest, X, j, _ => cons X (Z.map j) (rest.pushforward (Hom.pushforwardBlowUp j Z))

/-- Delete every blow-up whose centre is empty (the unit ideal sheaf `⊤`) and reindex the remaining
ones [Kol07, 32 and 34.1]. The empty blow-up `cons X ⊤ rest` is removed by carrying its tail `rest`,
a succession on `blowUp X ⊤`, back to `X` along the inverse of the isomorphism `blowUpπ X ⊤` (the
empty blow-up is trivial, [Kol07, Warning 20]: `isInvertible_top`,
`blowUp.isIso_π_of_isInvertible`), which is `pullback` along that inverse. -/
def eraseEmpty : {X : Scheme.{u}} → BlowUpSequence X → BlowUpSequence X
  | _, nil X => nil X
  | _, cons X D rest =>
    open scoped Classical in
    if h : D = ⊤ then
      have : IsIso D.blowUpπ := by
        subst h
        exact IdealSheafData.blowUp.isIso_π_of_isInvertible _
          Scheme.IdealSheafData.isInvertible_top
      rest.eraseEmpty.pullback (inv D.blowUpπ)
    else cons X D rest.eraseEmpty

end Scheme.BlowUpSequence

end AlgebraicGeometry

end
