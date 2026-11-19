/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Defs

/-!
# Divisor families: total transform along a morphism, appending a member

Two constructions on Kollár's divisors with ordered index set `DivisorFamily X`
[Kol07, Definition 31].

* `totalTransformAlong π F E`: the shape of the total transform of [Kol07, Definition 25] along a
  morphism `π : B ⟶ X` with a distinguished divisor `F` on `B` — the strict transforms along `π` of
  the components of `E`, in their order, followed by `F` as the last member. For the blow-up
  `π = D.blowUpπ` with `F = D.exceptionalDivisor` it is `E.totalTransform D`, and it is the shape
  of the recursion step of the total transform along a blow-up sequence.
* `append E J`: Kollár's `E + H` [Kol07, Corollary 85; also Definition 78], the family `E` with the
  divisor `H = V(J)` appended as its last member.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {X Y : Scheme.{u}}

namespace Scheme.DivisorFamily

open IdealSheafData

/-- The total transform of [Kol07, Definition 25] along a morphism `π : B ⟶ X` with a distinguished
divisor `F` on `B`: the strict transforms along `π`
(`AlgebraicGeometry.Scheme.IdealSheafData.strictTransformAlong`) of the components of `E`, in their
order, followed by `F` as the last component. For the blow-up `π = D.blowUpπ` with
`F = D.exceptionalDivisor` this is `E.totalTransform D` definitionally, and on a succession the
total transform at stage `i + 1` is this along `S.step i` with `F = S.exceptionalAt i`; it is the
shape of the recursion step of `BlowUpSequence.totalTransformSeq`. -/
def totalTransformAlong {B : Scheme.{u}} (π : B ⟶ X) (F : B.IdealSheafData) (E : DivisorFamily X) :
    DivisorFamily B where
  ι := E.ι ⊕ₗ PUnit.{u + 1}
  component := fun i =>
    Sum.elim (fun j => (E.component j).strictTransformAlong π F) (fun _ => F)
      (ofLex i)

/-- Kollár's `E + H` [Kol07, Corollary 85; also Definition 78]: the family `E` with the divisor
`H = V(J)` appended as its last member, so that "`E + H` has simple normal crossings" is
`(E.append J).IsSnc` and "`Z` has simple normal crossings with `E + H`" is
`(E.append J).HasSncWith Z`. -/
def append (E : DivisorFamily X) (J : X.IdealSheafData) : DivisorFamily X where
  ι := E.ι ⊕ₗ PUnit.{u + 1}
  component := fun i => Sum.elim E.component (fun _ => J) (ofLex i)

end Scheme.DivisorFamily

end AlgebraicGeometry

end
