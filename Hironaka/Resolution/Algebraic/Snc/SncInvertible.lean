/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Defs
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.IdealSheaf.Invertible
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.Family
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# The ideal of a simple normal crossing divisor is invertible

[Kol07, Theorem 35 (2)] says `Π^* I` is the ideal sheaf of a simple normal crossing divisor
(`IsIdealOfSncDivisor`: `∏ⁱ (E^i)^{a_i}` for an snc family `E`); the uses of the principalization
read this as *invertibility* — an effective Cartier divisor — as the proof of [Kol07, Corollary 22]
does ("its ideal sheaf `I` is not locally principal at `η_X`, and therefore some blow-up centre must
contain `η_X`"; a Cartier divisor as centre gives a trivial blow-up, [Kol07, Warning 20]). The
bridge is [Kol07, Definition 24 (1)–(3)]: at a point of a member `E^i` of an snc family the stalk of
`E^i` is `(z_{c(i)})` for a member `z_{c(i)}` of a regular system of parameters (`IsSncAt`), a
nonzerodivisor of the regular local ring `𝒪_{X,x}` (a domain, `isDomain_of_isRegularLocalRing` of
`Hironaka.Algebra.Local.Regular`); off `E^i` the stalk is the unit ideal. On a locally Noetherian
scheme the stalkwise criterion `isInvertible_of_forall_stalkIdeal_eq_span` of
`Hironaka.Scheme.IdealSheaf.Invertible` then gives `IsInvertible`, and products and
powers of invertible ideal sheaves are invertible (`IsInvertible.mul`, `isInvertible_pow`).

* `isSmoothDivisor_component_of_isSnc`: each member of an snc family on a scheme smooth over a field
  is a smooth divisor (`isSmoothDivisor_of_snc_data` of `Hironaka.Scheme.Snc.Family` read on a
  `DivisorFamily`; `BD.isSmoothDivisor_component` is its special case for the boundary of a triple);
* `isInvertible_of_isSmoothDivisor`: a smooth divisor is invertible;
* `IsSnc.isInvertible_component`;
  `AlgebraicGeometry.Scheme.IdealSheafData.IsIdealOfSncDivisor.isInvertible`.

Used by `Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36` (clause (2) of Theorem 35 as
local principality) and `Hironaka.Resolution.Algebraic.BoundaryClearing.Restriction`.

Sources: [Kol07, Theorem 35 (2); Definition 24; Warning 20; Corollary 22]; [Sta, Tag 01WS].
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme IdealSheafData

namespace Hironaka.Snc

open AlgebraicGeometry

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- [Kol07, Definition 24 (1)–(2)] on a divisor family: each member of a simple normal crossing
family on a scheme smooth over `k` is a smooth divisor (regular, and locally `(z_{c(i)} = 0)` for a
member of a regular system of parameters) — `isSmoothDivisor_of_snc_data` with the family's own snc
data (the general form of `BD.isSmoothDivisor_component`, which is the case `F = T.E` of a triple
`T`). -/
theorem isSmoothDivisor_component_of_isSnc (f : X ⟶ Spec (.of k)) [Smooth f] {F : DivisorFamily X}
    (hF : F.IsSnc) (j : F.ι) : IsSmoothDivisor (F.component j) :=
  isSmoothDivisor_of_snc_data F.component hF.1 (fun x => hF.2 x)
    (fun x => isRegularLocalRing_stalk f x) j

/-- A smooth divisor on a locally Noetherian scheme smooth over `k` is an effective Cartier divisor
([Kol07, Warning 20]; [Sta, Tag 01WS]) — at a point of the divisor its stalk is `(a)` with
`a ∈ 𝔪_x ∖ 𝔪_x²`, a nonzerodivisor of the regular local (hence integral) stalk; off the divisor the
stalk is the unit ideal `(1)`. -/
theorem isInvertible_of_isSmoothDivisor (f : X ⟶ Spec (.of k)) [Smooth f]
    {D : X.IdealSheafData} (hD : IsSmoothDivisor D) : D.IsInvertible := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  refine Scheme.IdealSheafData.isInvertible_of_forall_stalkIdeal_eq_span D fun x => ?_
  by_cases hx : x ∈ D.support
  · obtain ⟨a, _, ha2, hDa⟩ := hD.2 x hx
    have := isRegularLocalRing_stalk f x
    refine ⟨a, mem_nonZeroDivisors_of_ne_zero ?_, hDa⟩
    rintro rfl
    exact ha2 (Ideal.zero_mem _)
  · exact ⟨1, (nonZeroDivisors _).one_mem, by
      rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support D hx, Ideal.span_singleton_one]⟩

/-- Each member of a simple normal crossing family on a locally Noetherian scheme smooth over `k`
is an effective Cartier divisor. -/
theorem IsSnc.isInvertible_component (f : X ⟶ Spec (.of k)) [Smooth f]
    {F : DivisorFamily X} (hF : F.IsSnc) (j : F.ι) : (F.component j).IsInvertible :=
  isInvertible_of_isSmoothDivisor f (isSmoothDivisor_component_of_isSnc f hF j)

/-- [Kol07, Theorem 35 (2)] read as the proof of [Kol07, Corollary 22] does: the ideal sheaf of an
effective divisor supported on a simple normal crossing family, `∏ⁱ (E^i)^{a_i}`, is invertible — a
finite product of powers of invertible ideal sheaves. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsIdealOfSncDivisor.isInvertible
    (f : X ⟶ Spec (.of k)) [Smooth f] {I : X.IdealSheafData} (h : IsIdealOfSncDivisor I) :
    I.IsInvertible := by
  obtain ⟨F, a, hF, rfl⟩ := h
  exact Finset.prod_induction (fun j => F.component j ^ a j) Scheme.IdealSheafData.IsInvertible
    (fun _ _ h₁ h₂ => h₁.mul h₂)
    (by rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top)
    (fun j _ => Scheme.IdealSheafData.isInvertible_pow (IsSnc.isInvertible_component f hF j) (a j))

end Hironaka.Snc
