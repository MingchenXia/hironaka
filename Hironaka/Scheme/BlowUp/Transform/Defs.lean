/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.IdealSheaf.Defs

/-!
# Transforms of ideal sheaves under a blow-up

For the blow-up `π : W' → W` along `Z` with exceptional divisor `E`, an ideal `I` on `W` has the
*total transform* `I* = I·𝒪_{W'}` [Hau14, Definition 6.1], the *strict transform*
`Iˢ = ⋃_{i ≥ 0} (I* : I_E^i)`, the union of colon ideals [Hau14, Definition 6.2], and, for `c` at
most the order of `I` along `Z`, the *controlled transform* `I^!`, the unique ideal with
`I* = I_E^c · I^!` [Hau14, Definition 6.8], whose case `c = ord_Z I` is the *weak transform* `I^g`.
Hironaka defines the weak transform under a monoidal transformation with non-singular irreducible
centre `D` as the quotient of `f⁻¹(J)` by the `m`-th power of the ideal of `f⁻¹(D)`, `m = ν(J_x)` at
the generic point `x` of `D`, noting that `m = ν(f⁻¹(J)_y)` at the generic point `y` of `f⁻¹(D)`
[Hir64, Ch. 0, §5, p. 142]; so `m` is the largest power of that ideal dividing `f⁻¹(J)`, the
exponent used here. The strict transform of a closed subscheme is the subscheme cut out by the
sections supported on the exceptional divisor, i.e. the `I_E`-power torsion [Sta, Tag 080D].

The transforms are defined along any morphism `π : B ⟶ X` with a distinguished ideal sheaf `E` on
`B`, from the colon and the saturation of ideal sheaves: `strictTransformAlong π E J`,
`controlledTransformAlong π E J c`, `exceptionalOrderAlong π E J` (the supremum in `ℕ` of the
exponents `c` with `E ^ c ∣ J.comap π`, `0` when unbounded, i.e. when `J.comap π = 0`) and
`weakTransformAlong π E J`. Along the blow-up `D.blowUpπ` with `E = D.exceptionalDivisor` they are
the transforms of the main theorems: Hironaka's weak transform `J.weakTransform D` (with the
convention for a disconnected centre stated on its docstring), the strict transform
`Y.strictTransform D` of a closed subscheme, and Hironaka's `red(f⁻¹(E) ∪ f⁻¹(D))`,
`E.reducedTransform D`.

Boundary cases: `J.comap π = 0` gives exceptional order `0` and weak transform `0`; `c = 0` gives
the total transform as controlled transform.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open Scheme.IdealSheafData

section Along

variable {B X : Scheme.{u}}

/-- The strict transform of `J` along `π` with respect to the divisor `E`: the `E`-power torsion
saturation of the total transform `J.comap π` [Hau14, Definition 6.2]; [Sta, Tag 080D]. The
strict transform of a closed subscheme of `X` under the blow-up is this along `D.blowUpπ` with
`E` the exceptional ideal. -/
noncomputable def Scheme.IdealSheafData.strictTransformAlong (J : X.IdealSheafData) (π : B ⟶ X)
    (E : B.IdealSheafData) : B.IdealSheafData :=
  (J.comap π).saturate E

/-- The controlled transform of `J` with control `c`, `(J* : E^c)` [Hau14, Definition 6.8];
[Kol07, Definition 60, (60.1)]; for `E ^ c ∣ J*` it is the unique ideal sheaf with
`J* = E^c · J^!` (`pow_mul_colon_of_dvd`, `colon_pow_eq_of_mul_eq`). -/
noncomputable def Scheme.IdealSheafData.controlledTransformAlong (J : X.IdealSheafData)
    (π : B ⟶ X) (E : B.IdealSheafData) (c : ℕ) : B.IdealSheafData :=
  (J.comap π).colon (E ^ c)

/-- The exceptional order: the largest `m` such that `E ^ m` divides `J.comap π`, as a natural
number (`0` if unbounded, i.e. `J* = 0`). For a non-singular irreducible centre in a non-singular
scheme this is `ν(J)` at the generic point of the centre [Hir64, Ch. 0, §5, p. 142]. -/
noncomputable def exceptionalOrderAlong (π : B ⟶ X) (E : B.IdealSheafData) (J : X.IdealSheafData) :
    ℕ :=
  sSup {c : ℕ | E ^ c ∣ J.comap π}

/-- The weak transform, the controlled transform with the exceptional order as control
[Hir64, Ch. 0, §5, p. 142]; [Hau14, Definition 6.8] (`I^g = I_E^{-ord_Z I} · I*`). -/
noncomputable def Scheme.IdealSheafData.weakTransformAlong (J : X.IdealSheafData) (π : B ⟶ X)
    (E : B.IdealSheafData) : B.IdealSheafData :=
  J.controlledTransformAlong π E (exceptionalOrderAlong π E J)

end Along

section BlowUp

variable {X : Scheme.{u}}

/-- Hironaka's weak transform of `J` by the monoidal transformation with centre `D`
[Hir64, Ch. 0, §5, p. 142; Ch. I, §3, p. 176]: for `D` non-singular irreducible and
`m = ν(J_x)` at the generic point `x` of `D`, `f⁻¹(J)` is divisible by the `m`-th power of the
ideal of `f⁻¹(D)`, and the weak transform is the quotient.

Relation to the source.
* **Interpretation.** For a disconnected centre `D` the weak transform divides the pull-back of `J`
  by a single power of the whole exceptional divisor:
  `AlgebraicGeometry.Scheme.IdealSheafData.weakTransformAlong` is the colon ideal
  `(J.comap π).colon (E ^ c)` with `c = exceptionalOrderAlong π E J = sSup {c | E ^ c ∣ J.comap π}`
  for the whole exceptional divisor `E`, that is, the least of the orders along the components.
  Kollár's componentwise division [Kol07, 58 and Definition 60], stated under
  $\operatorname{ord}_{D_k} J = d$ for every component $D_k$, agrees with it only under
  equimultiplicity (the same order along every component of `D`), which holds wherever this
  definition enters a main theorem: Main Theorems II and II(N) and Corollary 1 require every centre
  to be non-singular and irreducible, II(N) and Corollary 1 moreover of constant order on the
  centre, and the centres of the resolution algorithm lie in the maximal-order locus. -/
noncomputable abbrev Scheme.IdealSheafData.weakTransform (J D : X.IdealSheafData) :
    D.blowUp.IdealSheafData :=
  J.weakTransformAlong D.blowUpπ D.exceptionalDivisor

/-- The strict (birational) transform of the closed subscheme `Y` under the blow-up with centre
`D` [Hir64, Ch. 0, §2, pp. 129–130]; [Kol07, Definition 30, 30.2]:
`AlgebraicGeometry.Scheme.IdealSheafData.strictTransformAlong`. -/
noncomputable abbrev Scheme.IdealSheafData.strictTransform (Y D : X.IdealSheafData) :
    D.blowUp.IdealSheafData :=
  Y.strictTransformAlong D.blowUpπ D.exceptionalDivisor

/-- Hironaka's `red(f⁻¹(E) ∪ f⁻¹(D))` [Hir64, Main Theorem II (iii); Main Theorem II(N) (3)]:
the reduced closed subscheme of the blow-up whose set of points is `f⁻¹(E) ∪ f⁻¹(D)`, as the
vanishing ideal sheaf of that closed set (II(N) writes `red(f⁻¹(E ∪ D))`, the same reduced
subscheme: both are the reduced structure on `f⁻¹(|E| ∪ |D|)`). -/
noncomputable def Scheme.IdealSheafData.reducedTransform (E D : X.IdealSheafData) :
    D.blowUp.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (E.support.preimage D.blowUpπ.continuous ⊔ D.support.preimage
        D.blowUpπ.continuous)

end BlowUp

end AlgebraicGeometry
