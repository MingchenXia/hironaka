/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# A blow-up sequence is an isomorphism over the locus its centers avoid

Clause (3) of [Kol07, Theorem 35] says the principalization `Π : X_r → X` is an isomorphism over
`X ∖ cosupp I`; the reason is the general fact that **a composite of blow-ups whose centers lie
over a closed set `Z` is an isomorphism over `X ∖ Z`**: a blow-up is an isomorphism off its center
(`blowUp.isIso_π_restrict_compl_support`, [Sta, Tag 02OS]) and the restriction of a composite to
an open is the composite of the restrictions (`morphismRestrict_comp`). This module proves that
statement for sequences, `isIso_composite_restrict_of_centers_disjoint`, by induction along the
sequence, from two general tools:

* `isIso_restrict_of_le`: an isomorphism over an open `V` is an isomorphism over every open
  `U ≤ V`, because `f ∣_ U` is the base change of `f ∣_ V` along `U ⟶ V` (the two squares of
  `isPullback_morphismRestrict`, pasted by `IsPullback.of_bot`) and isomorphisms are stable under
  base change;
* `isIso_eraseEmpty_composite_restrict`: deleting the empty blow-ups does not change the
  isomorphism locus, because the composite of `S.eraseEmpty` is the composite of `S` after the
  isomorphism `eraseEmptyLastHom` of the last stages (`eraseEmptyLastHom_comp_composite`).

The stalkwise form of the same fact is `isIso_over_of_centers_disjoint` of
`Hironaka/Resolution/Algebraic/Kol07/IsoLocus.lean`; here the conclusion is the isomorphism of the
restriction `S.composite ∣_ U` itself, the form in which clause (3) of the principalization theorem
is stated. Holds on any scheme.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace Hironaka.Sequence

variable {X Y : Scheme.{u}}

/-- `IsIso` of a restriction is transported along an equality of morphisms (the two restrictions
have different source objects only up to that equality, so `rw` cannot do it in place). -/
theorem isIso_restrict_congr {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) [IsIso (f ∣_ U)] :
    IsIso (g ∣_ U) := by
  subst e
  assumption

/-- The restriction of a composite is an isomorphism when both restricted factors are
(`morphismRestrict_comp`; the source objects `(f ≫ g) ⁻¹ᵁ U` and `f ⁻¹ᵁ (g ⁻¹ᵁ U)` agree only by
unfolding, hence the explicit `inferInstanceAs`). -/
theorem isIso_restrict_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    [IsIso (f ∣_ g ⁻¹ᵁ U)] [IsIso (g ∣_ U)] : IsIso ((f ≫ g) ∣_ U) := by
  rw [morphismRestrict_comp]
  exact inferInstanceAs (IsIso ((f ∣_ g ⁻¹ᵁ U) ≫ (g ∣_ U)))

/-- An isomorphism over an open `V` is an isomorphism over every open `U ≤ V`: the restriction
`f ∣_ U` is the base change of `f ∣_ V` along `U ⟶ V` (the two squares of
`isPullback_morphismRestrict`, pasted vertically), and isomorphisms are stable under base
change. -/
theorem isIso_restrict_of_le (f : X ⟶ Y) {U V : Y.Opens} (h : U ≤ V) [IsIso (f ∣_ V)] :
    IsIso (f ∣_ U) := by
  have h' : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ V := fun x hx => h hx
  have s : IsPullback (f ∣_ U) (X.homOfLE h' ≫ (f ⁻¹ᵁ V).ι) (Y.homOfLE h ≫ V.ι) f := by
    rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
    exact isPullback_morphismRestrict f U
  have p : (f ∣_ U) ≫ Y.homOfLE h = X.homOfLE h' ≫ (f ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι,
      morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  exact property_of_isPullback (MorphismProperty.isomorphisms Scheme)
    (IsPullback.of_bot s p (isPullback_morphismRestrict f V)) ‹IsIso (f ∣_ V)›

/-- A blow-up sequence whose centers avoid the preimages of an open `U` is an isomorphism over `U`
(the general form of clause (3) of [Kol07, Theorem 35]): by induction along the sequence, each
blow-up being an isomorphism off its center (`blowUp.isIso_π_restrict_compl_support`,
[Sta, Tag 02OS], restricted to `U` by `isIso_restrict_of_le`) and the restriction of a composite
being the composite of the restrictions (`morphismRestrict_comp`). -/
theorem isIso_composite_restrict_of_centers_disjoint :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (U : X.Opens),
      (∀ i : Fin S.length, Disjoint (((S.center i).support : Set (S.stage i.castSucc)))
        (S.stageMap i.castSucc ⁻¹' (U : Set X))) →
      IsIso (S.composite ∣_ U)
  | _, nil X, U, _ => by
    change IsIso ((𝟙 X : X ⟶ X) ∣_ U)
    infer_instance
  | _, cons X D rest, U, hZ => by
    have hd : Disjoint (D.support : Set X) (U : Set X) := hZ ⟨0, Nat.succ_pos _⟩
    have h0 : U ≤ D.support.compl := fun x hx => Set.disjoint_left.1 hd.symm hx
    have hrest : ∀ i : Fin rest.length,
        Disjoint (((rest.center i).support : Set (rest.stage i.castSucc)))
          (rest.stageMap i.castSucc ⁻¹'
            ((D.blowUpπ ⁻¹ᵁ U : D.blowUp.Opens) : Set D.blowUp)) := by
      intro i
      rw [Set.disjoint_left]
      intro y hy hy'
      exact Set.disjoint_left.1 (hZ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) hy hy'
    have ih := isIso_composite_restrict_of_centers_disjoint rest (D.blowUpπ ⁻¹ᵁ U) hrest
    have hπ := IdealSheafData.blowUp.isIso_π_restrict_compl_support D
    have h1 : IsIso (D.blowUpπ ∣_ U) := isIso_restrict_of_le D.blowUpπ h0
    exact isIso_restrict_comp rest.composite D.blowUpπ U

/-- Deleting the empty blow-ups does not change the isomorphism locus: the composite of
`S.eraseEmpty` is the composite of `S` after the isomorphism `eraseEmptyLastHom` of the last
stages. -/
theorem isIso_eraseEmpty_composite_restrict (S : BlowUpSequence X) (U : X.Opens)
    [IsIso (S.composite ∣_ U)] : IsIso (S.eraseEmpty.composite ∣_ U) :=
  have : IsIso ((S.eraseEmptyLastHom ≫ S.composite) ∣_ U) :=
    isIso_restrict_comp S.eraseEmptyLastHom S.composite U
  isIso_restrict_congr (eraseEmptyLastHom_comp_composite S) U

end Hironaka.Sequence
