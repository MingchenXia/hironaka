/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Reduced
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Scheme.BlowUpSequence.ClosedImmersionStalk
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Smooth pull-back of a reduced closed subscheme is reduced

Włodarczyk's embedded desingularization "commutes with smooth morphisms" ([Wlo05, Theorem 1.0.2,
(d)]; [Wlo05, §4.1]). The embedded resolution of `Hironaka/Resolution/` divides by the REDUCED
ideal `I_Γ = vanishingIdeal Γ` of the absorbed strict transforms; transporting it along a smooth
`h : X' → X` needs `(vanishingIdeal Γ).comap h = vanishingIdeal (h⁻¹ Γ)`, i.e. that the pull-back
of a reduced closed subscheme along a smooth morphism is reduced. In characteristic zero this is
[Sta, Tag 033B] read through Mathlib's `GeometricallyReduced`: a smooth morphism is geometrically
reduced (its fibres over fields are smooth over a field, hence regular, hence reduced:
`isRegularLocalRing_stalk` and `IsLocalRing.isDomain_of_isRegularLocalRing`), and a flat
geometrically reduced morphism from a reduced scheme with finitely many irreducible components
has a reduced source (Mathlib's
`GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents`).

* `geometricallyReduced_of_smooth`: smooth morphisms are geometrically reduced.
* `isReduced_subscheme_of_radical_eq_self`: a radical ideal sheaf cuts out a reduced subscheme
  (the converse of `AlgebraicGeometry.radical_eq_self_of_isReduced_subscheme`).
* `isReduced_comap_subscheme_of_smooth`: the smooth pull-back of a reduced closed subscheme of a
  Noetherian scheme is reduced.
* `comap_vanishingIdeal_of_smooth`: `(vanishingIdeal S).comap h = vanishingIdeal (h⁻¹ S)`.

Used for the functoriality of the embedded resolution under smooth morphisms
(`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedPullbackTools.lean`, `EmbeddedFunctorSplit.lean`) and
for normal crossings (`Hironaka/Resolution/Algebraic/Snc/SncLocal.lean`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka.Smooth

variable {X Y : Scheme.{u}}

/-- A smooth morphism is geometrically reduced: every fibre product with the spectrum of a field
is smooth over that field, so its local rings are regular (`isRegularLocalRing_stalk`), hence
domains, hence reduced. -/
instance (priority := 900) geometricallyReduced_of_smooth (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f where
  geometrically_isReduced := by
    intro K _ y Z fst snd hpb
    have hsm : Smooth snd := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb ‹Smooth f›
    have : ∀ z : Z, IsReduced (Z.presheaf.stalk z) := fun z => by
      have := isRegularLocalRing_stalk snd z
      have := IsLocalRing.isDomain_of_isRegularLocalRing (Z.presheaf.stalk z)
      infer_instance
    exact isReduced_of_isReduced_stalk Z

/-- A radical ideal sheaf cuts out a reduced closed subscheme: the stalks of the subscheme are the
quotients of the ambient stalks by the (radical) stalk ideals
(`AlgebraicGeometry.stalkEquivQuotient_of_isClosedImmersion`,
`Hironaka.Sequence.stalkIdeal_radical`). -/
theorem isReduced_subscheme_of_radical_eq_self (E : X.IdealSheafData) (hE : E.radical = E) :
    IsReduced E.subscheme := by
  have : ∀ y : E.subscheme, IsReduced (E.subscheme.presheaf.stalk y) := fun y => by
    have hrad : (E.stalkIdeal (E.subschemeι y)).IsRadical := by
      have h := Hironaka.Sequence.stalkIdeal_radical E (E.subschemeι y)
      rw [hE] at h
      exact Ideal.radical_eq_iff.mp h.symm
    have hq : IsReduced (X.presheaf.stalk (E.subschemeι y) ⧸ E.stalkIdeal (E.subschemeι y)) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp hrad
    have e := stalkEquivQuotient_of_isClosedImmersion E.subschemeι y
    rw [Scheme.IdealSheafData.ker_subschemeι] at e
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  exact isReduced_of_isReduced_stalk E.subscheme

/-- The pull-back of a reduced closed subscheme of a Noetherian scheme along a smooth morphism is
reduced: the fibre product `h⁻¹(V(I)) = V(I) ×_X X'` is the source of the flat, geometrically
reduced base change of `h`, over the reduced `V(I)` with finitely many irreducible components
(Mathlib's `GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents`); the subscheme
of `I.comap h` is that fibre product (`comapIso`). -/
theorem isReduced_comap_subscheme_of_smooth [NoetherianSpace X] (h : Y ⟶ X) [Smooth h]
    (I : X.IdealSheafData) [IsReduced I.subscheme] : IsReduced (I.comap h).subscheme := by
  have hN : NoetherianSpace I.subscheme := Hironaka.Resolution.noetherianSpace_subscheme I
  have hfin : Finite (irreducibleComponents I.subscheme) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have : IsReduced (pullback h I.subschemeι) :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
      (pullback.snd h I.subschemeι)
  exact isReduced_of_isOpenImmersion (I.comapIso h).hom

/-- The pull-back along a smooth morphism of the reduced ideal of a closed set is the reduced ideal
of the preimage (the compatibility with smooth morphisms behind [Wlo05, §4.1]). -/
theorem comap_vanishingIdeal_of_smooth [NoetherianSpace X] (h : Y ⟶ X) [Smooth h]
    (S : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal S).comap h =
      Scheme.IdealSheafData.vanishingIdeal (S.preimage h.continuous) := by
  have hred : IsReduced (Scheme.IdealSheafData.vanishingIdeal S).subscheme :=
    isReduced_subscheme_of_radical_eq_self _ (by
      rw [← Scheme.IdealSheafData.vanishingIdeal_support,
        Hironaka.Sequence.support_vanishingIdeal_eq])
  have hred' := isReduced_comap_subscheme_of_smooth h (Scheme.IdealSheafData.vanishingIdeal S)
  rw [← radical_eq_self_of_isReduced_subscheme
    ((Scheme.IdealSheafData.vanishingIdeal S).comap h),
    ← Scheme.IdealSheafData.vanishingIdeal_support, Scheme.IdealSheafData.support_comap,
    Hironaka.Sequence.support_vanishingIdeal_eq]

end Hironaka.Smooth
