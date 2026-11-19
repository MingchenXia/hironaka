/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso

/-!
# The exceptional set of a morphism

The exceptional set of a birational morphism `g : X' → X` is the set of points `x' ∈ X'` at which
`g` is not a local isomorphism, denoted `Ex(g)` [Kol07, Definition 25].  Here "local isomorphism
at `x'`" is read as: there is an open `U' ∋ x'` on which `g` restricts to an open immersion,
`IsOpenImmersion (U'.ι ≫ g)`.  Mathlib's `IsLocalIso g` is the global property (every point has
such a neighbourhood), so `Ex(g) = ∅ ↔ IsLocalIso g` (`exceptionalSet_eq_empty_iff`).

For a blow-up `π : B_Z X ⟶ X` the exceptional set is contained in the exceptional divisor
`F = π⁻¹(Z)` ([Sta, Tag 02OS]; the easy half of Kollár's remark that `Ex(Π) = Ex_tot(Π)` for a
sequence of nontrivial blow-ups [Kol07, Definition 25]): off `Z` the blow-up map is an
isomorphism, so a point of `B` over `X ∖ Z` lies in the open `π⁻¹(X ∖ Z)`, on which `π` is the
isomorphism `π ∣_ (X ∖ Z)` followed by the open immersion of `X ∖ Z`, hence an open immersion.
This is `exceptionalSet_subset_support_comap`, stated for any morphism that is an isomorphism over
the complement of the centre; `Hironaka.Scheme.BlowUp.ExceptionalSetSupport` applies it to the
monoidal transformation of the vocabulary.  The reverse inclusion for a blow-up along a smooth
centre of codimension at least two (the other half of Kollár's remark) is proved in
`Hironaka.Scheme.BlowUp.ExceptionalSetSmooth` and `ExceptionalSetSmoothCodim`.

The definition is placed in Mathlib's namespace `AlgebraicGeometry.Scheme.Hom` so that it reads
`g.exceptionalSet`; nothing here assumes `g` birational, the source's standing hypothesis, which
is not needed for the definition or for these lemmas.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory TopologicalSpace

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The exceptional set** of `f` [Kol07, Definition 25]: the set of points at which `f` is not a
local isomorphism — points with no open neighbourhood `U` such that `U.ι ≫ f` is an open
immersion. -/
def exceptionalSet : Set X :=
  {x | ¬ ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f)}

/-- Membership in the exceptional set, by definition. -/
theorem mem_exceptionalSet_iff {x : X} :
    x ∈ f.exceptionalSet ↔ ¬ ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) :=
  Iff.rfl

/-- A point is not exceptional iff `f` is an open immersion on some open neighbourhood of it. -/
theorem notMem_exceptionalSet_iff {x : X} :
    x ∉ f.exceptionalSet ↔ ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) :=
  not_not

/-- The comparison with Mathlib's global notion: `f` is a local isomorphism (`IsLocalIso f`,
source-locally an open immersion) iff its exceptional set is empty. -/
theorem exceptionalSet_eq_empty_iff : f.exceptionalSet = ∅ ↔ IsLocalIso f := by
  rw [isLocalIso_iff, Set.eq_empty_iff_forall_notMem]
  exact forall_congr' fun x => notMem_exceptionalSet_iff f

/-- A local isomorphism has empty exceptional set. -/
theorem exceptionalSet_eq_empty [IsLocalIso f] : f.exceptionalSet = ∅ :=
  (exceptionalSet_eq_empty_iff f).mpr ‹_›

/-- A point over an open `V` of the target on which `f` restricts to an isomorphism is not
exceptional: on `f⁻¹(V)` the morphism is `f ∣_ V` followed by the open immersion `V.ι`. -/
theorem notMem_exceptionalSet_of_isIso_restrict {V : Y.Opens} [IsIso (f ∣_ V)] {x : X}
    (hx : f x ∈ V) : x ∉ f.exceptionalSet := by
  rw [notMem_exceptionalSet_iff]
  refine ⟨f ⁻¹ᵁ V, hx, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

/-- If `f` is an isomorphism over an open `V`, its exceptional set lies over the complement. -/
theorem exceptionalSet_subset_compl_preimage {V : Y.Opens} [IsIso (f ∣_ V)] :
    f.exceptionalSet ⊆ ((f ⁻¹ᵁ V : Set X))ᶜ :=
  fun _ hx hxV => notMem_exceptionalSet_of_isIso_restrict f hxV hx

/-- **The exceptional set lies in the exceptional divisor** `|F| = |π⁻¹(Z)|`, the support of the
inverse image ideal sheaf `I·𝒪_B`, for any morphism `π : B ⟶ X` that is an isomorphism over the
complement of the centre `Z = V(I)` ([Sta, Tag 02OS]; the easy half of `Ex(Π) = Ex_tot(Π)` in
[Kol07, Definition 25]). -/
theorem exceptionalSet_subset_support_comap {B : Scheme.{u}} (π : B ⟶ X) (I : X.IdealSheafData)
    [IsIso (π ∣_ I.support.compl)] : π.exceptionalSet ⊆ ((I.comap π).support : Set B) := by
  intro x hx
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  by_contra h
  exact notMem_exceptionalSet_of_isIso_restrict π (V := I.support.compl) h hx

end AlgebraicGeometry.Scheme.Hom
