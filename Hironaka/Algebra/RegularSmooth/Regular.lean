/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Defs
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Regular points of a scheme: basic facts

Hironaka's simple points (`X.IsRegularAt x`: the stalk `𝒪_{X,x}` is a regular local ring), the
non-singular schemes (`IsRegular X`) and the singular locus `X.singularLocus`
[Hir64, Introduction, p. 112; Ch. I, p. 163], in which the main theorems are stated: their
unfolding lemmas, and the characterization of `IsRegular X` as the emptiness of the singular locus.
Over a field these notions are compared with Mathlib's smooth locus in
`Hironaka/Algebra/RegularSmooth/RegularSmoothEquiv.lean`: smooth at `x` implies `𝒪_{X,x}` regular
[Sta, Tag 00TT], and the converse holds over a perfect field [Sta, Tag 00TV].

The affine-local form (the reduction "the question is local" of [Sta, Tag 038X]): on an affine
open `U ∋ x`, with `𝔮 = hU.primeIdealOf ⟨x, hx⟩` the prime of `Γ(X, U)` corresponding to `x`,
the stalk `𝒪_{X,x}` is the localization `Γ(X, U)_𝔮` (`IsAffineOpen.isLocalization_stalk`), so
`X` is regular at `x` iff `Γ(X, U)_𝔮` is a regular local ring. Regularity of a local ring is
invariant under ring isomorphism (`IsRegularLocalRing.of_ringEquiv`), which is all the proof uses.
-/

public section

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

theorem isRegularAt_iff {x : X} : X.IsRegularAt x ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

theorem mem_singularLocus_iff {x : X} : x ∈ X.singularLocus ↔ ¬ X.IsRegularAt x :=
  Iff.rfl

/-- The affine-local form of regularity at a point: on an affine open `U ∋ x` with
`𝔮 = hU.primeIdealOf ⟨x, hx⟩` the prime of `x`, `X` is regular at `x` iff the localization
`Γ(X, U)_𝔮` is a regular local ring, because `𝒪_{X,x} ≅ Γ(X, U)_𝔮`
(`IsAffineOpen.isLocalization_stalk`) and regularity is invariant under ring isomorphism. -/
theorem isRegularAt_iff_isRegularLocalRing_localization {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) :
    X.IsRegularAt x ↔
      IsRegularLocalRing (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  let e := IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)
  exact ⟨fun h => haveI : IsRegularLocalRing (X.presheaf.stalk x) := h
      IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv,
    fun _ => IsRegularLocalRing.of_ringEquiv e.toRingEquiv⟩

end Scheme

variable {X : Scheme.{u}}

theorem isRegular_iff : IsRegular X ↔ ∀ x : X, X.IsRegularAt x :=
  ⟨fun h => h.isRegularAt, fun h => ⟨h⟩⟩

theorem isRegular_iff_singularLocus_eq_empty : IsRegular X ↔ X.singularLocus = ∅ := by
  simp only [isRegular_iff, Set.eq_empty_iff_forall_notMem, Scheme.mem_singularLocus_iff, not_not]

end AlgebraicGeometry
