/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Hironaka.Algebra.Local.Defs
import Hironaka.Algebra.Local.Order
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-!
# The order of an ideal sheaf at a point

[Kol07, Definition 47]: for an ideal sheaf `I` on a scheme `X` and a point `x`,
`ord_x I := max {r : 𝔪_xʳ 𝒪_{X,x} ⊇ I 𝒪_{X,x}}`, the order of vanishing of `I` at `x`;
[Hau03, Appendix A]: the order of `I` at `a` is the maximal power of `𝔪_a` containing the stalk
`I_a`, and "the zero ideal has infinite order". Here `I_x = stalkIdeal I x ⊆ 𝒪_{X,x}` is the stalk
of the ideal sheaf and the order `ord I x` is valued in `ℕ∞`.

* `ord I x` is Hironaka's order `ν(J_x)`, in which the main theorems are stated. It is the order
  of the ideal `I_x` in the local ring `𝒪_{X,x}` (`IsLocalRing.ord`; `ord_eq_ord_stalkIdeal`,
  `le_ord_iff`).
* `ord_x I = ∞` iff `I_x = 0` (Krull's intersection theorem in the Noetherian local ring
  `𝒪_{X,x}`, through `ord_eq_top_iff` of `Hironaka/Algebra/Local/Order.lean`); `ord_x I = 0` iff
  `x ∉ V(I) = Supp 𝒪/I`; `ord_x I ≥ 1` iff `x ∈ V(I)`. The link is
  `mem_support_iff_stalkIdeal_le_maximalIdeal`: `x` lies in the support exactly when the stalk
  ideal is proper, every section of `I` over an affine neighbourhood being a non-unit at `x`
  (Mathlib's `mem_zeroLocus_iff`, `Scheme.mem_basicOpen`).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open IsLocalRing TopologicalSpace

universe u

variable {X : Scheme.{u}}

variable (I : X.IdealSheafData) (x : X)

/-- The order at `x` is the order (`IsLocalRing.ord`) of the stalk ideal `I_x` in the local
ring `𝒪_{X,x}`. -/
theorem ord_eq_ord_stalkIdeal : I.ord x = IsLocalRing.ord (I.stalkIdeal x) := by
  unfold ord IsLocalRing.ord
  rw [iSup_subtype', ← sSup_range]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_range, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨m, rfl, hm⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, rfl, hm⟩

/-- Kollár's defining property ([Kol07, Definition 47]): `r ≤ ord_x I` iff `I_x ⊆ 𝔪_xʳ`. -/
theorem le_ord_iff {r : ℕ} :
    (r : ℕ∞) ≤ I.ord x ↔ I.stalkIdeal x ≤ maximalIdeal (X.presheaf.stalk x) ^ r := by
  rw [ord_eq_ord_stalkIdeal, IsLocalRing.le_ord_iff]

/-- The order is antitone in the ideal sheaf. -/
theorem ord_anti {I J : X.IdealSheafData} (h : I ≤ J) (x : X) : J.ord x ≤ I.ord x := by
  rw [ord_eq_ord_stalkIdeal, ord_eq_ord_stalkIdeal]
  exact IsLocalRing.ord_anti (stalkIdeal_mono h x)

/-- A point lies in the support `V(I)` exactly when the stalk ideal is proper, i.e. contained in
the maximal ideal of `𝒪_{X,x}`: every section of `I` over an affine neighbourhood is a non-unit at
`x` (Mathlib's `mem_zeroLocus_iff` and `Scheme.mem_basicOpen`). -/
theorem mem_support_iff_stalkIdeal_le_maximalIdeal :
    x ∈ I.support ↔ I.stalkIdeal x ≤ maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [mem_support_iff_of_mem hxU, mem_zeroLocus_iff, stalkIdeal_eq_map_germ I U hxU,
    Ideal.map_le_iff_le_comap]
  constructor
  · intro h f hf
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => h f hf ((Scheme.mem_basicOpen X f x hxU).mpr hu)
  · intro h f hf hxf
    have := h hf
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at this
    exact this ((Scheme.mem_basicOpen X f x hxU).mp hxf)

/-- The order vanishes exactly off the support `V(I) = Supp 𝒪_X/I`. -/
theorem ord_eq_zero_iff : I.ord x = 0 ↔ x ∉ I.support := by
  rw [ord_eq_ord_stalkIdeal, IsLocalRing.ord_eq_zero_iff,
    mem_support_iff_stalkIdeal_le_maximalIdeal]
  constructor
  · intro h hle
    rw [h] at hle
    exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)
  · intro h
    by_contra hne
    exact h ((le_maximalIdeal hne))

/-- `ord_x I ≥ 1` exactly on the support `V(I)`. -/
theorem one_le_ord_iff : 1 ≤ I.ord x ↔ x ∈ I.support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, ← pow_one (maximalIdeal (X.presheaf.stalk x)),
    ← le_ord_iff, Nat.cast_one]

/-- "The zero ideal has infinite order" ([Hau03, Appendix A]; Krull's intersection theorem in the
Noetherian local ring `𝒪_{X,x}`): `ord_x I = ∞` iff `I_x = 0`. -/
theorem ord_eq_top_iff [IsLocallyNoetherian X] : I.ord x = ⊤ ↔ I.stalkIdeal x = ⊥ := by
  rw [ord_eq_ord_stalkIdeal, IsLocalRing.ord_eq_top_iff]

/-- The order of the unit ideal sheaf is `0` everywhere. -/
@[simp]
theorem ord_top : (⊤ : X.IdealSheafData).ord x = 0 := by
  rw [ord_eq_zero_iff, support_top]
  exact not_false

/-- The order of the zero ideal sheaf is `∞` everywhere. -/
theorem ord_bot : (⊥ : X.IdealSheafData).ord x = ⊤ := by
  rw [ord_eq_ord_stalkIdeal]
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hxU, ideal_bot, Pi.bot_apply, Ideal.map_bot,
    IsLocalRing.ord_bot]

end AlgebraicGeometry.Scheme.IdealSheafData
