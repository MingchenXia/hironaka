/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Topology.JacobsonSpace
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-!
# Ideal sheaves are determined by their stalks: the stalk calculus

The stalk `J_x ⊆ 𝒪_{X,x}` of an ideal sheaf (`stalkIdeal`) is the image of `J(U)` under the germ
map for any affine `U ∋ x` (`stalkIdeal_eq_map_germ`), and `𝒪_{X,x}` is the localization of
`Γ(X, U)` at the prime of `x` (Mathlib's `IsAffineOpen.isLocalization_stalk`).  Since an
inclusion of ideals holds as soon as it holds after localizing at every maximal ideal (Mathlib's
`Ideal.le_of_localization_maximal`), **an inclusion of ideal sheaves can be checked on stalks**
(`le_of_stalkIdeal_le`, `ext_stalkIdeal`), and on a Jacobson scheme at the
closed points alone (`le_of_forall_stalkIdeal_le_of_isClosed`).  The stalk is compatible with the
operations used in the divisor calculus: products, powers, suprema, finite products, and the
colon by an invertible ideal sheaf (`stalkIdeal_colon_of_isInvertible`, Mathlib's colon commutes
with localization for finitely generated divisors, `map_colon_of_fg`).

These are the tools for computing saturations and orders of ideal sheaves on stalks throughout
the blow-up sequences of the resolution.

## Main declarations

* `stalkIdeal_top`, `stalkIdeal_bot`, `stalkIdeal_mul`, `stalkIdeal_pow`, `ideal_iSup'`,
  `stalkIdeal_iSup'` / `stalkIdeal_iSup`, `stalkIdeal_finset_prod`, `stalkIdeal_colon_le`,
  `stalkIdeal_colon_of_isInvertible`, `stalkIdeal_saturate_of_isInvertible`.
* `le_of_forall_stalkIdeal_le_of_isMaximal`, `le_of_stalkIdeal_le`,
  `le_of_forall_stalkIdeal_le_of_isClosed`, `ext_stalkIdeal`.  The last two but one
  and the last are one-line corollaries of `le_of_stalkIdeal_le` and `ext_stalkIdeal` of
  `Hironaka.Scheme.BlowUp.Descent`, kept under these names.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The stalk of the unit ideal sheaf is the unit ideal. -/
theorem stalkIdeal_top (x : X) : (⊤ : X.IdealSheafData).stalkIdeal x = ⊤ := by
  obtain ⟨U, hx⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hx]
  exact Ideal.map_top _

/-- The stalk of the zero ideal sheaf is zero. -/
theorem stalkIdeal_bot (x : X) : (⊥ : X.IdealSheafData).stalkIdeal x = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun U hx => ?_)
  rw [show (⊥ : X.IdealSheafData).ideal U = ⊥ from rfl, Ideal.map_bot]

/-- The stalk of a product is the product of the stalks. -/
theorem stalkIdeal_mul (I J : X.IdealSheafData) (x : X) :
    (I * J).stalkIdeal x = I.stalkIdeal x * J.stalkIdeal x := by
  obtain ⟨U, hx⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hx, stalkIdeal_eq_map_germ I U hx, stalkIdeal_eq_map_germ J U hx,
    ideal_mul, Pi.mul_apply, Ideal.map_mul]

/-- The stalk of a power is the power of the stalk. -/
theorem stalkIdeal_pow (I : X.IdealSheafData) (n : ℕ) (x : X) :
    (I ^ n).stalkIdeal x = I.stalkIdeal x ^ n := by
  obtain ⟨U, hx⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hx, stalkIdeal_eq_map_germ I U hx, ideal_pow, Pi.pow_apply,
    Ideal.map_pow]

/-- Mathlib's `ideal_iSup` for a `Sort`-indexed supremum (a bounded supremum `⨆ i ∈ s` is one). -/
theorem ideal_iSup' {ι : Sort*} (I : ι → X.IdealSheafData) :
    (⨆ i, I i).ideal = ⨆ i, (I i).ideal := by
  have h1 : (⨆ i, I i) = ⨆ i : PLift ι, I i.down := (iSup_plift_down I).symm
  rw [h1, ideal_iSup]
  exact iSup_plift_down fun i => (I i).ideal

/-- The stalk of a `Sort`-indexed supremum is the supremum of the stalks. -/
theorem stalkIdeal_iSup' {ι : Sort*} (I : ι → X.IdealSheafData) (x : X) :
    (⨆ i, I i).stalkIdeal x = ⨆ i, (I i).stalkIdeal x := by
  obtain ⟨U, hx⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hx, ideal_iSup', iSup_apply, Ideal.map_iSup]
  exact iSup_congr fun i => (stalkIdeal_eq_map_germ (I i) U hx).symm

/-- The stalk of a supremum is the supremum of the stalks (the `Type`-indexed instance of
`stalkIdeal_iSup'`). -/
theorem stalkIdeal_iSup {ι : Type*} (I : ι → X.IdealSheafData) (x : X) :
    (⨆ i, I i).stalkIdeal x = ⨆ i, (I i).stalkIdeal x :=
  stalkIdeal_iSup' I x

/-- The stalk of a finite product of ideal sheaves is the product of the stalks
(`stalkIdeal_mul` iterated; the empty product is the unit ideal, `stalkIdeal_top`). -/
@[simp]
theorem stalkIdeal_finset_prod {ι : Type*} (s : Finset ι) (g : ι → X.IdealSheafData) (x : X) :
    (∏ i ∈ s, g i).stalkIdeal x = ∏ i ∈ s, (g i).stalkIdeal x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top]
    exact stalkIdeal_top x
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, stalkIdeal_mul, ih]

/-- The stalk of a colon is contained in the colon of the stalks. -/
theorem stalkIdeal_colon_le (I K : X.IdealSheafData) (x : X) :
    (I.colon K).stalkIdeal x ≤
      (I.stalkIdeal x).colon (K.stalkIdeal x : Set (X.presheaf.stalk x)) := by
  intro r hr
  rw [Submodule.mem_colon]
  intro s hs
  have h := stalkIdeal_mono (colon_mul_le I K) x
  rw [stalkIdeal_mul] at h
  exact h (Ideal.mul_mem_mul hr hs)

/-- For an invertible `K` the stalk of the colon is the colon of the stalks (the colon by a
finitely generated ideal commutes with localization). -/
theorem stalkIdeal_colon_of_isInvertible (I : X.IdealSheafData) {K : X.IdealSheafData}
    (hK : K.IsInvertible) (x : X) :
    (I.colon K).stalkIdeal x =
      (I.stalkIdeal x).colon (K.stalkIdeal x : Set (X.presheaf.stalk x)) := by
  obtain ⟨U, hx⟩ := exists_affineOpens_mem x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := U.2.isLocalization_stalk ⟨x, hx⟩
  rw [stalkIdeal_eq_map_germ _ U hx, stalkIdeal_eq_map_germ I U hx, stalkIdeal_eq_map_germ K U hx,
    ideal_colon_of_isInvertible I K hK U]
  exact map_colon_of_fg (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _
    (hK.ideal K U).fg

/-- For an invertible `K` the stalk of the saturation `⋃ᵢ (I : Kⁱ)` is the saturation of the
stalks. -/
theorem stalkIdeal_saturate_of_isInvertible (I : X.IdealSheafData) {K : X.IdealSheafData}
    (hK : K.IsInvertible) (x : X) :
    (I.saturate K).stalkIdeal x =
      ⨆ i : ℕ, (I.stalkIdeal x).colon
        ((K.stalkIdeal x ^ i : Ideal (X.presheaf.stalk x)) : Set (X.presheaf.stalk x)) := by
  rw [saturate, stalkIdeal_iSup]
  refine iSup_congr fun i => ?_
  rw [stalkIdeal_colon_of_isInvertible I (isInvertible_pow hK i), stalkIdeal_pow]

/-- The core of `le_of_stalkIdeal_le`: an inclusion of ideal sheaves holds as soon as it
holds at the stalks of the points `hU.fromSpec ⟨P⟩` of the MAXIMAL ideals `P` of `Γ(X, U)`, `U`
affine — `𝒪_{X,x}` is the localization of `Γ(X, U)` at the prime of `x` for an affine `U ∋ x`, and
an inclusion of ideals holds after localizing at every maximal ideal (Mathlib's
`Ideal.le_of_localization_maximal`). -/
theorem le_of_forall_stalkIdeal_le_of_isMaximal {I J : X.IdealSheafData}
    (h : ∀ (U : X.affineOpens) (P : Ideal Γ(X, U)) (hP : P.IsMaximal),
      I.stalkIdeal (U.2.fromSpec ⟨P, hP.isPrime⟩) ≤ J.stalkIdeal (U.2.fromSpec ⟨P, hP.isPrime⟩)) :
    I ≤ J := by
  intro U
  refine Ideal.le_of_localization_maximal fun P hP => ?_
  have hU : IsAffineOpen U.1 := U.2
  have hx : hU.fromSpec ⟨P, hP.isPrime⟩ ∈ U.1 := by
    have : hU.fromSpec ⟨P, hP.isPrime⟩ ∈ Set.range hU.fromSpec := Set.mem_range_self _
    rwa [hU.range_fromSpec] at this
  let _ := X.presheaf.algebra_section_stalk ⟨hU.fromSpec ⟨P, hP.isPrime⟩, hx⟩
  have hloc : IsLocalization P.primeCompl (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) :=
    hU.isLocalization_stalk' ⟨P, hP.isPrime⟩ hx
  let e := IsLocalization.algEquiv P.primeCompl
    (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) (Localization.AtPrime P)
  have hmap : ∀ K : X.IdealSheafData,
      (K.ideal U).map (algebraMap Γ(X, U) (Localization.AtPrime P)) =
        (K.stalkIdeal (hU.fromSpec ⟨P, hP.isPrime⟩)).map
          (e : X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩) →+* Localization.AtPrime P) := by
    intro K
    rw [stalkIdeal_eq_map_germ K U hx, Ideal.map_map]
    congr 1
    exact RingHom.ext fun r => (e.commutes r).symm
  rw [hmap I, hmap J]
  exact Ideal.map_mono (h U P hP)

/-- The closed-point form of `le_of_stalkIdeal_le`: on a Jacobson scheme — every scheme
locally of finite type over a field, Mathlib's `LocallyOfFiniteType.jacobsonSpace` — an inclusion
of ideal sheaves can be checked at the closed points: the maximal ideals of `Γ(X, U)`, `U` affine,
are the closed points of `Spec Γ(X, U)`, and a closed point of an open subset of a Jacobson space
is closed in the space (`Topology.IsOpenEmbedding.preimage_closedPoints`). -/
theorem le_of_forall_stalkIdeal_le_of_isClosed [JacobsonSpace X] {I J : X.IdealSheafData}
    (h : ∀ x : X, IsClosed ({x} : Set X) → I.stalkIdeal x ≤ J.stalkIdeal x) : I ≤ J := by
  refine le_of_forall_stalkIdeal_le_of_isMaximal fun U P hP => h _ ?_
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hemb := U.2.fromSpec.isOpenEmbedding
  have hP' : (⟨P, hP.isPrime⟩ : PrimeSpectrum Γ(X, U)) ∈ closedPoints (Spec Γ(X, U)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hP
  rw [← hemb.preimage_closedPoints] at hP'
  exact hP'

end AlgebraicGeometry.Scheme.IdealSheafData
