/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Algebra.Local.RegularSystemCommon
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# The coordinates of Kollár's proof of Theorem 92 at a point of the cosupport

The proof of Theorem 92 ([Kol07, 95]) opens by choosing coordinates at a point `p` of the
cosupport: local sections `x₁, x₁' ∈ MC(I)` with `H = (x₁ = 0)` and `H' = (x₁' = 0)`, further
coordinates `x₂, …, x_{s+1}` with `Eⁱ = (x_{i+1} = 0)` for the components of `E`, and general
`x_{s+2}, …, xₙ`, such that both `x₁, x₂, …, xₙ` and `x₁', x₂, …, xₙ` are local coordinate systems.
This file proves that statement (`exists_coordinates`).

**The argument.** At `p ∈ cosupp(I, m)` the hypersurface of maximal contact `H` passes through
`p` (`H ⊆ MC(I)` as ideal sheaves and `p ∈ V(MC(I))`, `coe_support_MC`), so the simple normal
crossings of `H + E` at `p` ([Kol07, Definition 24]) give a regular system of parameters `z` of
`𝒪_{X,p}` with `H_p = (z_{p₀})` and `Eⁱ_p = (z_{c(i)})` for the components through `p`, `c`
injective: Kollár's `x₁ = z_{p₀}` and `x_{i+1} = z_{c(i)}`. Likewise `H' + E` gives `z'` with
`H'_p = (z'_{p₀'})`, `Eⁱ_p = (z'_{c'(i)})`. The two equations of `Eⁱ_p` differ by a unit, so the
classes `ē_i` and `ē'_i` in `𝔪/𝔪²` span the same subspace `U`, and the class of `x₁' = z'_{p₀'}`
is not in `U` (it is a basis vector of the second basis outside the `c'`-indices). The ring-level
lemma `exists_cons_regularSystem_common` then produces `y` containing the `Eⁱ`-coordinates such
that `(x₁, y)` and `(x₁', y)` are both regular systems of parameters; `x₁, x₁' ∈ MC(I)_p` because
`H_p, H'_p ⊆ MC(I)_p`.
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing Scheme

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

section Support

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

include n in
/-- A hypersurface of maximal contact (static form) passes through every point of `cosupp(I, m)`:
`H ⊆ MC(I)` and `p ∈ V(MC(I))` ([Kol07, Definition 79]). -/
theorem mem_support_of_isMaximalContact {I : X.IdealSheafData} {m : ℕ} (hm : 1 ≤ m)
    {H : X.IdealSheafData} (hH : IsMaximalContact f I m H) {p : X} (hp : (m : ℕ∞) ≤ I.ord p) :
    p ∈ H.support := by
  have hMC : p ∈ (MC f I m).support := by
    have h := coe_support_MC f n I hm
    have : p ∈ ((MC f I m).support : Set X) := by rw [h]; exact hp
    exact this
  exact support_antitone hH hMC

end Support

section Coordinates

variable {p : X}

/-- Two generators of one principal ideal of a domain have classes spanning the same line of the
cotangent space. -/
theorem span_toCotangent_eq_of_span_eq [IsRegularLocalRing (X.presheaf.stalk p)]
    {a a' : X.presheaf.stalk p} (ha : a ∈ maximalIdeal (X.presheaf.stalk p))
    (ha' : a' ∈ maximalIdeal (X.presheaf.stalk p)) (h : Ideal.span {a} = Ideal.span {a'}) :
    Submodule.span (ResidueField (X.presheaf.stalk p))
        {(maximalIdeal (X.presheaf.stalk p)).toCotangent ⟨a, ha⟩} =
      Submodule.span (ResidueField (X.presheaf.stalk p))
        {(maximalIdeal (X.presheaf.stalk p)).toCotangent ⟨a', ha'⟩} := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  -- `a * u = a'`
  have hsub : (⟨a', ha'⟩ : maximalIdeal (X.presheaf.stalk p)) =
      (u : X.presheaf.stalk p) • ⟨a, ha⟩ := by
    ext; simp [← hu, mul_comm]
  have hclass : (maximalIdeal (X.presheaf.stalk p)).toCotangent ⟨a', ha'⟩ =
      IsLocalRing.residue (X.presheaf.stalk p) u •
        (maximalIdeal (X.presheaf.stalk p)).toCotangent ⟨a, ha⟩ := by
    rw [hsub, map_smul]
    exact (algebraMap_smul (ResidueField (X.presheaf.stalk p)) (u : X.presheaf.stalk p) _).symm
  rw [hclass, Submodule.span_singleton_smul_eq]
  exact u.isUnit.map (IsLocalRing.residue (X.presheaf.stalk p))

end Coordinates

section Main

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

include n in
/-- The coordinates of Kollár's proof of Theorem 92 ([Kol07, 95]): at a point `p` of
`cosupp(I, m)`, local sections `x₁, x₁' ∈ MC(I)_p` with `H_p = (x₁)`, `H'_p = (x₁')`, and
`y = (x₂, …, xₙ)` such that `(x₁, y)` and `(x₁', y)` are both regular systems of parameters and
every component `Eⁱ` of `E` through `p` is `(y_{c(i)} = 0)`, `c` injective. -/
theorem exists_coordinates (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m) (E : DivisorFamily X)
    (H H' : X.IdealSheafData) (hH : IsMaximalContact f I m H)
    (hH' : IsMaximalContact f I m H') (hHE : (E.append H).IsSnc) (hH'E : (E.append H').IsSnc)
    (p : X) (hp : (m : ℕ∞) ≤ I.ord p) :
    ∃ (d : ℕ) (x₁ x₁' : X.presheaf.stalk p) (y : Fin d → X.presheaf.stalk p),
      x₁ ∈ (MC f I m).stalkIdeal p ∧ x₁' ∈ (MC f I m).stalkIdeal p ∧
      H.stalkIdeal p = Ideal.span {x₁} ∧ H'.stalkIdeal p = Ideal.span {x₁'} ∧
      IsRegularSystemOfParameters (Fin.cons x₁ y) ∧
      IsRegularSystemOfParameters (Fin.cons x₁' y) ∧
      ∃ c : {i : E.ι // p ∈ (E.component i).support} → Fin d, Function.Injective c ∧
        ∀ i, (E.component i.1).stalkIdeal p = Ideal.span {y (c i)} := by
  classical
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg : IsRegularLocalRing (X.presheaf.stalk p) :=
    isRegularLocalRing_stalk f p
  have hpH : p ∈ H.support := mem_support_of_isMaximalContact f n hm hH hp
  have hpH' : p ∈ H'.support := mem_support_of_isMaximalContact f n hm hH' hp
  obtain ⟨d₁, z, hz, c, hcinj, hc⟩ := hHE.2 p
  obtain ⟨d₂, z', hz', c', hcinj', hc'⟩ := hH'E.2 p
  cases d₁ with
  | zero => exact (c ⟨toLex (Sum.inr PUnit.unit), hpH⟩).elim0
  | succ d =>
  set p₀ : Fin (d + 1) := c ⟨toLex (Sum.inr PUnit.unit), hpH⟩ with hp₀
  set p₀' : Fin d₂ := c' ⟨toLex (Sum.inr PUnit.unit), hpH'⟩ with hp₀'
  set T : Set (Fin (d + 1)) :=
    Set.range fun i : {i : E.ι // p ∈ (E.component i).support} =>
      c ⟨toLex (Sum.inl i.1), i.2⟩ with hT
  set T' : Set (Fin d₂) :=
    Set.range fun i : {i : E.ι // p ∈ (E.component i).support} =>
      c' ⟨toLex (Sum.inl i.1), i.2⟩ with hT'
  have hp₀T : p₀ ∉ T := by
    rintro ⟨i, hi⟩
    exact Sum.inl_ne_inr (toLex.injective (congrArg Subtype.val (hcinj hi)))
  have hHp : H.stalkIdeal p = Ideal.span {z p₀} := hc ⟨toLex (Sum.inr PUnit.unit), hpH⟩
  have hH'p : H'.stalkIdeal p = Ideal.span {z' p₀'} := hc' ⟨toLex (Sum.inr PUnit.unit), hpH'⟩
  have hcE : ∀ i : {i : E.ι // p ∈ (E.component i).support},
      (E.component i.1).stalkIdeal p = Ideal.span {z (c ⟨toLex (Sum.inl i.1), i.2⟩)} :=
    fun i => hc ⟨toLex (Sum.inl i.1), i.2⟩
  have hcE' : ∀ i : {i : E.ι // p ∈ (E.component i).support},
      (E.component i.1).stalkIdeal p = Ideal.span {z' (c' ⟨toLex (Sum.inl i.1), i.2⟩)} :=
    fun i => hc' ⟨toLex (Sum.inl i.1), i.2⟩
  have hzspan : maximalIdeal (X.presheaf.stalk p) = Ideal.span (Set.range z) := hz.1.symm
  have hz'span : maximalIdeal (X.presheaf.stalk p) = Ideal.span (Set.range z') := hz'.1.symm
  obtain ⟨b, hb⟩ := exists_basis_cotangentSpace_of_span_eq z hzspan hz.2
  obtain ⟨b', hb'⟩ := exists_basis_cotangentSpace_of_span_eq z' hz'span hz'.2
  have hx₁'m : z' p₀' ∈ maximalIdeal (X.presheaf.stalk p) := mem_maximalIdeal_of_eq_span hz'span p₀'
  -- the classes of the `Eⁱ`-equations span the same subspace in both systems
  have hspanT : Submodule.span (ResidueField (X.presheaf.stalk p)) (b '' T) =
      Submodule.span (ResidueField (X.presheaf.stalk p)) (b' '' T') := by
    rw [hT, hT', ← Set.range_comp, ← Set.range_comp, Submodule.span_range_eq_iSup,
      Submodule.span_range_eq_iSup]
    refine iSup_congr fun i => ?_
    rw [Function.comp_apply, Function.comp_apply, hb, hb']
    exact span_toCotangent_eq_of_span_eq _ _ (by rw [← hcE i, hcE' i])
  -- the class of `x₁'` is not among them
  have hv : (maximalIdeal (X.presheaf.stalk p)).toCotangent ⟨z' p₀', hx₁'m⟩ ∉
      Submodule.span (ResidueField (X.presheaf.stalk p)) (b '' T) := by
    rw [hspanT]
    intro hmem
    have hvb : b' p₀' = (maximalIdeal (X.presheaf.stalk p)).toCotangent ⟨z' p₀', hx₁'m⟩ := by
      rw [hb']
    rw [← hvb] at hmem
    have hsupp := b'.mem_span_image.mp hmem
    rw [b'.repr_self, Finsupp.support_single _ one_ne_zero, Finset.coe_singleton,
      Set.singleton_subset_iff] at hsupp
    obtain ⟨i, hi⟩ := hsupp
    exact Sum.inl_ne_inr (toLex.injective (congrArg Subtype.val (hcinj' hi)))
  obtain ⟨y, hyT, hy₁, hy₁'⟩ :=
    exists_cons_regularSystem_common z hzspan p₀ T hp₀T (z' p₀') hx₁'m b hb hv
  refine ⟨d, z p₀, z' p₀', y, ?_, ?_, hHp, hH'p, ⟨hy₁.symm, hz.2⟩, ⟨hy₁'.symm, hz.2⟩, ?_⟩
  · exact stalkIdeal_mono hH p (hHp ▸ Ideal.mem_span_singleton_self _)
  · exact stalkIdeal_mono hH' p (hH'p ▸ Ideal.mem_span_singleton_self _)
  · choose j hj using fun i : {i : E.ι // p ∈ (E.component i).support} =>
      hyT (c ⟨toLex (Sum.inl i.1), i.2⟩) ⟨i, rfl⟩
    refine ⟨j, fun i i' h => ?_, fun i => by rw [hcE i, hj i]⟩
    have h1 : z (c ⟨toLex (Sum.inl i.1), i.2⟩) = z (c ⟨toLex (Sum.inl i'.1), i'.2⟩) := by
      rw [← hj i, ← hj i', h]
    have h2 : b (c ⟨toLex (Sum.inl i.1), i.2⟩) = b (c ⟨toLex (Sum.inl i'.1), i'.2⟩) := by
      rw [hb, hb]
      exact congrArg _ (Subtype.ext h1)
    have h3 := congrArg Subtype.val (hcinj (b.injective h2))
    exact Subtype.ext (Sum.inl.inj (toLex.injective h3))

end Main

end AlgebraicGeometry.Scheme.IdealSheafData
