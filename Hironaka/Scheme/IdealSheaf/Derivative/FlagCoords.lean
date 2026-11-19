/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Scheme.Snc.SmoothDivisor
public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
public import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Derivative.StalkCoords
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Flag coordinates at a point of a smooth centre inside a smooth hypersurface

The proof of [Kol07, Theorem 88] chooses, at a point of the centre `Z ⊆ S`, "coordinates
`x₁, …, xₙ` such that `S = (x₁ = 0)`" and the centre is `(x₁ = ⋯ = x_r = 0)`. This module produces
such coordinates on the stalk, in two steps.

* **The flag of parameters** (`exists_span_eq_and_chartCenter_eq`). Adapted parameters give a
  regular system of parameters `y` of `𝒪_{X,z}` with `Z_z = (y₀, …, y_{c−1})`
  (`exists_adaptedParameters_of_smooth`, `Hironaka/Scheme/BlowUpSequence/SmoothCenter.lean`). The
  local equation `a` of the smooth divisor `S` (`S_z = (a)`, `a ∈ 𝔪 ∖ 𝔪²`, `IsSmoothDivisor` of
  `Hironaka/Scheme/Snc/SmoothDivisor.lean`) lies in `Z_z`, so `a = ∑_{l < c} u_l y_l`; not every
  `u_l` lies in `𝔪`, else `a ∈ 𝔪 Z_z ⊆ 𝔪²`. For a unit `u_j`, replacing `y_j` by `a` changes neither
  `(y₀, …, y_{c−1})` nor `(y₀, …, y_{m−1})` (`exists_span_update` of
  `Hironaka/Algebra/Local/MaximalContact.lean`, the exchange of a parameter behind Kollár's local
  construction of a hypersurface of maximal contact, [Kol07, 51.2], here with the index kept below
  `c`), and the transposition `(0 j)` moves `a` to index `0`: `𝔪 = (x₀, …, x_{m−1})` with `x₀ = a`
  and `Z_z = (x₀, …, x_r) = chartCenter x r`, `r = c − 1` (or `n − 1` when `c ≥ n`).
* **The derivations** (`exists_flagCoords`, `exists_flagCoords_of_isAlgebraic`). The construction
  of the coordinate derivations of `Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean` runs for
  any prescribed regular system of parameters (`exists_regularCoords_stalk_of_span_eq`): the `∂ᵢ`
  dual to the `dxᵢ` are `k`-linear, and at a point with residue field algebraic over `k` (every
  closed point) they span the `k`-derivations, because the transcendence basis is empty.

Used in the proof of [Kol07, Theorem 88] for one blow-up
(`Hironaka/Resolution/Algebraic/Kol07/Theorem88BlowUp.lean`).
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ} (x : Fin n → R)

/-- The flag of parameters: if `x` generates `𝔪` and `a ∈ (x₀, …, x_{c−1}) ∖ 𝔪²`, some `x_j` with
`j < c` may be replaced by `a` and moved to index `0`: a family `x'` with `x'₀ = a` generating `𝔪`
and with `chartCenter x' r = (x'₀, …, x'_r) = (x₀, …, x_{c−1})`, `r = min (c − 1) (n − 1)`. -/
theorem exists_span_eq_and_chartCenter_eq (hx : maximalIdeal R = Ideal.span (Set.range x)) {c : ℕ}
    {a : R} (ha : a ∈ Ideal.span (x '' {j : Fin n | j.val < c})) (ha2 : a ∉ maximalIdeal R ^ 2) :
    ∃ (h0 : 0 < n) (r : Fin n) (x' : Fin n → R), x' ⟨0, h0⟩ = a ∧
      maximalIdeal R = Ideal.span (Set.range x') ∧
      chartCenter x' r = Ideal.span (x '' {j : Fin n | j.val < c}) := by
  classical
  -- the coefficients of `a` on `x_0, …, x_{c−1}`
  have ha' := ha
  rw [Set.image_eq_range] at ha'
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha'
  -- one coefficient is a unit, else `a ∈ 𝔪 · (x_0, …, x_{c−1}) ⊆ 𝔪²`
  have hex : ∃ i, IsUnit (u i) := by
    by_contra hcon
    push Not at hcon
    apply ha2
    rw [← hu, pow_two]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul ?_ ?_
    · by_contra h
      exact hcon i (notMem_maximalIdeal.mp h)
    · rw [hx]
      exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨⟨j, hjc⟩, hj⟩ := hex
  -- replacing `x_j` by `a` preserves the span over every index set containing `j` and `{l < c}`
  have hkey : ∀ T : Set (Fin n), j ∈ T → {l : Fin n | l.val < c} ⊆ T →
      Ideal.span (Function.update x j a '' T) = Ideal.span (x '' T) := by
    intro T hjT hcT
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨l, hl, rfl⟩
      by_cases hlj : l = j
      · rw [hlj, Function.update_self]
        exact Ideal.span_mono (Set.image_mono hcT) ha
      · rw [Function.update_of_ne hlj]
        exact Ideal.subset_span ⟨l, hl, rfl⟩
    · rintro _ ⟨l, hl, rfl⟩
      by_cases hlj : l = j
      · rw [hlj]
        -- `u_j x_j = a − ∑_{l' ≠ j} u_{l'} x_{l'}`, and `x_j = u_j⁻¹ · (u_j x_j)`
        have hsum : u ⟨j, hjc⟩ * x j + ∑ l' ∈ Finset.univ.erase ⟨j, hjc⟩, u l' * x l' = a :=
          (Finset.add_sum_erase _ (fun l' => u l' * x l') (Finset.mem_univ _)).trans hu
        have hmem : u ⟨j, hjc⟩ * x j ∈ Ideal.span (Function.update x j a '' T) := by
          rw [← sub_eq_of_eq_add hsum.symm]
          refine Ideal.sub_mem _ (Ideal.subset_span ⟨j, hjT, Function.update_self j a x⟩)
            (Ideal.sum_mem _ fun l' hl' => Ideal.mul_mem_left _ _
              (Ideal.subset_span ⟨l'.1, hcT l'.2, ?_⟩))
          exact Function.update_of_ne (fun h => Finset.ne_of_mem_erase hl' (Subtype.ext h)) a x
        have := Ideal.mul_mem_left _ (↑hj.unit⁻¹ : R) hmem
        rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this
      · exact Ideal.subset_span ⟨l, hl, Function.update_of_ne hlj a x⟩
  -- move `a` to index `0` by the transposition `(0 j)`, which preserves `{l | l.val < c}`
  have h0 : 0 < n := j.pos
  have hc0 : 0 < c := lt_of_le_of_lt (Nat.zero_le _) hjc
  obtain ⟨r, hr⟩ : ∃ r : Fin n, ∀ l : Fin n, l ≤ r ↔ l.val < c :=
    ⟨⟨min (c - 1) (n - 1), by omega⟩, fun l => by
      have := l.isLt
      rw [Fin.le_iff_val_le_val]
      dsimp only
      omega⟩
  have hσ : Equiv.swap (⟨0, h0⟩ : Fin n) j '' {l : Fin n | l.val < c} =
      {l : Fin n | l.val < c} := by
    ext l
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨l', hl', rfl⟩
      rw [Equiv.swap_apply_def]
      split_ifs <;> assumption
    · intro hl
      refine ⟨Equiv.swap ⟨0, h0⟩ j l, ?_, Equiv.swap_apply_self _ _ _⟩
      rw [Equiv.swap_apply_def]
      split_ifs <;> assumption
  have hset : {l : Fin n | l ≤ r} = {l : Fin n | l.val < c} := Set.ext fun l => hr l
  refine ⟨h0, r, Function.update x j a ∘ Equiv.swap ⟨0, h0⟩ j, ?_, ?_, ?_⟩
  · rw [Function.comp_apply, Equiv.swap_apply_left, Function.update_self]
  · rw [(Equiv.swap _ _).surjective.range_comp, ← Set.image_univ,
      hkey Set.univ (Set.mem_univ _) (Set.subset_univ _), Set.image_univ, hx]
  · unfold chartCenter
    rw [hset, Set.image_comp, hσ, hkey _ hjc subset_rfl]

end AlgebraicGeometry

namespace AlgebraicGeometry

open IsLocalRing AlgebraicGeometry Scheme.IdealSheafData

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (Z S : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]

include n in
/-- The construction: flag coordinates at `z ∈ Z ⊆ S` together with the spanning data of
`Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean`, lifts `w` of a transcendence basis of
`κ(z)/k` and the derivations `∂'ₗ` dual to the `dwₗ`, with `δ = ∑ᵢ δ(xᵢ) ∂ᵢ + ∑ₗ δ(wₗ) ∂'ₗ` for
every `k`-derivation `δ`. -/
theorem exists_flagCoords_aux (hS : IsSmoothDivisor S) (hZS : S ≤ Z) {z : X}
    (hz : z ∈ Z.support) :
    letI := f.stalkAlgebra z
    letI := f.stalkAlgebraRat z
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) z
    ∃ (n' t : ℕ) (c : RegularCoords (X.presheaf.stalk z) n') (h0 : 0 < n') (r : Fin n')
      (w : Fin t → X.presheaf.stalk z)
      (der' : Fin t → Derivation k (X.presheaf.stalk z) (X.presheaf.stalk z)),
      c.IsLinearOver k ∧ S.stalkIdeal z = Ideal.span {c.x ⟨0, h0⟩} ∧
        Z.stalkIdeal z = chartCenter c.x r ∧
        IsTranscendenceBasis k (fun j => residue (X.presheaf.stalk z) (w j)) ∧
        ∀ (δ : Derivation k (X.presheaf.stalk z) (X.presheaf.stalk z)) (a : X.presheaf.stalk z),
          δ a = ∑ i, δ (c.x i) * c.pderiv i a + ∑ j, δ (w j) * der' j a := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  -- adapted parameters `y` with `Z_z = (y_0, …, y_{c₀−1})`, and the local equation `a` of `S`
  obtain ⟨m, c₀, y, -, hm, hy, hZ⟩ := exists_adaptedParameters_of_smooth f Z hz
  have hzS : z ∈ S.support := support_antitone hZS hz
  obtain ⟨a, -, ha2, hSa⟩ := hS.2 z hzS
  have haZ : a ∈ Z.stalkIdeal z := by
    refine stalkIdeal_mono hZS z ?_
    rw [hSa]
    exact Ideal.mem_span_singleton_self a
  rw [hZ] at haZ
  -- the flag of parameters, then the coordinate derivations for it
  obtain ⟨h0, r, x', hx'0, hx', hcc⟩ := exists_span_eq_and_chartCenter_eq y hy haZ ha2
  obtain ⟨t, c, w, der', hcx, hk, hw, hspan⟩ :=
    exists_regularCoords_stalk_of_span_eq f n z m x' hm hx'
  refine ⟨m, t, c, h0, r, w, der', hk, ?_, ?_, hw, hspan⟩
  · rw [hcx, hx'0, hSa]
  · rw [hcx, hcc, hZ]

include n in
/-- **Flag coordinates** (the coordinates of the proof of [Kol07, Theorem 88]): at a point `z` of
the smooth centre `Z ⊆ S`, `S` a smooth hypersurface, the stalk has regular coordinates with
`k`-linear derivations, `S_z = (x₀)` and `Z_z = (x₀, …, x_r)`. -/
theorem exists_flagCoords (hS : IsSmoothDivisor S) (hZS : S ≤ Z) {z : X}
    (hz : z ∈ Z.support) :
    letI := f.stalkAlgebra z
    letI := f.stalkAlgebraRat z
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) z
    ∃ (n' : ℕ) (c : RegularCoords (X.presheaf.stalk z) n') (h0 : 0 < n') (r : Fin n'),
      c.IsLinearOver k ∧ S.stalkIdeal z = Ideal.span {c.x ⟨0, h0⟩} ∧
        Z.stalkIdeal z = chartCenter c.x r := by
  obtain ⟨n', -, c, h0, r, -, -, hk, hS', hZ', -, -⟩ := exists_flagCoords_aux f n Z S hS hZS hz
  exact ⟨n', c, h0, r, hk, hS', hZ'⟩

include n in
/-- At a point with residue field algebraic over `k` (every closed point), the flag coordinates
may be taken with derivations spanning the `k`-derivations
(`exists_regularCoords_stalk_of_isAlgebraic`): the transcendence basis is empty, so the
`∂'ₗ`-sum of the spanning formula is empty. -/
theorem exists_flagCoords_of_isAlgebraic (hS : IsSmoothDivisor S) (hZS : S ≤ Z)
    {z : X} (hz : z ∈ Z.support)
    (halg : letI := f.stalkAlgebra z
      Algebra.IsAlgebraic k (ResidueField (X.presheaf.stalk z))) :
    letI := f.stalkAlgebra z
    letI := f.stalkAlgebraRat z
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) z
    ∃ (n' : ℕ) (c : RegularCoords (X.presheaf.stalk z) n') (h0 : 0 < n') (r : Fin n'),
      c.IsLinearOver k ∧ c.SpansDerivations k ∧ S.stalkIdeal z = Ideal.span {c.x ⟨0, h0⟩} ∧
        Z.stalkIdeal z = chartCenter c.x r := by
  let _ := f.stalkAlgebra z
  let _ := f.stalkAlgebraRat z
  obtain ⟨n', t, c, h0, r, w, der', hk, hS', hZ', hw, hspan⟩ :=
    exists_flagCoords_aux f n Z S hS hZS hz
  have ht : IsEmpty (Fin t) := hw.isEmpty_iff_isAlgebraic.mpr halg
  refine ⟨n', c, h0, r, hk, fun δ a => ?_, hS', hZ'⟩
  have h0' : ∑ j, δ (w j) * der' j a = 0 := Finset.sum_eq_zero fun j _ => isEmptyElim j
  rw [hspan δ a, h0', add_zero]

end AlgebraicGeometry
