/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Tuning
public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
public import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.IdealSheaf.Derivative.Properties
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The maximal coefficient ideal of an ideal sheaf

Kollár's maximal coefficient ideals [Kol07, Definition 98]: for a smooth variety `X`, an ideal sheaf
`I ⊂ 𝒪_X` and `m = max-ord I`, the maximal coefficient ideal of order `s` of `I` is
`W_s(I) := ∑_{c : ∑ (m − j) c_j ≥ s} ∏_{j=0}^m (D^j I)^{c_j}`, where `D^j I` is the `j`-th
derivative ideal sheaf. The same definition on a regular local ring with coordinates is
`IsLocalRing.RegularCoords.W`, with the weight `IsLocalRing.wt m c = ∑ (m − j) c_j`; Theorem
100 and Corollary 101 (`Hironaka.Resolution.Algebraic.Tuning.Assemble`,
`Hironaka.Resolution.Algebraic.Tuning.Corollary101`) speak of ideal sheaves, so the definition is
given here for ideal sheaves, with the parameter `m` explicit as in the maximal-contact ideal `MC f
I m` (Kollár's `m = max-ord I` is a hypothesis where the theorems need it).

* `W f I m s := ⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e), ∏ j, (D^j I)^{e j}` on Mathlib's
  `IdealSheafData` (a complete lattice with products), with the characterisations `prod_le_W`,
  `W_le_iff` and the unfolding `W_eq`.
* The elementary facts of [Kol07, Proposition 99] at the level of ideal sheaves, proved as on a
  ring: `W_zero` (`W_0(I) = 𝒪_X`), `pow_le_W` (`I^c ⊆ W_s(I)` when `mc ≥ s`, the inclusion
  `I^{s'} ⊆ W_{ms'}(I)` through which the proof of Corollary 101 invokes Theorem 100), `MC_pow_le_W`
  (`MC(I)^s ⊆ W_s(I)`), `W_one` (`W_1(I) = MC(I)`, part of [Kol07, Proposition 99 (4)]) and the
  antitonicity `W_anti` ([Kol07, Proposition 99 (1)]).
* The stalk bridge `stalkIdeal_W`: for coordinates `c` on the stalk `𝒪_{X,p}` of a smooth variety
  that are `k`-linear and span the `k`-derivations, `(W_s(I))_p = W_{c,s}(I_p)`, so that everything
  proved in coordinates about `W` (the parts of Proposition 99 in `Hironaka.Local`) is available
  pointwise; the direction of Theorem 100 that needs `W`
  (`Hironaka.Resolution.Algebraic.Tuning.Sequence`) uses it.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-! ### Definition 98 for ideal sheaves -/

/-- **The maximal coefficient ideal of order `s`** of the ideal sheaf `I` [Kol07, Definition 98],
with the parameter `m` (Kollár's `max-ord I`) explicit:
`W_s(I) = ∑_{wt_m(e) ≥ s} ∏_{j ≤ m} (D^j I)^{e_j}`, the sum over all exponent vectors
`e : {0, …, m} → ℕ` of weight `wt_m(e) = ∑ (m − j) e_j ≥ s`, where `D^j I` is the `j`-th derivative
ideal sheaf `derivativeIter f j I`. -/
noncomputable def W (I : X.IdealSheafData) (m s : ℕ) : X.IdealSheafData :=
  ⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e), ∏ j : Fin (m + 1), derivativeIter f j I ^ e j

/-- Definition 98 unfolded (definitional). -/
theorem W_eq (I : X.IdealSheafData) (m s : ℕ) :
    W f I m s =
      ⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e), ∏ j : Fin (m + 1), derivativeIter f j I ^ e j :=
  rfl

/-- Every generating product of weight `≥ s` lies in `W_s(I)` [Kol07, Definition 98]. -/
theorem prod_le_W {I : X.IdealSheafData} {m s : ℕ} {e : Fin (m + 1) → ℕ} (he : s ≤ wt m e) :
    ∏ j : Fin (m + 1), derivativeIter f j I ^ e j ≤ W f I m s :=
  le_iSup₂_of_le e he le_rfl

/-- `W_s(I) ⊆ J` iff every generating product of weight `≥ s` lies in `J` [Kol07, Definition 98]. -/
theorem W_le_iff {I J : X.IdealSheafData} {m s : ℕ} :
    W f I m s ≤ J ↔
      ∀ e : Fin (m + 1) → ℕ, s ≤ wt m e → ∏ j : Fin (m + 1), derivativeIter f j I ^ e j ≤ J :=
  iSup₂_le_iff

/-- `W_0(I) = 𝒪_X`: the zero exponent vector has weight `0`. -/
@[simp]
theorem W_zero (I : X.IdealSheafData) (m : ℕ) : W f I m 0 = ⊤ := by
  have := prod_le_W f (I := I) (e := (0 : Fin (m + 1) → ℕ)) (Nat.zero_le _)
  simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one] at this
  exact top_le_iff.mp this

/-- `I^c ⊆ W_s(I)` whenever `mc ≥ s`: the exponent vector `e_0 = c` has weight `mc`. This is the
inclusion `I^{s'} ⊆ W_{ms'}(I)` through which the proof of [Kol07, Corollary 101] invokes Theorem
100, and it is used again in the proof of [Kol07, Theorem 103]. -/
theorem pow_le_W {I : X.IdealSheafData} {m s c : ℕ} (h : s ≤ m * c) : I ^ c ≤ W f I m s := by
  have hw : s ≤ wt m (Pi.single (0 : Fin (m + 1)) c) := by
    rw [wt_single]
    simpa using h
  refine le_trans ?_ (prod_le_W f hw)
  rw [Finset.prod_eq_single (0 : Fin (m + 1)) (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- `MC(I)^s ⊆ W_s(I)` for `m ≥ 1` [Kol07, Proposition 99, proof]: the exponent vector `e_{m−1} = s`
has weight `s`. -/
theorem MC_pow_le_W {m : ℕ} (hm : 1 ≤ m) (s : ℕ) (I : X.IdealSheafData) :
    MC f I m ^ s ≤ W f I m s := by
  have hw : s ≤ wt m (Pi.single (⟨m - 1, by omega⟩ : Fin (m + 1)) s) := by
    rw [wt_single]
    simp only
    rw [Nat.sub_sub_self hm, one_mul]
  refine le_trans ?_ (prod_le_W f hw)
  rw [Finset.prod_eq_single (⟨m - 1, by omega⟩ : Fin (m + 1))
    (fun j _ hj => by simp [hj]) (by simp)]
  simp [MC_eq]

/-- `W_1(I) = MC(I)` for `m ≥ 1`
[Kol07, Proposition 99 (4), proof: "`W_1(I) ⊂ ∑_{j<m} D^j(I) = D^{m−1}(I)`"]: `⊇` by `MC_pow_le_W`;
`⊆` because a generating product of weight `≥ 1` has some `e_j ≥ 1` with `j < m`, and so lies in
`D^j I ⊆ D^{m−1} I`. -/
theorem W_one {m : ℕ} (hm : 1 ≤ m) (I : X.IdealSheafData) : W f I m 1 = MC f I m := by
  refine le_antisymm ((W_le_iff f).mpr fun e he => ?_) (by simpa using MC_pow_le_W f hm 1 I)
  obtain ⟨j, hj⟩ : ∃ j : Fin (m + 1), 1 ≤ (m - (j : ℕ)) * e j := by
    by_contra hcon
    push Not at hcon
    have : wt m e = 0 := Finset.sum_eq_zero fun j _ => by have := hcon j; omega
    omega
  have hjm : (j : ℕ) < m := by
    by_contra h'
    push Not at h'
    rw [Nat.sub_eq_zero_of_le h', zero_mul] at hj
    omega
  have hej : e j ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hj
    omega
  calc ∏ j' : Fin (m + 1), derivativeIter f j' I ^ e j'
      ≤ derivativeIter f j I ^ e j := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        intro U
        exact Ideal.mul_le_left
    _ ≤ derivativeIter f j I := fun U => Ideal.pow_le_self hej
    _ ≤ derivativeIter f (m - 1) I := derivativeIter_mono_left f (by omega) I

/-- `W_t(I) ⊆ W_s(I)` for `s ≤ t` [Kol07, Proposition 99 (1)]. -/
theorem W_anti {I : X.IdealSheafData} {m s t : ℕ} (h : s ≤ t) : W f I m t ≤ W f I m s :=
  (W_le_iff f).mpr fun _ he => prod_le_W f (h.trans he)

/-! ### The stalk bridge -/

section Smooth

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

include n in
/-- The stalk of the maximal coefficient ideal: for coordinates `c` on `𝒪_{X,p}` that are `k`-linear
and span the `k`-derivations, `(W_s(I))_p = W_{c,s}(I_p)`, the maximal coefficient ideal of the
stalk computed in coordinates (`IsLocalRing.RegularCoords.W`). The stalk of a sum of products of
powers is the sum of the products of the powers of the stalks, and `(D^j I)_p = D_c^j(I_p)`
(`stalkIdeal_derivativeIter`, `derivativeIter_eq_Dpow`). -/
theorem stalkIdeal_W (I : X.IdealSheafData) (m s : ℕ) (p : X) {n' : ℕ}
    (c : letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      RegularCoords (X.presheaf.stalk p) n')
    (hk : letI := f.stalkAlgebra p; letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      c.IsLinearOver k)
    (hs : letI := f.stalkAlgebra p; letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      c.SpansDerivations k) :
    (W f I m s).stalkIdeal p =
      letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      c.W m s (I.stalkIdeal p) := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have := isRegularLocalRing_stalk f p
  change (⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e),
      ∏ j : Fin (m + 1), derivativeIter f j I ^ e j).stalkIdeal p =
    ⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e),
      ∏ j : Fin (m + 1), c.Dpow j (I.stalkIdeal p) ^ e j
  rw [iSup_subtype', iSup_subtype', stalkIdeal_iSup]
  refine iSup_congr fun e => ?_
  rw [stalkIdeal_finset_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [stalkIdeal_pow, stalkIdeal_derivativeIter f j I p, Ideal.derivativeIter_eq_Dpow c hk hs j]

end Smooth

end AlgebraicGeometry.Scheme.IdealSheafData
