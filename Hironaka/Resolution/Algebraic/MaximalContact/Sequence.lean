/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.MaximalContact.Restrict
import Hironaka.Resolution.Algebraic.MaximalContact.Transform
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 80 (1): a smooth static hypersurface of maximal contact is dynamic

Kollár's proof of [Kol07, Theorem 80 (1)], for a smooth blow-up sequence `Π` of order `m` starting
with `(X, I)` and a smooth `H` with `𝒪_X(−H) ⊆ MC(I)`:

1. **Corollary 77 at `j = m − 1`.** `Π` is a sequence of order `≥ m` for `(X, I, m)`, in the
   direction that needs no `max-ord I = m`, because the marked transforms with mark `m` of an
   order-`m` sequence are its weak transforms (`IsOrderSeq.isOrderGeSeq`); so
   [Kol07, Corollary 77] makes `(X_i, J_i, 1)` a sequence of order `≥ 1` starting with
   `(X, MC(I), 1)` (`IsOrderSeq.isOrderGeSeq_MC`), whence `ord_{Z_i} J_i ≥ 1` at every centre
   (`IsOrderSeq.leOrdAlong_markedTransformSeq_MC`).
2. **The induction.** Along any sequence of order `≥ 1` for `(X, J, 1)`, a smooth `H` with
   `𝒪(−H) ⊆ J` keeps `𝒪(−H_i) ⊆ J_i` and `H_i` smooth
   (`IsOrderGeSeq.strictTransformSeq_le_and_isSmoothDivisor`, by induction on the sequence): at
   each step `ord_{Z_i} J_i ≥ 1` forces `ord_{Z_i} H_i ≥ 1`, i.e. `Z_i ⊆ H_i` as closed
   subschemes, because the smooth centre is reduced (`le_of_leOrdAlong_one_of_smooth`: vanishing
   on the support of a reduced closed subscheme is membership in its ideal, stalkwise through the
   prime stalks of the centre), so the transform of a hypersurface through the centre
   (`Hironaka/Resolution/Algebraic/MaximalContact/Transform.lean`) applies:
   `𝒪(−H_{i+1}) = (π_i)⁻¹_*(𝒪(−H_i), 1) ⊆ (π_i)⁻¹_*(J_i, 1) = J_{i+1}` by the monotonicity of the
   marked transform, and `H_{i+1}` is smooth. Specialized to `J = MC(I)` this is Kollár's
   "`𝒪_{X_i}(−H_i) ⊂ J_i` for every `i`", with `Z_i ⊆ H_i` for every centre
   (`IsOrderSeq.strictTransformSeq_le_center_of_le_MC`) and, through Corollary 77's
   `J_i ⊆ D^{m−1}(I_i)`, the fact behind the Warning in [Kol07, 104] (keep the transforms of the
   old hypersurface of maximal contact after each blow-up): the transform `H_i` is again a static
   hypersurface of maximal contact for `(I_i, m)`
   (`IsOrderSeq.isMaximalContact_strictTransformSeq`).
3. **Theorem 80 (1).** Definition 78 asks the containment on every open `X⁰` for every order-`m`
   sequence of `(X⁰, I|_{X⁰})`; the static hypothesis and the smoothness of `H` restrict to `X⁰`
   (`Hironaka/Resolution/Algebraic/MaximalContact/Restrict.lean`), and step 2 applies there. The
   hypotheses `hI : max-ord I = m` and `hHI : I|_H ≠ 0` are part of Kollár's statement of Theorem 80
   (1) and are kept so that the theorem reads as printed. The proof does not need them: the
   containment `Z_i ⊆ H_i` comes from Corollary 77 at `j = m − 1` applied to a sequence of order
   `m`, for which `m ≥ 1` and `𝒪_X(−H) ⊆ MC(I) = D^{m−1}(I)` suffice, the mark `m` being a parameter
   of `MC f I m` rather than `max-ord I`; and `I|_H ≠ 0` enters Kollár's Definition 78 only through
   its second half, the restricted sequence as a sequence for the marked ideal `(H, I|_H, m)`,
   which the library's `IsDynamicMaximalContact` does not include and which
   `Hironaka/Resolution/Algebraic/MaximalContact/GoingDown.lean` treats separately, with the
   nonvanishing of `I|_H` on the components of `H` as the hypothesis of
   `not_component_subset_center_pullback`.

The containment `Z_i ⊆ H_i` is also [Wlo05, Lemma 2.7.6]. The results here feed going down
(`GoingDown.lean`), the local existence (`Existence.lean`), the induction for Theorem 97
(`Theorem97Induction.lean`) and the order reduction in the maximal contact case
(`Hironaka/Resolution/Algebraic/OrderReduction/Step21MaximalContact.lean`). -/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CharZero k] (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n

/-! ### The reduced centre: vanishing along `Z` is membership in the ideal of `Z` -/

/-- Kollár's "`ord_{Z_i} H_i ≥ 1`. Thus `Z_i ⊂ H_i`" in the proof of [Kol07, Theorem 80]: an ideal
sheaf of order `≥ 1` along a smooth centre `Z`, vanishing at the generic points of `Z` and hence
(upper semicontinuity) at every point of `Z`, is contained in the ideal sheaf of `Z`: `J` lies in
the vanishing ideal of `|Z|`, the radical of `Z`, and the stalks of a smooth `Z` at its points are
prime, so radical. -/
theorem le_of_leOrdAlong_one_of_smooth (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]
    {J : X.IdealSheafData} (hJ : J.LeOrdAlong Z.support 1) : J ≤ Z := by
  have hsupp : Z.support ≤ J.support := fun z hz =>
    (Scheme.IdealSheafData.one_le_ord_iff J z).mp
      ((Scheme.IdealSheafData.leOrdAlong_iff_forall_mem J f n Z.support 1).mp hJ z hz)
  have hrad : J ≤ Z.radical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hsupp
  refine Scheme.IdealSheafData.le_of_stalkIdeal_le fun x => ?_
  by_cases hx : x ∈ Z.support
  · have := isRegularLocalRing_quotient_stalkIdeal Z f hx
    have hprime : (Z.stalkIdeal x).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    obtain ⟨U, hxU⟩ := Scheme.IdealSheafData.exists_affineOpens_mem x
    rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ J U hxU] at *
    rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ Z U hxU] at hprime ⊢
    calc (J.ideal U).map (X.presheaf.germ U.1 x hxU).hom
        ≤ ((Z.ideal U).radical).map (X.presheaf.germ U.1 x hxU).hom := Ideal.map_mono (hrad U)
      _ ≤ ((Z.ideal U).map (X.presheaf.germ U.1 x hxU).hom).radical := Ideal.map_radical_le _
      _ = (Z.ideal U).map (X.presheaf.germ U.1 x hxU).hom := hprime.radical
  · rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support Z hx]
    exact le_top

/-! ### Corollary 77 at `j = m − 1` -/

section CorollarySeventySeven

variable {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}

/-- A smooth blow-up sequence of order `m` for `(X, I, E)` is one of order `≥ m` for
`(X, I, m, E)`: its marked transforms with mark `m` are its weak transforms
(`IsOrderSeq.markedTransformSeq_eq_weakTransformSeq`), along which the order is exactly `m`. This
direction needs no `max-ord I = m`. -/
theorem IsOrderSeq.isOrderGeSeq (h : S.IsOrderSeq f I E m) : S.IsOrderGeSeq f I m E :=
  ⟨h.1, fun i => ⟨(h.2 i).1, by
    rw [IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n h]
    exact fun η hη => ((h.2 i).2 η hη).ge⟩⟩

/-- Kollár's "applying (77) for `j = m − 1`" ([Kol07, Corollary 77]): along a smooth blow-up
sequence of order `m` for `(X, I, E)` with `m ≥ 1`, the marked transforms of `(MC(I), 1)` form a
sequence of order `≥ 1` starting with `(X, MC(I), 1, E)`. -/
theorem IsOrderSeq.isOrderGeSeq_MC (hm : 1 ≤ m) (h : S.IsOrderSeq f I E m) :
    S.IsOrderGeSeq f (MC f I m) 1 E := by
  have := isOrderGeSeq_derivativeIter f n S I E m (IsOrderSeq.isOrderGeSeq f n h) (Nat.sub_le m 1)
  rwa [Nat.sub_sub_self hm] at this

/-- Kollár's `ord_{Z_i} J_i ≥ 1`: the marked transform `J_i` of `(MC(I), 1)` has order `≥ 1` along
every centre. -/
theorem IsOrderSeq.leOrdAlong_markedTransformSeq_MC (hm : 1 ≤ m) (h : S.IsOrderSeq f I E m)
    (i : Fin S.length) :
    (S.markedTransformSeq (MC f I m) 1 i.castSucc).LeOrdAlong (S.center i).support 1 := by
  have := IsOrderGeSeq.leOrdAlong (IsOrderSeq.isOrderGeSeq_MC f n hm h) i
  rwa [Nat.cast_one] at this

end CorollarySeventySeven

/-! ### The induction along a sequence of order `≥ 1` -/

/-- The induction of the proof of [Kol07, Theorem 80 (1)] in its natural generality (compare
[Wlo05, Lemma 2.7.4 (1)]): along a smooth blow-up sequence of order `≥ 1` for `(X, J, 1, E)`, a
smooth hypersurface `H` with `𝒪(−H) ⊆ J` has smooth strict transforms `H_i` with `𝒪(−H_i) ⊆ J_i`
at every stage. At each step `ord_{Z_i} J_i ≥ 1` gives `ord_{Z_i} H_i ≥ 1`, hence `Z_i ⊆ H_i` for
the reduced centre, and `strictTransform_eq_markedTransform_one` turns the strict transform of
`H_i` into the marked transform `(π_i)⁻¹_*(𝒪(−H_i), 1) ⊆ (π_i)⁻¹_*(J_i, 1)`. -/
theorem IsOrderGeSeq.strictTransformSeq_le_and_isSmoothDivisor {S : BlowUpSequence X}
    {J H : X.IdealSheafData} {E : DivisorFamily X} (hS : S.IsOrderGeSeq f J 1 E)
    (hH : IsSmoothDivisor H) (hle : H ≤ J) (i : Fin (S.length + 1)) :
    S.strictTransformSeq H i ≤ S.markedTransformSeq J 1 i ∧
      IsSmoothDivisor (S.strictTransformSeq H i) := by
  induction S with
  | nil Y => exact ⟨hle, hH⟩
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hJD⟩, ht⟩ := (isOrderGeSeq_cons_iff f J E 1 D rest).1 hS
    have _ := hD
    have hHD : H.LeOrdAlong D.support 1 := fun η hη =>
      (hJD η hη).trans (Scheme.IdealSheafData.ord_anti hle η)
    have hHD' : H ≤ D := le_of_leOrdAlong_one_of_smooth f n D hHD
    rcases i with ⟨_ | i, hi⟩
    · exact ⟨hle, hH⟩
    · have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
        smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      have hH' : IsSmoothDivisor (H.strictTransform D) :=
        isSmoothDivisor_strictTransform_of_le f n D hD H hH hHD'
      have hle' : H.strictTransform D ≤ J.markedTransform D 1 := by
        rw [strictTransform_eq_markedTransform_one f n D hD H hH hHD']
        exact markedTransform_mono D hle 1
      exact ih (D.blowUpπ ≫ f) ht hH' hle' ⟨i, Nat.lt_of_succ_lt_succ hi⟩

section Sequence

variable {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}
  {H : X.IdealSheafData}

/-- Kollár's "`𝒪_{X_i}(−H_i) ⊂ J_i` for every `i`" in the proof of [Kol07, Theorem 80 (1)]. -/
theorem IsOrderSeq.strictTransformSeq_le_markedTransformSeq_MC (hm : 1 ≤ m)
    (h : S.IsOrderSeq f I E m) (hH : IsSmoothDivisor H) (hle : H ≤ MC f I m)
    (i : Fin (S.length + 1)) :
    S.strictTransformSeq H i ≤ S.markedTransformSeq (MC f I m) 1 i :=
  (IsOrderGeSeq.strictTransformSeq_le_and_isSmoothDivisor f n
    (IsOrderSeq.isOrderGeSeq_MC f n hm h) hH hle i).1

/-- Kollár's "`H_0` is smooth", carried along the sequence: every strict transform `H_i` is a
smooth hypersurface of `X_i`. -/
theorem IsOrderSeq.isSmoothDivisor_strictTransformSeq (hm : 1 ≤ m) (h : S.IsOrderSeq f I E m)
    (hH : IsSmoothDivisor H) (hle : H ≤ MC f I m) (i : Fin (S.length + 1)) :
    IsSmoothDivisor (S.strictTransformSeq H i) :=
  (IsOrderGeSeq.strictTransformSeq_le_and_isSmoothDivisor f n
    (IsOrderSeq.isOrderGeSeq_MC f n hm h) hH hle i).2

/-- Kollár's "Thus `Z_i ⊂ H_i` for every `i`" in the proof of [Kol07, Theorem 80 (1)]: every centre
lies in the strict transform of `H`, as closed subschemes (`H_i ≤ Z_i` as ideal sheaves). This is
also [Wlo05, Lemma 2.7.6]. -/
theorem IsOrderSeq.strictTransformSeq_le_center_of_le_MC (hm : 1 ≤ m) (h : S.IsOrderSeq f I E m)
    (hH : IsSmoothDivisor H) (hle : H ≤ MC f I m) (i : Fin S.length) :
    S.strictTransformSeq H i.castSucc ≤ S.center i := by
  have hJ := IsOrderSeq.leOrdAlong_markedTransformSeq_MC f n hm h i
  have hHi : (S.strictTransformSeq H i.castSucc).LeOrdAlong (S.center i).support 1 := fun η hη =>
    (hJ η hη).trans (Scheme.IdealSheafData.ord_anti
      (IsOrderSeq.strictTransformSeq_le_markedTransformSeq_MC f n hm h hH hle i.castSucc) η)
  have : SmoothOfRelativeDimension n (S.stageMap i.castSucc ≫ f) :=
    IsSmooth.smoothOfRelativeDimension_stageMap h.1 i.castSucc
  have : Smooth ((S.center i).subschemeι ≫ S.stageMap i.castSucc ≫ f) := h.1 i
  exact le_of_leOrdAlong_one_of_smooth (S.stageMap i.castSucc ≫ f) n (S.center i) hHi

/-- The transform `H_i` is again a static hypersurface of maximal contact for `(I_i, m)`:
`𝒪(−H_i) ⊆ J_i ⊆ D^{m−1}(I_i)` by [Kol07, Corollary 77]. This is what lets the Warning in
[Kol07, 104] keep the transforms of the old hypersurface of maximal contact after each blow-up. -/
theorem IsOrderSeq.isMaximalContact_strictTransformSeq (hm : 1 ≤ m) (h : S.IsOrderSeq f I E m)
    (hH : IsSmoothDivisor H) (hle : H ≤ MC f I m) (i : Fin (S.length + 1)) :
    IsMaximalContact (S.stageMap i ≫ f) (S.weakTransformSeq I i) m (S.strictTransformSeq H i) := by
  unfold IsMaximalContact
  refine (IsOrderSeq.strictTransformSeq_le_markedTransformSeq_MC f n hm h hH hle i).trans
    ?_
  have := markedTransformSeq_derivativeIter_le f n S I E m (IsOrderSeq.isOrderGeSeq f n h)
    (Nat.sub_le m 1) i
  rw [Nat.sub_sub_self hm, IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n h] at this
  exact this

end Sequence

/-! ### Theorem 80 (1) -/

/-- **[Kol07, Theorem 80 (1)]**: for `X` smooth over `k` of characteristic zero, `I` with
`m = max-ord I ≥ 1`, and a smooth hypersurface `H` with `𝒪_X(−H) ⊆ MC(I)` and `I|_H ≠ 0`, `H` is a
hypersurface of maximal contact in the dynamic sense of [Kol07, Definition 78]: on every open `X⁰`
the static hypothesis and the smoothness of `H` restrict, and
`IsOrderSeq.strictTransformSeq_le_center_of_le_MC` puts every centre of every order-`m` sequence
of `(X⁰, I|_{X⁰})` inside the transform of `H ∩ X⁰`. The hypotheses `hI : max-ord I = m` and
`hHI : I|_H ≠ 0` are part of Kollár's statement and are kept so that the theorem reads as printed;
the proof does not need them, because the containment of the centres needs only `m ≥ 1` and
`𝒪_X(−H) ⊆ MC(I)`, and `I|_H ≠ 0` concerns the restricted sequence, which is treated in
`Hironaka/Resolution/Algebraic/MaximalContact/GoingDown.lean` (module docstring, step 3). -/
theorem isDynamicMaximalContact_of_isMaximalContact (I H : X.IdealSheafData) {m : ℕ}
    (hI : I.maxOrd = m) (hm : 1 ≤ m) (hH : IsSmoothDivisor H)
    (hHI : IsNonzeroEverywhere (I.comap H.subschemeι)) (h : IsMaximalContact f I m H) :
    IsDynamicMaximalContact f I m H := by
  have _ := hI
  have _ := hHI
  intro Y j _ S hS i
  have : SmoothOfRelativeDimension (0 + n) (j ≫ f) := inferInstance
  exact IsOrderSeq.strictTransformSeq_le_center_of_le_MC (j ≫ f) (0 + n) hm hS
    (hH.comap_of_isOpenImmersion j) (h.comap f n j) i

end Hironaka.Sequence
