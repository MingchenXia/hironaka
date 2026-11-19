/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Restriction
public import Hironaka.Scheme.BlowUpSequence.Truncate
public import Hironaka.Resolution.Algebraic.Balanced.Order
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.BoundaryClearing.Center
import Hironaka.Resolution.Algebraic.BoundaryClearing.Transform
import Hironaka.Resolution.Algebraic.Kol07.GoingUp
import Hironaka.Scheme.BlowUp.BlowUpMap
public import Hironaka.Scheme.BlowUpSequence.InducedData
public import Hironaka.Scheme.BlowUpSequence.PullbackSnc
public import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.AlgebraicGeometry.Scheme
import Lean.Elab.Do.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Algebra.Polynomial.Laurent
public import Hironaka.Resolution.Algebraic.Snc.SncInvertible
import Lean.Message
import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
import Hironaka.Scheme.BlowUpSequence.Defs

/-!
# The composite sequence on `S = E^j` and going up

The proof of [Kol07, Lemma 102], third and fourth paragraphs: by the going-up theorem
[Kol07, Theorem 84], every blow-up sequence of order `≥ m` starting with
`(S, I_0|_S, m, (E − E^j)|_S)` corresponds to a blow-up sequence of order `m` starting with
`(X_0, I_0, E − E^j)`; since `S = E^j`, every blow-up center is a smooth subvariety of the
birational transform of `E^j`; and the output is `BMO_{n−1,m}(S, I_0|_S, m, (E − E^j)|_S)` pushed
forward ([Kol07, 30.3]) and composed on the right with the first blow-up `π_{-1}`.

**The first step on `S`.** `Z_{-1}|_S`, `Z_{-1}` viewed on `S = E^j`, pushes forward to `Z_{-1}`
(since `Z_{-1} ⊆ E^j`), is smooth over `k` (it is `Z_{-1}` itself, smooth by `Center.lean`), and
`I|_S` has order `≥ m` along it (the order of `I` is `≥ m` on `Z_{-1}` and does not drop under
restriction). Its exceptional divisor on `X_S = blowUp S (Z_{-1}|_S)` is empty: through the closed
immersion `τ = blowUpMap ι Z_{-1}` onto the birational transform of `E^j`, a point of `X_S` lies
over a point of `E^j` off `Z_{-1}` (`Transform.lean` describes that birational transform as the
saturation `(E^j : Z_{-1}^∞)`), so the pulled-back ideal of `Z_{-1}` is the unit ideal everywhere.
The restricted marked triple's fields are what its definition says (`restrictedTriple_X/I/m/E`),
its ideal is Kollár's `I_0|_S` (`markedTransform_centerS_eq`, the degenerate analogue of
[Kol07, Lemma 62]), and its old
members are the members of `E_0 − E^j` restricted along `τ`.

**Going up, and the Warning in [Kol07, 104].** Theorem 84 as printed needs a D-balanced ideal,
which `I_0` need not be; Kollár's reading is that the consequences of Theorem 84 hold for any
sequence of blow-ups of order `m` starting from the D-balanced `I`. So the composite sequence ON
`S`, first center `Z_{-1}|_S`, then `B`'s sequence on the restricted marked triple, is a smooth
blow-up sequence of order `≥ m` starting with `(S, I|_S, m, (E − E^j)|_S)`
(`isOrderGeSeq_cons_centerS`; [Kol07, Definition 66] step by step: the three facts about
`Z_{-1}|_S`, then `B`'s own order condition, whose data are exactly the induced marked triple after
the first step), and the going-up theorem (`Hironaka/Resolution/Algebraic/Kol07/GoingUp.lean`) for
the D-balanced `I` on `X` with `S = E^j` and `E − E^j` gives that its push-forward `rawSeq` is a
smooth blow-up sequence of order `m` starting with `(X, I, E − E^j)` (`isOrderSeq_rawSeq_erase`).
The push-forward is `π_{-1}` followed by `τ_* B(…)` (`rawSeq_eq`, `take_one_rawSeq`: its first
center is `Z_{-1}` by `map_centerS`), so Definition 66 after one step gives Kollár's sentence: `τ_*
B(…)` is a smooth blow-up sequence of order `m` starting with `(X_0, I_0, E_0 − E^j)`
(`isOrderSeq_pushforward_restricted`).

**Bookkeeping for the output.** Every center of `rawSeq` lies in the birational transform of `E^j`
at its stage (`strictTransformSeq_le_center_pushforward_subschemeι`), and only the first blow-up
`π_{-1}` can be empty: `B` returns no empty blow-ups and pushing a center forward along a closed
immersion preserves that.

Used by `Output.lean`, and outside this directory by the embedded-resolution modules
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedNilCaseA.lean`,
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedCP1Step22Core.lean` and
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedCP3Raw.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Hironaka Scheme Scheme.Hom BlowUpSequence Hironaka.Sequence Hironaka.Snc

namespace Hironaka.BD

variable {k : Type u} [Field k]

section FirstStepNoChar

variable (T : Triple k) (m : ℕ) (j : T.E.ι)

/-- The push-forward of `Z_{-1}|_S` to `X` is `Z_{-1}`: the first center of the pushed-forward
composite sequence is the center of `π_{-1}` (`map_comap_of_ker_le`; `Z_{-1} ⊆ E^j` by
`Basic.lean`). -/
theorem map_centerS :
    (centerS T m j).map (T.E.component j).subschemeι = Zminus1 T.I m (T.E.component j) :=
  map_comap_of_ker_le _ _ (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact component_le_Zminus1 T m j)

end FirstStepNoChar

section FirstStep

variable [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)

/-- `Z_{-1}|_S` is smooth over `k` ([Kol07, Definition 65]; [Kol07, Notation 19]): as a closed
subscheme of `S` it is `Z_{-1}`, which is smooth (`Center.lean`). -/
theorem smooth_centerS :
    Smooth ((centerS T m j).subschemeι ≫ (T.E.component j).subschemeι ≫
      (T.X.left ↘ Spec (.of k))) := by
  obtain ⟨φ, hφ⟩ := exists_iso_subscheme_comap_of_ker_le (T.E.component j).subschemeι
    (Zminus1 T.I m (T.E.component j)) (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact component_le_Zminus1 T m j)
  have := smooth_Zminus1 T m j
  rw [← Category.assoc]
  change Smooth (((Zminus1 T.I m (T.E.component j)).comap (T.E.component j).subschemeι).subschemeι ≫
    (T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k)))
  rw [← Category.assoc, ← hφ, Category.assoc]
  infer_instance

/-- `I|_S` has order `≥ m` along `Z_{-1}|_S` (the order condition of [Kol07, Definition 65] for the
marked triple): the order of `I` is `≥ m` on `Z_{-1}` (`Basic.lean`) and does not decrease under
restriction. -/
theorem leOrdAlong_centerS :
    (T.I.comap (T.E.component j).subschemeι).LeOrdAlong (centerS T m j).support (m : ℕ∞) := by
  intro η hη
  have hx : (T.E.component j).subschemeι η ∈ (Zminus1 T.I m (T.E.component j)).support :=
    (mem_support_comap_iff_apply _ _ η).mp hη.1
  exact (support_Zminus1_subset_cosupp T m j hx).trans (ord_le_ord_comap T.I _ η)

omit [CharZero k] in
/-- The exceptional divisor of `Z_{-1}|_S` on `X_S` is empty: `X_S` maps by `τ` onto the birational
transform of `E^j`, whose points lie over `E^j` off `Z_{-1}` (the saturation description of
`Transform.lean`), so the pulled-back ideal of `Z_{-1}` is the unit ideal at every point of
`X_S`. -/
theorem exceptionalDivisor_centerS_eq_top :
    (centerS T m j).exceptionalDivisor = ⊤ := by
  change ((Zminus1 T.I m (T.E.component j)).comap
      (T.E.component j).subschemeι).exceptionalDivisor = ⊤
  set Z := Zminus1 T.I m (T.E.component j) with hZdef
  set ι := (T.E.component j).subschemeι with hιdef
  set τ := Scheme.Hom.blowUpMap ι Z with hτdef
  refine (Scheme.IdealSheafData.support_eq_bot_iff
    (I := (Z.comap ι).exceptionalDivisor)).mp
    (le_bot_iff.mp fun y hy => ?_)
  exfalso
  -- `π_S y ∈ Z_{-1}|_S`, i.e. `ι (π_S y) ∈ Z_{-1}`
  have h1 : (Z.comap ι).blowUpπ y ∈ (Z.comap ι).support :=
    (mem_support_comap_iff_apply _ _ y).mp hy
  have h2 : ι ((Z.comap ι).blowUpπ y) ∈ Z.support :=
      (mem_support_comap_iff_apply _ _ _).mp h1
  -- `ι (π_S y) = π_X (τ y)`
  have hcomm : (Z.comap ι).blowUpπ ≫ ι = τ ≫ Z.blowUpπ :=
    (blowUpMap_π ι Z).symm
  have h3 : ι ((Z.comap ι).blowUpπ y) = Z.blowUpπ (τ y) := by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  -- `τ y` lies on the birational transform of `E^j`, i.e. `π_X (τ y)` lies on `E^j` off `Z_{-1}`
  have hτ : IsClosedImmersion τ :=
    isClosedImmersion_blowUpMap_of_isClosedImmersion ι Z
  have hker : τ.ker = (T.E.component j).strictTransform Z := ker_blowUpMap_component T m j
  have h4 : τ y ∈ τ.ker.support := by
    have hy' : τ y = τ.imageι (τ.toImage y) := by
      rw [← Scheme.Hom.comp_apply, τ.toImage_imageι]
    rw [hy']
    exact subschemeι_mem_support τ.ker (τ.toImage y)
  rw [hker, strictTransform_eq_comap_saturate T m j] at h4
  have h5 := (mem_support_comap_iff_apply _ _ _).mp h4
  rw [mem_support_saturate_iff T m j] at h5
  exact h5.2 (h3 ▸ h2)

end FirstStep

section Restricted

variable [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
  (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m)

/-- The scheme of the restricted marked triple is `X_S = blowUp S (Z_{-1}|_S)`, Kollár's `S = E^j`
on `X_0` (the proof of [Kol07, Lemma 102]). -/
theorem restrictedTriple_X :
    (restrictedTriple T m j hI hmax).X.left = (centerS T m j).blowUp :=
  rfl

/-- The ideal of the restricted marked triple is the marked transform of `I|_S` with control `m`
along `Z_{-1}|_S`. -/
theorem restrictedTriple_I :
    (restrictedTriple T m j hI hmax).I =
      (T.I.comap (T.E.component j).subschemeι).markedTransform (centerS T m j) m :=
  rfl

/-- The mark of the restricted marked triple is `m`. -/
theorem restrictedTriple_m : (restrictedTriple T m j hI hmax).m = m :=
  rfl

/-- The family of the restricted marked triple is the total transform of `(E − E^j)|_S` along
`Z_{-1}|_S` (Kollár's `E_S := (E − E^j)|_S`). -/
theorem restrictedTriple_E :
    (restrictedTriple T m j hI hmax).E =
      ((T.E.erase j).comap (T.E.component j).subschemeι).totalTransform (centerS T m j) :=
  rfl

/-- The ideal of the restricted marked triple is the restriction of `I_0 = (π_{-1})^{-1}_* I` along
`τ = blowUpMap ι Z_{-1}`, Kollár's `I_0|_S` (`markedTransform_centerS_eq`, the degenerate analogue
of [Kol07, Lemma 62]; [Kol07, Remark 67]). -/
theorem restrictedTriple_I_eq_comap :
    (restrictedTriple T m j hI hmax).I =
      (T.I.weakTransform (Zminus1 T.I m (T.E.component j))).comap
        (Scheme.Hom.blowUpMap (T.E.component j).subschemeι (Zminus1 T.I m (T.E.component j))) :=
  markedTransform_centerS_eq T m j hmax

/-- The old members of the restricted family are the restrictions along `τ` of the members of
`E_0 − E^j`, the birational transforms of the members of `E` other than `E^j`
(`strictTransform_comap_blowUpMap_of_hasSncWith`, with `(E − E^j) + E^j = E` having snc with
`Z_{-1}` by `Center.lean`). -/
theorem restrictedTriple_E_component_inl (i : (T.E.erase j).ι) :
    (restrictedTriple T m j hI hmax).E.component (toLex (Sum.inl i)) =
      ((T.E.totalTransform (Zminus1 T.I m (T.E.component j))).component (toLex (Sum.inl i.1))).comap
        (Scheme.Hom.blowUpMap (T.E.component j).subschemeι (Zminus1 T.I m (T.E.component j))) := by
  have hb : ((T.E.erase j).append (T.E.component j).subschemeι.ker).HasSncWith
      (Zminus1 T.I m (T.E.component j)) := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hasSncWith_of_equiv (DivisorFamily.eraseAppendEquiv T.E j).symm
      (DivisorFamily.append_erase_component_eraseAppendEquiv_symm T.E j) (hasSncWith_Zminus1 T m j)
  exact strictTransform_comap_blowUpMap_of_hasSncWith (T.X.left ↘ Spec (.of k))
    (T.E.component j).subschemeι hb (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact component_le_Zminus1 T m j) i

variable {n : ℕ} (hn : T.HasDimLE n) {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)
  (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')

/-- The composite sequence on `S`, first center `Z_{-1}|_S`, then the output of `B` on the
restricted marked triple, is a smooth blow-up sequence of order `≥ m` starting with
`(S, I|_S, m, (E − E^j)|_S)` (the proof of [Kol07, Lemma 102] read through the Warning in
[Kol07, 104]): [Kol07, Definition 66] step by step (`isOrderGeSeq_cons_iff`), the three facts about
`Z_{-1}|_S`, then `B`'s own order condition on the induced marked triple. -/
theorem isOrderGeSeq_cons_centerS (hR : Dom (restrictedTriple T m j hI hmax)) :
    (cons (T.E.component j).subscheme (centerS T m j)
      (B.seq (restrictedTriple T m j hI hmax) hR)).IsOrderGeSeq
        ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k)))
        (T.I.comap (T.E.component j).subschemeι) m
        ((T.E.erase j).comap (T.E.component j).subschemeι) :=
  (isOrderGeSeq_cons_iff ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k)))
    (T.I.comap (T.E.component j).subschemeι) ((T.E.erase j).comap (T.E.component j).subschemeι) m
    (centerS T m j) _).2
    ⟨⟨smooth_centerS T m j, hasSncWith_centerS T m j, leOrdAlong_centerS T m j⟩,
      B.isOrderGeSeq _ hR⟩

/-- The output before the deletion of empty blow-ups is the push-forward ([Kol07, 30.3]) of the
composite sequence: first the blow-up of `X` along `(Z_{-1}|_S).map ι`, then `tailSeq = τ_* B(…)`
(`pushforward_cons`). -/
theorem rawSeq_eq :
    rawSeq T m j hI hmax hn B hDom =
      cons T.X.left ((centerS T m j).map (T.E.component j).subschemeι)
        (tailSeq T m j hI hmax hn B hDom) :=
  rfl

/-- The first blow-up of the output is `π_{-1}` (Kollár composes "on the right with our first
blow-up `π_{-1}`", the proof of [Kol07, Lemma 102]): its center is `(Z_{-1}|_S).map ι = Z_{-1}`. -/
theorem take_one_rawSeq :
    (rawSeq T m j hI hmax hn B hDom).take 1 = piMinusOne T.I m (T.E.component j) := by
  have h0 : ∀ {Y : Scheme.{u}} (R : BlowUpSequence Y), R.take 0 = nil Y := fun R => by
    cases R <;> rfl
  change cons T.X.left ((centerS T m j).map (T.E.component j).subschemeι)
    ((tailSeq T m j hI hmax hn B hDom).take 0) = _
  rw [h0, piMinusOne, map_centerS]

/-- The output is a smooth blow-up sequence of order `m` starting with `(X, I, E − E^j)`: the
going-up theorem [Kol07, Theorem 84] applied, per the Warning in [Kol07, 104], to the composite
sequence from the D-balanced `I`, with `S = E^j` (a smooth divisor) and `(E − E^j) + E^j = E` snc
(`Hironaka/Resolution/Algebraic/Kol07/GoingUp.lean`). -/
theorem isOrderSeq_rawSeq_erase :
    (rawSeq T m j hI hmax hn B hDom).IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I (T.E.erase j) m := by
  obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
  exact IsDBalanced.isOrderSeq_pushforward (T.X.left ↘ Spec (.of k)) n₀ (T.E.component j) T.I
    (T.E.erase j) m _ hI hmax (isSmoothDivisor_component T j)
    (DivisorFamily.isSnc_erase_append T.E j T.isSnc) (isOrderGeSeq_cons_centerS T m j hI hmax B _)

/-- The tail of the output, `τ_* B(S, I_0|_S, m, E_S)`, is a smooth blow-up sequence of order `m`
starting with `(X_0, I_0, E_0 − E^j)`, where `X_0` is the blow-up of `X` along
`(Z_{-1}|_S).map ι = Z_{-1}` (Kollár's "blow-up sequence of order `m` starting with
`(X_0, I_0, E − E^j)`", the proof of [Kol07, Lemma 102]): [Kol07, Definition 66] after the first
step (`isOrderSeq_cons_iff`). -/
theorem isOrderSeq_pushforward_restricted :
    (tailSeq T m j hI hmax hn B hDom).IsOrderSeq
      (((centerS T m j).map (T.E.component j).subschemeι).blowUpπ ≫ (T.X.left ↘ Spec
          (.of k)))
      (T.I.weakTransform ((centerS T m j).map (T.E.component j).subschemeι))
      ((T.E.erase j).totalTransform ((centerS T m j).map (T.E.component j).subschemeι)) m := by
  have h := isOrderSeq_rawSeq_erase T m j hI hmax hn B hDom
  rw [rawSeq_eq] at h
  exact ((isOrderSeq_cons_iff (T.X.left ↘ Spec (.of k)) T.I (T.E.erase j) m _ _).1 h).2

/-- Each center of the output lies in the birational transform of `E^j` at its stage (Kollár's
"every blow-up center is a smooth subvariety" of that birational transform, the proof of
[Kol07, Lemma 102]): `strictTransformSeq_le_center_pushforward_subschemeι`. -/
theorem strictTransformSeq_le_center_rawSeq (i : Fin (rawSeq T m j hI hmax hn B hDom).length) :
    (rawSeq T m j hI hmax hn B hDom).strictTransformSeq (T.E.component j) i.castSucc ≤
      (rawSeq T m j hI hmax hn B hDom).center i :=
  strictTransformSeq_le_center_pushforward_subschemeι (T.E.component j) _ i

/-- Only the first blow-up of the output can be empty: `B` returns no empty blow-ups ([Kol07, 32]
for `BMO`), and pushing a center forward along a closed immersion preserves nonemptiness
(`comap_map`). -/
theorem center_rawSeq_ne_top_of_pos (i : Fin (rawSeq T m j hI hmax hn B hDom).length)
    (hi : 0 < i.val) : (rawSeq T m j hI hmax hn B hDom).center i ≠ ⊤ := by
  obtain ⟨i, hi'⟩ := i
  cases i with
  | zero => exact absurd hi (lt_irrefl 0)
  | succ i =>
    set R := restrictedTriple T m j hI hmax with hRdef
    set hR : Dom R := hDom _ (hasDimLE_restrictedTriple T m j hI hmax hn) rfl with hRdef'
    set g := pushforwardBlowUp (T.E.component j).subschemeι (centerS T m j) with hgdef
    have hg : IsClosedImmersion g :=
      inferInstanceAs (IsClosedImmersion
        (pushforwardBlowUp (T.E.component j).subschemeι (centerS T m j)))
    let Q : BlowUpSequence (centerS T m j).blowUp :=
        B.seq R hR
    change (Q.pushforward g).center ⟨i, Nat.lt_of_succ_lt_succ hi'⟩ ≠ ⊤
    have hi2 : i < Q.length := by
      have h1 := length_pushforward Q g
      have h2 : (rawSeq T m j hI hmax hn B hDom).length = (Q.pushforward g).length + 1 := rfl
      omega
    have hidx : (⟨i, Nat.lt_of_succ_lt_succ hi'⟩ : Fin (Q.pushforward g).length) =
        Q.pushforwardCenterIdx g ⟨i, hi2⟩ := Fin.ext rfl
    rw [hidx, center_pushforward_mk]
    intro htop
    have hci := isClosedImmersion_pushforwardStageHom_mk Q g i (Nat.lt_succ_of_lt hi2)
    have h2 := comap_map_of_isClosedImmersion
      (Q.pushforwardStageHom g ⟨i, Nat.lt_succ_of_lt hi2⟩) (Q.center ⟨i, hi2⟩)
    rw [htop, Scheme.IdealSheafData.comap_top] at h2
    exact B.noEmptyCenters R hR ⟨i, hi2⟩ h2.symm

end Restricted

end Hironaka.BD
