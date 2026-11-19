/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.Snc.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
public import Hironaka.Scheme.Snc.SncOn
import Hironaka.Resolution.Algebraic.Snc.SncOnTransport
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.RestrictDivisorsOn
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The exceptional sub-family with the transform of a hypersurface is snc everywhere

Along a smooth blow-up sequence of order `m` whose centers lie in the transforms of `H` (smooth
divisors), the selected members of `E_r` together with `H_r` are snc at every point, provided the
selected members of `E` with `H` are (`isSncOn_univ_subfamily_append_of_forall_le_center`, by
induction along the sequence). Kollár states this along the cosupport of `I_r`
[Kol07, 104, Step 2.1]; the cosupport serves only to exclude the not-yet-cleared original members,
so with nothing selected at the start the induction runs on the whole space. Its base case is `H`
alone, a smooth divisor on a smooth scheme, snc everywhere
(`isSnc_append_empty_of_isSmoothDivisor`); its step uses the smoothness and normal crossing
conditions of [Kol07, Definition 66] at the center, the pointwise snc data on the exceptional
divisor and the local isomorphism off it. The selected members at the end are the exceptional ones,
those that are not birational transforms of original members (`originalIdx`): `exceptionalFamily`.
So `F_r + H_r` is snc everywhere (`isSnc_exceptionalFamily_append`). This is what makes
`(X_r, I_r, F_r + H_r)` a triple in the sense of [Kol07, Notation 64] when the maximal contact case
of the proof of Theorem 103 restricts to the hypersurface [Kol07, 104, Step 2.2]: Kollár's "`H + E`
is also a simple normal crossing divisor" holds for the exceptional sub-family.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Ideal Scheme
  IdealSheafData BlowUpSequence Scheme.IdealSheafData Hironaka.Snc

namespace Hironaka.Sequence

open AlgebraicGeometry

section Family

variable {X : Scheme.{u}}

/-- **The exceptional sub-family** of the total transform of `E` at the end of a sequence: the
members that are not the birational transform of an original member (`originalIdx`). It is the
family `F_r` for which "`H_r + F_r` is a simple normal crossing divisor" holds in the maximal
contact case of the proof of Theorem 103 [Kol07, 104, Step 2.2]. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.BlowUpSequence.exceptionalFamily
    (S : BlowUpSequence X)
    (E : DivisorFamily X) : DivisorFamily (S.stage (Fin.last _)) :=
  (S.totalTransformSeq E (Fin.last _)).subfamily fun b => ∀ a, b ≠ S.originalIdx E (Fin.last _) a

theorem exceptionalFamily_component (S : BlowUpSequence X) (E : DivisorFamily X)
    (b : (S.exceptionalFamily E).ι) :
    (S.exceptionalFamily E).component b = (S.totalTransformSeq E (Fin.last _)).component b.1 :=
  rfl

end Family

variable {k : Type u} [Field k] [CharZero k]

/-- The global form of the snc induction of [Kol07, 104, Step 2.1]: along a smooth blow-up sequence
of order `m` all of whose centers lie in the transforms of a divisor `H` with smooth transforms, the
selected members of the total transform together with the transform of `H` are snc at every point,
provided the selected members of `E` with `H` are. -/
theorem isSncOn_univ_subfamily_append_of_forall_le_center (n : ℕ) : ∀ {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (S : BlowUpSequence X)
    {J : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}, S.IsOrderSeq f J E m →
    ∀ (H : X.IdealSheafData),
    (∀ i : Fin (S.length + 1), IsSmoothDivisor (S.strictTransformSeq H i)) →
    (∀ i : Fin S.length, S.strictTransformSeq H i.castSucc ≤ S.center i) → ∀ (p : E.ι → Prop),
    ((E.subfamily p).append H).IsSncOn Set.univ →
    (((S.totalTransformSeq E (Fin.last _)).subfamily
        (fun i => ∀ a, i = S.originalIdx E (Fin.last _) a → p a)).append
      (S.strictTransformSeq H (Fin.last _))).IsSncOn Set.univ
  | _, _, _, nil _, _, _, _, _, H, _, _, _, hp =>
    isSncOn_subfamily_append_mono (fun i hi => hi i rfl) H hp
  | X, f, _, cons _ D₀ rest, J, E, m, hS, H, hHs, hcen, p, hp => by
    obtain ⟨hhead, ht⟩ := (isOrderSeq_cons_iff f J E m D₀ rest).1 hS
    have hsm : Smooth (D₀.subschemeι ≫ f) := hhead.1
    have : SmoothOfRelativeDimension n (D₀.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D₀
    have hf : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hleH : H ≤ D₀ := hcen ⟨0, Nat.succ_pos _⟩
    have hZF : (E.subfamily p).HasSncWith D₀ := HasSncWith.subfamily hhead.2.1 p
    have hG : ((E.subfamily p).append H).HasSncWith D₀ :=
      hasSncWith_append_of_le_on f (fun x _ => hp x trivial) hZF hleH
    have hnext : (((E.subfamily p).append H).totalTransform D₀).IsSncOn Set.univ := by
      intro x' _
      have hdata : ∀ x ∈ D₀.support, ∃ (n₀ : ℕ) (z : Fin n₀ → X.presheaf.stalk x),
          (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
            (n₀ : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
          (∃ c : {i : ((E.subfamily p).append H).ι //
              x ∈ (((E.subfamily p).append H).component i).support} → Fin n₀,
            Function.Injective c ∧
              ∀ i, (((E.subfamily p).append H).component i.1).stalkIdeal x = span {z (c i)}) ∧
          ∃ s : Finset (Fin n₀), D₀.stalkIdeal x = span (z '' ↑s) := by
        intro x hx
        obtain ⟨n₀, z, ⟨hrs, c, hcinj, hc⟩, s, hs⟩ := hG x hx
        exact ⟨n₀, z, hrs, ⟨c, hcinj, hc⟩, s, hs⟩
      by_cases hexc : x' ∈ D₀.exceptionalDivisor.support
      · obtain ⟨-, m₀, z, hz, c', hc'inj, hc'⟩ :=
          exists_snc_data_totalTransform_of_mem_support f ((E.subfamily p).append H).component D₀
            hdata x' hexc
        exact ⟨m₀, z, hz, c', hc'inj, hc'⟩
      · obtain ⟨n₀, z, ⟨hspan, hdim⟩, c, hcinj, hc⟩ := hp (D₀.blowUpπ x') trivial
        have h' := exists_snc_data_totalTransform_of_notMem_support D₀
          ((E.subfamily p).append H).component hexc hspan.symm hdim c hcinj hc
        exact ⟨n₀, fun i => D₀.blowUpπ.stalkMap x' (z i), ⟨h'.1.1.symm, h'.1.2⟩, h'.2⟩
    have hnext' : (((E.totalTransform D₀).subfamily (extendPred p)).append
        (H.strictTransform D₀)).IsSncOn Set.univ :=
      isSncOn_of_injective_components (stepIdx E p) (stepIdx_injective E p)
        (component_stepIdx E p D₀ H) hnext
    have ih := isSncOn_univ_subfamily_append_of_forall_le_center n
        (D₀.blowUpπ ≫ f) rest ht
      (H.strictTransform D₀) (fun i => hHs i.succ) (fun i => hcen i.succ) (extendPred p) hnext'
    refine isSncOn_subfamily_append_mono ?_ _ ih
    intro i hi b hb
    rcases b with a | u
    · exact hi a hb
    · trivial

/-- "`H + E` is also a simple normal crossing divisor" [Kol07, 104, Step 2.2], for the exceptional
sub-family: along a smooth blow-up sequence of order `m` starting with an snc family `E`, whose
centers lie in the transforms of a smooth divisor `H` with smooth transforms, the exceptional
sub-family of `E_r` together with `H_r` is a simple normal crossing family. -/
theorem isSnc_exceptionalFamily_append (n : ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] (S : BlowUpSequence X) {J : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f J E m) (hE : E.IsSnc)
    (H : X.IdealSheafData) (hH : IsSmoothDivisor H)
    (hHs : ∀ i : Fin (S.length + 1), IsSmoothDivisor (S.strictTransformSeq H i))
    (hcen : ∀ i : Fin S.length, S.strictTransformSeq H i.castSucc ≤ S.center i) :
    ((S.exceptionalFamily E).append (S.strictTransformSeq H (Fin.last _))).IsSnc := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  refine (DivisorFamily.isSnc_iff_isSncOn_univ _).mpr ⟨?_, ?_⟩
  · intro i
    rcases i with b | u
    · exact (IsOrderSeq.isSnc_totalTransformSeq f n hS hE (Fin.last _)).1 b.1
    · exact (hHs (Fin.last _)).1
  · exact isSncOn_univ_subfamily_append_of_forall_le_center n f S hS H hHs hcen (fun _ => False)
      (isSncOn_subfamily_false_append f E hH Set.univ)

end Hironaka.Sequence
