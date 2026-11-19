/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step3Globalization
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.MaximalContact.PullbackSmooth
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Pulling a local cover back along a smooth morphism

[Kol07, 34]: "the claimed isomorphism is unique, and hence the existence is a local question". The
functoriality of the globalised functor `BO_{n,m}` is checked after pulling a local cover of the
target back to the source. This module supplies that pull-back: for a local cover `g : TU → T` (an
`M`-cover into the local class in the sense of [Kol07, Theorem 105], `IsLocalCover`) and a smooth
`h : T' → T` along which `T'` carries the pull-back data of `T`, the fibre product `W = TU ×_T T'`
is a local cover of `T'` along the second projection (an open-immersion coproduct, surjective),
carries the pull-back data of `TU` along the first projection (smooth, and surjective when `h` is),
and lies in the local class: `BOClass` along the open-immersion leg, the hypersurface of maximal
contact pulled back along the smooth leg (`isSmoothDivisor_comap_of_smooth`,
`isMaximalContact_comap_of_smooth`). The construction is `exists_fibreTriple` of
`Hironaka/Resolution/Algebraic/Kol07/GlobalizeDescent.lean` with one leg smooth instead of an
open-immersion coproduct; the triple on `W` is `Triple.pullback` along the open-immersion leg. It is
used in `Hironaka/Resolution/Algebraic/OrderReduction/Step3Clauses.lean`.
-/

public section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Hironaka Scheme
  BlowUpSequence Hironaka.Sequence Hironaka.Snc Scheme.IdealSheafData

namespace Hironaka.BO

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

/-- The pull-back of a local cover along a smooth morphism carrying pull-back data: for
`hc : IsLocalCover … T TU g` and `h : T'.X.left ⟶ T.X.left` smooth with `T'.IsPullbackOf T h`, the
fibre product `W = TU ×_T T'` is a local cover of `T'` along the projection `g'` and carries the
pull-back data of `TU` along the smooth projection `h'`, which is surjective when `h` is. -/
theorem exists_localCover_pullback {T T' TU : Triple k} {h : T'.X.left ⟶ T.X.left} [Smooth h]
    (hpb : T'.IsPullbackOf T h) {g : TU.X.left ⟶ T.X.left}
    (hc : Triple.IsLocalCover openImmersionCoprods (Triple.BOClass n m) (localClass n m) T TU g)
    (hT' : Triple.BOClass n m T') :
    ∃ (W : Triple k) (h' : W.X.left ⟶ TU.X.left) (g' : W.X.left ⟶ T'.X.left), IsPullback h' g' g h ∧
      W.IsPullbackOf TU h' ∧
      Triple.IsLocalCover openImmersionCoprods (Triple.BOClass n m) (localClass n m) T' W g' ∧
      Smooth h' ∧ (Function.Surjective h → Function.Surjective h') := by
  obtain ⟨hT, hTU, hM, hs, hp⟩ := hc
  have sq : IsPullback (Limits.pullback.fst g h) (Limits.pullback.snd g h) g h :=
    IsPullback.of_hasPullback g h
  have hM' : openImmersionCoprods (Limits.pullback.snd g h) :=
    isStableUnderBaseChange_openImmersionCoprods.of_isPullback sq hM
  have hsm' : Smooth (Limits.pullback.fst g h) :=
    smooth_isStableUnderBaseChange.of_isPullback sq.flip ‹Smooth h›
  have hs' : Function.Surjective (Limits.pullback.snd g h) := fun y' => by
    obtain ⟨y, hy⟩ := hs (h y')
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := h) y y' hy
    exact ⟨z, hz⟩
  have hsurj : Function.Surjective h → Function.Surjective (Limits.pullback.fst g h) := by
    intro hhs y
    obtain ⟨y', hy'⟩ := hhs (g y)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := h) y y' hy'.symm
    exact ⟨z, hz⟩
  have hsep : IsSeparated (Limits.pullback.snd g h) := openImmersionCoprods_isSeparated hM'
  have het : Etale (Limits.pullback.snd g h) := openImmersionCoprods_etale _ hM'
  let _ : (Limits.pullback g h).Over (Spec (CommRingCat.of k)) :=
    ⟨Limits.pullback.snd g h ≫ (T'.X.left ↘ Spec (CommRingCat.of k))⟩
  have _ : (Limits.pullback.snd g h).IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have hqc : QuasiCompact g := by
    have : QuasiCompact (g ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := by
      rw [hp.1]
      infer_instance
    exact QuasiCompact.of_comp g (T.X.left ↘ Spec (CommRingCat.of k))
  have hcpt : CompactSpace T'.X.left :=
    QuasiCompact.compactSpace_of_compactSpace (T'.X.left ↘ Spec (CommRingCat.of k))
  have : LocallyOfFiniteType ((Limits.pullback g h) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs
      (LocallyOfFiniteType (Limits.pullback.snd g h ≫ (T'.X.left ↘ Spec (CommRingCat.of k))))
  have : IsSeparated ((Limits.pullback g h) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (IsSeparated (Limits.pullback.snd g h ≫ (T'.X.left ↘ Spec (CommRingCat.of k))))
  have : QuasiCompact ((Limits.pullback g h) ↘ Spec (CommRingCat.of k)) := inferInstance
  have hY : ∃ n : ℕ,
      SmoothOfRelativeDimension n ((Limits.pullback g h) ↘ Spec (CommRingCat.of k)) := by
    obtain ⟨n, hn⟩ := T'.smoothOfRelativeDimension
    exact ⟨n, by
      simpa using smoothOfRelativeDimension_comp 0 n (Limits.pullback.snd g h)
        (T'.X.left ↘ Spec (CommRingCat.of k))⟩
  have hW' := Triple.isPullbackOf_pullback T' hY (Limits.pullback.snd g h)
  have hcond : Limits.pullback.fst g h ≫ g = Limits.pullback.snd g h ≫ h :=
    Limits.pullback.condition
  have hWU : (Triple.pullback T' hY (Limits.pullback.snd g h)).IsPullbackOf TU
      (Limits.pullback.fst g h) := by
    refine ⟨?_, ?_, ?_⟩
    · change Limits.pullback.fst g h ≫ (TU.X.left ↘ Spec (CommRingCat.of k)) =
        Limits.pullback.snd g h ≫ (T'.X.left ↘ Spec (CommRingCat.of k))
      rw [← hp.1, ← hpb.1, ← Category.assoc, ← Category.assoc, hcond]
    · change T'.I.comap (Limits.pullback.snd g h) = TU.I.comap (Limits.pullback.fst g h)
      rw [hp.2.1, hpb.2.1, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        hcond]
    · change T'.E.comap (Limits.pullback.snd g h) = TU.E.comap (Limits.pullback.fst g h)
      rw [hp.2.2, hpb.2.2, ← DivisorFamily.comap_comp, ← DivisorFamily.comap_comp, hcond]
  have hL : localClass n m (Triple.pullback T' hY (Limits.pullback.snd g h)) := by
    refine ⟨boClass_isPullbackOf hT' hM' hW', ?_⟩
    obtain ⟨H, hH, hle⟩ := hTU.2
    obtain ⟨d, hd⟩ := TU.smoothOfRelativeDimension
    refine ⟨H.comap (Limits.pullback.fst g h),
      isSmoothDivisor_comap_of_smooth (TU.X.left ↘ Spec (.of k)) (Limits.pullback.fst g h) hH, ?_⟩
    have e1 : Limits.pullback.fst g h ≫ (TU.X.left ↘ Spec (.of k)) =
        Limits.pullback.snd g h ≫ (T'.X.left ↘ Spec (.of k)) := by
      rw [← hp.1, ← hpb.1, ← Category.assoc, ← Category.assoc, hcond]
    have e2 : TU.I.comap (Limits.pullback.fst g h) = T'.I.comap (Limits.pullback.snd g h) := by
      rw [hp.2.1, hpb.2.1, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        hcond]
    have := IdealSheafData.isMaximalContact_comap_of_smooth (TU.X.left ↘ Spec (.of k)) d
        (Limits.pullback.fst g h) hle
    rw [e1, e2] at this
    exact this
  exact ⟨Triple.pullback T' hY (Limits.pullback.snd g h), Limits.pullback.fst g h,
    Limits.pullback.snd g h, sq, hWU, ⟨hT', hL, hM', hs', hW'⟩, hsm', hsurj⟩

end Hironaka.BO
