/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Theorem97Setup
public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeq
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.CentersCosupport
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 97: the setting and the induction, in marked form

[Kol07, Theorem 97] and its proof: with `ψ, ψ' : U ⇉ X` the maps of an étale equivalence and
`B^U := ψ^*B = ψ'^*B'` the common pull-back, the proof is an induction on the stage carrying
(1) `(X_i, I_i) = (X'_i, I'_i)`, (2) the lifts `ψ_i, ψ'_i : U_i ⇉ X_i` satisfy
`im(ψ^*_i − ψ'^*_i) ⊂ (Π^U_i)^{-1}_*(MC(I^U_0), 1)`, (3) `Z_{i−1} = Z'_{i−1}`, with the remark that
`Z^U_i ⊂ W_i := cosupp((Π^U_i)^{-1}_*(MC(I^U_0), 1))` by Corollary 77. This file recasts the
induction in a **marked form**: the datum carried along the induction is the marked ideal
`(M, 1)`, `M := MC(ψ^*I)`, with `M_i := (Π^U_i)^{-1}_*(M, 1) ≤ 𝒪(Z^U_i)` (the containment of
ideals, `IsMarkedOneSeq` of `Hironaka/Resolution/Algebraic/MaximalContact/Theorem97Setup.lean`), and
no property of `I` is used; indeed the transforms `I_i` are, as the Warning in [Kol07, 104] says, in
general neither D-balanced nor MC-invariant.

* **The setting**: `C = ψ^*B` is a smooth blow-up sequence of order `m` for `(U, ψ^*I, ψ^{-1}E)`
  (`IsOrderSeq.pullback` along the étale `ψ`) and has no empty centre.
* **The marked ideals**: [Kol07, Corollary 77] with `j = m − 1`
  (`IsOrderSeq.leOrdAlong_markedTransformSeq_MC`) gives `ord_{Z^U_i} M_i ≥ 1`; the centres are
  smooth, hence reduced, so `M_i ≤ 𝒪(Z^U_i)`, the hypothesis (ii) of the marked form. The
  containment must be one of ideals: for a non-reduced centre `J = (x², y²)` and `M = (x, y)` have
  equal zero sets but `M ⊄ J`.
* **The lifts**: the stage lifts `ψ_i` are étale (base change), and every centre of `B` (of `B'`)
  lies in the image of the lift of `ψ` (of `ψ'`), `CentersInRange`, because the centres of an
  order-`m` sequence lie over `cosupp(I, m) ⊆ im ψ`: the hypothesis (iii).
* **The induction**: a structural induction on the common pull-back `C`, generalizing the base
  `X` and the sequences and maps. For `C = cons U Z^U C₁` both `B` and `B'` are `cons`, with
  `Z.comap ψ = Z^U = Z'.comap ψ'`; the first centres are equal by the descent of closed subschemes
  along flat maps agreeing on the common preimage (`eq_of_comap_eq_of_agreeOn`; Kollár's
  `Z_i = ψ_i(Z^U_i) = ψ'_i(Z^U_i) = Z'_i`), and after the substitution `Z' := Z` the two lifts
  `blowUpMap ψ Z`, `blowUpMap ψ' Z`, the second transported to the common source along
  `Z.comap ψ = Z.comap ψ'`, agree on `V(π^{-1}_*(M, 1))` by the **one-step descent of agreement
  through a blow-up**, taken here as an explicit hypothesis `hstep` in its exact statement and
  proved as `agreeOn_blowUpMap` in
  `Hironaka/Resolution/Algebraic/MaximalContact/AgreeOnBlowUpKernel.lean`; the two are combined in
  `Hironaka/Resolution/Algebraic/MaximalContact/Theorem97.lean`. The tails are handled by the
  induction hypothesis.
* **Theorem 97 from the marked form**: with `M := MC(ψ^*I)`, (i) is condition (2) of
  [Kol07, Definition 96], (ii) the marked ideals, (iii) the lifts.
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory Scheme IdealSheafData BlowUpSequence AlgebraicGeometry Algebra
  Hironaka.Sequence

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The étale part of Kollár's assertion (2), "`ψ, ψ'` lift to étale surjections
`ψ_i, ψ'_i : U_i ⇉ X_i`" (proof of [Kol07, Theorem 97]): the stage lifts of an étale `ψ` are
étale, by base change along the cartesian squares `isPullback_pullbackStageHom`. -/
theorem etale_pullbackStageHom {U : Scheme.{u}} (S : BlowUpSequence X) (ψ : U ⟶ X) [Etale ψ]
    (i : Fin (S.length + 1)) : Etale (S.pullbackStageHom ψ i) :=
  property_of_isPullback @Etale (isPullback_pullbackStageHom S ψ i) inferInstance

section Setting

variable [CharZero k]

/-- Kollár's common pull-back `B^U`: the pull-back `ψ^*B` of a smooth blow-up sequence of order `m`
for `(X, I, E)` along the étale `ψ` of an étale equivalence is a smooth blow-up sequence of order
`m` for `(U, ψ^*I, ψ^{-1}E)` (`IsOrderSeq.pullback` along a map smooth of relative dimension
`0`). -/
theorem EtaleEquivSeq.isOrderSeq_pullback (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    {B B' : BlowUpSequence X} (hB : B.IsOrderSeq f I E m) (e : EtaleEquivSeq f I m B B') :
    (B.pullback e.ψ).IsOrderSeq (e.ψ ≫ f) (I.comap e.ψ) (E.comap e.ψ) m :=
  IsOrderSeq.pullback f n e.ψ (d := 0) hB

/-- The common pull-back of an étale equivalence has no empty centre when `B` has none: every centre
of the order-`m` sequence `B` lies over `cosupp(I, m) ⊆ im ψ` (`centersInRange_of_cosupp_le_range`,
`noEmptyCenters_pullback_of_centersInRange`). -/
theorem EtaleEquivSeq.noEmptyCenters_pullback (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    {B B' : BlowUpSequence X} (hB : B.IsOrderSeq f I E m) (hne : B.NoEmptyCenters)
    (e : EtaleEquivSeq f I m B B') : (B.pullback e.ψ).NoEmptyCenters :=
  noEmptyCenters_pullback_of_centersInRange e.ψ hne
    (centersInRange_of_cosupp_le_range f n hB e.ψ e.covers)

/-- Kollár's "étale surjections `ψ_i`" in the form where images contain the cosupport: every centre
of `B` lies in the image of the corresponding lift of `ψ`,
`Z_i ⊆ Π_i^{-1}(cosupp(I, m)) ⊆ Π_i^{-1}(im ψ) = im ψ_i`. -/
theorem EtaleEquivSeq.centersInRange (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    {B B' : BlowUpSequence X} (hB : B.IsOrderSeq f I E m) (e : EtaleEquivSeq f I m B B') :
    B.CentersInRange e.ψ :=
  centersInRange_of_cosupp_le_range f n hB e.ψ e.covers

/-- The second map: every centre of `B'` lies in the image of the corresponding lift of `ψ'`. -/
theorem EtaleEquivSeq.centersInRange' (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {I : X.IdealSheafData} {m : ℕ} {E' : DivisorFamily X}
    {B B' : BlowUpSequence X} (hB' : B'.IsOrderSeq f I E' m) (e : EtaleEquivSeq f I m B B') :
    B'.CentersInRange e.ψ' :=
  centersInRange_of_cosupp_le_range f n hB' e.ψ' e.covers'

/-- Kollár's "note that `Z^U_i ⊂ W_i` by (77)" (proof of [Kol07, Theorem 97]): for `m ≥ 1` the
common pull-back `C = ψ^*B` is of order `≥ 1` for the marked ideal `(MC(ψ^*I), 1)` in the
containment form, `M_i = (Π^U_i)^{-1}_*(MC(ψ^*I), 1) ≤ 𝒪(Z^U_i)` at every stage:
[Kol07, Corollary 77] with `j = m − 1` (`IsOrderSeq.leOrdAlong_markedTransformSeq_MC`) gives
`ord_{Z^U_i} M_i ≥ 1`, and the centre `Z^U_i` is smooth, hence reduced, so `M_i ≤ 𝒪(Z^U_i)`
(`le_of_leOrdAlong_one_of_smooth` on the stage `U_i`, smooth of relative dimension `n` over `k`). -/
theorem EtaleEquivSeq.isMarkedOneSeq_pullback (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {I : X.IdealSheafData} {m : ℕ} (hm : 1 ≤ m)
    {E : DivisorFamily X} {B B' : BlowUpSequence X} (hB : B.IsOrderSeq f I E m)
    (e : EtaleEquivSeq f I m B B') :
    (B.pullback e.ψ).IsMarkedOneSeq (MC (e.ψ ≫ f) (I.comap e.ψ) m) := by
  have hC := e.isOrderSeq_pullback f n hB
  have hψf : SmoothOfRelativeDimension n (e.ψ ≫ f) := by
    have := smoothOfRelativeDimension_comp 0 n e.ψ f
    simpa using this
  intro i
  have hle := IsOrderSeq.leOrdAlong_markedTransformSeq_MC (e.ψ ≫ f) n hm hC i
  have hsm : SmoothOfRelativeDimension n ((B.pullback e.ψ).stageMap i.castSucc ≫ (e.ψ ≫ f)) :=
    IsSmooth.smoothOfRelativeDimension_stageMap hC.1 i.castSucc
  have hsmZ := hC.1 i
  exact le_of_leOrdAlong_one_of_smooth ((B.pullback e.ψ).stageMap i.castSucc ≫ (e.ψ ≫ f)) n
    ((B.pullback e.ψ).center i) hle

end Setting

/-- **The marked form of [Kol07, Theorem 97]**, given the one-step descent: for flat
`ψ, ψ' : U ⟶ X`, an ideal sheaf `M` on `U`, and blow-up sequences `B, B'` on `X` with a common
pull-back `C = ψ^*B = ψ'^*B'`, if (i) `ψ, ψ'` agree on `V(M)`, (ii) `C` is of order `≥ 1` for
`(M, 1)` (`IsMarkedOneSeq`), and (iii) the centres of `B` (of `B'`) lie in the images of the lifts
of `ψ` (of `ψ'`), then `B = B'`, **given the one-step descent of agreement through a blow-up** (the
hypothesis `hstep`, in the exact shape of `agreeOn_blowUpMap`). Structural induction on `C`: for
`nil`, both sequences have length `0` (`length_pullback`); for `cons U Z^U C₁`, both sequences are
`cons` with `Z.comap ψ = Z^U = Z'.comap ψ'` (the injectivity of `cons`, then the substitution
`Z^U := Z.comap ψ`), the first centres are equal by the descent of closed subschemes along flat
maps agreeing on the common preimage (`eq_of_comap_eq_of_agreeOn`, the agreement on `V(Z^U)` from
`V(M)` by `AgreeOn.mono` and (ii) at stage `0`), the lifts `blowUpMap ψ Z` and `blowUpMap ψ' Z`
(the latter transported to the common source along `Z.comap ψ = Z.comap ψ'`) agree on
`V(π^{-1}_*(M, 1))` by `hstep`, and the induction hypothesis applies to the tails with (ii), (iii)
read off by `isMarkedOneSeq_cons_iff`, `centersInRange_cons_iff` and the transports
`pullback_eqToHom_comp`, `centersInRange_eqToHom_comp`. Of Kollár's three assertions, (3) is the
descent, (1) the substitution, (2) `hstep`. -/
theorem eq_of_pullback_eq_of_agreeOn_of_step
    (hstep : ∀ {U X : Scheme.{u}} (f g : U ⟶ X) (C : X.IdealSheafData) (M : U.IdealSheafData)
      (hJ : C.comap f = C.comap g), M ≤ C.comap f → AgreeOn f g M →
      AgreeOn (Scheme.Hom.blowUpMap f C) (eqToHom (congrArg Scheme.IdealSheafData.blowUp hJ) ≫
          Scheme.Hom.blowUpMap g C)
        (M.markedTransform (C.comap f) 1))
    {U : Scheme.{u}} (ψ ψ' : U ⟶ X) [Flat ψ] [Flat ψ'] (M : U.IdealSheafData)
    (h1 : AgreeOn ψ ψ' M) (B B' : BlowUpSequence X) (C : BlowUpSequence U)
    (hB : B.pullback ψ = C) (hB' : B'.pullback ψ' = C) (h2 : C.IsMarkedOneSeq M)
    (h3 : B.CentersInRange ψ) (h3' : B'.CentersInRange ψ') : B = B' := by
  induction C generalizing X with
  | nil U =>
    cases B with
    | nil _ =>
      cases B' with
      | nil _ => rfl
      | cons _ D' r' =>
        have hl := congrArg BlowUpSequence.length hB'
        rw [length_pullback] at hl
        exact absurd hl (by simp [BlowUpSequence.length])
    | cons _ D r =>
      have hl := congrArg BlowUpSequence.length hB
      rw [length_pullback] at hl
      exact absurd hl (by simp [BlowUpSequence.length])
  | cons U ZU C₁ ih =>
    cases B with
    | nil _ =>
      have hl := congrArg BlowUpSequence.length hB
      rw [length_pullback] at hl
      exact absurd hl (by simp [BlowUpSequence.length])
    | cons _ Z r =>
      cases B' with
      | nil _ =>
        have hl := congrArg BlowUpSequence.length hB'
        rw [length_pullback] at hl
        exact absurd hl (by simp [BlowUpSequence.length])
      | cons _ Z' r' =>
        rw [pullback_cons] at hB hB'
        obtain ⟨e, hr⟩ := BlowUpSequence.cons.inj hB
        subst e
        obtain ⟨e', hr'⟩ := BlowUpSequence.cons.inj hB'
        obtain ⟨hM0, h2t⟩ := (isMarkedOneSeq_cons_iff _ _ _).1 h2
        obtain ⟨hZ0, h3t⟩ := (centersInRange_cons_iff _ _ _).1 h3
        obtain ⟨hZ0', h3t'⟩ := (centersInRange_cons_iff _ _ _).1 h3'
        have hZZ : Z = Z' :=
          eq_of_comap_eq_of_agreeOn ψ ψ' Z Z' hZ0 hZ0' e'.symm (AgreeOn.mono hM0 h1)
        subst hZZ
        have hstep' := hstep ψ ψ' Z M e'.symm hM0 h1
        have hflat : Flat (Scheme.Hom.blowUpMap ψ Z) :=
          property_of_isPullback @Flat (isPullback_blowUpMap ψ Z)
            inferInstance
        have hflat₀ : Flat (Scheme.Hom.blowUpMap ψ' Z) :=
          property_of_isPullback @Flat (isPullback_blowUpMap ψ' Z)
            inferInstance
        have hflat' : Flat (eqToHom (congrArg Scheme.IdealSheafData.blowUp e'.symm) ≫
            Scheme.Hom.blowUpMap ψ' Z) := inferInstance
        have hr'' : r'.pullback (eqToHom (congrArg Scheme.IdealSheafData.blowUp e'.symm) ≫
            Scheme.Hom.blowUpMap ψ' Z) = C₁ :=
          eq_of_heq
            ((pullback_eqToHom_comp r' (congrArg Scheme.IdealSheafData.blowUp e'.symm)
                (Scheme.Hom.blowUpMap ψ' Z)).trans hr')
        exact congrArg (cons X Z) (ih (Scheme.Hom.blowUpMap ψ Z)
          (eqToHom (congrArg Scheme.IdealSheafData.blowUp e'.symm) ≫ Scheme.Hom.blowUpMap ψ' Z)
          (M.markedTransform (Z.comap ψ) 1) hstep' r r' (eq_of_heq hr) hr'' h2t h3t
          ((centersInRange_eqToHom_comp r' (congrArg Scheme.IdealSheafData.blowUp e'.symm)
              (Scheme.Hom.blowUpMap ψ' Z)).2 h3t'))

/-- [Kol07, Theorem 97] reduced to the marked form: for `X` smooth of relative dimension `n` over
`k` of characteristic zero, `m ≥ 1`, smooth blow-up sequences `B, B'` of order `m` for `(X, I, E)`,
`(X, I, E')` that are étale equivalent through `e`, and the one-step descent `hstep`, `B = B'`: the
marked form with `M := MC(ψ^*I)`; (i) is condition (2) of [Kol07, Definition 96] (`e.h2`), (ii) is
`isMarkedOneSeq_pullback`, (iii) is `centersInRange`/`centersInRange'`; étale maps are flat. -/
theorem eq_of_etaleEquivSeq_of_step
    (hstep : ∀ {U X : Scheme.{u}} (f g : U ⟶ X) (C : X.IdealSheafData) (M : U.IdealSheafData)
      (hJ : C.comap f = C.comap g), M ≤ C.comap f → AgreeOn f g M →
      AgreeOn (Scheme.Hom.blowUpMap f C) (eqToHom (congrArg Scheme.IdealSheafData.blowUp hJ) ≫
          Scheme.Hom.blowUpMap g C)
        (M.markedTransform (C.comap f) 1))
    [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {I : X.IdealSheafData} {m : ℕ} (hm : 1 ≤ m) {E E' : DivisorFamily X} {B B' : BlowUpSequence X}
    (hB : B.IsOrderSeq f I E m) (hB' : B'.IsOrderSeq f I E' m) (e : EtaleEquivSeq f I m B B') :
    B = B' :=
  eq_of_pullback_eq_of_agreeOn_of_step hstep e.ψ e.ψ' (MC (e.ψ ≫ f) (I.comap e.ψ) m) e.h2 B B'
    (B.pullback e.ψ) rfl e.h3.symm (e.isMarkedOneSeq_pullback f n hm hB) (e.centersInRange f n hB)
    (e.centersInRange' f n hB')

end AlgebraicGeometry.Scheme.IdealSheafData
