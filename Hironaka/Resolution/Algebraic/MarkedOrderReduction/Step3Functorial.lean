/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step3Input
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.Monomial.Geometric.EnumerationIndep
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Exponent
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Monomial.Geometric.PullbackRun
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.IdealSheaf.Order.Smooth
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functoriality of the geometric Step 3 on a marked triple under smooth surjections

The first clause of [Kol07, 34.1] for Step 3 of the proof of [Kol07, Theorem 107]: the geometric
Step 3 of the pull-back data `(Y, h^* I, m, h^{-1} E)` is the pull-back of the geometric Step 3 of
`(X, I, m, E)`. `Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackRun.lean` proves it for a
piece family refining the input family along `h` (`realize_pullback_of_surjective`), and
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Refinement.lean` produces the concrete refining
family: the components of `h^{-1} E` with the exponents `Φ.exponentAt ∘ h`
(`refinesAlong_ofDivisorFamily`). Step 3's input family on `Y` (`step3Family`) has the same
components and labels but the exponents `ord_η (h^* I)` at the generic points `η` of the components
of `h^{-1} E`: they agree with `Φ.exponentAt (h η)` because a flat morphism sends `η` to a generic
point of the member (`mem_genericPoints_support_of_flat`), where the marked monomial ideal `M(I)`
has the order of `I` (`ord_monomialPart_of_mem_genericPoints`) and the order of the monomial ideal
is the sum over the single piece through the point (`ord_monomial_eq_total`,
`faceAt_eq_singleton_of_mem_genericPoints`); this is `exponentAt_step3Family_of_mem_genericPoints`.
The refining family is taken with Step 3's own enumeration of the components of `h^{-1} E`
(`componentsEquiv`), so the two families on `Y` coincide outright
(`ofDivisorFamily_congr_of_forall`); the pull-back data are canonical (`T'.I = h^* I`, `T'.E =
h^{-1} E`, `T'.m = m`, the structure morphism `h ≫ f`), which the proof of
`step3Seq_pullback_of_surjective` makes literal by destructuring `T'`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Monomial Hironaka.Monomial.PieceFamily

namespace Hironaka.Monomial.PieceFamily

/-- The realized runs of two equal families, with any two validity proofs, coincide. -/
theorem realize_congr_family {X : Scheme.{u}} {Φ₁ Φ₂ : PieceFamily X} (e : Φ₁ = Φ₂) {n m : ℕ}
    (hV₁ : Φ₁.IsValid n m) (hV₂ : Φ₂.IsValid n m) : Φ₁.realize n m hV₁ = Φ₂.realize n m hV₂ := by
  subst e
  rfl

end Hironaka.Monomial.PieceFamily

namespace Hironaka.BMO

section Exponent

variable {k : Type u} [Field k] [CharZero k] (T : MarkedTriple k)

/-- At a generic point of a component of a member, the exponent of Step 3's input family is the
order of `I`: the point lies on exactly one piece, whose exponent is the order of the marked
monomial ideal `M(I)` there (`ord_monomial_eq_total` through `monomial_exponentAt_step3Family`),
which is the order of `I` at a generic point. -/
theorem exponentAt_step3Family_of_mem_genericPoints {j : T.E.ι} {x : T.X.left}
    (hx : x ∈ (T.E.component j).support.genericPoints) :
    (step3Family T).exponentAt x = (T.I.ord x).toNat := by
  have := T.smooth
  obtain ⟨c, -, -, -, hface, hexp⟩ := faceAt_eq_singleton_of_mem_genericPoints
    (f := T.X.left ↘ Spec (.of k)) (Φ := step3Family T) T.isSnc (step3Family_realizes T) hx
  have h1 := ord_monomial_eq_total (f := T.X.left ↘ Spec (.of k)) (Φ := step3Family T) T.isSnc
    (step3Family_realizes T) x
  rw [monomial_exponentAt_step3Family, ord_monomialPart_of_mem_genericPoints T.toTriple j hx,
    hface] at h1
  rw [h1, hexp, ENat.toNat_natCast]
  exact (Finset.sum_singleton _ _).symm

end Exponent

section Step3

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

/-- **The geometric Step 3 of a marked triple commutes with smooth surjections** (the first clause
of [Kol07, 34.1] for Step 3; [Kol07, 111]: "the functoriality conditions are just as obvious as
before"): the input family of the pull-back data is the concrete refining family of
`refinesAlong_ofDivisorFamily`, taken with Step 3's own enumeration of the components
(`componentsEquiv`), up to the exponents, which agree at the generic points
(`exponentAt_step3Family_of_mem_genericPoints`); the two families are then equal
(`ofDivisorFamily_congr_of_forall`), and `realize_pullback_of_surjective` applies. -/
theorem step3Seq_pullback_of_surjective (T T' : MarkedTriple k)
    (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') : step3Seq T' hT' = (step3Seq T hT).pullback h := by
  obtain ⟨⟨hover, hI, hE⟩, hm⟩ := hp
  cases T' with
  | mk toT m' =>
  cases toT with
  | mk X' eq' I' hI' E' hE' =>
  obtain ⟨⟨X', _, hom'⟩, ft, sep⟩ := X'
  dsimp only at h hover hI hE hm
  change h ≫ (T.X.left ↘ Spec (.of k)) = hom' at hover
  subst hI hE hm hover
  have hsm := T.smooth
  have hqc' : QuasiCompact (h ≫ (T.X.left ↘ Spec (.of k))) := ft.toQuasiCompact
  have hN := Hironaka.BD.noetherianSpace_triple T.toTriple
  have hN' : NoetherianSpace X' := Hironaka.BD.noetherianSpace_triple
    (⟨.ofHom (h ≫ (T.X.left ↘ Spec (.of k))) ft sep, eq', T.I.comap h, hI', T.E.comap h, hE'⟩ :
      Triple k)
  -- the refining family on `Y`, with Step 3's enumeration of the components
  set σ' : Fin (Nat.card (Components (T.E.comap h))) ≃ Components (T.E.comap h) :=
    @componentsEquiv _ hN' (T.E.comap h) with hσ'
  have hρ := refinesAlong_ofDivisorFamily (f := T.X.left ↘ Spec (.of k)) (h := h)
    (Φ := step3Family T) T.isSnc (step3Family_realizes T) hE' σ'
  have hreal : (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
      (labelIso T.E) σ').Realizes (T.E.comap h) (labelIso T.E) :=
    ofDivisorFamily_realizes (T.E.comap h) _ (labelIso T.E) σ' hE'
  have hΦ' : (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
      (labelIso T.E) σ').Realizes (T.E.comap h)
      ((labelIso T.E).trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) := by
    refine ⟨fun j => ?_, hreal.disjoint⟩
    change ((T.E.comap h).component j).support =
      ((Finset.range (ofDivisorFamily (T.E.comap h)
        (fun y => (step3Family T).exponentAt (h y)) (labelIso T.E) σ').nextComp).filter
        fun c => (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
          (labelIso T.E) σ').label c = (labelIso T.E j : ℕ)).sup
        (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
          (labelIso T.E) σ').piece
    exact hreal.support_eq j
  have hn' : ∃ n' ≤ n, SmoothOfRelativeDimension n' (h ≫ (T.X.left ↘ Spec (.of k))) := hT'.2.1
  have hV' : (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
      (labelIso T.E) σ').IsValid n m :=
    valid_of_realizes _ (h ≫ (T.X.left ↘ Spec (.of k))) hE' hreal hT.1 hn'
  have key := realize_pullback_of_surjective (T.X.left ↘ Spec (.of k)) hs T.isSnc
    (step3Family_realizes T) (step3Family_isValid T hT) hT.2.1 hn' hρ hΦ' hV'
  -- the input family of the pull-back data is the refining family, up to the exponents
  have hagree : ∀ c : Components (T.E.comap h),
      ((T.I.comap h).ord (c.2 : X')).toNat = (step3Family T).exponentAt (h (c.2 : X')) := by
    intro c
    rw [Scheme.IdealSheafData.ord_comap_of_smooth]
    exact (exponentAt_step3Family_of_mem_genericPoints T
      (mem_genericPoints_support_of_flat h _ c.2.2)).symm
  have hfam : ofDivisorFamily (T.E.comap h) (fun y => ((T.I.comap h).ord y).toNat)
      (labelIso T.E) σ' = ofDivisorFamily (T.E.comap h)
        (fun y => (step3Family T).exponentAt (h y)) (labelIso T.E) σ' :=
    ofDivisorFamily_congr_of_forall (E := T.E.comap h) _ _ (labelIso T.E) σ' hagree
  change (ofDivisorFamily (T.E.comap h) (fun y => ((T.I.comap h).ord y).toNat) (labelIso T.E)
    σ').realize n m _ = ((step3Family T).realize n m (step3Family_isValid T hT)).pullback h
  rw [← key]
  exact realize_congr_family hfam _ _

end Step3

end Hironaka.BMO
