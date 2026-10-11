/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSNCSupportedMonomialIdeal
import Hironaka.Invariant.PrincipalMonomialExponent
import Hironaka.Invariant.PrincipalIdealProducts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Nodup

set_option autoImplicit false

/-!
# Produced SNC coefficients are exponents of the original divisor

Actual powers and products are given genuine coordinate generators;
the established principal-monomial exponent calculation then identifies
the produced coefficients at every original point of their carrier.
Source: Włodarczyk 2005, Step 2.
Blueprint: `hironaka-snc-component-coefficients.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSNCComponentCoefficients

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open NormalCrossings InvertibleIdealQuotient HironakaDivisorResidual
  HironakaDivisorResidualUnit HironakaSNCSupportedMonomialIdeal
  MonomialPart MonomialCase MemberPullback IdealWeightPowers
  GermIdealTotalTransform RelativePrincipalizationSpan BlowupFlatCoordinates
  DivisorExponent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine principal stalk generation produces generation of every
actual ideal power, including the zeroth power. -/
theorem idealPow_mem_iff_of_generator {I : GermIdeal n M} {x : M} {u : M → ℂ}
    (hu : HolomorphicAt n u x)
    (hgen : ∀ g, I.mem x g ↔ IsInSpanAt (n := n) (· = u) x g) (a : ℕ) (g : M → ℂ) :
    (idealPow I a).mem x g ↔ IsInSpanAt (n := n) (· = fun y => u y ^ a) x g := by
  induction a generalizing g with
  | zero => simpa only [idealPow_zero, unitIdeal, pow_zero] using (isInSpanAt_one_iff g).symm
  | succ a ih =>
    simpa only [idealPow_succ, pow_succ] using
      mul_mem_iff_of_generators ih hgen
        (CompanionReduction.holomorphicAt_pow_of hu a) hu g

private theorem holomorphicAt_weighted_list_product (A : List (Set M × ℕ))
    (u : Set M → M → ℂ) {x : M} (hu : ∀ p ∈ A, HolomorphicAt n (u p.1) x) :
    HolomorphicAt n (fun y => (A.map fun p => u p.1 y ^ p.2).prod) x := by
  induction A with
  | nil => simpa using holomorphicAt_const (n := n) (x := x) (1 : ℂ)
  | cons p A ih =>
    have hp := CompanionReduction.holomorphicAt_pow_of (hu p (by simp)) p.2
    have ht := ih (fun q hq => hu q (List.mem_cons_of_mem p hq))
    simpa only [List.map_cons, List.prod_cons] using hp.mul ht

/-- All original product-stalk members are exactly the holomorphic
multiples of the product of the genuine factor generators. -/
theorem componentPowerProduct_mem_iff_of_generators (A : List (Set M × ℕ))
    (u : Set M → M → ℂ) {x : M} (hu : ∀ p ∈ A, HolomorphicAt n (u p.1) x)
    (hgen : ∀ p ∈ A, ∀ g, (idealPow (vanishingIdeal (n := n) p.1) p.2).mem x g ↔
      IsInSpanAt (n := n) (· = fun y => u p.1 y ^ p.2) x g) (g : M → ℂ) :
    (componentPowerProduct (n := n) A).mem x g ↔
      IsInSpanAt (n := n) (· = fun y => (A.map fun p => u p.1 y ^ p.2).prod) x g := by
  induction A generalizing g with
  | nil => simpa only [componentPowerProduct, unitIdeal, List.map_nil, List.prod_nil] using
      (isInSpanAt_one_iff g).symm
  | cons p A ih =>
    have hp := CompanionReduction.holomorphicAt_pow_of (hu p (by simp)) p.2
    have ht := holomorphicAt_weighted_list_product A u
      (fun q hq => hu q (List.mem_cons_of_mem p hq))
    simpa only [componentPowerProduct, List.map_cons, List.prod_cons] using
      mul_mem_iff_of_generators (hgen p (by simp))
        (ih (fun q hq => hu q (List.mem_cons_of_mem p hq))
          (fun q hq => hgen q (List.mem_cons_of_mem p hq))) hp ht g

private def coefficientAt (A : List (Set M × ℕ)) (i : Fin (A.map Prod.fst).length) : ℕ :=
  (A.get ⟨i.val, by simpa only [List.length_map] using i.isLt⟩).2

open Classical in
/-- The actual full product ideal internally produces its SNC coordinate
generator, with exactly the given list coefficients. -/
theorem exists_generator_componentPowerProduct (hn : 0 < n)
    (A : List (Set M × ℕ)) (hE : IsSNCDivisor n (A.map Prod.fst))
    (hnd : (A.map Prod.fst).Nodup) (x : M) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (σ : Fin (A.map Prod.fst).length → Fin n),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      Set.InjOn σ (Finset.univ.filter fun i => x ∈ (A.map Prod.fst).get i) ∧
      (∀ i, x ∈ (A.map Prod.fst).get i → ∀ {y : M},
        y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ (A.map Prod.fst).get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i) = 0)) ∧
      ∀ᶠ y in 𝓝 x, ∀ g, (componentPowerProduct (n := n) A).mem y g ↔
        IsInSpanAt (n := n)
          (· = fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ (A.map Prod.fst).get i),
            flatCoord Φ (σ i) z ^ coefficientAt A i) y g := by
  classical
  let E := A.map Prod.fst
  obtain ⟨Φ, σ, hsrc, h0, hσ, hflat⟩ := exists_snc_chart hn hE x
  let u : Set M → M → ℂ := fun W =>
    if h : x ∈ W ∧ W ∈ E then
      flatCoord Φ (σ ⟨E.idxOf W, List.idxOf_lt_length_iff.mpr h.2⟩)
    else fun _ => 1
  have hui (i : Fin E.length) (hi : x ∈ E.get i) :
      u (E.get i) = flatCoord Φ (σ i) := by
    dsimp only [u]
    rw [dif_pos ⟨hi, List.get_mem _ _⟩]
    congr 1
    exact congrArg σ (Fin.ext (List.get_idxOf hnd i))
  have huoff {W : Set M} (hxW : x ∉ W) : u W = fun _ => 1 := by
    dsimp only [u]
    rw [dif_neg (fun h => hxW h.1)]
  have havoid : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, x ∉ E.get i → y ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ h => (h hxi).elim
    · have hi : ∀ᶠ y in 𝓝 x, y ∉ E.get i :=
        (hE.1 _ (List.get_mem _ _)).isOpen_compl.mem_nhds hxi
      exact hi.mono fun _ hy _ => hy
  have hprod : (fun z => (A.map fun p => u p.1 z ^ p.2).prod) =
      fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ E.get i),
        flatCoord Φ (σ i) z ^ coefficientAt A i := by
    funext z
    have hall : (A.map fun p => u p.1 z ^ p.2).prod =
        ∏ i : Fin E.length, u (E.get i) z ^ coefficientAt A i := by
      calc
        (A.map fun p => u p.1 z ^ p.2).prod =
            ∏ j : Fin A.length, u A[j.val].1 z ^ A[j.val].2 :=
          (Fin.prod_univ_fun_getElem A (fun p => u p.1 z ^ p.2)).symm
        _ = ∏ i : Fin E.length, u (E.get i) z ^ coefficientAt A i := by
          apply Fintype.prod_equiv (finCongr (show A.length = E.length by simp [E]))
          intro j
          simp only [E, coefficientAt, List.get_eq_getElem, List.getElem_map]
          rfl
    rw [hall, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : x ∈ E.get i
    · rw [if_pos hi, hui i hi]
    · rw [if_neg hi, huoff hi]
      simp
  refine ⟨Φ, σ, hsrc, h0, hσ, hflat, ?_⟩
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ), havoid]
    with y hyD hyavoid g
  have hhol : ∀ p ∈ A, HolomorphicAt n (u p.1) y := by
    intro p hp
    have hpE : p.1 ∈ E := List.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hpE
    by_cases hxp : x ∈ p.1
    · rw [← hi, hui i (hi.symm ▸ hxp)]
      exact holomorphicAt_flatCoord Φ (σ i) hyD
    · rw [huoff hxp]
      exact holomorphicAt_const 1
  have hgen : ∀ p ∈ A, ∀ f, (idealPow (vanishingIdeal (n := n) p.1) p.2).mem y f ↔
      IsInSpanAt (n := n) (· = fun z => u p.1 z ^ p.2) y f := by
    intro p hp f
    have hpE : p.1 ∈ E := List.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hpE
    apply idealPow_mem_iff_of_generator (hhol p hp)
    intro v
    by_cases hxp : x ∈ p.1
    · rw [← hi, hui i (hi.symm ▸ hxp)]
      exact vanishingIdeal_mem_iff_flatCoord Φ (hflat i (hi.symm ▸ hxp)) hyD v
    · have hyp : y ∉ p.1 := hi ▸ hyavoid i (hi.symm ▸ hxp)
      rw [huoff hxp, isInSpanAt_one_iff]
      constructor
      · exact fun hv => hv.1
      · intro hv
        refine ⟨hv, ?_⟩
        filter_upwards [(hE.1 p.1 hpE).isOpen_compl.mem_nhds hyp] with z hz hzp
        exact (hz hzp).elim
  have hfull := componentPowerProduct_mem_iff_of_generators A u hhol hgen g
  rw [hprod] at hfull
  exact hfull

/-- The actual exponent of an actual weighted SNC product along every
original member at every original point is its product coefficient. -/
theorem divExp_componentPowerProduct_eq (A : List (Set M × ℕ))
    (hE : IsSNCDivisor n (A.map Prod.fst)) (hnd : (A.map Prod.fst).Nodup)
    {p : Set M × ℕ} (hp : p ∈ A) {x : M} (hx : x ∈ p.1) :
    divExp n (componentPowerProduct (n := n) A) p.1 x = p.2 := by
  classical
  let E := A.map Prod.fst
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
  let i : Fin E.length := ⟨j.val, by simpa only [E, List.length_map] using j.isLt⟩
  have hget : E.get i = p.1 := by
    simpa only [E, i, List.get_eq_getElem, List.getElem_map] using congrArg Prod.fst hj
  have hcoef : coefficientAt A i = p.2 := by
    simpa only [coefficientAt, i, List.get_eq_getElem] using congrArg Prod.snd hj
  have hxi : x ∈ E.get i := hget.symm ▸ hx
  by_cases hn : 0 < n
  · obtain ⟨Φ, σ, hsrc, -, hσ, hflat, hgen⟩ :=
      exists_generator_componentPowerProduct hn A hE hnd x
    have hhol : ∀ y g, (componentPowerProduct (n := n) A).mem y g →
        HolomorphicAt n g y := by
      intro y g hg
      cases A with
      | nil => exact hg
      | cons p A => exact hg.1
    have hiT : i ∈ Finset.univ.filter (fun k => x ∈ E.get k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩
    have hcal := MonomialCase.divExp_eq_of_principal hsrc hσ
      (fun k hk => hflat k (Finset.mem_filter.mp hk).2)
      (coefficientAt A) hgen hhol hiT hxi
    change divExp n (componentPowerProduct (n := n) A) (E.get i) x = coefficientAt A i at hcal
    rw [hget, hcoef] at hcal
    exact hcal
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact (notMem_member_of_dim_zero E hE i x hxi).elim

/-- Produce both the actual factorization and identification of every
coefficient with the ORIGINAL divisor exponent, without assuming either. -/
theorem exists_componentPowerProduct_eq_original_exponents (D : EffectiveDivisor n M)
    (F : List (Set M)) (hF : IsSNCDivisor n F) (hnd : F.Nodup)
    (hconnected : ∀ W ∈ F, ∃ d, IsClosedConnectedSubmanifold n W d ∧ d + 1 = n)
    (hsupport : D.support ⊆ ⋃ W ∈ F, W) :
    ∃ A : List (Set M × ℕ), A.map Prod.fst = F ∧
      D.ideal = componentPowerProduct (n := n) A ∧
      ∀ p ∈ A, ∀ x ∈ p.1, divExp n D.ideal p.1 x = p.2 := by
  obtain ⟨A, hAF, hD⟩ := exists_componentPowerProduct_eq D F hF hconnected hsupport
  have hA : IsSNCDivisor n (A.map Prod.fst) := by simpa only [hAF] using hF
  have hAnd : (A.map Prod.fst).Nodup := by simpa only [hAF] using hnd
  refine ⟨A, hAF, hD, ?_⟩
  intro p hp x hx
  rw [hD]
  exact divExp_componentPowerProduct_eq A hA hAnd hp hx

end
end Hironaka.HironakaSNCComponentCoefficients
