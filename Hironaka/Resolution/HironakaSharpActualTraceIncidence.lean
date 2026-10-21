/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualMaximumMemberOrders
import Hironaka.Resolution.HironakaEffectiveDivisorSum

/-!
# Actual monomial support along the same full boundary-incidence stratum

Whole original ideal predicates, actual positive powers, and genuine exponent
local constancy retain the monomial-unit profile. The final generic consequence
retains its current whole trace factor explicitly as an induction hypothesis;
it assumes no modified history or incidence conclusion.
Blueprint: `hironaka-sharp-actual-trace-incidence-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualTraceIncidence
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong DivisorExponentAlong
  NormalCrossings IdealWeightPowers
variable {n : ℕ} {X : CMfd.{u} n}

private theorem positive_vanishing_power_eval {H : Set X} {x : X} (hx : x ∈ H)
    (k : ℕ) (g : X → ℂ)
    (hg : (idealPow (vanishingIdeal (n := n) H) (k+1)).mem x g) : g x=0 := by
  obtain ⟨_hhol,r,s,a,hs,_ha,he⟩ := hg
  rw [he.self_of_nhds]
  apply Finset.sum_eq_zero
  intro i _hi
  obtain ⟨b,c,_hb,hc,hbc⟩ := hs i
  rw [hbc]
  change a i x*(b x*c x)=0
  rw [hc.2.self_of_nhds hx,mul_zero,mul_zero]

/-- The literal whole monomial ideal detects precisely its incident positive exponents. -/
theorem one_mem_monomialPartAlong_iff {N : Set X} (I : GermIdeal n X)
    (E : List (Set X)) {x : X} (hx : x ∈ N) :
    (monomialPartAlong n N I E).mem x 1 ↔
      ∀ i : Fin E.length,x ∈ E.get i → divExpAlong n N I (E.get i) x=0 := by
  constructor
  · intro h i hi
    by_contra hn
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hh := h.2 i hx hi
    rw [hk] at hh
    obtain ⟨r,s,a,hs,_ha,he⟩ := hh
    have hz : (1 : ℂ)=0 := by
      change (1 : X → ℂ) x = 0
      rw [he.self_of_nhds hx]
      apply Finset.sum_eq_zero
      intro j _hj
      rw [positive_vanishing_power_eval hi k (s j) (hs j),mul_zero]
    exact one_ne_zero hz
  · intro h
    refine ⟨holomorphicAt_const 1,fun i _hx hi => ?_⟩
    rw [h i hi]
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self
      (holomorphicAt_const 1) (holomorphicAt_const 1))

/-- Actual exponent constancy and whole boundary incidence give the SAME monomial-unit profile. -/
theorem eventually_monomial_unit_of_stable_incidence (hn : 0<n)
    {N C : Set X} (hN : IsClosedSubmanifold n N) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hCN : C ⊆ N)
    {x : X} (hx : x ∈ C)
    (hinc : ∀ᶠ y in 𝓝 x,y ∈ C → ∀ i : Fin E.length,(y ∈ E.get i ↔ x ∈ E.get i)) :
    ∀ᶠ y in 𝓝 x,y ∈ C →
      ((monomialPartAlong n N I E).mem y 1 ↔ (monomialPartAlong n N I E).mem x 1) := by
  have hexp : ∀ᶠ y in 𝓝 x,∀ i : Fin E.length,x ∈ E.get i → y ∈ N → y ∈ E.get i →
      divExpAlong n N I (E.get i) y=divExpAlong n N I (E.get i) x := by
    apply eventually_all.mpr
    intro i
    by_cases hi : x ∈ E.get i
    · filter_upwards [eventually_divExpAlong_get_eq hn hN hE hT hI hnz i (hCN hx) hi]
        with y hy _hxi hyN hyi
      exact hy hyN hyi
    · exact Eventually.of_forall fun _ hxi => (hi hxi).elim
  filter_upwards [hinc,hexp] with y hy he hyC
  rw [one_mem_monomialPartAlong_iff I E (hCN hyC),one_mem_monomialPartAlong_iff I E (hCN hx)]
  constructor
  · intro h i hi
    have hyi := (hy hyC i).mpr hi
    rw [←he i hi (hCN hyC) hyi]
    exact h i hyi
  · intro h i hi
    have hxi := (hy hyC i).mp hi
    rw [he i hxi (hCN hyC) hi]
    exact h i hxi

/-- True whole relative restriction preserves the whole zero locus ON the carrier. -/
theorem zeroLocus_restrictOn_iff {N : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) {x : X} (hx : x ∈ N) :
    x ∈ (restrictOn n N I).zeroLocus ↔ x ∈ I.zeroLocus := by
  constructor
  · intro h g hg
    exact h g (le_restrictOn hI x g hg)
  · intro h g hg
    obtain ⟨r,s,a,hs,_ha,he⟩ := hg.2
    rw [he.self_of_nhds hx]
    exact Finset.sum_eq_zero fun i _ => by rw [h _ (hs i),mul_zero]

private theorem not_unit_iff_zeroLocus (I : GermIdeal n X) (hI : I.IsCoherent) (x : X) :
    ¬I.mem x 1 ↔ x ∈ I.zeroLocus := by
  simpa only [HironakaSharpActualChronologicalDistinctDefect.actualProperPositions,
    Finset.mem_filter,Finset.mem_univ,true_and] using
    (HironakaSharpActualChronologicalDistinctDefect.actual_proper_iff_zeroLocus
      (F := fun _ : Fin 1 => I) (fun _ => hI) 0 x)

/-- A genuine current-stage whole factor, actual born incidence and normalized
unit profiles force local incidence with the SAME actual old member. -/
theorem eventually_trace_incidence_of_factor (hn : 0<n)
    {N C H : Set X} (hN : IsClosedSubmanifold n N) (hH : IsClosedSubmanifold n H)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (hnz : ∀ y ∈ N,IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) y)
    (J : GermIdeal n X) (hJ : J.IsCoherent) (hCN : C ⊆ N)
    (hfactor : restrictOn n N (vanishingIdeal (n := n) H)=
      restrictOn n N ((monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) E).mul J))
    {x : X} (hx : x ∈ C)
    (hinc : ∀ᶠ y in 𝓝 x,y ∈ C → ∀ i : Fin E.length,(y ∈ E.get i ↔ x ∈ E.get i))
    (hunit : ∀ᶠ y in 𝓝 x,y ∈ C → (J.mem y 1 ↔ J.mem x 1)) :
    ∀ᶠ y in 𝓝 x,y ∈ C → (y ∈ H ↔ x ∈ H) := by
  let I := restrictOn n N (vanishingIdeal (n := n) H)
  let D := monomialPartAlong n N I E
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hcI := isCoherent_restrictOn_of_isClosedSubmanifold hcH hN
  have hcD : D.IsCoherent := isCoherent_monomialPartAlong hn hN hE hT hcI hnz
  have hzero : ∀ y∈N,(y ∈ H ↔ y ∈ D.zeroLocus ∨ y ∈ J.zeroLocus) := by
    intro y hy
    have hIH : y ∈ I.zeroLocus ↔ y ∈ H :=
      (zeroLocus_restrictOn_iff hcH hy).trans (by rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1])
    have hprod : y ∈ I.zeroLocus ↔ y ∈ (D.mul J).zeroLocus := by
      change y ∈ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus ↔ _
      rw [hfactor]
      exact zeroLocus_restrictOn_iff (isCoherent_mul hcD hJ) hy
    exact hIH.symm.trans (hprod.trans (by rw [HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union hcD hJ];rfl))
  have hDunit := eventually_monomial_unit_of_stable_incidence hn hN hE hT I hcI hnz hCN hx hinc
  filter_upwards [hDunit,hunit] with y hyD hyJ hyC
  rw [hzero y (hCN hyC),hzero x (hCN hx),
    ←not_unit_iff_zeroLocus D hcD y,←not_unit_iff_zeroLocus D hcD x,
    ←not_unit_iff_zeroLocus J hJ y,←not_unit_iff_zeroLocus J hJ x,
    hyD hyC,hyJ hyC]

end
end Hironaka.HironakaSharpActualTraceIncidence
