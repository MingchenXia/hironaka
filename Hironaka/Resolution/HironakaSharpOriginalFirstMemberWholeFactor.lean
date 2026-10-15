/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalFirstMemberRelativeStrict

/-! WHOLE actual relative STRICT equality/coherence and genuine normalized
TOTAL = restrictOn N (exceptionalPower * STRICT) germ dictionaries. Carrier
normal germs are retained; no ambient-principal product is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalFirstMemberWholeFactor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalFirstMemberRelativeStrict HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMemberProductDomain RelativePrincipalizationSpan RestrictedIdealExtension
  RestrictedIdealQuotient MonomialPartAlong DivisorExponentAlong NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers InvertibleIdealQuotient
variable {n : ℕ} {X : CMfd.{u} n}

private theorem restrictOn_off_carrier {N : Set X} (hN : IsClosed N) {x : X} (hx : x ∉ N)
    (I : GermIdeal n X) (g : X → ℂ) : (restrictOn n N I).mem x g ↔ HolomorphicAt n g x := by
  refine ⟨fun hg => hg.1,fun hg => ?_⟩
  exact restrictOn_eq_top_of_disjoint hN.isOpen_compl hx (by simp) hg

private theorem restrictOn_idempotent (N : Set X) (I : GermIdeal n X) :
    restrictOn n N (restrictOn n N I)=restrictOn n N I := by
  ext x g
  constructor
  · rintro ⟨hg,hspan⟩
    exact ⟨hg,IsInSpanOnAt.trans (fun s hs => hs.2) hspan⟩
  · intro hg
    exact ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩

/-- Genuine off-carrier unit geometry supplies WHOLE equality before actual
coherence and nonzero are transferred to the independent saturation. -/
theorem actual_single_exceptional_saturation_eq_residual (hn : 0 < n) {N D : Set X}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n [D]) (hT : IsTransverse n N [D])
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    (hprincipal : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) :
    relativeExceptionalSaturation N I D=nonmonomialPartAlong n N I [D] ∧
      (relativeExceptionalSaturation N I D).IsCoherent ∧
      ∀ x ∈ N,IsNonzeroAlongAt N (relativeExceptionalSaturation N I D) x := by
  have heq : relativeExceptionalSaturation N I D=nonmonomialPartAlong n N I [D] := by
    ext x g
    by_cases hx : x ∈ N
    · obtain ⟨f,hf,hgen⟩ := hprincipal x hx
      exact actual_single_exceptional_saturation_mem_iff_residual hn hN hE hT hI hnz hx f hf hgen g
    · have hS : (relativeExceptionalSaturation N I D).mem x g ↔ HolomorphicAt n g x := by
        refine ⟨fun hg => hg.choose_spec.1,fun hg => ?_⟩
        exact ⟨0,hg,fun a ha => (restrictOn_off_carrier hN.1 hx I _).mpr (ha.mul hg)⟩
      have hJ : (nonmonomialPartAlong n N I [D]).mem x g ↔ HolomorphicAt n g x := by
        refine ⟨fun hg => hg.1,fun hg => ?_⟩
        exact ⟨hg,fun a ha => (restrictOn_off_carrier hN.1 hx I _).mpr (ha.1.mul hg)⟩
      exact hS.trans hJ.symm
  refine ⟨heq,?_,?_⟩
  · rw [heq]
    exact isCoherent_nonmonomialPartAlong hn hN hE hT hI hnz
  · rw [heq]
    exact fun x hx => InvDomainCompanion.isNonzeroAlongAt_nonmonomialPartAlong hn hN hE hT hI hnz hx

/-- The REAL intrinsic exponent is used at incident points; zero is literal elsewhere. -/
def singleExceptionalExponent (N : Set X) (I : GermIdeal n X) (D : Set X) (x : X) : ℕ :=
  if x ∈ D then divExpAlong n N I D x else 0

/-- BOTH true whole monomial germ directions give the genuine normalized
exceptional ideal power, without supplying an exponent/factor dictionary. -/
theorem actual_single_monomial_mem_iff_power {N D : Set X} {I : GermIdeal n X}
    {x : X} (hx : x ∈ N) (g : X → ℂ) :
    (monomialPartAlong n N I [D]).mem x g ↔
      (restrictOn n N (idealPow (vanishingIdeal (n := n) D) (singleExceptionalExponent N I D x))).mem x g := by
  by_cases hxD : x ∈ D
  · simp only [singleExceptionalExponent,if_pos hxD]
    constructor
    · intro hg
      exact ⟨hg.1,hg.2 (0 : Fin [D].length) hx hxD⟩
    · intro hg
      refine ⟨hg.1,?_⟩
      intro i _hiN _hiD
      have hi : i=(0 : Fin [D].length) := Fin.ext (by
        have hi1 := i.isLt
        simp only [List.length_singleton] at hi1
        simp only [Fin.val_zero]
        omega)
      subst i
      exact hg.2
  · simp only [singleExceptionalExponent,if_neg hxD,idealPow_zero]
    constructor
    · intro hg
      exact ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg.1 hg.1)⟩
    · intro hg
      refine ⟨hg.1,?_⟩
      intro i _hiN hiD
      have hi : i=(0 : Fin [D].length) := Fin.ext (by
        have hi1 := i.isLt
        simp only [List.length_singleton] at hi1
        simp only [Fin.val_zero]
        omega)
      subst i
      exact False.elim (hxD hiD)

private theorem restricted_product_left_substitute {N : Set X} {A B J : GermIdeal n X} {x : X}
    (hB : B.IsCoherent) (hJ : J.IsCoherent)
    (hAB : ∀ a,A.mem x a → IsInSpanOnAt (n := n) N (B.mem x) x a)
    {g : X → ℂ} (hg : IsInSpanOnAt (n := n) N ((A.mul J).mem x) x g) :
    IsInSpanOnAt (n := n) N ((B.mul J).mem x) x g := by
  refine IsInSpanOnAt.trans (fun v hv => ?_) hg
  change IsInSpanAt (n := n) (fun s => ∃ a b,A.mem x a ∧ J.mem x b ∧ s=a*b) x v at hv
  refine IsInSpanOnAt.trans (fun s hs => ?_) (IsInSpanAt.restrict hv)
  obtain ⟨a,b,ha,hb,rfl⟩ := hs
  obtain ⟨K,t,c,ht,hc,heq⟩ := hAB a ha
  refine ⟨K,fun j => t j*b,c,fun j => ?_,hc,?_⟩
  · exact HomogenizedIdeal.mul_mem_mul (ht j) hb
      ((RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB (ht j)).mul
        (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hb))
  · filter_upwards [heq] with y hy hyN
    change a y*b y=∑ j,c j y*(t j y*b y)
    rw [hy hyN,Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- Genuine intrinsic factorization plus true finite product substitution
proves the TOTAL factor dictionary with the necessary outer carrier restriction. -/
theorem actual_single_total_normalized_factor_mem_iff (hn : 0 < n) {N D : Set X}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n [D]) (hT : IsTransverse n N [D])
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    (x : X) (g : X → ℂ) :
    (restrictOn n N I).mem x g ↔
      (restrictOn n N ((idealPow (vanishingIdeal (n := n) D) (singleExceptionalExponent N I D x)).mul
        (nonmonomialPartAlong n N I [D]))).mem x g := by
  by_cases hx : x ∈ N
  · let M := monomialPartAlong n N I [D]
    let J := nonmonomialPartAlong n N I [D]
    let B := idealPow (vanishingIdeal (n := n) D) (singleExceptionalExponent N I D x)
    have hM : M.IsCoherent := isCoherent_monomialPartAlong hn hN hE hT hI hnz
    have hJ : J.IsCoherent := isCoherent_nonmonomialPartAlong hn hN hE hT hI hnz
    have hB : B.IsCoherent := GermIdealPullbackCalculus.isCoherent_idealPow
      (VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE (0 : Fin [D].length))) _
    have hMB (a : X → ℂ) (ha : M.mem x a) : IsInSpanOnAt (n := n) N (B.mem x) x a :=
      ((actual_single_monomial_mem_iff_power hx a).mp ha).2
    have hBM (a : X → ℂ) (ha : B.mem x a) : IsInSpanOnAt (n := n) N (M.mem x) x a :=
      IsInSpanAt.restrict (isInSpanAt_self
        ((actual_single_monomial_mem_iff_power hx a).mpr (le_restrictOn hB x a ha))
        (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB ha))
    constructor
    · intro hg
      have hprod := IsInSpanOnAt.trans (fun s hs => restrictLe_mul_along hn hN hE hT hI hnz x hx s hs) hg.2
      exact ⟨hg.1,restricted_product_left_substitute hB hJ hMB hprod⟩
    · intro hg
      have hprod := restricted_product_left_substitute hM hJ hBM hg.2
      exact ⟨hg.1,IsInSpanOnAt.trans (fun s hs => restrictLe_mul_along' hN hI x hx s hs) hprod⟩
  · exact (restrictOn_off_carrier hN.1 hx I g).trans (restrictOn_off_carrier hN.1 hx _ g).symm

/-- ONLY original data yield WHOLE true STRICT coherence and the actual
normalized exceptional-power TOTAL factor on the SAME first projection. -/
theorem exists_actual_original_first_member_whole_strict_and_factor (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1 ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),IsBlowupAlong n C π ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E) ∧
      ∀ i : Fin E.length,
        let P := memberTotalMarked W (E.get i) C π
        let S := firstRelativeStrictMemberIdeal W (E.get i) C π
        S=memberExceptionalResidual W (E.get i) C π ∧ S.IsCoherent ∧
          (∀ y ∈ P.N,IsNonzeroAlongAt P.N S y) ∧
          ∀ y : Y,∀ g : Y → ℂ,P.ideal.mem y g ↔
            (restrictOn n P.N ((idealPow (vanishingIdeal (n := n) (π ⁻¹' C))
              (singleExceptionalExponent P.N P.ideal (π ⁻¹' C) y)).mul S)).mem y g := by
  obtain ⟨C,Y,π,hπ,hCeq,hgeom⟩ := exists_actual_original_first_member_exceptional_factor hn hW hE hd hreg hdense hcompact hne
  refine ⟨C,Y,π,hπ,hCeq,?_⟩
  intro i
  dsimp only
  let P := memberTotalMarked W (E.get i) C π
  obtain ⟨hw,hTotal,hnz,_hJ,_hnzJ,_hfac,_hnot⟩ := hgeom i
  have hpr := fun y (_hy : y ∈ P.N) => exists_actual_original_member_total_principal (W := W) hn hE hπ i y
  obtain ⟨hwhole,hcoh,hnzS⟩ := actual_single_exceptional_saturation_eq_residual hn hw.isClosedSubmanifold_N
    hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz hpr
  have hSat : relativeExceptionalSaturation P.N P.ideal (π ⁻¹' C)=firstRelativeStrictMemberIdeal W (E.get i) C π := by
    ext y g
    rw [hTotal]
    exact relativeExceptionalSaturation_restrictOn_mem_iff _ _ _ y g
  rw [hSat] at hwhole hcoh hnzS
  refine ⟨hwhole,hcoh,hnzS,?_⟩
  intro y g
  have hnorm : restrictOn n P.N P.ideal=P.ideal := by
    rw [hTotal]
    exact restrictOn_idempotent _ _
  rw [hwhole]
  have hfactor := actual_single_total_normalized_factor_mem_iff hn hw.isClosedSubmanifold_N
    hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz y g
  rw [hnorm] at hfactor
  exact hfactor

end
end Hironaka.HironakaSharpOriginalFirstMemberWholeFactor
