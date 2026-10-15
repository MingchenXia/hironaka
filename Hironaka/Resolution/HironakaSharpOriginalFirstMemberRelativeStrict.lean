/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualExceptionalPowerCancellation

/-! Literal all-power relative saturation of the GENUINE raw total pullback
is proved equal to the actual first member residual. No residual is named
strict by definition; chronological strict histories remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalFirstMemberRelativeStrict
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualExceptionalPowerCancellation HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMemberProduct
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
variable {n : ℕ} {X : CMfd.{u} n}

/-- The literal arbitrary-exceptional-power relative STRICT construction,
defined independently from the intrinsic greatest-factor residual. -/
def relativeExceptionalSaturation (N : Set X) (I : GermIdeal n X) (D : Set X) : GermIdeal n X where
  mem x g := ∃ k : ℕ,(colonAlong n N I (idealPow (vanishingIdeal (n := n) D) k)).mem x g

/-- Actual finite restricted-span substitution gives BOTH full restriction
idempotence directions before any saturation comparison. -/
theorem relativeExceptionalSaturation_restrictOn_mem_iff (N : Set X) (I : GermIdeal n X) (D : Set X)
    (x : X) (g : X → ℂ) :
    (relativeExceptionalSaturation N (restrictOn n N I) D).mem x g ↔
      (relativeExceptionalSaturation N I D).mem x g := by
  have hid (v : X → ℂ) : (restrictOn n N (restrictOn n N I)).mem x v ↔ (restrictOn n N I).mem x v := by
    constructor
    · rintro ⟨hv,hspan⟩
      exact ⟨hv,IsInSpanOnAt.trans (fun s hs => hs.2) hspan⟩
    · intro hv
      exact ⟨hv.1,IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hv hv.1)⟩
  constructor
  · rintro ⟨k,hg,hcolon⟩
    exact ⟨k,hg,fun a ha => (hid _).mp (hcolon a ha)⟩
  · rintro ⟨k,hg,hcolon⟩
    exact ⟨k,hg,fun a ha => (hid _).mpr (hcolon a ha)⟩

/-- BOTH arbitrary-power colon directions identify the real singleton
exceptional saturation with the independently defined genuine residual. -/
theorem actual_single_exceptional_saturation_mem_iff_residual (hn : 0 < n) {N D : Set X}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n [D]) (hT : IsTransverse n N [D])
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    {x : X} (hx : x ∈ N) (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hgen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (g : X → ℂ) :
    (relativeExceptionalSaturation N I D).mem x g ↔ (nonmonomialPartAlong n N I [D]).mem x g := by
  let J := nonmonomialPartAlong n N I [D]
  constructor
  · rintro ⟨k,hg,hcolon⟩
    apply (actual_residual_member_power_colon_mem_iff hn hN hE hT hI hnz hx f hf hgen (0 : Fin [D].length) k g).mp
    refine ⟨hg,fun a ha => ?_⟩
    have hh := hcolon a ha
    exact ⟨hh.1,IsInSpanOnAt.mono
      (fun s hs => NonmonomialTransformAlong.le_nonmonomialPartAlong_self hI x s hs) hh.2⟩
  · intro hg
    by_cases hxD : x ∈ D
    · let e := divExpAlong n N I D x
      refine ⟨e,hg.1,fun a ha => ?_⟩
      have haHol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        (GermIdealPullbackCalculus.isCoherent_idealPow
          (VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE (0 : Fin [D].length))) e) ha
      have haM : (monomialPartAlong n N I [D]).mem x a := by
        refine ⟨haHol,?_⟩
        intro i _hiN _hiD
        have hi : i=(0 : Fin [D].length) := Fin.ext (by
          have hi1 := i.isLt
          simp only [List.length_singleton] at hi1
          simp only [Fin.val_zero]
          omega)
        subst i
        exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self ha haHol)
      exact hg.2 a haM
    · have h1M : (monomialPartAlong n N I [D]).mem x (1 : X → ℂ) := by
        refine ⟨holomorphicAt_const 1,?_⟩
        intro i _hiN hiD
        have hi : i=(0 : Fin [D].length) := Fin.ext (by
          have hi1 := i.isLt
          simp only [List.length_singleton] at hi1
          simp only [Fin.val_zero]
          omega)
        subst i
        exact False.elim (hxD hiD)
      have hres := hg.2 (1 : X → ℂ) h1M
      have hresg : (restrictOn n N I).mem x g := by
        convert hres using 1
        funext y
        simp
      refine ⟨0,hg.1,fun a ha => ?_⟩
      exact restrictOn_mul_left ha hresg

/-- Literal first relative STRICT ideal: raw genuine total pullback restricted
to the actual carrier, saturated by ALL real exceptional ideal powers. -/
def firstRelativeStrictMemberIdeal {Y : CMfd.{u} n} (W H C : Set X) (π : Y → X) : GermIdeal n Y :=
  relativeExceptionalSaturation (memberTotalMarked W H C π).N
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) (π ⁻¹' C)

/-- ONLY original inputs prove true first BM relative STRICT equals the
independently defined actual residual at EVERY real carrier point/germ. -/
theorem exists_actual_original_first_member_relative_strict_eq_residual (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1 ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),IsBlowupAlong n C π ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E) ∧
      ∀ i : Fin E.length,∀ y ∈ (memberTotalMarked W (E.get i) C π).N,∀ g : Y → ℂ,
        (firstRelativeStrictMemberIdeal W (E.get i) C π).mem y g ↔
          (memberExceptionalResidual W (E.get i) C π).mem y g := by
  obtain ⟨C,Y,π,hπ,hCeq,hgeom⟩ := exists_actual_original_first_member_exceptional_factor hn hW hE hd hreg hdense hcompact hne
  refine ⟨C,Y,π,hπ,hCeq,?_⟩
  intro i y hy g
  let P := memberTotalMarked W (E.get i) C π
  obtain ⟨hw,hTotal,hnz,_hJ,_hnzJ,_hfac,_hnot⟩ := hgeom i
  obtain ⟨f,hf,hgen⟩ := exists_actual_original_member_total_principal hn hE hπ i y
  have hwhole := actual_single_exceptional_saturation_mem_iff_residual hn hw.isClosedSubmanifold_N
    hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz hy f hf hgen g
  have hrestriction := relativeExceptionalSaturation_restrictOn_mem_iff P.N
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))) (π ⁻¹' C) y g
  rw [← hTotal] at hrestriction
  exact hrestriction.symm.trans hwhole

end
end Hironaka.HironakaSharpOriginalFirstMemberRelativeStrict
