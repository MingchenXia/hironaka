/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalFirstMemberExceptionalFactor

/-! Genuine BOTH relative principal directions for actual first original member
residuals. Real greatest-factor cancellation precedes the dictionary. These
are whole holomorphic germ ideals along the carrier, not ambient principal
ideals; arbitrary-colon strict saturation/history identity stays OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalFirstMemberResidualPrincipal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct MarkedIdeals MarkedIdeals.MarkedIdeal
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  MonomialPartAlong InvDomainCompanion DivisorExponentAlong InvertibleIdealQuotient
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual monomial generator nonzero geometry permits restricted cancellation,
constructing BOTH residual-principal directions from genuine total principality. -/
theorem exists_actual_relative_principal_residual (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : NormalCrossings.IsSNCDivisor n E)
    (hT : NormalCrossings.IsTransverse n N E) {I : GermIdeal n X} (hI : I.IsCoherent)
    (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y) {x : X} (hx : x ∈ N)
    (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hgenI : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) :
    ∃ m c,HolomorphicAt n m x ∧ (monomialPartAlong n N I E).mem x m ∧
      (nonmonomialPartAlong n N I E).mem x c ∧
      (∀ᶠ z in 𝓝 x,z ∈ N → f z=m z*c z) ∧
      ∀ g,(nonmonomialPartAlong n N I E).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=c) x g := by
  obtain ⟨m,hmhol,_hpow,hmgen,hmne⟩ := exists_generator_monomialPartAlong hn hN hE hT hI hnz hx
  have hmh := hmhol.self_of_nhds
  have hM := hmgen.self_of_nhds
  have hm : (monomialPartAlong n N I E).mem x m := (hM m).mpr
    ⟨hmh,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => (one_mul _).symm⟩⟩
  have hfI : I.mem x f := (hgenI f).mpr
    ⟨hf,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => (one_mul _).symm⟩⟩
  obtain ⟨c,hc,hfc⟩ := isInSpanOnAt_eq_iff.mp ((hM f).mp (le_monomialPartAlong hn hE hT hI x f hfI)).2
  have hcJ : (nonmonomialPartAlong n N I E).mem x c := by
    refine ⟨hc,?_⟩
    intro a ha
    obtain ⟨b,hb,hab⟩ := isInSpanOnAt_eq_iff.mp ((hM a).mp ha).2
    refine restrictOn_congr (restrictOn_mul_left hb (le_restrictOn hI x f hfI)) (((hM a).mp ha).1.mul hc) ?_
    filter_upwards [hab,hfc] with z hz hfz hzN
    rw [hz hzN,hfz hzN]
    ring
  obtain ⟨U,hU,hUo,hxU⟩ := mem_nhds_iff.mp hmne
  have hnon : ∀ V : Set X,IsOpen V → V ⊆ U → (V ∩ N).Nonempty → ∃ y ∈ V ∩ N,m y ≠ 0 := by
    intro V hVo hVU hVN
    obtain ⟨y,hyV,hyN⟩ := hVN
    obtain ⟨z,⟨hzN,hmz⟩,hzV⟩ := ((hU (hVU hyV) hyN).and_eventually (hVo.mem_nhds hyV)).exists
    exact ⟨z,⟨hzV,hzN⟩,hmz⟩
  refine ⟨m,c,hmh,hm,hcJ,hfc.mono (fun _ h hN => (h hN).trans (mul_comm _ _)),?_⟩
  intro g
  constructor
  · intro hg
    have hspan : IsInSpanOnAt (n := n) N (·=f) x (fun z => m z*g z) :=
      IsInSpanOnAt.trans (fun a ha => ((hgenI a).mp ha).2) (hg.2 m hm).2
    obtain ⟨a,ha,hmg⟩ := isInSpanOnAt_eq_iff.mp hspan
    have hcancel : ∀ᶠ z in 𝓝 x,z ∈ N → m z*g z=m z*(a z*c z) := by
      filter_upwards [hmg,hfc] with z hz hfz hzN
      rw [hz hzN,hfz hzN]
      ring
    have hgc := eventuallyEq_within_of_mul_eventuallyEq_within hUo hnon hxU hg.1 (ha.mul hc) hcancel
    exact ⟨hg.1,isInSpanOnAt_eq_iff.mpr ⟨a,ha,hgc⟩⟩
  · rintro ⟨hg,hspan⟩
    obtain ⟨a,ha,hgc⟩ := isInSpanOnAt_eq_iff.mp hspan
    refine ⟨hg,?_⟩
    intro b hb
    refine restrictOn_congr (restrictOn_mul_left ha (hcJ.2 b hb)) (((hM b).mp hb).1.mul hg) ?_
    filter_upwards [hgc] with z hz hzN
    rw [hz hzN]
    ring

private theorem pullback_principal_dictionary {I : GermIdeal n X} (hI : I.IsCoherent)
    {π : Y → X} (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    (y : Y) (f : X → ℂ) (hf : HolomorphicAt n f (π y))
    (hgen : ∀ g,I.mem (π y) g ↔ IsInSpanAt (n := n) (·=f) (π y) g) :
    HolomorphicAt n (f ∘ π) y ∧ ∀ g,(GermIdeal.pullback (m := n) π I).mem y g ↔ IsInSpanAt (n := n) (·=f ∘ π) y g := by
  have hfp := hf.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiffAt)
  have hfI : I.mem (π y) f := (hgen f).mpr (isInSpanAt_eq_iff.mpr
    ⟨hf,1,holomorphicAt_const 1,Eventually.of_forall fun _ => (one_mul _).symm⟩)
  have hfP : (GermIdeal.pullback (m := n) π I).mem y (f ∘ π) := GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_self ⟨f,hfI,rfl⟩ hfp)
  refine ⟨hfp,?_⟩
  intro g
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro a ⟨b,hb,rfl⟩
    obtain ⟨hbh,c,hc,hbc⟩ := isInSpanAt_eq_iff.mp ((hgen b).mp hb)
    exact isInSpanAt_eq_iff.mpr ⟨hbh.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiffAt),c ∘ π,hc.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiffAt),hπ.continuous.tendsto y |>.eventually hbc⟩
  · intro hg
    exact HomogenizedIdeal.mem_of_isInSpanAt (GermIdealPullbackCalculus.isCoherent_pullback hπ hI)
      (IsInSpanAt.mono (S := (·=f ∘ π)) (T := (GermIdeal.pullback (m := n) π I).mem y) (fun a ha => ha ▸ hfP) hg)

/-- SAME original member data internally construct actual total relative principality. -/
theorem exists_actual_original_member_total_principal (hn : 0 < n)
    {W C : Set X} {E : List (Set X)} (hE : NormalCrossings.IsSNCDivisor n E)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (i : Fin E.length) (y : Y) :
    ∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,(memberTotalMarked W (E.get i) C π).ideal.mem y g ↔
      HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) (memberTotalMarked W (E.get i) C π).N (·=f) y g := by
  obtain ⟨f,hf,hgen⟩ := exists_originalMember_principal hn hE (List.get_mem E i) (π y)
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  obtain ⟨hfp,hP⟩ := pullback_principal_dictionary hI hπ.contMDiff y f hf hgen
  have hfmem : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))).mem y (f ∘ π) :=
    (hP _).mpr (isInSpanAt_eq_iff.mpr ⟨hfp,1,holomorphicAt_const 1,Eventually.of_forall fun _ => (one_mul _).symm⟩)
  refine ⟨f ∘ π,hfp,?_⟩
  intro g
  rw [show (memberTotalMarked W (E.get i) C π).ideal=
      restrictOn n (memberTotalMarked W (E.get i) C π).N (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))) from
    geoTransform_zeroMark_ideal_eq_restricted_total (memberZeroMarked W (E.get i)) rfl C π]
  constructor
  · intro hg
    exact ⟨hg.1,IsInSpanOnAt.trans (fun a ha => IsInSpanAt.restrict ((hP a).mp ha)) hg.2⟩
  · rintro ⟨hg,hspan⟩
    exact ⟨hg,IsInSpanOnAt.mono (S := (·=f ∘ π)) (T := (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))).mem y) (fun a ha => ha ▸ hfmem) hspan⟩

/-- ONLY original inputs yield the genuine relative principal residual at EVERY
actual first carrier point, without a chosen projection or desired presentation. -/
theorem exists_actual_original_first_member_residual_principal (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    {d : ℕ} (hd : d+1 ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),IsBlowupAlong n C π ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E) ∧
      ∀ i : Fin E.length,∀ y ∈ (memberTotalMarked W (E.get i) C π).N,
        ∃ c : Y → ℂ,(memberExceptionalResidual W (E.get i) C π).mem y c ∧
          ∀ g,(memberExceptionalResidual W (E.get i) C π).mem y g ↔ HolomorphicAt n g y ∧
            IsInSpanOnAt (n := n) (memberTotalMarked W (E.get i) C π).N (·=c) y g := by
  obtain ⟨C,Y,π,hπ,hCeq,hgeom⟩ := exists_actual_original_first_member_exceptional_factor hn hW hE hd hreg hdense hcompact hne
  refine ⟨C,Y,π,hπ,hCeq,?_⟩
  intro i y hy
  obtain ⟨hw,_hTotal,hnz,_hJ,_hnzJ,_hfac,_hnot⟩ := hgeom i
  obtain ⟨f,hf,hgen⟩ := exists_actual_original_member_total_principal hn hE hπ i y
  obtain ⟨_m,c,_hm,_hmM,hc,_hfc,hJ⟩ := exists_actual_relative_principal_residual hn
    hw.isClosedSubmanifold_N hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz hy f hf hgen
  exact ⟨c,hc,hJ⟩

end
end Hironaka.HironakaSharpOriginalFirstMemberResidualPrincipal
