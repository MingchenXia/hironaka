/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualDynamicDistinctCentre

/-! WHOLE true mark-zero TOTAL commutes with actual relative finite products.
Real strict-carrier pullback and BOTH normal germ directions precede comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualRelativeProductTotal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualRelativeProductOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalStrictStep
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaSharpOriginalFirstMemberWholeFactor
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong InvertibleIdealQuotient
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual paired generator multiplication fixes the real finite product function. -/
theorem paired_relative_product_principal (N : Set X) (P : List (GermIdeal n X × (X → ℂ))) {x : X}
    (hP : ∀ p ∈ P,HolomorphicAt n p.2 x ∧ ∀ a,p.1.mem x a ↔ HolomorphicAt n a x ∧
      IsInSpanOnAt (n := n) N (·=p.2) x a) :
    HolomorphicAt n (P.map Prod.snd).prod x ∧ ∀ a,(relativeIdealListProduct N (P.map Prod.fst)).mem x a ↔
      HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=(P.map Prod.snd).prod) x a := by
  induction P with
  | nil =>
    refine ⟨holomorphicAt_const 1,fun a => ?_⟩
    exact ⟨fun ha => ⟨ha,isInSpanOnAt_eq_iff.mpr ⟨a,ha,Eventually.of_forall fun _ _ => by simp⟩⟩,fun ha => ha.1⟩
  | cons p P ih =>
    obtain ⟨hf,hgen⟩ := hP p (by simp)
    obtain ⟨hg,hrest⟩ := ih (fun a ha => hP a (List.mem_cons_of_mem _ ha))
    exact ⟨hf.mul hg,restrictOn_mul_relative_principal_mem_iff hf hg hgen hrest⟩

private theorem exists_relative_product_generator (N : Set X) (L : List (GermIdeal n X)) (x : X)
    (hpr : ∀ I ∈ L,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧
      IsInSpanOnAt (n := n) N (·=f) x a) :
    ∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ a,(relativeIdealListProduct N L).mem x a ↔
      HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a := by
  induction L with
  | nil =>
    refine ⟨1,holomorphicAt_const 1,fun a => ?_⟩
    exact ⟨fun ha => ⟨ha,isInSpanOnAt_eq_iff.mpr ⟨a,ha,Eventually.of_forall fun _ _ => by simp⟩⟩,fun ha => ha.1⟩
  | cons I L ih =>
    obtain ⟨f,hf,hgen⟩ := hpr I (by simp)
    obtain ⟨g,hg,hrest⟩ := ih (fun J hJ => hpr J (List.mem_cons_of_mem _ hJ))
    exact ⟨f*g,hf.mul hg,restrictOn_mul_relative_principal_mem_iff hf hg hgen hrest⟩

/-- SAME actual chosen old generator composes with the TRUE strict projection. -/
theorem nextTotal_same_actual_relative_generator {N C : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) {π : Y → X} (hπ : IsBlowupAlong n C π)
    {y : Y} (_hy : y ∈ geoStrictTransform π C N) (f : X → ℂ) (hf : HolomorphicAt n f (π y))
    (hgen : ∀ a,I.mem (π y) a ↔ HolomorphicAt n a (π y) ∧ IsInSpanOnAt (n := n) N (·=f) (π y) a) :
    ∀ a,(nextTotalMarked N I C π).ideal.mem y a ↔ HolomorphicAt n a y ∧
      IsInSpanOnAt (n := n) (geoStrictTransform π C N) (·=f ∘ π) y a := by
  have hmaps := geoStrictTransform_subset_preimage (C := C) hπ.contMDiff.continuous hN.1
  have hfp := hf.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
  have hfI : I.mem (π y) f := (hgen f).mpr ⟨hf,isInSpanOnAt_eq_iff.mpr
    ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  have hfP : (GermIdeal.pullback (m := n) π I).mem y (f ∘ π) := GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_self ⟨f,hfI,rfl⟩ hfp)
  have heq : (nextTotalMarked N I C π).ideal=restrictOn n (geoStrictTransform π C N)
      (GermIdeal.pullback (m := n) π I) :=
    geoTransform_zeroMark_ideal_eq_restricted_total (⟨N,[],I,0⟩ : MarkedIdeal n X) rfl C π
  intro a
  rw [heq]
  constructor
  · intro ha
    refine ⟨ha.1,IsInSpanOnAt.trans (fun b hb => ?_) ha.2⟩
    refine IsInSpanOnAt.trans (fun v hv => ?_) (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp hb))
    obtain ⟨b,hb,rfl⟩ := hv
    obtain ⟨c,hc,hbc⟩ := isInSpanOnAt_eq_iff.mp ((hgen b).mp hb).2
    refine isInSpanOnAt_eq_iff.mpr ⟨c ∘ π,hc.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt),?_⟩
    filter_upwards [hπ.contMDiff.continuous.tendsto y |>.eventually hbc] with z hz hzN
    exact hz (hmaps hzN)
  · rintro ⟨ha,hspan⟩
    exact ⟨ha,IsInSpanOnAt.mono (S := (·=f ∘ π)) (fun b hb => hb ▸ hfP) hspan⟩

private theorem restrictOn_off_carrier {N : Set Y} (hN : IsClosed N) {y : Y} (hy : y ∉ N)
    (I : GermIdeal n Y) (a : Y → ℂ) : (restrictOn n N I).mem y a ↔ HolomorphicAt n a y := by
  exact ⟨fun h => h.1,fun ha => restrictOn_eq_top_of_disjoint hN.isOpen_compl hy (by simp) ha⟩

private theorem relative_product_off_carrier {N : Set Y} (hN : IsClosed N) {y : Y} (hy : y ∉ N)
    (L : List (GermIdeal n Y)) (a : Y → ℂ) :
    (relativeIdealListProduct N L).mem y a ↔ HolomorphicAt n a y := by
  cases L with
  | nil => rfl
  | cons I L => exact restrictOn_off_carrier hN hy _ a

/-- Actual WHOLE TOTAL commutation, retaining all carrier-normal germs. -/
theorem nextTotal_relative_product_eq_relative_product_totals {N C : Set X}
    (hN : IsClosedSubmanifold n N) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (L : List (GermIdeal n X))
    (hpr : ∀ I ∈ L,∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧
      IsInSpanOnAt (n := n) N (·=f) x a) :
    (nextTotalMarked N (relativeIdealListProduct N L) C π).ideal=
      relativeIdealListProduct (geoStrictTransform π C N) (L.map fun I => (nextTotalMarked N I C π).ideal) := by
  have hB : IsClosed (geoStrictTransform π C N) := isClosed_closure
  have hmaps := geoStrictTransform_subset_preimage (C := C) hπ.contMDiff.continuous hN.1
  induction L with
  | nil =>
    ext y a
    by_cases hy : y ∈ geoStrictTransform π C N
    · have hgen : ∀ b,(IdealWeightPowers.unitIdeal n X).mem (π y) b ↔ HolomorphicAt n b (π y) ∧
          IsInSpanOnAt (n := n) N (·=(1 : X → ℂ)) (π y) b := by
        intro b
        exact ⟨fun hb => ⟨hb,isInSpanOnAt_eq_iff.mpr ⟨b,hb,Eventually.of_forall fun _ _ => by simp⟩⟩,fun hb => hb.1⟩
      have ht := nextTotal_same_actual_relative_generator hN hπ hy 1 (holomorphicAt_const 1) hgen a
      exact ht.trans ⟨fun h => h.1,fun ha => ⟨ha,isInSpanOnAt_eq_iff.mpr
        ⟨a,ha,Eventually.of_forall fun _ _ => by simp⟩⟩⟩
    · change ((⟨N,[],relativeIdealListProduct N [],0⟩ : MarkedIdeal n X).geoTransform C π).ideal.mem y a ↔ _
      rw [geoTransform_zeroMark_ideal_eq_restricted_total (⟨N,[],relativeIdealListProduct N [],0⟩ : MarkedIdeal n X) rfl C π]
      exact restrictOn_off_carrier hB hy _ a
  | cons I L ih =>
    have hprL := fun J hJ => hpr J (List.mem_cons_of_mem _ hJ)
    have htail := ih hprL
    ext y a
    by_cases hy : y ∈ geoStrictTransform π C N
    · obtain ⟨f,hf,hfi⟩ := hpr I (by simp) (π y) (hmaps hy)
      obtain ⟨g,hg,hgp⟩ := exists_relative_product_generator N L (π y) (fun J hJ => hprL J hJ (π y) (hmaps hy))
      have hgenOld := restrictOn_mul_relative_principal_mem_iff hf hg hfi hgp
      have htOld := nextTotal_same_actual_relative_generator hN hπ hy (f*g) (hf.mul hg) hgenOld a
      have htI := nextTotal_same_actual_relative_generator hN hπ hy f hf hfi
      have htL := nextTotal_same_actual_relative_generator hN hπ hy g hg hgp
      rw [htail] at htL
      have hfp := hf.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
      have hgp' := hg.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
      exact htOld.trans (restrictOn_mul_relative_principal_mem_iff hfp hgp' htI htL a).symm
    · change ((⟨N,[],relativeIdealListProduct N (I::L),0⟩ : MarkedIdeal n X).geoTransform C π).ideal.mem y a ↔ _
      rw [geoTransform_zeroMark_ideal_eq_restricted_total (⟨N,[],relativeIdealListProduct N (I::L),0⟩ : MarkedIdeal n X) rfl C π]
      exact (restrictOn_off_carrier hB hy _ a).trans (relative_product_off_carrier hB hy _ a).symm

/-- ONLY original chronological data supply WHOLE true product TOTAL transport. -/
theorem original_chronological_product_whole_total_transport (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Z : CMfd.{u} n} (T : BlowupTower X Z) (ht : IsGeoTestTower (geometricTemplate W []) T)
    {C : Set Z} {π : Y → Z} (hπ : IsBlowupAlong n C π) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    (nextTotalMarked N (chronologicalMemberProduct W E T) C π).ideal=
      relativeIdealListProduct (geoStrictTransform π C N)
        ((chronologicalMemberFamily W E T).map fun I => (nextTotalMarked N I C π).ideal) := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,NormalCrossings.isSNCDivisor_nil,NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht
  apply nextTotal_relative_product_eq_relative_product_totals hwT.isClosedSubmanifold_N hπ (chronologicalMemberFamily W E T)
  intro I hI x hx
  obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
  obtain ⟨hNi,_hEi,_hmi,_hwi,_hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T ht
  rw [hNi] at hpri
  exact hpri x hx

end
end Hironaka.HironakaSharpActualRelativeProductTotal
