/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSelectedContactCosupport
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
/-! Actual finite-span nonzero reflection and genuine smooth locality of
WHOLE selected/remaining contact components and all four remainder fields. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalContactRemainderSmoothNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan BlowupTowers
  DivisorExponentAlong HironakaStepOneSpecialAnalyticLoci
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneZeroContactRemainderGlueing
  HironakaStepOneZeroContactRemainderExtension HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionCoefficientIdeals
variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m}

/-- Actual finite pullback spans and continuity reflect frequent nonzero
carrier values; no coherence, smooth-carrier or principal model is supplied. -/
theorem isNonzeroAlongAt_of_pullback {f : Y → X} {y : Y}
    (hf : ContinuousAt f y) {N : Set X} {I : GermIdeal n X}
    (h : IsNonzeroAlongAt (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) y) :
    IsNonzeroAlongAt N I (f y) := by
  obtain ⟨g,hg,hfreq⟩ := h
  by_contra hbase
  have hZero (b : X → ℂ) (hb : I.mem (f y) b) : ∀ᶠ x in 𝓝 (f y),x ∈ N → b x=0 := by
    have hh : ¬ ∃ᶠ x in 𝓝 (f y),x ∈ N ∧ b x ≠ 0 := fun hne => hbase ⟨b,hb,hne⟩
    filter_upwards [not_frequently.mp hh] with x hx hxN
    by_contra hne
    exact hx ⟨hxN,hne⟩
  obtain ⟨_hgHol,r,s,a,hs,_ha,hEq⟩ := GermIdeal.mem_pullback_iff.mp hg
  have hEach (i : Fin r) : ∀ᶠ z in 𝓝 y,z ∈ f ⁻¹' N → s i z=0 := by
    obtain ⟨b,hb,he⟩ := hs i
    rw [he]
    exact hf.eventually (hZero b hb)
  have hAll : ∀ᶠ z in 𝓝 y,∀ i : Fin r,z ∈ f ⁻¹' N → s i z=0 := eventually_all.mpr hEach
  have hz : ∀ᶠ z in 𝓝 y,z ∈ f ⁻¹' N → g z=0 := by
    filter_upwards [hAll,hEq] with z hzs heq hzN
    rw [heq]
    apply Finset.sum_eq_zero
    intro i _hi
    rw [hzs i hzN,mul_zero]
  obtain ⟨z,⟨hzN,hzne⟩,hzz⟩ := (hfreq.and_eventually hz).exists
  exact hzne (hzz hzN)

/-- BOTH genuine nonzero directions for ANY actual carrier under an actual
mixed-dimensional holomorphic submersion. -/
theorem isNonzeroAlongAt_pullback_submersion_iff {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    {N : Set X} {I : GermIdeal n X} (hI : I.IsCoherent) (y : Y) :
    IsNonzeroAlongAt (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) y ↔
      IsNonzeroAlongAt N I (f y) :=
  ⟨isNonzeroAlongAt_of_pullback ((hf.contMDiff y).continuousAt),
    isNonzeroAlongAt_preimage_submersion hf hI⟩

private theorem selected_subset {d : ℕ} {Z : CMfd.{u} d}
    (L : MarkedIdeal d Z) (hN : IsClosedSubmanifold d L.N) :
    selectedComponents (n := d) L.N L.cosupp ⊆ L.N := by
  rintro z ⟨K,⟨hK,_hKC⟩,hzK⟩
  exact GlobalComponents.subset_of_mem_globalComponents
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN) hK hzK

/-- True pointwise zero-germ equivalence gives WHOLE selected-component
preimage equality without surjectivity or a global component correspondence. -/
theorem selectedComponents_preimage_submersion {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1 ≤ L.d) :
    selectedComponents (n := m) (markedPullback (m := m) f L).N
      (markedPullback (m := m) f L).cosupp = f ⁻¹' selectedComponents (n := n) L.N L.cosupp := by
  let P := markedPullback (m := m) f L
  have hPN : IsClosedSubmanifold m P.N := isClosedSubmanifold_preimage_submersion hf hN
  have hPI : P.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hI
  apply Set.ext
  intro y
  by_cases hy : f y ∈ L.N
  · have hSP := selectedComponents_iff_not_isNonzeroAlongAt P hPN hPI hd hy
    have hSL := selectedComponents_iff_not_isNonzeroAlongAt L hN hI hd hy
    exact hSP.trans ((not_congr (isNonzeroAlongAt_pullback_submersion_iff hf hI y)).trans hSL.symm)
  · exact iff_of_false (fun hs => hy (selected_subset P hPN hs))
      (fun hs => hy (selected_subset L hN hs))

/-- The actual remaining union is the true carrier difference, so the whole
set pulls back after the independently proved selected-union equality. -/
theorem remainingComponents_preimage_submersion {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1 ≤ L.d) :
    remainingComponents (n := m) (markedPullback (m := m) f L).N
      (markedPullback (m := m) f L).cosupp = f ⁻¹' remainingComponents (n := n) L.N L.cosupp := by
  have hPN : IsClosedSubmanifold m (markedPullback (m := m) f L).N :=
    isClosedSubmanifold_preimage_submersion hf hN
  rw [remainingComponents_eq_diff_selected hPN,remainingComponents_eq_diff_selected hN,
    selectedComponents_preimage_submersion hf L hN hI hd]
  rfl

/-- WHOLE actual lower remainder records commute, retaining the SAME number
of literal historical empty entries and the entire ordered boundary suffix. -/
theorem contactRemainderMarked_markedPullback {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1 ≤ L.d) (b : ℕ) :
    markedPullback (m := m) f (contactRemainderMarked L b) =
      contactRemainderMarked (markedPullback (m := m) f L) b := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact (remainingComponents_preimage_submersion hf L hN hI hd).symm
  · change (List.replicate b ∅ ++ L.E.drop b).map (f ⁻¹' ·) =
      List.replicate b ∅ ++ (L.E.map (f ⁻¹' ·)).drop b
    rw [List.map_append,List.map_replicate,preimage_empty,List.map_drop]
  · rfl
  · rfl

end
end Hironaka.HironakaOriginalContactRemainderSmoothNaturality
