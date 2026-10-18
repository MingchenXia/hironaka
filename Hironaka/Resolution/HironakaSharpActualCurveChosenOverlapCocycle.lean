/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveNestedComparison

/-! Actual restrictions of the chosen pairwise terminal maps satisfy their
true triple-open cocycle. No endpoint recipe or empty-step compression is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveChosenOverlapCocycle
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail MaxLocusLocal
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveNestedComparison
variable {n : ℕ} {X : CMfd.{u} n}


/-- The genuine ambient open inclusion internally gives the smaller
window inclusion in either original local chart. -/
theorem commonWindowInclusion (U I O : Opens X) (hOI : O≤I) : nestedOpens U O≤nestedOpens U I :=
  fun _ hx => hOI hx

/-- The real common-open base maps keep the SAME original ambient point,
so the two actual smaller-window membership predicates coincide. -/
theorem commonWindow_membership (U V I O : Opens X) (hIU : I≤U) (hIV : I≤V) :
    ∀ x : nestedOpens U I,
      (commonOpenBase U V I hIU hIV x : CMfd.of (n := n) V) ∈ nestedOpens V O ↔
        (x : CMfd.of (n := n) U) ∈ nestedOpens U O := fun _ => Iff.rfl

/-- The genuinely constructed nested base is EXACTLY the true direct
common-open base, by both actual subtype point identities. -/
theorem common_nested_base_eq (U V I O : Opens X) (hIU : I≤U) (hIV : I≤V) (hOI : O≤I) :
    nestedBaseComparison (X' := CMfd.of (n := n) U) (X := CMfd.of (n := n) V) (nestedOpens U I) (nestedOpens V I) (nestedOpens U O) (nestedOpens V O)
      (commonWindowInclusion U I O hOI) (commonWindowInclusion V I O hOI)
      (commonOpenBase U V I hIU hIV) (commonWindow_membership U V I O hIU hIV)=
      commonOpenBase U V O (hOI.trans hIU) (hOI.trans hIV) := by
  apply Diffeomorph.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  rfl


/-- All smaller-window geometry is supplied internally from the actual
common-open base. The terminal map is the OLD chosen pairwise map. -/
theorem exists_chosen_overlap_map_restriction (U V I O : Opens X)
    (hIU : I≤U) (hIV : I≤V) (hOI : O≤I)
    {Y1 Y2 Z1 Z2 : CMfd.{u} n}
    (P1 : BlowupTower (CMfd.of (n := n) U) Y1) (P2 : BlowupTower (CMfd.of (n := n) V) Y2)
    (S1 : BlowupTower Y1 Z1) (S2 : BlowupTower Y2 Z2) (L : ℕ)
    (χ : CMfd.of (n := n) (openPreimage S1 (openPreimage P1 (nestedOpens U I)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage S2 (openPreimage P2 (nestedOpens V I))))
    (h : IsTowerIso (commonOpenBase U V I hIU hIV)
      (paddedHistory (restrict (nestedOpens U I) P1) (restrict (openPreimage P1 (nestedOpens U I)) S1) L)
      (paddedHistory (restrict (nestedOpens V I) P2) (restrict (openPreimage P2 (nestedOpens V I)) S2) L) χ) :
    ∃ e : CMfd.of (n := n) (openPreimage S1 (openPreimage P1 (nestedOpens U O)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage S2 (openPreimage P2 (nestedOpens V O))),
      IsTowerIso (commonOpenBase U V O (hOI.trans hIU) (hOI.trans hIV))
        (paddedHistory (restrict (nestedOpens U O) P1) (restrict (openPreimage P1 (nestedOpens U O)) S1) L)
        (paddedHistory (restrict (nestedOpens V O) P2) (restrict (openPreimage P2 (nestedOpens V O)) S2) L) e ∧
      ∀ z,(e z : Z2)=(χ ⟨z.val,openPreimage_mono S1 (openPreimage_mono P1
        (commonWindowInclusion U I O hOI)) z.property⟩ : Z2) := by
  obtain ⟨e,he,hPoint⟩ := exists_nested_padded_comparison
    (X' := CMfd.of (n := n) U) (X := CMfd.of (n := n) V)
    (nestedOpens U I) (nestedOpens V I) (nestedOpens U O) (nestedOpens V O)
    (commonWindowInclusion U I O hOI) (commonWindowInclusion V I O hOI)
    (commonOpenBase U V I hIU hIV) (commonWindow_membership U V I O hIU hIV) P1 P2 S1 S2 L χ h
  rw [common_nested_base_eq U V I O hIU hIV hOI] at he
  exact ⟨e,he,hPoint⟩

/-- A direct comparison at any other bounded cut equals the real restriction
of the already chosen pairwise map on every underlying endpoint point. -/
theorem chosen_overlap_direct_point (U V I O : Opens X)
    (hIU : I≤U) (hIV : I≤V) (hOI : O≤I)
    {Y1 Y2 Z1 Z2 : CMfd.{u} n}
    (P1 : BlowupTower (CMfd.of (n := n) U) Y1) (P2 : BlowupTower (CMfd.of (n := n) V) Y2)
    (S1 : BlowupTower Y1 Z1) (S2 : BlowupTower Y2 Z2)
    (L K : ℕ) (hL1 : S1.length≤L) (hL2 : S2.length≤L) (hK1 : S1.length≤K) (hK2 : S2.length≤K)
    (χ : CMfd.of (n := n) (openPreimage S1 (openPreimage P1 (nestedOpens U I)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage S2 (openPreimage P2 (nestedOpens V I))))
    (h : IsTowerIso (commonOpenBase U V I hIU hIV)
      (paddedHistory (restrict (nestedOpens U I) P1) (restrict (openPreimage P1 (nestedOpens U I)) S1) L)
      (paddedHistory (restrict (nestedOpens V I) P2) (restrict (openPreimage P2 (nestedOpens V I)) S2) L) χ)
    (e : CMfd.of (n := n) (openPreimage S1 (openPreimage P1 (nestedOpens U O)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage S2 (openPreimage P2 (nestedOpens V O))))
    (he : IsTowerIso (commonOpenBase U V O (hOI.trans hIU) (hOI.trans hIV))
      (paddedHistory (restrict (nestedOpens U O) P1) (restrict (openPreimage P1 (nestedOpens U O)) S1) K)
      (paddedHistory (restrict (nestedOpens V O) P2) (restrict (openPreimage P2 (nestedOpens V O)) S2) K) e) :
    ∀ z,(e z : Z2)=(χ ⟨z.val,openPreimage_mono S1 (openPreimage_mono P1
      (commonWindowInclusion U I O hOI)) z.property⟩ : Z2) := by
  have he' := BlowupTowerSplitIso.IsTowerIso.congr_base he
    (Φ' := nestedBaseComparison (X' := CMfd.of (n := n) U) (X := CMfd.of (n := n) V)
      (nestedOpens U I) (nestedOpens V I) (nestedOpens U O) (nestedOpens V O)
      (commonWindowInclusion U I O hOI) (commonWindowInclusion V I O hOI)
      (commonOpenBase U V I hIU hIV) (commonWindow_membership U V I O hIU hIV))
    (fun z => DFunLike.congr_fun (common_nested_base_eq U V I O hIU hIV hOI) z)
  exact nested_padded_comparison_direct
    (X' := CMfd.of (n := n) U) (X := CMfd.of (n := n) V)
    (nestedOpens U I) (nestedOpens V I) (nestedOpens U O) (nestedOpens V O)
    (commonWindowInclusion U I O hOI) (commonWindowInclusion V I O hOI)
    (commonOpenBase U V I hIU hIV) (commonWindow_membership U V I O hIU hIV)
    P1 P2 S1 S2 L K hL1 hL2 hK1 hK2 χ h e he'


/-- The literal actual endpoint over O, with no geometric certificate fields. -/
abbrev localEndpoint (U O : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z) : CMfd.{u} n :=
  CMfd.of (n := n) (openPreimage S (openPreimage P (nestedOpens U O)))

/-- Ordinary actual tower data, retaining all true trace and empty padding positions. -/
abbrev localPaddedHistory (U O : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z) (L : ℕ) :
    BlowupTower (CMfd.of (n := n) (nestedOpens U O)) (localEndpoint U O P S) :=
  paddedHistory (restrict (nestedOpens U O) P) (restrict (openPreimage P (nestedOpens U O)) S) L

/-- Actual restrictions of ALL THREE already chosen pairwise maps are
constructed before their real common-open triple cocycle. -/
theorem exists_chosen_pairwise_overlap_cocycle (U1 U2 U3 O : Opens X)
    (hO1 : O≤U1) (hO2 : O≤U2) (hO3 : O≤U3)
    {Y1 Y2 Y3 Z1 Z2 Z3 : CMfd.{u} n}
    (P1 : BlowupTower (CMfd.of (n := n) U1) Y1)
    (P2 : BlowupTower (CMfd.of (n := n) U2) Y2)
    (P3 : BlowupTower (CMfd.of (n := n) U3) Y3)
    (S1 : BlowupTower Y1 Z1) (S2 : BlowupTower Y2 Z2) (S3 : BlowupTower Y3 Z3)
    (L12 L23 L13 : ℕ) (h12₁ : S1.length≤L12) (h12₂ : S2.length≤L12)
    (h23₂ : S2.length≤L23) (h23₃ : S3.length≤L23)
    (h13₁ : S1.length≤L13) (h13₃ : S3.length≤L13)
    (χ12 : localEndpoint U1 (U1⊓U2) P1 S1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      localEndpoint U2 (U1⊓U2) P2 S2)
    (χ23 : localEndpoint U2 (U2⊓U3) P2 S2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      localEndpoint U3 (U2⊓U3) P3 S3)
    (χ13 : localEndpoint U1 (U1⊓U3) P1 S1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      localEndpoint U3 (U1⊓U3) P3 S3)
    (h12 : IsTowerIso (commonOpenBase U1 U2 (U1⊓U2) inf_le_left inf_le_right)
      (localPaddedHistory U1 (U1⊓U2) P1 S1 L12) (localPaddedHistory U2 (U1⊓U2) P2 S2 L12) χ12)
    (h23 : IsTowerIso (commonOpenBase U2 U3 (U2⊓U3) inf_le_left inf_le_right)
      (localPaddedHistory U2 (U2⊓U3) P2 S2 L23) (localPaddedHistory U3 (U2⊓U3) P3 S3 L23) χ23)
    (h13 : IsTowerIso (commonOpenBase U1 U3 (U1⊓U3) inf_le_left inf_le_right)
      (localPaddedHistory U1 (U1⊓U3) P1 S1 L13) (localPaddedHistory U3 (U1⊓U3) P3 S3 L13) χ13) :
    ∃ e12 : localEndpoint U1 O P1 S1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ localEndpoint U2 O P2 S2,
    ∃ e23 : localEndpoint U2 O P2 S2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ localEndpoint U3 O P3 S3,
    ∃ e13 : localEndpoint U1 O P1 S1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ localEndpoint U3 O P3 S3,
      IsTowerIso (commonOpenBase U1 U2 O hO1 hO2)
        (localPaddedHistory U1 O P1 S1 L12) (localPaddedHistory U2 O P2 S2 L12) e12 ∧
      IsTowerIso (commonOpenBase U2 U3 O hO2 hO3)
        (localPaddedHistory U2 O P2 S2 L23) (localPaddedHistory U3 O P3 S3 L23) e23 ∧
      IsTowerIso (commonOpenBase U1 U3 O hO1 hO3)
        (localPaddedHistory U1 O P1 S1 L13) (localPaddedHistory U3 O P3 S3 L13) e13 ∧
      (∀ z,(e12 z : Z2)=(χ12 ⟨z.val,openPreimage_mono S1 (openPreimage_mono P1
        (commonWindowInclusion U1 (U1⊓U2) O (le_inf hO1 hO2))) z.property⟩ : Z2)) ∧
      (∀ z,(e23 z : Z3)=(χ23 ⟨z.val,openPreimage_mono S2 (openPreimage_mono P2
        (commonWindowInclusion U2 (U2⊓U3) O (le_inf hO2 hO3))) z.property⟩ : Z3)) ∧
      (∀ z,(e13 z : Z3)=(χ13 ⟨z.val,openPreimage_mono S1 (openPreimage_mono P1
        (commonWindowInclusion U1 (U1⊓U3) O (le_inf hO1 hO3))) z.property⟩ : Z3)) ∧
      e12.trans e23=e13 := by
  obtain ⟨e12,he12,hPoint12⟩ := exists_chosen_overlap_map_restriction
    U1 U2 (U1⊓U2) O inf_le_left inf_le_right (le_inf hO1 hO2) P1 P2 S1 S2 L12 χ12 h12
  obtain ⟨e23,he23,hPoint23⟩ := exists_chosen_overlap_map_restriction
    U2 U3 (U2⊓U3) O inf_le_left inf_le_right (le_inf hO2 hO3) P2 P3 S2 S3 L23 χ23 h23
  obtain ⟨e13,he13,hPoint13⟩ := exists_chosen_overlap_map_restriction
    U1 U3 (U1⊓U3) O inf_le_left inf_le_right (le_inf hO1 hO3) P1 P3 S1 S3 L13 χ13 h13
  have he13' := BlowupTowerSplitIso.IsTowerIso.congr_base he13
    (Φ' := (commonOpenBase U1 U2 O hO1 hO2).trans (commonOpenBase U2 U3 O hO2 hO3))
    (fun z => DFunLike.congr_fun (commonOpenBase_trans U1 U2 U3 O hO1 hO2 hO3) z)
  refine ⟨e12,e23,e13,he12,he23,he13,hPoint12,hPoint23,hPoint13,?_⟩
  exact terminal_padding_comparison_cocycle
    (P1 := restrict (nestedOpens U1 O) P1) (P2 := restrict (nestedOpens U2 O) P2)
    (P3 := restrict (nestedOpens U3 O) P3)
    (S1 := restrict (openPreimage P1 (nestedOpens U1 O)) S1)
    (S2 := restrict (openPreimage P2 (nestedOpens U2 O)) S2)
    (S3 := restrict (openPreimage P3 (nestedOpens U3 O)) S3) L12 L23 L13
    (by simpa only [length_restrict] using h12₁) (by simpa only [length_restrict] using h12₂)
    (by simpa only [length_restrict] using h23₂) (by simpa only [length_restrict] using h23₃)
    (by simpa only [length_restrict] using h13₁) (by simpa only [length_restrict] using h13₃) he12 he23 he13'

end
end Hironaka.HironakaSharpActualCurveChosenOverlapCocycle
