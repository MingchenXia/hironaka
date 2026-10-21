/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaLocallyFiniteResolutionSequence
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix
import Hironaka.Resolution.HironakaOriginalTerminalProjectionUniqueness

/-!
# Genuine stabilizing windows and late-prefix maps of actual LF histories

No marked record, canonicality, compatible atlas or comparison map is incoming.
Blueprint: `hironaka-actual-locally-finite-history-comparison-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualLocallyFiniteHistoryComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq RestrictEmptyTower HironakaLocallyFiniteResolutionSequence
  HironakaOriginalEmptyHeadPrefix HironakaOriginalTerminalProjectionUniqueness
  BlowupTowerIsoTail MaxLocusLocal
variable {n : ℕ} {X : CMfd.{u} n}

/-- Raw actual LF images give a genuine avoided open and every whole empty
restricted finite tail, with no canonical invariant premise. -/
theorem exists_actual_stabilizing_window (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (x : X) :
    ∃ (N : ℕ) (U : Opens X),x∈U ∧
      (∀ i,N ≤ i → Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X))) ∧
      ∀ r,ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 U) (tailTower s N r)) := by
  obtain ⟨V,hV,hfin⟩ := hLF x
  obtain ⟨U,hUV,hUo,hxU⟩ := mem_nhds_iff.mp hV
  obtain ⟨B,hB⟩ := hfin.bddAbove
  have hAvoid : ∀ i,B + 1 ≤ i →
      Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' U) := by
    intro i hi
    apply disjoint_left.mpr
    intro y hyC hyU
    have hhit : (centreImage s i ∩ V).Nonempty := ⟨(s.stage i).2.proj y,
      ⟨y,hyC,rfl⟩,hUV hyU⟩
    have hh := hB hhit
    omega
  refine ⟨B+1,⟨U,hUo⟩,hxU,hAvoid,?_⟩
  intro r
  exact (isEmptyTower_restrict_iff _ _).mpr (centresAvoid_tailTower s (B+1) ⟨U,hUo⟩ hAvoid r)

private theorem exists_to_stable_prefix
    (s : GrowingSeq X) (U : Opens X) (N : ℕ)
    (hAvoid : ∀ i,N ≤ i → Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X)))
    (j : ℕ) (hj : N ≤ j) :
    ∃ β : CMfd.of (n := n) (openPreimage (s.stage j).2 U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage (s.stage N).2 U),
      ∀ z,(restrict U (s.stage N).2).proj (β z)=(restrict U (s.stage j).2).proj z := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hj
  let TN := (s.stage N).2
  let S := tailTower s N r
  let W := openPreimage TN U
  have he : ResolutionInvariantExt.IsEmptyTower (restrict W S) :=
    (isEmptyTower_restrict_iff _ _).mpr (centresAvoid_tailTower s N U hAvoid r)
  obtain ⟨β,hβ⟩ := exists_empty_tower_projection (restrict W S) he
  have hOpen : openPreimage S W=openPreimage (s.stage (N+r)).2 U := by
    rw [openPreimage_append,append_tailTower]
  let e := (opensCongr hOpen.symm).trans β
  refine ⟨e,?_⟩
  intro z
  apply Subtype.ext
  rw [proj_restrict,proj_restrict]
  change TN.proj ((e z).val)=(s.stage (N+r)).2.proj z.val
  have hb := congrArg Subtype.val (hβ (opensCongr hOpen.symm z))
  rw [proj_restrict] at hb
  change (e z).val=S.proj z.val at hb
  rw [hb]
  have hp := congrArg (fun T : BlowupTower X (s.stage (N+r)).1 => T.proj z.val)
    (append_tailTower s N r)
  simpa only [BlowupTower.proj_append,Function.comp_apply] using hp

/-- The unique actual late endpoint map is internally produced from the SAME
history's real empty tails, not from a supplied stage comparison. -/
theorem exists_unique_late_prefix_comparison
    (s : GrowingSeq X) (U : Opens X) (N : ℕ)
    (hAvoid : ∀ k,N ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (U : Set X)))
    (i j : ℕ) (hi : N ≤ i) (hj : N ≤ j) :
    ∃! β : CMfd.of (n := n) (openPreimage (s.stage j).2 U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage (s.stage i).2 U),
      ∀ z,(restrict U (s.stage i).2).proj (β z)=(restrict U (s.stage j).2).proj z := by
  obtain ⟨βi,hiβ⟩ := exists_to_stable_prefix s U N hAvoid i hi
  obtain ⟨βj,hjβ⟩ := exists_to_stable_prefix s U N hAvoid j hj
  let β := βj.trans βi.symm
  have hβ : ∀ z,(restrict U (s.stage i).2).proj (β z)=(restrict U (s.stage j).2).proj z := by
    intro z
    have hh := hiβ (βi.symm (βj z))
    rw [βi.apply_symm_apply] at hh
    exact hh.symm.trans (hjβ z)
  refine ⟨β,hβ,?_⟩
  intro γ hγ
  exact biholomorphisms_eq_of_actual_proj_eq (restrict U (s.stage i).2) γ β
    (fun z => (hγ z).trans (hβ z).symm)

variable (s : GrowingSeq X) (U : Opens X) (N : ℕ)
  (hAvoid : ∀ k,N ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (U : Set X)))

/-- The actual unique late-prefix map, chosen only from the real history and
its genuine stabilizing window. -/
def latePrefixComparison (i j : ℕ) (hi : N ≤ i) (hj : N ≤ j) :
    CMfd.of (n := n) (openPreimage (s.stage j).2 U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (s.stage i).2 U) :=
  (exists_unique_late_prefix_comparison s U N hAvoid i j hi hj).choose

theorem latePrefixComparison_proj (i j : ℕ) (hi : N ≤ i) (hj : N ≤ j)
    (z : openPreimage (s.stage j).2 U) :
    (restrict U (s.stage i).2).proj (latePrefixComparison s U N hAvoid i j hi hj z)=
      (restrict U (s.stage j).2).proj z :=
  (exists_unique_late_prefix_comparison s U N hAvoid i j hi hj).choose_spec.1 z

theorem latePrefixComparison_self (i : ℕ) (hi : N ≤ i) :
    latePrefixComparison s U N hAvoid i i hi hi=
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (openPreimage (s.stage i).2 U)) ∞ := by
  exact ((exists_unique_late_prefix_comparison s U N hAvoid i i hi hi).choose_spec.2 _
    (fun _ => rfl)).symm

theorem latePrefixComparison_symm (i j : ℕ) (hi : N ≤ i) (hj : N ≤ j) :
    (latePrefixComparison s U N hAvoid i j hi hj).symm=
      latePrefixComparison s U N hAvoid j i hj hi := by
  apply biholomorphisms_eq_of_actual_proj_eq (restrict U (s.stage j).2)
  intro z
  have hh := latePrefixComparison_proj s U N hAvoid i j hi hj
    ((latePrefixComparison s U N hAvoid i j hi hj).symm z)
  rw [Diffeomorph.apply_symm_apply] at hh
  exact hh.symm.trans (latePrefixComparison_proj s U N hAvoid j i hj hi z).symm

theorem latePrefixComparison_trans (i j k : ℕ) (hi : N ≤ i) (hj : N ≤ j) (hk : N ≤ k) :
    (latePrefixComparison s U N hAvoid j k hj hk).trans
      (latePrefixComparison s U N hAvoid i j hi hj)=
      latePrefixComparison s U N hAvoid i k hi hk := by
  apply biholomorphisms_eq_of_actual_proj_eq (restrict U (s.stage i).2)
  intro z
  exact (latePrefixComparison_proj s U N hAvoid i j hi hj
    (latePrefixComparison s U N hAvoid j k hj hk z)).trans
      ((latePrefixComparison_proj s U N hAvoid j k hj hk z).trans
        (latePrefixComparison_proj s U N hAvoid i k hi hk z).symm)

end
end Hironaka.HironakaActualLocallyFiniteHistoryComparison
