import Hironaka.Resolution.HironakaG3LocalMixedSeparation
import Hironaka.Resolution.HironakaG3MixedTreeSmoothPullback
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3LocalMixedOverlap
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdealRestrictOpen BlowupRestrictOpen
  HironakaBaseChange NormalCrossings RestrictEmptyTower MaxLocusLocal
  HironakaG3FiniteMixedBadLocus HironakaG3MixedOrderedSeparation HironakaG3MixedOrderedComparison
  HironakaG3MixedTreeSmoothPullback HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCartesianTowerChoiceComparison HironakaSmoothSubmersionOrderedGlobalTrace
  HironakaOriginalUntestedCurveSmoothValues HironakaOriginalTerminalOverlapComparison
  HironakaOriginalCanonicalSeparationChainChoice HironakaEmbeddedAnalyticLocal

/-- The actual smooth pullback of a local mixed tree to any smaller open,
identified with its literal tower restriction. -/
theorem local_mixed_tree_actual_restriction {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (E : List (Set X)) (U : Opens X) {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y)
    (Ef : List (Set Y))
    (hTree : CanonicalMixedSeparation (E.map ((Subtype.val : U → X) ⁻¹' ·))
      ((List.finRange k).map fun a => ((Subtype.val : U → X) ⁻¹' (V a).carrier,(V a).dim)) T Ef)
    (hOver : CentresOver ((Subtype.val : U → X) ⁻¹' mixedBadLocus V) T)
    (W : Opens (CMfd.of (n := n) U)) :
    ∃ (C : CMfd.{0} n) (Q : BlowupTower (CMfd.of (n := n) W) C) (g : C → Y)
      (β : C ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T W)),
      CanonicalMixedSeparation ((E.map ((Subtype.val : U → X) ⁻¹' ·)).map ((Subtype.val : W → U) ⁻¹' ·))
        (((List.finRange k).map fun a => ((Subtype.val : U → X) ⁻¹' (V a).carrier,(V a).dim)).map
          (fun p => ((Subtype.val : W → U) ⁻¹' p.1,p.2))) Q (Ef.map (g ⁻¹' ·)) ∧
      (∀ q, (restrict W T).proj (β q) = Q.proj q) ∧ (∀ q, (β q : openPreimage T W).val = g q) := by
  let GU := (Subtype.val : U → X) ⁻¹' mixedBadLocus V
  let LU := (List.finRange k).map fun a => ((Subtype.val : U → X) ⁻¹' (V a).carrier,(V a).dim)
  have hData := mixedBadLocus_closed_and_good V hDim hDistinct
  have hGU : IsClosed GU := hData.1.preimage continuous_subtype_val
  have hLU : ∀ p ∈ LU, IsComplexAnalyticSubset (n := n) p.1 := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val (V a).irreducible_carrier.analytic
  have hdLU : ∀ p ∈ LU, p.1 ⊆ closure (p.1 \ GU) := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    calc
      (Subtype.val : U → X) ⁻¹' (V a).carrier ⊆
          (Subtype.val : U → X) ⁻¹' closure ((V a).carrier \ mixedBadLocus V) :=
        preimage_mono (hData.2 a).2.2.2.2
      _ = closure ((Subtype.val : U → X) ⁻¹' (V a).carrier \ GU) := by
        have hval := isOpenHoloEmbedding_val (n := n) U
        rw [hval.preimage_closure,preimage_sdiff]
  obtain ⟨C,Q,g,hactual,hsrc,_hstrict⟩ := mixed_tree_smooth_pullback
    (Y := CMfd.of (n := n) W) hTree GU hGU hLU hdLU hOver
    (b := (Subtype.val : W → U)) (isSubmersion_val W)
  obtain ⟨β,⟨hproj,hval⟩,_huniq⟩ :=
    existsUnique_whole_cartesian_comparison hactual (open_inclusion_actual_tower W T)
  refine ⟨C,Q,g,β,?_,hproj,hval⟩
  simpa only [Nat.sub_self,Nat.add_zero] using hsrc

private theorem filter_preimage {P Q : Type*} (f : P → Q) (hf : Surjective f)
    (E : List (Set Q)) :
    (E.map (f ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
      (E.filter (fun H => decide H.Nonempty)).map (f ⁻¹' ·) := by
  induction E with
  | nil => rfl
  | cons H E ih =>
    have hh : (f ⁻¹' H).Nonempty ↔ H.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨f x,hx⟩,fun h => h.preimage hf⟩
    by_cases hne : H.Nonempty <;> simp [hh,hne,ih]

/-- Independently constructed local mixed trees compare on their literal
ambient overlap, retaining every labelled component including empty traces. -/
theorem local_mixed_trees_overlap {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (E : List (Set X)) (U₁ U₂ : Opens X) {Y₁ Y₂ : CMfd.{0} n}
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁)
    (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (Ef₁ : List (Set Y₁)) (Ef₂ : List (Set Y₂))
    (hTree₁ : CanonicalMixedSeparation (E.map ((Subtype.val : U₁ → X) ⁻¹' ·))
      ((List.finRange k).map fun a => ((Subtype.val : U₁ → X) ⁻¹' (V a).carrier,(V a).dim)) T₁ Ef₁)
    (hTree₂ : CanonicalMixedSeparation (E.map ((Subtype.val : U₂ → X) ⁻¹' ·))
      ((List.finRange k).map fun a => ((Subtype.val : U₂ → X) ⁻¹' (V a).carrier,(V a).dim)) T₂ Ef₂)
    (hOver₁ : CentresOver ((Subtype.val : U₁ → X) ⁻¹' mixedBadLocus V) T₁)
    (hOver₂ : CentresOver ((Subtype.val : U₂ → X) ⁻¹' mixedBadLocus V) T₂) :
    let W₁ := nestedOpens U₁ (U₁ ⊓ U₂)
    let W₂ := nestedOpens U₂ (U₁ ⊓ U₂)
    ∃ η : CMfd.of (n := n) (openPreimage T₁ W₁) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₂ W₂),
      ∀ z, ((T₂.proj (η z).val : U₂) : X) = ((T₁.proj z.val : U₁) : X) := by
  let W₁ := nestedOpens U₁ (U₁ ⊓ U₂)
  let W₂ := nestedOpens U₂ (U₁ ⊓ U₂)
  let Φ := overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  obtain ⟨C₁,Q₁,g₁,β₁,hQ₁,hβ₁,_hg₁⟩ :=
    local_mixed_tree_actual_restriction V hDim hDistinct E U₁ T₁ Ef₁ hTree₁ hOver₁ W₁
  obtain ⟨C₂,Q₂,g₂,β₂,hQ₂,hβ₂,_hg₂⟩ :=
    local_mixed_tree_actual_restriction V hDim hDistinct E U₂ T₂ Ef₂ hTree₂ hOver₂ W₂
  let E₁ := (E.map ((Subtype.val : U₁ → X) ⁻¹' ·)).map ((Subtype.val : W₁ → U₁) ⁻¹' ·)
  let E₂ := (E.map ((Subtype.val : U₂ → X) ⁻¹' ·)).map ((Subtype.val : W₂ → U₂) ⁻¹' ·)
  let L₁ := ((List.finRange k).map fun a => ((Subtype.val : U₁ → X) ⁻¹' (V a).carrier,(V a).dim)).map
    (fun p => ((Subtype.val : W₁ → U₁) ⁻¹' p.1,p.2))
  let L₂ := ((List.finRange k).map fun a => ((Subtype.val : U₂ → X) ⁻¹' (V a).carrier,(V a).dim)).map
    (fun p => ((Subtype.val : W₂ → U₂) ⁻¹' p.1,p.2))
  have hEeq : E₁ = E₂.map (Φ ⁻¹' ·) := by
    simp only [E₁,E₂,List.map_map,Function.comp_def]
    congr 1
  have hEfilter : E₁.filter (fun H => decide H.Nonempty) =
      (E₂.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·) := by
    rw [hEeq,filter_preimage Φ Φ.surjective]
  have hLeq : L₁ = pulledParts Φ L₂ := by
    simp only [L₁,L₂,pulledParts,List.map_map,Function.comp_def]
    congr 1
  have hQ₁' : CanonicalMixedSeparation E₁ (pulledParts Φ L₂) Q₁ (Ef₁.map (g₁ ⁻¹' ·)) := by
    rw [← hLeq]
    exact hQ₁
  obtain ⟨γ,⟨hγ,_hγE,_hγstrict⟩,_hγuniq⟩ :=
    ordered_mixed_tree_choice hQ₂ Φ E₁ Q₁ hEfilter hQ₁'
  let η := β₁.symm.trans (γ.trans β₂)
  refine ⟨η,?_⟩
  intro z
  let q := β₁.symm z
  have h₁ := congrArg (fun p : W₁ => ((p.val : U₁) : X)) (hβ₁ q)
  have h₂ := congrArg (fun p : W₂ => ((p.val : U₂) : X)) (hβ₂ (γ q))
  have hγ' : ((Q₂.proj (γ q) : W₂).val : U₂) =
      (Φ (Q₁.proj q)).val := congrArg Subtype.val (hγ q)
  have hγ'' : (((Q₂.proj (γ q) : W₂).val : U₂) : X) =
      (((Q₁.proj q : W₁).val : U₁) : X) := by
    rw [hγ']
    rfl
  simp only [proj_restrict] at h₁ h₂
  have hq : β₁ q = z := β₁.apply_symm_apply z
  rw [hq] at h₁
  change ((T₂.proj (β₂ (γ q)).val : U₂) : X) = ((T₁.proj z.val : U₁) : X)
  exact h₂.trans (hγ''.trans h₁.symm)

end
end Hironaka.HironakaG3LocalMixedOverlap
