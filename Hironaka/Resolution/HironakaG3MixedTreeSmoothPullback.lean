import Hironaka.Resolution.HironakaG3MixedOrderedSupport
import Hironaka.Resolution.HironakaOriginalOrderedTreeSmoothPullback
import Hironaka.Resolution.HironakaOriginalUntestedCurveSmoothValues
import Hironaka.Resolution.HironakaSmoothSubmersionCartesianTowerChoiceComparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3MixedTreeSmoothPullback
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaAdmissibleSequence HironakaAdmissibleCalculus RestrictEmptyTower
  HironakaOriginalCanonicalPartListResolution HironakaOriginalCanonicalOrderedResolution
  HironakaOriginalOrderedTreeSmoothPullback HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaOriginalStoppedPrefixSmoothComparison
  HironakaG3MixedOrderedSeparation HironakaG3MixedOrderedSupport
  HironakaOriginalUntestedCurveSmoothValues HironakaSmoothSubmersionOrderedGlobalTrace
  HironakaSmoothSubmersionCartesianTowerChoiceComparison MarkedIdealRestrictOpen BlowupRestrictOpen

/-- An actual mixed-separator tree with analytic parts and a closed avoided
support pulls back to an intrinsic actual mixed-separator tree on every
smooth source, with no source compactness or supplied history. -/
theorem mixed_tree_smooth_pullback
    {n m : ℕ} {X D : CMfd.{0} n} {Y : CMfd.{0} m}
    {E : List (Set X)} {L : List (Set X × ℕ)} {T : BlowupTower X D} {Ef : List (Set D)}
    (htree : CanonicalMixedSeparation E L T Ef)
    (F : Set X) (hF : IsClosed F)
    (hL : ∀ p ∈ L, IsComplexAnalyticSubset (n := n) p.1)
    (hdL : ∀ p ∈ L, p.1 ⊆ closure (p.1 \ F))
    (hover : CentresOver F T) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    ∃ (C : CMfd.{0} m) (Q : BlowupTower Y C) (g : C → D),
      IsActualTowerPullback b Q T g ∧
      CanonicalMixedSeparation (E.map (b ⁻¹' ·))
        (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) Q (Ef.map (g ⁻¹' ·)) ∧
      ∀ P : Set X, P ⊆ closure (P \ F) →
        strictTransform m Q.proj (b ⁻¹' P) = g ⁻¹' strictTransform n T.proj P := by
  induction htree generalizing m Y with
  | @nil X E =>
    have h := IsActualTowerPullback.refl hb
    refine ⟨Y,.refl,b,h,.nil,?_⟩
    intro P hd
    let O : Opens X := ⟨Fᶜ,hF.isOpen_compl⟩
    exact IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb h O True.intro P hd
  | @cons X D₀ D E A d L E₁ E₂ T₀ T hsep htail ih =>
    obtain ⟨hover₀,hoverT⟩ := (centresOver_append_iff F T₀ T).mp hover
    have hAa := hL (A,d) (List.mem_cons_self ..)
    have hdA := hdL (A,d) (List.mem_cons_self ..)
    have hLt : ∀ p ∈ L, IsComplexAnalyticSubset (n := n) p.1 :=
      fun p hp => hL p (List.mem_cons_of_mem _ hp)
    have hdLt : ∀ p ∈ L, p.1 ⊆ closure (p.1 \ F) :=
      fun p hp => hdL p (List.mem_cons_of_mem _ hp)
    obtain ⟨C₀,Q₀,g₀,hactual₀,hsepQ,_hoverQ₀,_hadmQ₀,hstrict₀⟩ :=
      separation_chain_smooth_pullback hsep F hF hAa hLt hdA hdLt hover₀ hb
    let F₁ := T₀.proj ⁻¹' F
    let L₁ := strictParts T₀ L
    have hF₁ : IsClosed F₁ := hF.preimage T₀.contMDiff_proj.continuous
    have hL₁ : ∀ p ∈ L₁, IsComplexAnalyticSubset (n := n) p.1 := by
      intro p hp
      obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
      exact isComplexAnalyticSubset_strictTransform T₀.isBlowupSequence (hLt p₀ hp₀)
    have hdL₁ : ∀ p ∈ L₁, p.1 ⊆ closure (p.1 \ F₁) := by
      intro p hp
      obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
      exact strictTransform_subset_closure_diff T₀.contMDiff_proj (hLt p₀ hp₀).isClosed (hdLt p₀ hp₀)
    obtain ⟨C,Q,g,hactual,hTreeQ,_hstrictQ⟩ :=
      ih F₁ hF₁ hL₁ hdL₁ hoverT hactual₀.isSubmersion
    have hList : L₁.map (fun p => (g₀ ⁻¹' p.1,p.2+(m-n))) =
        strictParts Q₀ (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) := by
      simp only [L₁,strictParts,List.map_map]
      apply List.map_congr_left
      intro p hp
      apply Prod.ext
      · exact (hstrict₀ p.1 (hdLt p hp)).symm
      · rfl
    have hTreeQ' : CanonicalMixedSeparation (E₁.map (g₀ ⁻¹' ·))
        (strictParts Q₀ (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n))))) Q (E₂.map (g ⁻¹' ·)) := by
      rw [← hList]
      exact hTreeQ
    have hwhole : IsActualTowerPullback b (Q₀.append Q) (T₀.append T) g := hactual₀.append hactual
    have hsrc : CanonicalMixedSeparation (E.map (b ⁻¹' ·))
        (((A,d)::L).map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) (Q₀.append Q) (E₂.map (g ⁻¹' ·)) :=
      .cons Q₀ Q hsepQ hTreeQ'
    refine ⟨C,Q₀.append Q,g,hwhole,hsrc,?_⟩
    intro P hd
    let O : Opens X := ⟨Fᶜ,hF.isOpen_compl⟩
    have hav := centresAvoid_of_centresOver O disjoint_compl_left (T₀.append T) hover
    exact IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hwhole O hav P hd

/-- The constructed full ordered separator of incomparable irreducible
components pulls back intrinsically to every smooth source. -/
theorem full_mixed_tree_smooth_pullback
    {n m k : ℕ} {X D : CMfd.{0} n} {Y : CMfd.{0} m}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    {E : List (Set X)} {T : BlowupTower X D} {Ef : List (Set D)}
    (htree : CanonicalMixedSeparation E ((List.finRange k).map fun a => ((V a).carrier,(V a).dim)) T Ef)
    {b : Y → X} (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    ∃ (C : CMfd.{0} m) (Q : BlowupTower Y C) (g : C → D),
      IsActualTowerPullback b Q T g ∧
      CanonicalMixedSeparation (E.map (b ⁻¹' ·))
        (((List.finRange k).map fun a => ((V a).carrier,(V a).dim)).map
          (fun p => (b ⁻¹' p.1,p.2+(m-n)))) Q (Ef.map (g ⁻¹' ·)) ∧
      ∀ P : Set X, P ⊆ closure (P \ intersectionSupport V) →
        strictTransform m Q.proj (b ⁻¹' P) = g ⁻¹' strictTransform n T.proj P := by
  have hF := intersectionSupport_analytic_and_dense V hDistinct
  apply mixed_tree_smooth_pullback htree (intersectionSupport V) hF.1.isClosed
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact (V a).irreducible_carrier.analytic
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact hF.2 a
  · exact full_mixed_tree_centresOver_intersections V htree
  · exact hb


/-- Over a literal open, the intrinsic actual source tree has the unique
endpoint identification with the literal restriction of the original tower. -/
theorem full_mixed_tree_actual_open
    {n k : ℕ} {X D : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    {E : List (Set X)} {T : BlowupTower X D} {Ef : List (Set D)}
    (htree : CanonicalMixedSeparation E ((List.finRange k).map fun a => ((V a).carrier,(V a).dim)) T Ef)
    (U : Opens X) :
    ∃ (C : CMfd.{0} n) (Q : BlowupTower (CMfd.of (n := n) U) C) (g : C → D)
      (β : C ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U)),
      IsActualTowerPullback (Subtype.val : U → X) Q T g ∧
      CanonicalMixedSeparation (E.map ((Subtype.val : U → X) ⁻¹' ·))
        (((List.finRange k).map fun a => ((V a).carrier,(V a).dim)).map
          (fun p => ((Subtype.val : U → X) ⁻¹' p.1,p.2))) Q (Ef.map (g ⁻¹' ·)) ∧
      (∀ q, (restrict U T).proj (β q) = Q.proj q) ∧
      (∀ q, (β q : openPreimage T U).val = g q) := by
  obtain ⟨C,Q,g,hactual,hsrc,_hstrict⟩ :=
    full_mixed_tree_smooth_pullback (Y := CMfd.of (n := n) U) V hDistinct htree
      (b := (Subtype.val : U → X)) (isSubmersion_val U)
  obtain ⟨β,⟨hproj,hval⟩,_huniq⟩ :=
    existsUnique_whole_cartesian_comparison hactual (open_inclusion_actual_tower U T)
  refine ⟨C,Q,g,β,hactual,?_,hproj,hval⟩
  simpa only [Nat.sub_self,Nat.add_zero] using hsrc

end
end Hironaka.HironakaG3MixedTreeSmoothPullback
