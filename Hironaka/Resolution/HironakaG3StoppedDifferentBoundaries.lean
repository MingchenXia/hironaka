import Hironaka.Resolution.HironakaG3StoppedBoundaryStructuralOverlap
import Hironaka.Resolution.HironakaG3EmptyInitialBoundaryAlignment
set_option autoImplicit false
open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StoppedDifferentBoundaries
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres MaxLocusLocal RestrictEmptyTower
  HironakaOriginalTerminalOverlapComparison HironakaOriginalBoundaryEmptyBaseComparison HironakaG3RTowerClass
  HironakaG3RStoppedOverlap HironakaG3RBoundaryOverlap HironakaG3EmptyAwareHistory
  HironakaG3EmptyInitialBoundaryAlignment
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- Stopped native histories from two boundary lists align on an overlap if
there their filtered original slots and stopping opens agree. -/
theorem stopped_structural_overlap_different_boundaries {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {V : Set X} (hV : IsClosed V) (E₁ E₂ : List (Set X)) (O₁ O₂ : Opens X)
    (hEO₁ : ∀ H ∈ E₁, Disjoint H (O₁ : Set X))
    (hEO₂ : ∀ H ∈ E₂, Disjoint H (O₂ : Set X)) {d : ℕ}
    (hpure₁ : ∀ x : O₁, (x : X) ∈ V → RegularAtDim (n := n) V x d)
    (hpure₂ : ∀ x : O₂, (x : X) ∈ V → RegularAtDim (n := n) V x d)
    (hdense₁ : V ⊆ closure (V ∩ O₁)) (hdense₂ : V ⊆ closure (V ∩ O₂))
    (hdom₁ : IsInvDomain n (⟨univ, E₁, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (hdom₂ : IsInvDomain n (⟨univ, E₂, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U₁ U₂ : Opens X) {Y₁ Y₂ : CMfd.{0} n}
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (h₁ : stoppedClass (⟨univ, E₁, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O₁ U₁ Y₁ T₁)
    (h₂ : stoppedClass (⟨univ, E₂, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O₂ U₂ Y₂ T₂)
    (hE : (((pullback (Subtype.val : nestedOpens U₁ (U₁ ⊓ U₂) → U₁)
      (pullback (Subtype.val : U₁ → X) (⟨univ, E₁, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).E).filter
        (fun H => decide H.Nonempty)) =
      ((((pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂)
      (pullback (Subtype.val : U₂ → X) (⟨univ, E₂, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).E).map
        ((overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) ⁻¹' ·)).filter
        (fun H => decide H.Nonempty)))
    (hO : nestedOpens (nestedOpens U₁ (U₁ ⊓ U₂)) (nestedOpens U₁ O₁) =
      HironakaOriginalBoundaryEmptyBaseComparison.baseOpen
        (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (nestedOpens (nestedOpens U₂ (U₁ ⊓ U₂)) (nestedOpens U₂ O₂))) :
    ∃ ψ : (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) ψ := by
  have hR₁ := isStopped_restrict_nested_bdry hV O₁ hEO₁ hpure₁ hdense₁ hdom₁ U₁ (U₁ ⊓ U₂) T₁ h₁
  have hR₂ := isStopped_restrict_nested_bdry hV O₂ hEO₂ hpure₂ hdense₂ hdom₂ U₂ (U₁ ⊓ U₂) T₂ h₂
  let M : MarkedIdeal n X := ⟨univ,E₂,vanishingIdeal (n := n) V,1⟩
  let M₁ := pullback (Subtype.val : nestedOpens U₁ (U₁ ⊓ U₂) → U₁)
    (pullback (Subtype.val : U₁ → X) (⟨univ,E₁,vanishingIdeal (n := n) V,1⟩ : MarkedIdeal n X))
  let M₂ := pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂)
    (pullback (Subtype.val : U₂ → X) M)
  let Φ := overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  have he := original_overlap_whole_marked_dictionary M hdom₂ (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  have hN : M₁.N = Φ ⁻¹' M₂.N := by
    have h := congrArg MarkedIdeal.N he.symm
    exact h
  have hI : M₁.ideal = GermIdeal.pullback (m := n) Φ M₂.ideal := by
    have h := congrArg MarkedIdeal.ideal he.symm
    exact h
  have hd : M₁.d = M₂.d := by
    have h := congrArg MarkedIdeal.d he.symm
    exact h
  have hdomU₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hdom₂
  have hdomW := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens U₂ (U₁ ⊓ U₂)) hdomU₂
  have hmem : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom₂.isWellFormed.isCoherent hg
  have hmemU : ∀ x g, (pullback (Subtype.val : U₂ → X) M).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomU₂.isWellFormed.isCoherent hg
  have hcosW : M₂.cosupp = {q : nestedOpens U₂ (U₁ ⊓ U₂) | ((q : U₂) : X) ∈ V} := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ hmemU, MarkedIdealRestrictOpen.cosupp_pullback_val _ hmem,
      HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hV]
    rfl
  have hcases : (M₂.cosupp ∩ (nestedOpens (nestedOpens U₂ (U₁ ⊓ U₂)) (nestedOpens U₂ O₂) : Set _)).Nonempty ∨
      M₂.cosupp = ∅ := by
    rw [hcosW]
    by_cases hx : ∃ x ∈ V, x ∈ O₂ ∧ x ∈ U₁ ∧ x ∈ U₂
    · obtain ⟨x,hxV,hxO,hx₁,hx₂⟩ := hx
      exact Or.inl ⟨⟨⟨x,hx₂⟩,hx₁,hx₂⟩,hxV,hxO⟩
    · refine Or.inr (eq_empty_of_forall_notMem fun q hq => ?_)
      have hq₁ : ((q : U₂) : X) ∈ (U₁ ⊓ U₂ : Opens X) := q.2
      obtain ⟨x',hx'W,hx'V,hx'O⟩ := mem_closure_iff.mp (hdense₂ hq) _ (U₁ ⊓ U₂).isOpen hq₁
      exact hx ⟨x',hx'V,hx'O,hx'W.1,hx'W.2⟩
  apply stopped_emptyAware_over_base_across_empty_initial_boundaries hn M₂ M₁ hdomW Φ hN hI hd hE
    (nestedOpens (nestedOpens U₂ (U₁ ⊓ U₂)) (nestedOpens U₂ O₂)) hcases
    (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂)
  · exact hO ▸ hR₁
  · exact hR₂
end
end Hironaka.HironakaG3StoppedDifferentBoundaries
