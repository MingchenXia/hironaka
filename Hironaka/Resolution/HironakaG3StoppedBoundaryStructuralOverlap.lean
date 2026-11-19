import Hironaka.Resolution.HironakaG3StoppedStructuralOverlap
import Hironaka.Resolution.HironakaG3RBoundaryOverlap
set_option autoImplicit false
open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StoppedBoundaryStructuralOverlap
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres MaxLocusLocal RestrictEmptyTower
  HironakaOriginalTerminalOverlapComparison HironakaOriginalBoundaryEmptyBaseComparison HironakaG3RTowerClass
  HironakaG3RStoppedOverlap HironakaG3RBoundaryOverlap HironakaG3EmptyAwareHistory HironakaG3BiholomorphicFirstMeeting
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- The two actual stopped histories restricted to an overlap have an
empty-aware structural alignment over the canonical overlap base map. -/
theorem stopped_structural_overlap_bdry {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {V : Set X} (hV : IsClosed V) {E : List (Set X)} (O : Opens X)
    (hEO : ∀ H ∈ E, Disjoint H (O : Set X)) {d : ℕ}
    (hpure : ∀ x : O, (x : X) ∈ V → RegularAtDim (n := n) V x d) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain n (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U₁ U₂ : Opens X) {Y₁ Y₂ : CMfd.{0} n}
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (h₁ : stoppedClass (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O U₁ Y₁ T₁)
    (h₂ : stoppedClass (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O U₂ Y₂ T₂) :
    ∃ ψ : (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) ψ := by
  have hR₁ := isStopped_restrict_nested_bdry hV O hEO hpure hdense hdom U₁ (U₁ ⊓ U₂) T₁ h₁
  have hR₂ := isStopped_restrict_nested_bdry hV O hEO hpure hdense hdom U₂ (U₁ ⊓ U₂) T₂ h₂
  have he := original_overlap_whole_marked_dictionary _ hdom (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  rw [← he] at hR₁
  have hdomU₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hdom
  have hdomW := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens U₂ (U₁ ⊓ U₂)) hdomU₂
  have hmem : ∀ x g, (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X).ideal.mem x g →
      HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
  have hmemU : ∀ x g, (pullback (Subtype.val : U₂ → X)
      (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomU₂.isWellFormed.isCoherent hg
  have hcosW : (pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
      (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp =
      {q : nestedOpens U₂ (U₁ ⊓ U₂) | ((q : U₂) : X) ∈ V} := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ hmemU, MarkedIdealRestrictOpen.cosupp_pullback_val _ hmem,
      HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hV]
    rfl
  have hcases : ((pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
      (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp ∩
        (nestedOpens (nestedOpens U₂ (U₁ ⊓ U₂)) (nestedOpens U₂ O) : Set _)).Nonempty ∨
      (pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
        (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp = ∅ := by
    rw [hcosW]
    by_cases hx : ∃ x ∈ V, x ∈ O ∧ x ∈ U₁ ∧ x ∈ U₂
    · obtain ⟨x, hxV, hxO, hx₁, hx₂⟩ := hx
      exact Or.inl ⟨⟨⟨x, hx₂⟩, hx₁, hx₂⟩, hxV, hxO⟩
    · refine Or.inr (eq_empty_of_forall_notMem fun q hq => ?_)
      have hq₁ : ((q : U₂) : X) ∈ (U₁ ⊓ U₂ : Opens X) := q.2
      obtain ⟨x', hx'W, hx'V, hx'O⟩ := mem_closure_iff.mp (hdense hq) _ (U₁ ⊓ U₂).isOpen hq₁
      exact hx ⟨x', hx'V, hx'O, hx'W.1, hx'W.2⟩
  exact stopped_emptyAware_over_base hn _ hdomW (overlapBaseEquiv (n := n)
    (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) _ hcases _ _ (hR₁.congr_open (Set.ext fun _ => Iff.rfl)) hR₂


end
end Hironaka.HironakaG3StoppedBoundaryStructuralOverlap
