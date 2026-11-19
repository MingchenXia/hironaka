import Hironaka.Resolution.HironakaG3BiholomorphicFirstMeeting
set_option autoImplicit false
open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StoppedStructuralOverlap
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres MaxLocusLocal RestrictEmptyTower
  HironakaOriginalTerminalOverlapComparison HironakaOriginalBoundaryEmptyBaseComparison HironakaG3RTowerClass
  HironakaG3RStoppedOverlap HironakaG3EmptyAwareHistory HironakaG3BiholomorphicFirstMeeting
  HironakaDisjointFiniteControlledHistory
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- The two actual stopped histories restricted to an overlap have an
empty-aware structural alignment over the canonical overlap base map. -/
theorem stopped_structural_overlap {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {V : Set X} (hV : IsClosed V) (O : Opens X) {d : ℕ}
    (hpure : ∀ x : O, (x : X) ∈ V → RegularAtDim (n := n) V x d) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U₁ U₂ : Opens X) {Y₁ Y₂ : CMfd.{0} n}
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (h₁ : stoppedClass (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O U₁ Y₁ T₁)
    (h₂ : stoppedClass (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O U₂ Y₂ T₂) :
    ∃ ψ : (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) ψ := by
  have hR₁ := isStopped_restrict_nested hV O hpure hdense hdom U₁ (U₁ ⊓ U₂) T₁ h₁
  have hR₂ := isStopped_restrict_nested hV O hpure hdense hdom U₂ (U₁ ⊓ U₂) T₂ h₂
  have he := original_overlap_whole_marked_dictionary _ hdom (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  rw [← he] at hR₁
  have hdomU₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hdom
  have hdomW := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens U₂ (U₁ ⊓ U₂)) hdomU₂
  have hmem : ∀ x g, (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X).ideal.mem x g →
      HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
  have hmemU : ∀ x g, (pullback (Subtype.val : U₂ → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomU₂.isWellFormed.isCoherent hg
  have hcosW : (pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp =
      {q : nestedOpens U₂ (U₁ ⊓ U₂) | ((q : U₂) : X) ∈ V} := by
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val _ hmemU, MarkedIdealRestrictOpen.cosupp_pullback_val _ hmem,
      HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hV]
    rfl
  have hcases : ((pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp ∩
        (nestedOpens (nestedOpens U₂ (U₁ ⊓ U₂)) (nestedOpens U₂ O) : Set _)).Nonempty ∨
      (pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) (pullback (Subtype.val : U₂ → X)
        (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))).cosupp = ∅ := by
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

/-- Compatible actual ambient lifts of the two restricted stopped histories
have endpoint comparisons over their common ambient initial space. -/
theorem stopped_ambient_overlap {n t : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {V : Set X} (hV : IsClosed V) (O : Opens X) {d : ℕ}
    (hpure : ∀ x : O, (x : X) ∈ V → RegularAtDim (n := n) V x d) (hdense : V ⊆ closure (V ∩ O))
    (hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U₁ U₂ : Opens X) {Y₁ Y₂ : CMfd.{0} n}
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (h₁ : stoppedClass (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O U₁ Y₁ T₁)
    (h₂ : stoppedClass (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) O U₂ Y₂ T₂)
    {P : CMfd.{0} (n+t)} {N : Set P} {B : List (Set P)} {J : GermIdeal (n+t) P}
    {ι₁ : nestedOpens U₁ (U₁ ⊓ U₂) → P} {ι₂ : nestedOpens U₂ (U₁ ⊓ U₂) → P}
    (hι : ∀ x, ι₂ (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right x) = ι₁ x)
    {M₁ : MarkedIdeal n (CMfd.of (n := n) (nestedOpens U₁ (U₁ ⊓ U₂)))}
    {M₂ : MarkedIdeal n (CMfd.of (n := n) (nestedOpens U₂ (U₁ ⊓ U₂)))}
    {Z₁ Z₂ : CMfd.{0} (n+t)} {A₁ : BlowupTower P Z₁} {A₂ : BlowupTower P Z₂}
    {η₁ : openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)) → Z₁}
    {η₂ : openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂)) → Z₂}
    (hA₁ : CoupledHistory N B J ι₁ M₁ (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) A₁ η₁)
    (hA₂ : CoupledHistory N B J ι₂ M₂ (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) A₂ η₂) :
    ∃ (ψ : (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))))
      (β : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ Z₂),
      (∀ z, A₂.proj (β z) = A₁.proj z) ∧ ∀ q, β (η₁ q) = η₂ (ψ q) := by
  obtain ⟨ψ,hψ⟩ := stopped_structural_overlap hn hV O hpure hdense hdom U₁ U₂ T₁ T₂ h₁ h₂
  obtain ⟨β,hβ,hη⟩ := exists_ambient_comparison_of_empty_aware_lower_histories
    (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right) hψ hι hA₁ hA₂
  exact ⟨ψ,β,hβ,hη⟩

end
end Hironaka.HironakaG3StoppedStructuralOverlap
