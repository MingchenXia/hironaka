/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDiscreteCosupportCanonicalHistory
import Hironaka.Resolution.HironakaDimensionGlobalComponents
import Hironaka.Resolution.HironakaPrincipalizationBoundary
import Hironaka.MarkedIdeal.CodimOneSupportAlong

/-!
# Actual global histories from compact connected ORIGINAL support components

Analyticity internally proves local finiteness of actual connected components.
Their whole complements construct exact support-isolating opens; compactness
of each original component then forces local termination of ONE internally
constructed actual global blowup history. Connected ambient manifolds and
positive-dimensional singular components are allowed. The arbitrary connected
noncompact-support scheduler remains separate.
Blueprint: `hironaka-original-compact-support-component-history-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCompactSupportComponentHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSeq ResolutionDriver CanonicalCentres
  HironakaComponentwiseCanonicalCentre HironakaComponentwiseCanonicalHistory
  HironakaSupportDisjointCanonicalCentre HironakaDiscreteCosupportCanonicalHistory
  HironakaLocallyFiniteResolutionSequence GlobalComponents RegularLocusComponent DivisorExponentAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual nonempty connected components of a support; no partition is input. -/
def supportComponents (S : Set X) : Set (Set X) :=
  {C | ∃ x∈S,C=connectedComponentIn S x}

theorem component_subset {S C : Set X} (hC : C∈supportComponents S) : C⊆S := by
  obtain ⟨x,_hx,rfl⟩ := hC
  exact connectedComponentIn_subset S x

theorem component_nonempty {S C : Set X} (hC : C∈supportComponents S) : C.Nonempty := by
  obtain ⟨x,hx,rfl⟩ := hC
  exact ⟨x,mem_connectedComponentIn hx⟩

theorem component_eq_of_inter {S C D : Set X}
    (hC : C∈supportComponents S) (hD : D∈supportComponents S)
    (hCD : (C∩D).Nonempty) : C=D := by
  obtain ⟨x,_hx,rfl⟩ := hC
  obtain ⟨z,_hz,rfl⟩ := hD
  obtain ⟨y,hyC,hyD⟩ := hCD
  exact (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hyD).symm

theorem component_isClosed {S C : Set X} (hS : IsClosed S)
    (hC : C∈supportComponents S) : IsClosed C := by
  obtain ⟨x,hx,rfl⟩ := hC
  apply closure_subset_iff_isClosed.mp
  exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
    (subset_closure (mem_connectedComponentIn hx))
    (closure_minimal (connectedComponentIn_subset S x) hS)

theorem component_pairwise_disjoint (S : Set X) :
    Pairwise (fun C D : supportComponents S => Disjoint (C : Set X) (D : Set X)) := by
  intro C D hne
  apply disjoint_left.mpr
  intro x hxC hxD
  exact hne (Subtype.ext (component_eq_of_inter C.property D.property ⟨x,hxC,hxD⟩))

theorem sUnion_supportComponents (S : Set X) : ⋃₀ supportComponents S=S := by
  apply Subset.antisymm (sUnion_subset fun _ hC => component_subset hC)
  intro x hx
  exact mem_sUnion.mpr ⟨connectedComponentIn S x,⟨x,hx,rfl⟩,mem_connectedComponentIn hx⟩

private theorem global_component_nonempty {S B : Set X}
    (hB : B∈globalComponents (n := n) S) : B.Nonempty := by
  obtain ⟨x,⟨k,hx⟩,rfl⟩ := hB
  exact ⟨x,subset_closure (mem_component_self hx)⟩

private theorem global_component_preconnected {S B : Set X}
    (hB : B∈globalComponents (n := n) S) : IsPreconnected B := by
  obtain ⟨x,_hx,rfl⟩ := hB
  exact isPreconnected_connectedComponentIn.closure

private def componentContaining (S : Set X) (hS : IsComplexAnalyticSubset (n := n) S)
    (B : globalComponents (n := n) S) : supportComponents S :=
  let x := (global_component_nonempty B.property).choose
  ⟨connectedComponentIn S x,x,
    subset_of_mem_globalComponents hS B.property (global_component_nonempty B.property).choose_spec,rfl⟩

private theorem subset_componentContaining (S : Set X) (hS : IsComplexAnalyticSubset (n := n) S)
    (B : globalComponents (n := n) S) : (B : Set X)⊆componentContaining S hS B := by
  exact (global_component_preconnected B.property).subset_connectedComponentIn
    (global_component_nonempty B.property).choose_spec (subset_of_mem_globalComponents hS B.property)

/-- Genuine G5 irreducible components internally prove local finiteness of the
ACTUAL connected support components, including intersecting branch clusters. -/
theorem locallyFinite_supportComponents {S : Set X}
    (hS : IsComplexAnalyticSubset (n := n) S) :
    LocallyFinite (fun C : supportComponents S => (C : Set X)) := by
  intro x
  obtain ⟨U,hUx,hfin⟩ := locallyFinite_globalComponents hS x
  refine ⟨U,hUx,(hfin.image (componentContaining S hS)).subset ?_⟩
  rintro C ⟨y,hyC,hyU⟩
  have hyS := component_subset C.property hyC
  have hyUnion : y∈⋃₀ globalComponents (n := n) S := by rw [sUnion_globalComponents hS];exact hyS
  obtain ⟨B,hB,hyB⟩ := mem_sUnion.mp hyUnion
  refine ⟨⟨B,hB⟩,⟨y,hyB,hyU⟩,?_⟩
  apply Subtype.ext
  exact component_eq_of_inter (componentContaining S hS ⟨B,hB⟩).property C.property
    ⟨y,subset_componentContaining S hS ⟨B,hB⟩ hyB,hyC⟩

/-- Whole complements of other ACTUAL components; no isolating cover is input. -/
def componentWindow (S : Set X) (hS : IsComplexAnalyticSubset (n := n) S)
    (C : supportComponents S) : Opens X :=
  ⟨(⋃ D : {D : supportComponents S // D≠C},(D.val.val : Set X))ᶜ,
    (((locallyFinite_supportComponents hS).comp_injective Subtype.val_injective).isClosed_iUnion
      (fun D => component_isClosed hS.isClosed D.val.property)).isOpen_compl⟩

theorem component_subset_window (S : Set X) (hS : IsComplexAnalyticSubset (n := n) S)
    (C : supportComponents S) : (C : Set X)⊆componentWindow S hS C := by
  intro x hx hother
  obtain ⟨D,hxD⟩ := mem_iUnion.mp hother
  exact D.property (Subtype.ext (component_eq_of_inter D.val.property C.property ⟨x,hxD,hx⟩))

theorem componentWindow_inter_support (S : Set X) (hS : IsComplexAnalyticSubset (n := n) S)
    (C : supportComponents S) : (componentWindow S hS C : Set X)∩S=C := by
  apply Subset.antisymm
  · rintro x ⟨hxU,hxS⟩
    have hh : x∈⋃₀ supportComponents S := by rw [sUnion_supportComponents];exact hxS
    obtain ⟨D,hD,hxD⟩ := mem_sUnion.mp hh
    have he : (⟨D,hD⟩ : supportComponents S)=C := by
      by_contra hne
      exact hxU (mem_iUnion.mpr ⟨⟨⟨D,hD⟩,hne⟩,hxD⟩)
    simpa only [← he] using hxD
  · intro x hx
    exact ⟨component_subset_window S hS C hx,component_subset C.property hx⟩

theorem componentWindow_cover (S : Set X) (hS : IsComplexAnalyticSubset (n := n) S) :
    ∀ x∈S,∃ C : supportComponents S,x∈componentWindow S hS C := by
  intro x hx
  exact ⟨⟨connectedComponentIn S x,x,hx,rfl⟩,
    component_subset_window S hS _ (mem_connectedComponentIn hx)⟩

theorem componentWindow_support_disjoint (S : Set X) (hS : IsComplexAnalyticSubset (n := n) S) :
    Pairwise (fun C D : supportComponents S =>
      Disjoint ((componentWindow S hS C : Set X)∩S) ((componentWindow S hS D : Set X)∩S)) := by
  simpa only [componentWindow_inter_support] using component_pairwise_disjoint S

/-- Original coherence supplies the actual entire analytic support. -/
theorem original_cosupp_analytic (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    IsComplexAnalyticSubset (n := n) M.cosupp :=
  CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hM.isWellFormed.isCoherent
    hM.isWellFormed.isClosedSubmanifold_N hM.one_le_d

/-- Compactness concerns the literal whole original restricted cosupport. -/
theorem isCompact_restricted_component_cosupp (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (C : supportComponents M.cosupp) (hC : IsCompact (C : Set X)) :
    IsCompact (MarkedIdeal.pullback
      (Subtype.val : componentWindow M.cosupp (original_cosupp_analytic M hM) C → X) M).cosupp := by
  let hS := original_cosupp_analytic M hM
  let U := componentWindow M.cosupp hS C
  have he : (Subtype.val : U → X) ⁻¹' M.cosupp=(Subtype.val : U → X) ⁻¹' (C : Set X) := by
    ext z
    constructor
    · intro hz
      exact (Set.ext_iff.mp (componentWindow_inter_support M.cosupp hS C) z.val).mp ⟨z.property,hz⟩
    · exact fun hz => component_subset C.property hz
  rw [cosupp_pullback_val M
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)]
  change IsCompact ((Subtype.val : U → X) ⁻¹' M.cosupp)
  rw [he]
  exact Topology.IsInducing.subtypeVal.isCompact_preimage' hC (by
    intro x hx
    exact ⟨⟨x,component_subset_window M.cosupp hS C hx⟩,rfl⟩)

/-- Transparent OUTPUT of a genuine history; every window and its analytic
support are computed from the original input, never caller supplied. -/
def LocallyTerminalComponentHistory (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (s : GrowingSeq X) : Prop :=
  let U := componentWindow M.cosupp (original_cosupp_analytic M hM)
  (∀ j,IsGeoTestTower M (s.stage j).2) ∧
    (∀ C j,IsCanonical (MarkedIdeal.pullback (Subtype.val : U C → X) M)
      ((canonicalInvariant n).inv (MarkedIdeal.pullback (Subtype.val : U C → X) M))
      (restrict (U C) (s.stage j).2)) ∧
    ParallelSteps (canonicalInvariant n) M U s ∧
    (∀ C,∃ N,∀ j,N≤j →
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U C → X) M)
        (restrict (U C) (s.stage j).2)) ∧
    LocallyFinite (centreImage s) ∧ (∀ j,IsClosed (centreImage s j)) ∧
    ∀ x : X,∃ (N : ℕ) (W : Opens X),x∈W ∧
      (∀ j,N≤j → ∃ (π : (s.stage (j+1)).1 → (s.stage j).1)
        (hπ : IsBlowupAlong n (stepCentre s j) π),
        (s.stage (j+1)).2=.step (s.stage j).2 (stepCentre s j) π hπ ∧
        IsIsomorphismOver n π ((s.stage j).2.proj ⁻¹' (W : Set X))) ∧
      ∀ a,ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 W)
          (HironakaLocallyFiniteResolutionSequence.tailTower s N a))

/-- ONLY original domain and compactness of its ACTUAL connected support
components internally construct every global intermediate blowup and local tail. -/
theorem exists_original_component_compact_locally_terminal_history
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hcompact : ∀ C∈supportComponents M.cosupp,IsCompact C) :
    ∃ s : GrowingSeq X,LocallyTerminalComponentHistory M hM s := by
  let hS := original_cosupp_analytic M hM
  let U := componentWindow M.cosupp hS
  have hcover := componentWindow_cover M.cosupp hS
  have hdisj := componentWindow_support_disjoint M.cosupp hS
  obtain ⟨s,hTest,hCan,hSteps⟩ := exists_support_disjoint_canonical_sequence
    (canonicalInvariant n) M hM U hcover hdisj
  have hterminal : ∀ C,∃ N,∀ j,N≤j →
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U C → X) M)
        (restrict (U C) (s.stage j).2) := by
    intro C
    let MC := MarkedIdeal.pullback (Subtype.val : U C → X) M
    have hd : IsInvDomain n MC := InvDomainTowerAlong.isInvDomain_pullback_val (U C) hM
    have hk : IsCompact MC.cosupp := isCompact_restricted_component_cosupp M hM C
      (hcompact C.val C.property)
    exact eventually_resolves_maximum_sequence (canonicalInvariant n) MC hd hk
      (s.restrict (U C)) (hCan C)
      (restricted_steps_are_support_maxima (canonicalInvariant n) M hM U hdisj s hTest hSteps C)
  exact ⟨s,hTest,hCan,hSteps,hterminal,
    locally_finite_empty_tails_support_disjoint (canonicalInvariant n) M hM U
      hcover hdisj s hTest hSteps hterminal⟩

/-- Natural ORIGINAL ideal inputs construct the actual domain and the SAME
locally finite growing history; no history/domain certificate is incoming. -/
theorem exists_original_ideal_component_compact_history
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∀ x,IsNonzeroAlongAt univ I x)
    (E₀ : List (Set X)) (hE₀ : NormalCrossings.IsSNCDivisor n E₀)
    (hcompact : ∀ C∈supportComponents I.zeroLocus,IsCompact C) :
    let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
    let hM := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
    ∃ s : GrowingSeq X,LocallyTerminalComponentHistory M hM s := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
  have hM : IsInvDomain n M :=
    HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
  apply exists_original_component_compact_locally_terminal_history M hM
  simpa only [show M.cosupp=I.zeroLocus from HironakaAdmissibleSequence.cosupp_univ_one hI] using hcompact

end
end Hironaka.HironakaOriginalCompactSupportComponentHistory
