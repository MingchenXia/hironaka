import Hironaka.Resolution.HironakaG8CompactEventAncestry
import Hironaka.Resolution.HironakaG8DisjointMarkedSwap

/-! # Spatially localized branching for actual physical stages -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8SpatialDependencyBranching

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG3RTowerClass HironakaG8CompactEventAncestry HironakaG8DisjointMarkedSwap
  HironakaEmbeddedAnalytic

section Charts
variable {n : ℕ} {X Z : CMfd.{0} n} {I ε : Type*}
  {A : LocalTowerClass X} {P : Z → X} (c : I → TowerChart A Z P)
  (event : ∀ i, Fin (centreFootprints (c i).T).length → ε)

/-- Local finiteness of the chart cover implies local finiteness of the
actual projected event footprints. No global event ordering or choice of
an identification of distinct events is required for this implication. -/
theorem locallyFinite_projected_eventFootprints
    (hLF : LocallyFinite (fun i => ((c i).U : Set X))) :
    LocallyFinite (eventFootprint c event) := by
  intro x
  obtain ⟨V,hV,hFin⟩ := hLF x
  refine ⟨V,hV,(hFin.biUnion (fun i _ => finite_range (event i))).subset ?_⟩
  rintro e ⟨y,⟨i,j,rfl,z,_,rfl⟩,hyV⟩
  exact mem_iUnion₂.mpr ⟨i,⟨z.val,z.property,hyV⟩,j,rfl⟩

/-- If the chosen dependency relation only records spatially meeting
physical events, compactness of each whole projected event footprint
bounds the number of immediate predecessors. -/
theorem finite_incoming_of_compact_projected_events
    (hLF : LocallyFinite (fun i => ((c i).U : Set X)))
    (before : ε → ε → Prop)
    (hSpatial : ∀ ⦃a b⦄, before a b → (eventFootprint c event a ∩ eventFootprint c event b).Nonempty)
    (b : ε) (hB : IsCompact (eventFootprint c event b)) :
    {a | before a b}.Finite :=
  ((locallyFinite_projected_eventFootprints c event hLF).finite_nonempty_inter_compact hB).subset
    (fun _ ha => hSpatial ha)

end Charts

section Pairs
variable {n : ℕ} {A B C : CMfd.{0} n}

/-- The exact existence of the reversed pair in the original TEST and
intrinsic singular category, with a biholomorphic endpoint over the
common source. This predicate does not impose a canonical epoch clock. -/
abbrev HasReversedSingularTestPair (S : Set A) (M : MarkedIdeal n A)
    (D : Set A) (E : Set B) (π : B → A) (q : C → B) : Prop :=
  ∃ (B' C' : CMfd.{0} n) (ρ : B' → A) (r : C' → B')
    (hρ : IsBlowupAlong n (π '' E) ρ)
    (hr : IsBlowupAlong n (ρ ⁻¹' D) r),
    IsGeoTestTower M (.step (.step .refl (π '' E) ρ hρ) (ρ ⁻¹' D) r hr) ∧
    π '' E ⊆ singularSet (n := n) S ∧
    ρ ⁻¹' D ⊆ singularSet (n := n) (strictTransform n ρ S) ∧
    ∃ e : C ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ C',
      (ρ ∘ r) ∘ e = π ∘ q

/-- If a real adjacent pair cannot be reversed even as singular TESTs,
its projected loci meet. This implication only uses an actual swapped
tower and endpoint equivalence, so no ancestry or label is inferred. -/
theorem projected_loci_meet_of_no_reversed_singular_test_pair
    (S : Set A) (hS : IsClosed S) (M : MarkedIdeal n A) (hM : M.IsWellFormed)
    {D : Set A} {E : Set B} {π : B → A} {q : C → B}
    (hπ : IsBlowupAlong n D π) (hq : IsBlowupAlong n E q)
    (hTest : IsGeoTestTower M (.step (.step .refl D π hπ) E q hq))
    (hD : D ⊆ singularSet (n := n) S)
    (hE : E ⊆ singularSet (n := n) (strictTransform n π S))
    (hNo : ¬ HasReversedSingularTestPair S M D E π q) :
    (D ∩ π '' E).Nonempty := by
  by_contra h
  have hd : Disjoint D (π '' E) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    exact h
  exact hNo (swap_actual_steps_of_disjoint_projected_footprints S hS M hM hπ hq hd hTest hD hE)

end Pairs

/-- The compact terminal event has a finite set of possible predecessors
arising from local adjacent pairs which cannot be reversed as singular
TESTs. A witness places both actual projected loci in their respective
event footprints through a common physical prefix on a chart. -/
theorem finite_spatial_candidates_for_actual_singular_test_pairs
    {n : ℕ} {X Z : CMfd.{0} n} {I ε : Type*}
    {K : LocalTowerClass X} {p : Z → X} (c : I → TowerChart K Z p)
    (event : ∀ i, Fin (centreFootprints (c i).T).length → ε)
    (hLF : LocallyFinite (fun i => ((c i).U : Set X)))
    (b : ε) (hB : IsCompact (eventFootprint c event b)) :
    ∃ F : Set ε, F.Finite ∧
      ∀ (a : ε) (i : I) {A B C : CMfd.{0} n}
        (P : BlowupTower (CMfd.of (n := n) (c i).U) A)
        (S : Set A) (_hS : IsClosed S)
        (M : MarkedIdeal n A) (_hM : M.IsWellFormed)
        {D : Set A} {E : Set B} {π : B → A} {q : C → B}
        (hπ : IsBlowupAlong n D π) (hq : IsBlowupAlong n E q),
        IsGeoTestTower M (.step (.step .refl D π hπ) E q hq) →
        D ⊆ singularSet (n := n) S →
        E ⊆ singularSet (n := n) (strictTransform n π S) →
        (fun x => (P.proj x).val) '' D ⊆ eventFootprint c event a →
        (fun x => (P.proj x).val) '' (π '' E) ⊆ eventFootprint c event b →
        (¬ HasReversedSingularTestPair S M D E π q) → a ∈ F := by
  let F := {a | (eventFootprint c event a ∩ eventFootprint c event b).Nonempty}
  refine ⟨F, (locallyFinite_projected_eventFootprints c event hLF).finite_nonempty_inter_compact hB,?_⟩
  intro a i A B C P S hS M hM D E π q hπ hq hTest hD hE hLeft hRight hNo
  obtain ⟨x,hxL,hxR⟩ := projected_loci_meet_of_no_reversed_singular_test_pair
    S hS M hM hπ hq hTest hD hE hNo
  exact ⟨(P.proj x).val,hLeft (mem_image_of_mem _ hxL),hRight (mem_image_of_mem _ hxR)⟩

end Hironaka.HironakaG8SpatialDependencyBranching
