/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualChronologicalOpenNaturality
import Hironaka.Resolution.HironakaSharpActualChronologicalDistinctDefect
/-! Whole ideal-germ relations and genuine DISTINCT quotient images commute
with actual opens, including every bad-point collision and empty position. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualDistinctCountOpenNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualChronologicalOpenNaturality HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalDistinctDefect RelativePrincipalizationSpan
  MarkedIdealRestrictOpen NormalCrossings
variable {n m : ℕ} {X : CMfd.{u} n}

private theorem coherent_mem_comp_val_iff (I : GermIdeal n X) (hc : I.IsCoherent)
    (U : Opens X) (x : U) (g : X → ℂ) :
    (GermIdeal.pullback (m := n) (Subtype.val : U → X) I).mem x (g ∘ Subtype.val) ↔ I.mem x.val g := by
  constructor
  · intro hg
    have hext := (mem_pullback_val_iff U hc).mp hg
    have heq : extendOpens U (g ∘ Subtype.val)=ᶠ[𝓝 x.val] g :=
      (eventually_nhds_val_iff U).mpr (Eventually.of_forall fun y => by simp)
    exact HomogenizedIdeal.mem_congr hc hext heq
  · exact comp_val_mem_pullback_val U hc

/-- BOTH actual ideal-germ predicate directions, for EVERY germ. -/
theorem actual_ideal_germ_relation_open (F : Fin m → GermIdeal n X)
    (hc : ∀ i,(F i).IsCoherent) (U : Opens X) (x : U) (i j : Fin m) :
    (actualIdealGermSetoid (X := CMfd.of (n := n) U) (fun a => GermIdeal.pullback (m := n) (Subtype.val : U → X) (F a)) x).r i j ↔
      (actualIdealGermSetoid F x.val).r i j := by
  constructor
  · intro h g
    constructor
    · intro hg
      exact (coherent_mem_comp_val_iff (F j) (hc j) U x g).mp
        ((h (g ∘ Subtype.val)).mp ((coherent_mem_comp_val_iff (F i) (hc i) U x g).mpr hg))
    · intro hg
      exact (coherent_mem_comp_val_iff (F i) (hc i) U x g).mp
        ((h (g ∘ Subtype.val)).mpr ((coherent_mem_comp_val_iff (F j) (hc j) U x g).mpr hg))
  · intro h g
    change (GermIdeal.pullback (m := n) (Subtype.val : U → X) (F i)).mem x g ↔
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) (F j)).mem x g
    rw [mem_pullback_val_iff U (hc i),mem_pullback_val_iff U (hc j)]
    exact h (extendOpens U g)

/-- Cardinality of the TRUE proper quotient image, never an indexed count. -/
theorem actual_distinct_proper_count_open (F : Fin m → GermIdeal n X)
    (hc : ∀ i,(F i).IsCoherent) (U : Opens X) (x : U) :
    actualDistinctProperCount (X := CMfd.of (n := n) U) (fun a => GermIdeal.pullback (m := n) (Subtype.val : U → X) (F a)) x=
      actualDistinctProperCount F x.val := by
  let FU := fun a => GermIdeal.pullback (m := n) (Subtype.val : U → X) (F a)
  have hRel : ∀ i j,(actualIdealGermSetoid F x.val).r i j ↔
      (actualIdealGermSetoid (X := CMfd.of (n := n) U) FU x).r i j := fun i j => (actual_ideal_germ_relation_open F hc U x i j).symm
  let eQ := Quotient.congr (Equiv.refl (Fin m)) hRel
  have hProper : actualProperPositions (X := CMfd.of (n := n) U) FU x=actualProperPositions F x.val := by
    ext i
    simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and]
    exact not_congr (coherent_mem_comp_val_iff (F i) (hc i) U x (1 : X → ℂ))
  have hmk : Quotient.mk (actualIdealGermSetoid (X := CMfd.of (n := n) U) FU x)=
      eQ ∘ Quotient.mk (actualIdealGermSetoid F x.val) := by
    funext i
    exact (Quotient.congr_mk (Equiv.refl (Fin m)) hRel i).symm
  change ((actualProperPositions (X := CMfd.of (n := n) U) FU x).image (Quotient.mk (actualIdealGermSetoid (X := CMfd.of (n := n) U) FU x))).card=_
  rw [hProper,hmk,←Finset.image_image,Finset.card_image_of_injective _ eQ.injective]
  rfl

/-- ONLY original data supply every chronological member before the whole count dictionary. -/
theorem original_chronological_distinct_count_open (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (U : Opens X) (x : openPreimage T U) :
    actualDistinctProperCount (X := CMfd.of (n := n) (openPreimage T U)) (fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) ((Subtype.val : U → X) ⁻¹' E.get i)) (restrict U T)).ideal) x=
      actualDistinctProperCount (fun i : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) x.val := by
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hc : ∀ i,(F i).IsCoherent := by
    intro i
    exact (original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT).2.2.2.1.isCoherent
  have heq : (fun i : Fin E.length => GermIdeal.pullback (m := n)
      (Subtype.val : openPreimage T U → Y) (F i))=
      (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) ((Subtype.val : U → X) ⁻¹' E.get i)) (restrict U T)).ideal) := by
    funext i
    exact congrArg MarkedIdeal.ideal (original_members_chronological_open hn hW hE hdense i T hT U)
  rw [←heq]
  exact actual_distinct_proper_count_open F hc (openPreimage T U) x
end
end Hironaka.HironakaSharpActualDistinctCountOpenNaturality
