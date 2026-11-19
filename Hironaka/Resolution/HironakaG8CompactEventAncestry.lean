import Hironaka.Resolution.HironakaG3RTowerClass
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Data.Set.Card

set_option autoImplicit false
open Set TopologicalSpace

namespace Hironaka.HironakaG8CompactEventAncestry

open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass

/-- Project each physical stage centre to the original base, retaining its
position in the finite history. Empty centres contribute the empty set. -/
def centreFootprints {n : ℕ} {X : CMfd.{0} n} :
    {Y : CMfd.{0} n} → BlowupTower X Y → List (Set X)
  | _, .refl => []
  | _, .step T C _ _ => centreFootprints T ++ [T.proj '' C]

/-- The support of an event records all its chart occurrences. -/
def eventFootprint {n : ℕ} {X Z : CMfd.{0} n} {I ε : Type*}
    {A : LocalTowerClass X} {P : Z → X} (c : I → TowerChart A Z P)
    (event : ∀ i, Fin (centreFootprints (c i).T).length → ε) (e : ε) : Set X :=
  {x | ∃ i j, event i j = e ∧
      x ∈ (Subtype.val : (c i).U → X) '' (centreFootprints (c i).T).get j}

/-- A compact set meets representatives of only finitely many event classes
on a locally finite physical chart family. -/
theorem finite_events_meeting_compact {n : ℕ} {X Z : CMfd.{0} n} {I ε : Type*}
    {A : LocalTowerClass X} {P : Z → X} (c : I → TowerChart A Z P)
    (event : ∀ i, Fin (centreFootprints (c i).T).length → ε)
    (hLF : LocallyFinite (fun i => ((c i).U : Set X)))
    {K : Set X} (hK : IsCompact K) :
    {e | (eventFootprint c event e ∩ K).Nonempty}.Finite := by
  let F := {i | (((c i).U : Set X) ∩ K).Nonempty}
  have hF : F.Finite := hLF.finite_nonempty_inter_compact hK
  have h : (⋃ i ∈ F, range (event i)).Finite := hF.biUnion (fun i _ => finite_range (event i))
  refine h.subset ?_
  rintro e ⟨x,⟨i,j,rfl,y,_,rfl⟩,hxK⟩
  exact mem_iUnion₂.mpr ⟨i,⟨y.val,y.property,hxK⟩,j,rfl⟩

/-- If the ancestors of each event admit representatives over a compact set,
their finite cardinalities give strict natural chronological ranks. The
compact set can depend on the terminal event. -/
theorem natural_rank_of_compactly_represented_ancestry
    {n : ℕ} {X Z : CMfd.{0} n} {I ε : Type*}
    {A : LocalTowerClass X} {P : Z → X} (c : I → TowerChart A Z P)
    (event : ∀ i, Fin (centreFootprints (c i).T).length → ε)
    (hLF : LocallyFinite (fun i => ((c i).U : Set X))) (before : ε → ε → Prop)
    (acyclic : ∀ a, ¬ Relation.TransGen before a a)
    (compactAncestors : ∀ b, ∃ K : Set X, IsCompact K ∧
      ∀ a, Relation.TransGen before a b → (eventFootprint c event a ∩ K).Nonempty) :
    ∃ r : ε → ℕ, ∀ ⦃a b⦄, before a b → r a < r b := by
  let predecessors (b : ε) := {a | Relation.TransGen before a b}
  have hFinite (b : ε) : (predecessors b).Finite := by
    obtain ⟨K,hK,hAll⟩ := compactAncestors b
    exact (finite_events_meeting_compact c event hLF hK).subset fun a ha => hAll a ha
  refine ⟨fun b => (predecessors b).ncard, ?_⟩
  intro a b hab
  have edge := Relation.TransGen.single hab
  apply Set.ncard_lt_ncard _ (hFinite b)
  exact ⟨fun _ h => h.trans edge, fun h => acyclic a (h edge)⟩

#print axioms finite_events_meeting_compact
#print axioms natural_rank_of_compactly_represented_ancestry

end Hironaka.HironakaG8CompactEventAncestry
