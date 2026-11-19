import Hironaka.Resolution.HironakaG8SpatialDependencyBranching

/-! # Finite ancestry for well-founded dependency graphs -/
set_option autoImplicit false

namespace Hironaka.HironakaG8FiniteBranchingAncestry

open Set
open HironakaG8SpatialDependencyBranching
open BlowupTowers HironakaG3RTowerClass HironakaG8CompactEventAncestry

/-- In a well-founded dependency relation, finite immediate incoming sets
imply finite sets of all incoming ancestors. -/
theorem finite_ancestors_of_finite_incoming {ι : Type*} {before : ι → ι → Prop}
    (hWell : WellFounded before) (hFinite : ∀ b, {a | before a b}.Finite) (b : ι) :
    {a | Relation.TransGen before a b}.Finite := by
  refine hWell.induction (C := fun c => {a | Relation.TransGen before a c}.Finite) b
    fun b ih => ?_
  have hUnion := (hFinite b).biUnion
    (t := fun c => insert c {a | Relation.TransGen before a c})
    (fun c hc => (ih c hc).insert c)
  refine hUnion.subset ?_
  intro a ha
  obtain ⟨c, hac, hcb⟩ := Relation.TransGen.tail'_iff.mp ha
  refine Set.mem_iUnion₂.mpr ⟨c, hcb, ?_⟩
  rcases hac.cases_tail with rfl | ⟨d, had, hdc⟩
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ (Relation.TransGen.tail' had hdc)

/-- Counting strict ancestors assigns increasing natural stages simultaneously
along every direct or transitive dependency. -/
theorem exists_natural_rank_of_finite_incoming {ι : Type*} {before : ι → ι → Prop}
    (hWell : WellFounded before) (hFinite : ∀ b, {a | before a b}.Finite) :
    ∃ rank : ι → ℕ, ∀ ⦃a b⦄, Relation.TransGen before a b → rank a < rank b := by
  classical
  have hIrrefl (b : ι) : ¬ Relation.TransGen before b b := by
    refine hWell.induction (C := fun c => ¬ Relation.TransGen before c c) b
      fun b ih hLoop => ?_
    obtain ⟨c, hbc, hcb⟩ := Relation.TransGen.tail'_iff.mp hLoop
    exact ih c hcb (Relation.TransGen.head' hcb hbc)
  let ancestors (b : ι) := (finite_ancestors_of_finite_incoming hWell hFinite b).toFinset
  have hMem (a b : ι) : a ∈ ancestors b ↔ Relation.TransGen before a b :=
    (finite_ancestors_of_finite_incoming hWell hFinite b).mem_toFinset
  refine ⟨fun b => (ancestors b).card, fun {a b} hab => ?_⟩
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨fun c hc => ?_, fun hEq => ?_⟩
  · exact (hMem c b).mpr (((hMem c a).mp hc).trans hab)
  · have ha : a ∈ ancestors b := (hMem a b).mpr hab
    rw [← hEq] at ha
    exact hIrrefl a ((hMem a a).mp ha)

/-- For finite immediate incoming sets, well-foundedness is exactly the
condition for a natural-number clock. -/
theorem exists_natural_rank_iff_wellFounded {ι : Type*} (before : ι → ι → Prop)
    (hFinite : ∀ b, {a | before a b}.Finite) :
    (∃ rank : ι → ℕ, ∀ ⦃a b⦄, before a b → rank a < rank b) ↔ WellFounded before := by
  constructor
  · rintro ⟨rank, hr⟩
    exact (InvImage.wf rank Nat.lt_wfRel.wf).mono fun _ _ h => hr h
  · intro hWell
    obtain ⟨rank, hr⟩ := exists_natural_rank_of_finite_incoming hWell hFinite
    exact ⟨rank, fun {_ _} h => hr (.single h)⟩

/-- For locally finite physical charts, a well-founded relation whose
edges join meeting compact projected event footprints has a natural rank. -/
theorem exists_natural_rank_of_compact_spatial_dependency
    {n : ℕ} {X Z : CMfd.{0} n} {I ε : Type*}
    {K : LocalTowerClass X} {p : Z → X} (c : I → TowerChart K Z p)
    (event : ∀ i, Fin (centreFootprints (c i).T).length → ε)
    (hLF : LocallyFinite (fun i => ((c i).U : Set X)))
    (before : ε → ε → Prop) (hWell : WellFounded before)
    (hSpatial : ∀ ⦃a b⦄, before a b →
      (eventFootprint c event a ∩ eventFootprint c event b).Nonempty)
    (hCompact : ∀ b, IsCompact (eventFootprint c event b)) :
    ∃ rank : ε → ℕ, ∀ ⦃a b⦄, Relation.TransGen before a b → rank a < rank b :=
  exists_natural_rank_of_finite_incoming hWell
    (fun b => finite_incoming_of_compact_projected_events c event hLF before hSpatial b (hCompact b))

end Hironaka.HironakaG8FiniteBranchingAncestry
