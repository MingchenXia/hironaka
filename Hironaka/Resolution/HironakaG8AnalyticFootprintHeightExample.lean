import Hironaka.Resolution.HironakaG8CountablePlaneArrangement
import Hironaka.Resolution.HironakaResolutionSpaceSingular
import Hironaka.Resolution.HironakaG8StageRankCoherence

/-! Analytic projected support data of width three can have unbounded incoming height. -/
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.HironakaG8AnalyticFootprintHeightExample

open HironakaG8CountablePlaneSheets HironakaG8CountablePlaneArrangement
  HironakaResolutionSpaceSingular AnalyticSubsetOpens HironakaG8StageRankCoherence

/-- Use only the origin in each genuine coordinate plane sheet. The
terminal footprint contains all sheet origins and each other footprint two. -/
def analyticChainFootprint : Option ℕ → Set PlaneSheets
  | none => {x | x.2 = 0}
  | some k => {x | x.2 = 0 ∧ (x.1 = k ∨ x.1 = k+1)}

theorem analyticChainFootprint_analytic (a : Option ℕ) :
    IsComplexAnalyticSubset (n := 2) (analyticChainFootprint a) := by
  have hRoot : IsComplexAnalyticSubset (n := 2) (analyticChainFootprint none) := by
    change IsComplexAnalyticSubset (n := 2) {x : PlaneSheets | x.2 = 0}
    rw [← countablePlaneArrangement_singularSet]
    exact isComplexAnalyticSubset_singularSet isComplexAnalyticSubset_countablePlaneArrangement
  cases a with
  | none => exact hRoot
  | some k =>
    apply isComplexAnalyticSubset_of_forall_opens
    intro x
    let U := arrangementSheetOpen x.1
    have hxU : x ∈ U := ⟨mem_singleton _,mem_univ _⟩
    refine ⟨U,hxU,?_⟩
    have hEq (y : U) : y.val.1 = x.1 := mem_singleton_iff.mp y.property.1
    by_cases hk : x.1 = k ∨ x.1 = k+1
    · have h : (Subtype.val : U → PlaneSheets) ⁻¹' analyticChainFootprint (some k) =
          Subtype.val ⁻¹' analyticChainFootprint none := by
        ext y
        change (y.val.2 = 0 ∧ (y.val.1 = k ∨ y.val.1 = k+1)) ↔ y.val.2 = 0
        simp only [hEq y,hk,and_true]
      rw [h]
      exact isComplexAnalyticSubset_preimage_val hRoot U
    · have h : (Subtype.val : U → PlaneSheets) ⁻¹' analyticChainFootprint (some k) = ∅ := by
        ext y
        change (y.val.2 = 0 ∧ (y.val.1 = k ∨ y.val.1 = k+1)) ↔ False
        simp only [hEq y,hk,and_false]
      rw [h]
      exact isComplexAnalyticSubset_empty

private theorem only_three_meet_sheet (k : ℕ) (a : Option ℕ) :
    (analyticChainFootprint a ∩ (arrangementSheetOpen k : Set PlaneSheets)).Nonempty →
    a ∈ ({none,some k,some (k-1)} : Finset (Option ℕ)) := by
  rintro ⟨x,hx,hxU⟩
  have hxK : x.1 = k := mem_singleton_iff.mp hxU.1
  cases a with
  | none => simp
  | some l =>
    rcases hx.2 with hl | hl
    · have he : l = k := hl.symm.trans hxK
      simp [he]
    · have he : l = k-1 := by omega
      simp [he]

/-- One whole analytic sheet meets at most three footprints. -/
theorem analyticChainFootprint_uniform_local_width (x : PlaneSheets) :
    ∃ U : Opens PlaneSheets, x ∈ U ∧ ∃ F : Finset (Option ℕ), F.card ≤ 3 ∧
      ∀ a, (analyticChainFootprint a ∩ (U : Set PlaneSheets)).Nonempty → a ∈ F := by
  refine ⟨arrangementSheetOpen x.1,⟨mem_singleton _,mem_univ _⟩,
    {none,some x.1,some (x.1-1)},?_,only_three_meet_sheet x.1⟩
  have h₁ := Finset.card_insert_le (none : Option ℕ) {some x.1,some (x.1-1)}
  have h₂ := Finset.card_insert_le (some x.1) {some (x.1-1)}
  rw [Finset.card_singleton] at h₂
  omega

theorem analyticChainFootprint_locallyFinite : LocallyFinite analyticChainFootprint := by
  intro x
  obtain ⟨U,hx,F,_,hF⟩ := analyticChainFootprint_uniform_local_width x
  exact ⟨U,U.isOpen.mem_nhds hx,F.finite_toSet.subset hF⟩

/-- A total chronological order with the terminal event last. -/
def analyticChronology (a b : Option ℕ) : Prop :=
  match a,b with
  | some k,some l => k < l
  | some _,none => True
  | _,_ => False

theorem analyticChronology_total {a b : Option ℕ} (h : a ≠ b) :
    analyticChronology a b ∨ analyticChronology b a := by
  cases a with
  | none => cases b with
    | none => contradiction
    | some k => exact Or.inr trivial
  | some k => cases b with
    | none => exact Or.inl trivial
    | some l => exact lt_or_gt_of_ne (fun hkl => h (congrArg some hkl))

theorem analyticChronology_trans {a b c : Option ℕ}
    (hab : analyticChronology a b) (hbc : analyticChronology b c) :
    analyticChronology a c := by
  cases a <;> cases b <;> cases c <;> simp_all [analyticChronology]
  omega

theorem analyticChronology_irrefl (a : Option ℕ) : ¬ analyticChronology a a := by
  cases a <;> simp [analyticChronology]

def analyticSpatialBefore (a b : Option ℕ) : Prop :=
  analyticChronology a b ∧ (analyticChainFootprint a ∩ analyticChainFootprint b).Nonempty

theorem analyticSpatialBefore_next (k : ℕ) : analyticSpatialBefore (some k) (some (k+1)) :=
  ⟨Nat.lt_succ_self k,(k+1,0),⟨rfl,Or.inr rfl⟩,⟨rfl,Or.inl rfl⟩⟩

theorem analyticSpatialBefore_terminal (k : ℕ) : analyticSpatialBefore (some k) none :=
  ⟨trivial,(k,0),⟨rfl,Or.inl rfl⟩,rfl⟩

theorem analyticSpatialBefore_wellFounded : WellFounded analyticSpatialBefore := by
  have hLeaf : ∀ k, Acc analyticSpatialBefore (some k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      apply Acc.intro
      intro a ha
      cases a with
      | none => exact ha.1.elim
      | some l => exact ih l ha.1
  constructor
  intro a
  cases a with
  | some k => exact hLeaf k
  | none =>
    apply Acc.intro
    intro a ha
    cases a with
    | none => exact ha.1.elim
    | some k => exact hLeaf k

theorem analyticSpatialBefore_unbounded_terminal_height (k : ℕ) :
    DependencyPath analyticSpatialBefore (k+1) none := by
  have hLeaf (j : ℕ) : DependencyPath analyticSpatialBefore j (some j) := by
    induction j with
    | zero => exact .nil _
    | succ j ih => exact .step (analyticSpatialBefore_next j) ih
  exact .step (analyticSpatialBefore_terminal k) (hLeaf k)

theorem no_weak_rank_analyticSpatialBefore :
    ¬ ∃ r : Option ℕ → ℕ, ∀ ⦃a b⦄, analyticSpatialBefore a b → r a < r b := by
  intro h
  obtain ⟨k,hk⟩ := (exists_natural_rank_iff _).mp h none
  exact (Nat.not_succ_le_self k) (hk _ (analyticSpatialBefore_unbounded_terminal_height k))

end Hironaka.HironakaG8AnalyticFootprintHeightExample
