import Hironaka.Resolution.HironakaG8RankedEmptyPadding
import Hironaka.Resolution.HironakaG8OccupiedSlotComparison

/-! Reading a natural occurrence rank on literal physical towers. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8RankOccupiedAnnotation
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG8RankedEmptyPadding HironakaG8OccupiedSlotComparison
  HironakaG8CofinalOccupiedAncestry HironakaG3EmptyAwareHistory BlowupTowerIsomorphism
  HironakaG3RTowerClass

variable {n : ℕ} {X Y A B : CMfd.{0} n}

/-- The assigned slot of a raw physical step of a decorated tower. -/
def assignedSlot : {Y : CMfd.{0} n} → {T : BlowupTower X Y} → {k : ℕ} →
    RankedTower X T k → ℕ → ℕ
  | _,_,_,.refl,_ => 0
  | _,_,_,@RankedTower.step _ _ _ _ T _ r D _ _ _ _,i =>
    if i = T.length then r else assignedSlot D i

theorem assignedSlot_restrict (U : Opens X) {T : BlowupTower X Y} {k : ℕ}
    (D : RankedTower X T k) (i : ℕ) :
    assignedSlot (D.restrict U) i = assignedSlot D i := by
  induction D with
  | refl => rfl
  | step D h hπ ih => simp only [RankedTower.restrict,assignedSlot,length_restrict,ih]

/-- Increasing assignments on the literal finite slot list construct the
actual padding decoration. The terminal clock is bounded by any common cap. -/
theorem exists_rankedTower_of_strictMono_slots (T : BlowupTower X Y)
    (rank : Fin T.length → ℕ) (hRank : StrictMono rank) (N : ℕ) (hN : ∀ i, rank i < N) :
    ∃ k, k ≤ N ∧ ∃ D : RankedTower X T k, ∀ i : Fin T.length, assignedSlot D i.val = rank i := by
  induction T generalizing N with
  | refl => exact ⟨0,Nat.zero_le _,.refl,fun i => Fin.elim0 i⟩
  | @step V W T C π hπ ih =>
    let r : ℕ := rank ⟨T.length,Nat.lt_succ_self _⟩
    let f (i : Fin T.length) : Fin (T.length+1) := ⟨i.val,Nat.lt_succ_of_lt i.isLt⟩
    have hf : StrictMono f := fun _ _ h => h
    have hLower (i : Fin T.length) : rank (f i) < r := hRank i.isLt
    obtain ⟨k,hk,D,hD⟩ := ih (rank ∘ f) (hRank.comp hf) r hLower
    refine ⟨r+1,Nat.succ_le_of_lt (hN _),.step D hk hπ,?_⟩
    intro i
    change (if i.val = T.length then r else assignedSlot D i.val) = rank i
    by_cases hi : i.val = T.length
    · rw [if_pos hi]
      exact congrArg rank (Fin.ext hi.symm)
    · rw [if_neg hi]
      have hp : i.val < T.length := by
        have h := i.isLt
        change i.val < T.length+1 at h
        omega
      exact hD ⟨i.val,hp⟩

/-- In an empty-free actual source tower, an increasing rank on occupied
events directly constructs its literal padding decoration. -/
theorem exists_rankedTower_of_occupied_ranks (T : BlowupTower X Y)
    (hOcc : ∀ i : Fin T.length, Occupied T i.val)
    (rank : {i // Occupied T i} → ℕ) (hRank : StrictMono rank) :
    ∃ k, ∃ D : RankedTower X T k, ∀ i : {i // Occupied T i}, assignedSlot D i.val = rank i := by
  let f (i : Fin T.length) : {i // Occupied T i} := ⟨i.val,hOcc i⟩
  have hf : StrictMono f := fun _ _ h => h
  let N := (Finset.univ.image (rank ∘ f)).sup id + 1
  have hN (i : Fin T.length) : (rank ∘ f) i < N := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  obtain ⟨k,_,D,hD⟩ := exists_rankedTower_of_strictMono_slots T (rank ∘ f) (hRank.comp hf) N hN
  refine ⟨k,D,fun i => ?_⟩
  exact hD ⟨i.val,occupied_lt_length T i.property⟩

/-- Assigned ranks in chronological order, with all empty steps ignored. -/
def occupiedRanks {T : BlowupTower X Y} {k : ℕ} (D : RankedTower X T k) : List ℕ :=
  (occupiedSlots T).map (assignedSlot D)

private theorem occupiedRanks_step {V : CMfd.{0} n} {T : BlowupTower X Y}
    {C : Set Y} {π : V → Y} {i r : ℕ} (D : RankedTower X T i)
    (h : i ≤ r) (hπ : IsBlowupAlong n C π) :
    occupiedRanks (.step D h hπ) = occupiedRanks D ++ if C.Nonempty then [r] else [] := by
  have hMap : (occupiedSlots T).map (assignedSlot (.step D h hπ)) =
      (occupiedSlots T).map (assignedSlot D) := by
    apply List.map_congr_left
    intro k hk
    have hk' := occupied_lt_length T ((mem_occupiedSlots T k).mp hk)
    simp [assignedSlot,Nat.ne_of_lt hk']
  unfold occupiedRanks
  rw [occupiedSlots,List.map_append,hMap]
  by_cases hc : C.Nonempty <;> simp [hc,assignedSlot]

/-- A physical empty-aware comparison needs only equality of the
chronological occupied rank lists. This constructs its rank annotation. -/
theorem occupiedComparison_of_eq_occupiedRanks
    {T : BlowupTower X Y} {S : BlowupTower A B}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    (h : EmptyAwareTowerIso φ T S ψ) :
    ∀ {i j : ℕ} (D : RankedTower X T i) (F : RankedTower A S j),
      occupiedRanks D = occupiedRanks F → OccupiedComparison φ D F ψ := by
  induction h with
  | refl =>
    intro i j D F _
    cases D
    cases F
    exact .refl
  | @step Y B Z W T S ψ h C π hπ K ρ hρ χ hMap hC ih =>
    intro i j D F hEq
    cases D with
    | @step _ _ _ i r D hD _ _ _ =>
      cases F with
      | @step _ _ _ j s F hF _ _ _ =>
        have he : C.Nonempty ↔ K.Nonempty := by
          rw [← hC]
          exact ψ.surjective.nonempty_preimage
        rw [occupiedRanks_step,occupiedRanks_step] at hEq
        by_cases hOcc : C.Nonempty
        · simp only [if_pos hOcc,if_pos (he.mp hOcc)] at hEq
          have hr := List.append_inj hEq (by simpa using congrArg List.length hEq)
          have hSlots : r = s := by simpa using hr.2
          exact .pair (ih D F hr.1) hD hF hπ hρ χ hMap hC (fun _ => hSlots)
        · simp only [if_neg hOcc,if_neg ((not_congr he).mp hOcc),List.append_nil] at hEq
          exact .pair (ih D F hEq) hD hF hπ hρ χ hMap hC (fun hn => (hOcc hn).elim)
  | @leftEmpty Y B Z T S ψ h ρ hρ e he ih =>
    intro i j D F hEq
    cases D with
    | @step _ _ _ i r D hD _ _ _ =>
      rw [occupiedRanks_step] at hEq
      exact .left (ih D F (by simpa using hEq)) hD hρ e he
  | @rightEmpty Y B W T S ψ h ρ hρ e he ih =>
    intro i j D F hEq
    cases F with
    | @step _ _ _ j r F hF _ _ _ =>
      rw [occupiedRanks_step] at hEq
      exact .right (ih D F (by simpa using hEq)) hF hρ e he


/-- Agreeing on the canonical physical occupied matches suffices to
construct the exact rank-annotated comparison without annotating empties. -/
theorem occupiedComparison_of_agreeing_occupied_slots
    {T : BlowupTower X Y} {S : BlowupTower A B}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    (h : EmptyAwareTowerIso φ T S ψ)
    {i j : ℕ} (D : RankedTower X T i) (F : RankedTower A S j)
    (hRank : ∀ p : {k // Occupied T k},
      assignedSlot D p.val = assignedSlot F (occupiedComparison h p).val) :
    OccupiedComparison φ D F ψ := by
  apply occupiedComparison_of_eq_occupiedRanks h D F
  have hLen : (occupiedSlots T).length = (occupiedSlots S).length := by
    rw [occupiedSlots_length,occupiedSlots_length,occupiedCount_emptyAware h]
  unfold occupiedRanks
  apply List.ext_getElem (by simp only [List.length_map,hLen])
  intro k hkT hkS
  rw [List.getElem_map,List.getElem_map]
  let p := occupiedOrdinalIso T ⟨k,by simpa only [List.length_map] using hkT⟩
  have hj : occupiedComparison h p =
      occupiedOrdinalIso S ⟨k,by simpa only [List.length_map] using hkS⟩ := by
    simp [occupiedComparison,p]
  have hh := hRank p
  rw [hj] at hh
  exact hh

/-- The consumer for strict padded comparisons. Original-chart ranks
restrict unchanged, so agreement on the occupied overlap means no
separate rank annotation on either restricted tower is an input. -/
theorem strict_padded_overlap_of_agreeing_occupied_slots
    {T : BlowupTower X Y} {S : BlowupTower A B}
    {i j : ℕ} (D : RankedTower X T i) (F : RankedTower A S j)
    (U : Opens X) (V : Opens A)
    {φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V}
    {ψ : CMfd.of (n := n) (openPreimage T U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S V)}
    (h : EmptyAwareTowerIso φ (restrict U T) (restrict V S) ψ)
    (hRank : ∀ p : {k // Occupied (restrict U T) k},
      assignedSlot D p.val = assignedSlot F (occupiedComparison h p).val)
    (N : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    ∃ χ : CMfd.of (n := n) (openPreimage (D.through N) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (F.through N) V),
      IsTowerIso φ (restrict U (D.through N)) (restrict V (F.through N)) χ := by
  have hAnno : OccupiedComparison φ (D.restrict U) (F.restrict V) ψ :=
    occupiedComparison_of_agreeing_occupied_slots h _ _ (fun p => by
      rw [assignedSlot_restrict,assignedSlot_restrict]
      exact hRank p)
  obtain ⟨χ,hχ,_⟩ := strict_overlap_of_ranked_occupied_comparison D F U V φ ψ hAnno N hi hj
  exact ⟨χ,hχ⟩


/-- A full earlier chart compares strictly to a literal restriction of
the padded later chart from agreement on the occupied lift. -/
theorem strict_padded_nested_overlap_of_agreeing_occupied_slots
    {T : BlowupTower X Y} {S : BlowupTower A B}
    {i j : ℕ} (D : RankedTower X T i) (F : RankedTower A S j)
    (V : Opens A)
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S V)}
    (h : EmptyAwareTowerIso φ T (restrict V S) ψ)
    (hRank : ∀ p : {k // Occupied T k},
      assignedSlot D p.val = assignedSlot F (occupiedLiftOnOpen V S h p).val)
    (N : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    ∃ χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (F.through N) V),
      IsTowerIso φ (D.through N) (restrict V (F.through N)) χ := by
  have hAnno : OccupiedComparison φ D (F.restrict V) ψ :=
    occupiedComparison_of_agreeing_occupied_slots h _ _ (fun p => by
      rw [assignedSlot_restrict]
      exact hRank p)
  have hc := (hAnno.isTowerIso_through N hi hj).trans (F.restrict_through_iso V N).symm
  exact ⟨_,BlowupTowerSplitIso.IsTowerIso.congr_base hc (Φ' := φ) (fun _ => rfl)⟩


/-- Finite predecessors of the actual cofinal events produce decorations
of every empty-free chart. Each occupied slot has exactly its event rank. -/
theorem exists_decorations_of_finite_predecessors
    {P : B → X} {K : LocalTowerClass X} {c : ℕ → TowerChart K B P}
    {ι : Type*} (E : CofinalEvents c ι)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hFinite : ∀ a, {b | E.Before b a}.Finite)
    (hOcc : ∀ i (p : Fin (c i).T.length), Occupied (c i).T p.val) :
    ∃ rank : ι → ℕ,
      (∀ ⦃a b⦄, E.Before a b → rank a < rank b) ∧
      ∀ i, ∃ k, ∃ D : RankedTower (CMfd.of (n := n) (c i).U) (c i).T k,
        ∀ p : {k // Occupied (c i).T k}, assignedSlot D p.val = rank (E.event i p) := by
  obtain ⟨rank,hRank⟩ := (E.exists_rank_iff_finite_predecessors hOccurs).mpr hFinite
  refine ⟨rank,hRank,fun i => ?_⟩
  exact exists_rankedTower_of_occupied_ranks (c i).T (hOcc i) (rank ∘ E.event i)
    (fun p q hpq => hRank ((E.before_iff_slot_lt i p q).mpr hpq))


end
end Hironaka.HironakaG8RankOccupiedAnnotation
