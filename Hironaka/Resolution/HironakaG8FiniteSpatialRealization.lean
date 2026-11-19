import Hironaka.Resolution.HironakaG8FiniteSpatialOrdering
import Hironaka.Resolution.HironakaG8IndexedDisjointSwap

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FiniteSpatialRealization

open HironakaG8FiniteSpatialOrdering HironakaG8IndexedDisjointSwap BlowupTowers

private theorem SwapAt.index_data {α : Type*} {I : α → α → Prop}
    {i : ℕ} {l m : List α} (h : SwapAt I i l m) :
    (∃ a b, l[i]? = some a ∧ l[i+1]? = some b ∧ I a b) ∧
      ∀ j, m[j]? = l[Equiv.swap i (i+1) j]? := by
  induction h with
  | @here a b s hi =>
    refine ⟨⟨a,b,rfl,rfl,hi⟩,?_⟩
    intro j
    rcases j with _ | _ | j
    · simp [Equiv.swap_apply_left]
    · simp [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      rfl
  | @later i l m a _ ih =>
    obtain ⟨⟨b,c,hb,hc,hI⟩,hπ⟩ := ih
    refine ⟨⟨b,c,hb,hc,hI⟩,?_⟩
    intro j
    cases j with
    | zero =>
      rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      rfl
    | succ j =>
      simp only [List.getElem?_cons_succ]
      rw [hπ]
      have he : (Equiv.swap i (i+1) j)+1 = Equiv.swap (i+1) (i+1+1) (j+1) := by
        by_cases h0 : j = i
        · subst j
          rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
        by_cases h1 : j = i+1
        · subst j
          rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
        rw [Equiv.swap_apply_of_ne_of_ne h0 h1,
          Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      rw [← he]
      rfl

variable {n : ℕ} {B : CMfd.{0} n}

private theorem SwapWord.index_certificate {A : ℕ → Set B} (U : Opens B)
    {w : List ℕ} {l m : List ℕ}
    (h : SwapWord (fun i j => (A j).Nonempty ∧ Disjoint (A i) (A j) ∧
      (Disjoint (U : Set B) (A i) ∨ Disjoint (U : Set B) (A j))) w l m)
    (σ : ℕ ≃ ℕ) (hl : ∀ j a, l[j]? = some a → σ j = a) :
    IsDisjointSwapWord A σ w ∧ OpenAvoidsSwapPairs U A σ w ∧
      ∀ j a, m[j]? = some a → reordering σ w j = a := by
  induction h generalizing σ with
  | nil => exact ⟨trivial,trivial,hl⟩
  | @cons i w l m t h _ ih =>
    obtain ⟨⟨a,b,ha,hb,hDisj⟩,hπ⟩ := SwapAt.index_data h
    let σ' := (Equiv.swap i (i+1)).trans σ
    have hm (j b : ℕ) (hj : m[j]? = some b) : σ' j = b :=
      hl _ _ ((hπ j).symm.trans hj)
    obtain ⟨hWord,hAvoid,hTgt⟩ := ih σ' hm
    refine ⟨⟨?_,?_,hWord⟩,⟨?_,hAvoid⟩,hTgt⟩
    · rw [hl _ _ hb]
      exact hDisj.1
    · rw [hl _ _ ha,hl _ _ hb]
      exact hDisj.2.1
    · rw [hl _ _ ha,hl _ _ hb]
      exact hDisj.2.2

private theorem exists_word_of_target_rank (A : ℕ → Set B) (N : ℕ)
    (U : Opens B) (target : List ℕ) (rank : ℕ → ℕ)
    (hPerm : (List.range N).Perm target) (hOcc : ∀ i < N, (A i).Nonempty)
    (hPreserve : ∀ i j : ℕ, i < j → j < N →
      ((A i ∩ A j).Nonempty ∨
        ((U : Set B) ∩ A i).Nonempty ∧ ((U : Set B) ∩ A j).Nonempty) → rank i < rank j)
    (hTarget : target.Pairwise (fun i j => rank i < rank j)) :
    ∃ w, IsDisjointSwapWord A (Equiv.refl ℕ) w ∧ OpenAvoidsSwapPairs U A (Equiv.refl ℕ) w ∧
      ∀ j a, target[j]? = some a → reordering (Equiv.refl ℕ) w j = a := by
  classical
  have hSource : (List.range N).Pairwise
      (fun i j => ((A j).Nonempty ∧ Disjoint (A i) (A j) ∧
        (Disjoint (U : Set B) (A i) ∨ Disjoint (U : Set B) (A j))) ∨ rank i < rank j) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j _ hj hij
    simp only [List.getElem_range]
    have hjN : j < N := by simpa using hj
    by_cases hd : Disjoint (A i) (A j)
    · by_cases hOpen : Disjoint (U : Set B) (A i) ∨ Disjoint (U : Set B) (A j)
      · exact Or.inl ⟨hOcc j hjN,hd,hOpen⟩
      · push Not at hOpen
        exact Or.inr (hPreserve i j hij hjN (Or.inr
          ⟨Set.not_disjoint_iff_nonempty_inter.mp hOpen.1,
            Set.not_disjoint_iff_nonempty_inter.mp hOpen.2⟩))
    · exact Or.inr (hPreserve i j hij hjN (Or.inl (Set.not_disjoint_iff_nonempty_inter.mp hd)))
  obtain ⟨w,hw⟩ := exists_swap_word_of_preserved_order rank hPerm hSource hTarget
  refine ⟨w,SwapWord.index_certificate U hw (Equiv.refl ℕ) ?_⟩
  intro j a ha
  obtain ⟨_,hr⟩ := List.getElem?_eq_some_iff.mp ha
  simpa using hr

/-- An all-occupied finite source range with target order preserved on
intersecting footprints supplies the exact operational swap certificate. -/
theorem exists_disjoint_swap_word_of_target_order (A : ℕ → Set B) (N : ℕ)
    (target : List ℕ) (rank : ℕ → ℕ)
    (hPerm : (List.range N).Perm target) (hOcc : ∀ i < N, (A i).Nonempty)
    (hPreserve : ∀ i j : ℕ, i < j → j < N → (A i ∩ A j).Nonempty → rank i < rank j)
    (hTarget : target.Pairwise (fun i j => rank i < rank j)) :
    ∃ w, IsDisjointSwapWord A (Equiv.refl ℕ) w ∧
      ∀ j a, target[j]? = some a → reordering (Equiv.refl ℕ) w j = a := by
  obtain ⟨w,hw,_,hh⟩ := exists_word_of_target_rank A N ⊥ target rank hPerm hOcc
    (fun i j hij hj h => hPreserve i j hij hj (by simpa using h)) hTarget
  exact ⟨w,hw,hh⟩

/-- A target that preserves intersecting pairs and pairs visible in the
open has a disjoint swap word that also avoids swapping two visible events. -/
theorem exists_disjoint_swap_word_of_visible_order (A : ℕ → Set B) (N : ℕ)
    (U : Opens B) (target : List ℕ) (hPerm : (List.range N).Perm target)
    (hOcc : ∀ i < N, (A i).Nonempty)
    (hPreserve : ∀ i j : ℕ, i < j → j < N →
      ((A i ∩ A j).Nonempty ∨
        ((U : Set B) ∩ A i).Nonempty ∧ ((U : Set B) ∩ A j).Nonempty) →
      target.idxOf i < target.idxOf j) :
    ∃ w, IsDisjointSwapWord A (Equiv.refl ℕ) w ∧ OpenAvoidsSwapPairs U A (Equiv.refl ℕ) w ∧
      ∀ j a, target[j]? = some a → reordering (Equiv.refl ℕ) w j = a := by
  apply exists_word_of_target_rank A N U target target.idxOf hPerm hOcc hPreserve
  have hNodup := hPerm.nodup_iff.mp List.nodup_range
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  rw [hNodup.idxOf_getElem i hi, hNodup.idxOf_getElem j hj]
  exact hij

/-- The target list itself supplies the rank, so preservation of its
intersecting pairs is the only ordering premise. -/
theorem exists_disjoint_swap_word_of_intersection_order (A : ℕ → Set B) (N : ℕ)
    (target : List ℕ) (hPerm : (List.range N).Perm target)
    (hOcc : ∀ i < N, (A i).Nonempty)
    (hPreserve : ∀ i j : ℕ, i < j → j < N → (A i ∩ A j).Nonempty →
      target.idxOf i < target.idxOf j) :
    ∃ w, IsDisjointSwapWord A (Equiv.refl ℕ) w ∧
      ∀ j a, target[j]? = some a → reordering (Equiv.refl ℕ) w j = a := by
  obtain ⟨w,hw,_,hh⟩ := exists_disjoint_swap_word_of_visible_order A N ⊥ target hPerm hOcc
    (fun i j hij hj h => hPreserve i j hij hj (by simpa using h))
  exact ⟨w,hw,hh⟩

open Hironaka.BlowupSequences BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8OccupiedSlotComparison HironakaG8FirstFootprintOrder

/-- A target list preserving intersecting footprints is realized by an
actual original TEST tower with exactly the listed occupied slots. -/
theorem realize_target_intersection_order {F : CMfd.{0} n}
    (T : BlowupTower B F) (target : List ℕ) (hPerm : (List.range T.length).Perm target)
    (hOcc : ∀ i < T.length, (slotFootprint T i).Nonempty)
    (hPreserve : ∀ i j : ℕ, i < j → j < T.length →
      (slotFootprint T i ∩ slotFootprint T j).Nonempty → target.idxOf i < target.idxOf j)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      (∀ j a, target[j]? = some a → slotFootprint R j = slotFootprint T a) ∧
      ∀ j, (slotFootprint R j).Nonempty ↔ j < target.length := by
  obtain ⟨w,hw,hOrder⟩ := exists_disjoint_swap_word_of_intersection_order
    (slotFootprint T) T.length target hPerm hOcc hPreserve
  obtain ⟨G,R,e,hR,hProj,hStages,hFoot⟩ :=
    realize_disjoint_swap_word T w hw W M hM hN hTest hStage
  let σ := reordering (Equiv.refl ℕ) w
  have hListed j a (h : target[j]? = some a) : slotFootprint R j = slotFootprint T a :=
    (hFoot j).trans (congrArg (slotFootprint T) (hOrder j a h))
  refine ⟨G,R,e,hR,hProj,hStages,hListed,?_⟩
  intro j
  constructor
  · rintro ⟨x,hx⟩
    have hxT : x ∈ slotFootprint T (σ j) := (hFoot j) ▸ hx
    have ha : σ j ∈ target := hPerm.mem_iff.mp (List.mem_range.mpr (hit_slot_lt_length T hxT))
    let k := target.idxOf (σ j)
    have hk : k < target.length := List.idxOf_lt_length_iff.mpr ha
    have hka : target[k]? = some (σ j) := List.getElem?_idxOf ha
    have he : σ k = σ j := hOrder k (σ j) hka
    rwa [σ.injective he] at hk
  · intro hj
    have hGet : target[j]? = some target[j] := List.getElem?_eq_getElem hj
    rw [hListed j _ hGet]
    have hMem : target[j] ∈ target := List.getElem_mem hj
    exact hOcc _ (List.mem_range.mp (hPerm.mem_iff.mpr hMem))

open G3UniverseEmptyAwareCore

/-- Reorder one actual finite TEST tower while preserving its literal
restricted history up to empty-aware comparison on the visible open. -/
theorem realize_target_visible_order {F : CMfd.{0} n}
    (T : BlowupTower B F) (U : Opens B) (target : List ℕ)
    (hPerm : (List.range T.length).Perm target)
    (hOcc : ∀ i < T.length, (slotFootprint T i).Nonempty)
    (hPreserve : ∀ i j : ℕ, i < j → j < T.length →
      ((slotFootprint T i ∩ slotFootprint T j).Nonempty ∨
        ((U : Set B) ∩ slotFootprint T i).Nonempty ∧
          ((U : Set B) ∩ slotFootprint T j).Nonempty) → target.idxOf i < target.idxOf j)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      (∀ j a, target[j]? = some a → slotFootprint R j = slotFootprint T a) ∧
      ∃ χ : CMfd.of (n := n) (openPreimage T U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
        (∀ z, (χ z).val = e z.val) ∧
        EmptyAwareTowerIso
          (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
          (restrict U T) (restrict U R) χ := by
  obtain ⟨w,hw,hAvoid,hOrder⟩ := exists_disjoint_swap_word_of_visible_order
    (slotFootprint T) T.length U target hPerm hOcc hPreserve
  obtain ⟨G,R,e,hR,hProj,hStages,hFoot,hRead⟩ :=
    realize_disjoint_swap_word_with_readback T w hw W M hM hN hTest hStage
  exact ⟨G,R,e,hR,hProj,hStages,
    fun j a ha => (hFoot j).trans (congrArg (slotFootprint T) (hOrder j a ha)),hRead U hAvoid⟩

end Hironaka.HironakaG8FiniteSpatialRealization

#print axioms Hironaka.HironakaG8FiniteSpatialRealization.exists_disjoint_swap_word_of_target_order

#print axioms Hironaka.HironakaG8FiniteSpatialRealization.exists_disjoint_swap_word_of_intersection_order

#print axioms Hironaka.HironakaG8FiniteSpatialRealization.realize_target_intersection_order

#print axioms Hironaka.HironakaG8FiniteSpatialRealization.realize_target_visible_order
