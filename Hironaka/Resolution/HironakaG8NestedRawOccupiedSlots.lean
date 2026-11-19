import Hironaka.Resolution.HironakaG8CofinalOccupiedAncestry
import Hironaka.Resolution.HironakaG8CompactEventAncestry
import Mathlib.Data.List.GetD

/-! # Literal raw projected slots on nested open restrictions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NestedRawOccupiedSlots

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerIsomorphism HironakaG3RTowerClass
  HironakaG8CofinalOccupiedAncestry HironakaG8CompactEventAncestry MaxLocusLocal

variable {n : ℕ} {X Y : CMfd.{0} n}

theorem centreFootprints_length (T : BlowupTower X Y) :
    (centreFootprints T).length = T.length := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    simp [centreFootprints,BlowupTower.length_step,ih]

/-- Literal restriction keeps every projected raw stage in its original
position. An erased centre is represented by its empty trace. -/
theorem centreFootprints_restrict (U : Opens X) (T : BlowupTower X Y) :
    centreFootprints (restrict U T) =
      (centreFootprints T).map ((Subtype.val : U → X) ⁻¹' ·) := by
  induction T with
  | refl => rfl
  | @step Y Z T C π hπ ih =>
    change centreFootprints (restrict U T) ++
      [(restrict U T).proj '' ((Subtype.val : openPreimage T U → Y) ⁻¹' C)] =
      (centreFootprints T ++ [T.proj '' C]).map ((Subtype.val : U → X) ⁻¹' ·)
    rw [List.map_append,ih]
    congr 1
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.val,hy,(proj_restrict U T y).symm⟩
    · rintro ⟨y,hy,h⟩
      have hyU : T.proj y ∈ U := h.symm ▸ x.property
      refine ⟨⟨y,hyU⟩,hy,Subtype.ext ?_⟩
      exact (proj_restrict U T ⟨y,hyU⟩).trans h

/-- A raw footprint lookup also handles out-of-range indices by the empty set. -/
def projectedSlot (T : BlowupTower X Y) (i : ℕ) : Set X :=
  (centreFootprints T).getD i ∅

theorem projectedSlot_restrict (U : Opens X) (T : BlowupTower X Y) (i : ℕ) :
    projectedSlot (restrict U T) i = (Subtype.val : U → X) ⁻¹' projectedSlot T i := by
  unfold projectedSlot
  rw [centreFootprints_restrict U T]
  simpa only [preimage_empty] using
    (List.getD_map (l := centreFootprints T) (d := (∅ : Set X)) (n := i)
      (fun F => (Subtype.val : U → X) ⁻¹' F))

/-- A slot is genuinely occupied exactly when its projected footprint
has a point, even if earlier raw slots are empty. -/
theorem occupied_iff_projectedSlot_nonempty (T : BlowupTower X Y) (i : ℕ) :
    Occupied T i ↔ (projectedSlot T i).Nonempty := by
  induction T with
  | refl => exact iff_of_false id (fun h => Set.not_nonempty_empty h)
  | @step Y Z T C π hπ ih =>
    change (Occupied T i ∨ (i = T.length ∧ C.Nonempty)) ↔
      ((centreFootprints T ++ [T.proj '' C]).getD i ∅).Nonempty
    by_cases h : i < T.length
    · rw [List.getD_append _ _ _ _ (by rwa [centreFootprints_length])]
      simp only [Nat.ne_of_lt h, false_and, or_false]
      exact ih
    · have hLen : (centreFootprints T).length ≤ i := by rw [centreFootprints_length]; omega
      rw [List.getD_append_right _ _ _ _ hLen,centreFootprints_length]
      have hOld : ¬ Occupied T i := fun hi => h (occupied_lt_length T hi)
      simp only [hOld,false_or]
      rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt h) with he | hl
      · subst i
        simp
      · have hPos : 1 ≤ i-T.length := by omega
        rw [List.getD_eq_default _ _ (show [T.proj '' C].length ≤ i-T.length from hPos)]
        exact iff_of_false (fun hh => (Nat.ne_of_gt hl) hh.1) Set.not_nonempty_empty

/-- The complete footprint list on a double restriction is the trace of
the smaller direct restriction, with the same raw slots under the
canonical nested-base map. -/
theorem centreFootprints_nested (U V : Opens X) (hUV : U ≤ V) (T : BlowupTower X Y) :
    centreFootprints (restrict (nestedOpens V U) (restrict V T)) =
      (centreFootprints (restrict U T)).map ((nestedOpensDiffeo (n := n) hUV) ⁻¹' ·) := by
  rw [centreFootprints_restrict,centreFootprints_restrict,centreFootprints_restrict,
    List.map_map,List.map_map]
  rfl

/-- For three nested opens, the three successive footprint traces are
exactly the smallest trace pulled back by the composite inclusion.
This includes empty and out-of-range slots. -/
theorem projectedSlot_triple_nested (U V W : Opens X) (hUV : U ≤ V) (hVW : V ≤ W)
    (T : BlowupTower X Y) (i : ℕ) :
    let V' := nestedOpens W V
    let U' := nestedOpens W U
    let U'' := nestedOpens V' U'
    let h : U' ≤ V' := fun _ hz => hUV hz
    let e := (nestedOpensDiffeo (n := n) h).trans (nestedOpensDiffeo (n := n) (hUV.trans hVW))
    projectedSlot (restrict U'' (restrict V' (restrict W T))) i =
      e ⁻¹' projectedSlot (restrict U T) i := by
  intro V' U' U'' e
  rw [projectedSlot_restrict,projectedSlot_restrict,projectedSlot_restrict,projectedSlot_restrict]
  rfl

/-- A visible occupied event on a smaller open lifts to its same raw slot
on the larger open. No alignment of independently chosen towers enters. -/
def nestedOccupiedSlotLift {U V : Opens X} (hUV : U ≤ V) (T : BlowupTower X Y) :
    {i : ℕ // Occupied (restrict U T) i} → {i : ℕ // Occupied (restrict V T) i} := by
  intro i
  refine ⟨i.val,(occupied_iff_projectedSlot_nonempty _ _).mpr ?_⟩
  obtain ⟨x,hx⟩ := (occupied_iff_projectedSlot_nonempty _ _).mp i.property
  rw [projectedSlot_restrict] at hx ⊢
  exact ⟨⟨x.val,hUV x.property⟩,hx⟩

theorem nestedOccupiedSlotLift_comp {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W)
    (T : BlowupTower X Y) :
    nestedOccupiedSlotLift hVW T ∘ nestedOccupiedSlotLift hUV T =
      nestedOccupiedSlotLift (hUV.trans hVW) T := by
  funext i
  exact Subtype.ext rfl

theorem nestedOccupiedSlotLift_strictMono {U V : Opens X} (hUV : U ≤ V)
    (T : BlowupTower X Y) : StrictMono (nestedOccupiedSlotLift hUV T) :=
  fun _ _ h => h

theorem nestedOccupiedSlotLift_unique {U V : Opens X} (hUV : U ≤ V)
    (T : BlowupTower X Y)
    (f : {i : ℕ // Occupied (restrict U T) i} → {i : ℕ // Occupied (restrict V T) i})
    (hf : ∀ i, (f i).val = i.val) :
    f = nestedOccupiedSlotLift hUV T := by
  funext i
  exact Subtype.ext (hf i)

/-- A strict physical tower isomorphism transports every original raw
footprint at the same index, including empty slots. -/
theorem centreFootprints_of_strict_towerIso {X' Y' : CMfd.{0} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso φ T' T χ) :
    centreFootprints T' = (centreFootprints T).map (φ ⁻¹' ·) := by
  induction h with
  | refl => rfl
  | @step Y' Y Z' Z T' T e h C' π' hπ' C π hπ χ hc hCentre ih =>
    change centreFootprints T' ++ [T'.proj '' C'] =
      (centreFootprints T ++ [T.proj '' C]).map (φ ⁻¹' ·)
    rw [List.map_append,ih]
    congr 1
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨e y,?_,(h.proj_comm y).symm⟩
      change y ∈ e ⁻¹' C
      rwa [hCentre]
    · rintro ⟨y,hy,he⟩
      refine ⟨e.symm y,?_,φ.injective ?_⟩
      · rw [← hCentre]
        change e (e.symm y) ∈ C
        rwa [e.apply_symm_apply]
      · change φ (T'.proj (e.symm y)) = φ x
        rw [h.proj_comm,e.apply_symm_apply]
        exact he

theorem occupied_iff_of_strict_towerIso {X' Y' : CMfd.{0} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso φ T' T χ) (i : ℕ) :
    Occupied T' i ↔ Occupied T i := by
  rw [occupied_iff_projectedSlot_nonempty,occupied_iff_projectedSlot_nonempty]
  unfold projectedSlot
  rw [centreFootprints_of_strict_towerIso h]
  have hMap := List.getD_map (l := centreFootprints T) (d := (∅ : Set X)) (n := i)
    (fun F => φ ⁻¹' F)
  rw [preimage_empty] at hMap
  rw [hMap]
  exact φ.surjective.nonempty_preimage

/-- A genuine head retains exactly the same footprint at every raw slot
that survives the cut. -/
theorem projectedSlot_head (T : BlowupTower X Y) (j i : ℕ)
    (hi : i < (head T j).length) :
    projectedSlot (head T j) i = projectedSlot T i := by
  induction T generalizing j with
  | refl =>
    cases j <;> rfl
  | @step Y Z T C π hπ ih =>
    cases j with
    | zero => rfl
    | succ j =>
      change i < (head T j).length at hi
      have hLen : (head T j).length ≤ T.length := by rw [length_head]; omega
      rw [show head (.step T C π hπ) (j+1) = head T j from rfl,ih j hi]
      unfold projectedSlot
      rw [centreFootprints, List.getD_append _ _ _ _ (by rw [centreFootprints_length]; omega)]

theorem occupied_of_head (T : BlowupTower X Y) (j i : ℕ)
    (h : Occupied (head T j) i) : Occupied T i := by
  have hi := occupied_lt_length (head T j) h
  rw [occupied_iff_projectedSlot_nonempty] at h ⊢
  rwa [projectedSlot_head T j i hi] at h

/-- Under a strict comparison to a genuine larger head, each kept
chart occurrence has exactly the trace of its larger raw footprint
under the canonical inclusion of the nested bases. -/
theorem projectedSlot_of_strict_nested_head
    (U V : Opens X) (hUV : U ≤ V) {Z D : CMfd.{0} n}
    (S : BlowupTower (CMfd.of (n := n) U) Z)
    (T : BlowupTower (CMfd.of (n := n) V) D) (cut i : ℕ) (hi : i < S.length)
    {χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (head T cut) (nestedOpens V U))}
    (h : IsTowerIso (nestedOpensDiffeo (n := n) hUV).symm S
      (restrict (nestedOpens V U) (head T cut)) χ) :
    projectedSlot S i = (fun x : U => (⟨x.val,hUV x.property⟩ : V)) ⁻¹' projectedSlot T i := by
  have hLen := h.length_eq
  rw [length_restrict] at hLen
  have hSmall : i < (head T cut).length := hLen ▸ hi
  let φ := (nestedOpensDiffeo (n := n) hUV).symm
  have hMap := List.getD_map
    (l := centreFootprints (restrict (nestedOpens V U) (head T cut)))
    (d := (∅ : Set (nestedOpens V U))) (n := i) (fun F => φ ⁻¹' F)
  rw [preimage_empty] at hMap
  have hFoot : projectedSlot S i =
      φ ⁻¹' projectedSlot (restrict (nestedOpens V U) (head T cut)) i := by
    unfold projectedSlot
    rw [centreFootprints_of_strict_towerIso h]
    exact hMap
  rw [hFoot,projectedSlot_restrict,projectedSlot_head T cut i hSmall]
  rfl

/-- A nested sequence of actual charts comes with coherent cofinal
occupied slot lifts whenever the supplied physical comparisons identify
each earlier tower with the literal restriction of an actual larger head
by strict tower isomorphisms. The event identifier is the unchanged raw slot number. -/
def cofinalEvents_of_strict_nested_restrictions
    {Z : CMfd.{0} n} {K : LocalTowerClass X} {p : Z → X}
    (c : ℕ → TowerChart K Z p) (hNest : ∀ ⦃i j⦄, i ≤ j → (c i).U ≤ (c j).U)
    (hIso : ∀ ⦃i j⦄ (h : i ≤ j),
      ∃ cut : ℕ, ∃ χ, IsTowerIso (nestedOpensDiffeo (n := n) (hNest h)).symm (c i).T
        (restrict (nestedOpens (c j).U (c i).U) (head (c j).T cut)) χ) :
    CofinalEvents c ℕ where
  event _ k := k.val
  injective _ := Subtype.val_injective
  lift := by
    intro i j h k
    refine ⟨k.val,?_⟩
    obtain ⟨cut,χ,hχ⟩ := hIso h
    exact occupied_of_head (c j).T cut k.val
      (occupied_of_restrict (nestedOpens (c j).U (c i).U) (head (c j).T cut)
        ((occupied_iff_of_strict_towerIso hχ k.val).mp k.property))
  lift_event := by intros; rfl
  lift_mono := by intros; assumption

theorem cofinalEvents_strict_nested_lift_comp
    {Z : CMfd.{0} n} {K : LocalTowerClass X} {p : Z → X}
    (c : ℕ → TowerChart K Z p) (hNest : ∀ ⦃i j⦄, i ≤ j → (c i).U ≤ (c j).U)
    (hIso : ∀ ⦃i j⦄ (h : i ≤ j),
      ∃ cut : ℕ, ∃ χ, IsTowerIso (nestedOpensDiffeo (n := n) (hNest h)).symm (c i).T
        (restrict (nestedOpens (c j).U (c i).U) (head (c j).T cut)) χ)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : {r // Occupied (c i).T r}) :
    let A := cofinalEvents_of_strict_nested_restrictions c hNest hIso
    A.lift hjk (A.lift hij a) = A.lift (hij.trans hjk) a := by
  exact Subtype.ext rfl

end Hironaka.HironakaG8NestedRawOccupiedSlots
