import Hironaka.Resolution.HironakaG8CofinalOccupiedAncestry

/-! Canonical chronological matching of nonempty physical blowup slots. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8OccupiedSlotComparison
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry
variable {n : ℕ} {X A Y B : CMfd.{0} n}

/-- Actual occupied raw indices in increasing chronological order. -/
def occupiedSlots : {Y : CMfd.{0} n} → BlowupTower X Y → List ℕ
  | _, .refl => []
  | _, .step T C _ _ => occupiedSlots T ++ if C.Nonempty then [T.length] else []

theorem mem_occupiedSlots (T : BlowupTower X Y) (i : ℕ) :
    i ∈ occupiedSlots T ↔ Occupied T i := by
  induction T with
  | refl => simp [occupiedSlots,Occupied]
  | step T C π hπ ih =>
    by_cases h : C.Nonempty <;> simp [occupiedSlots,Occupied,h,ih]

theorem occupiedSlots_length (T : BlowupTower X Y) :
    (occupiedSlots T).length = occupiedCount T := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    by_cases h : C.Nonempty <;> simp [occupiedSlots,occupiedCount,h,ih]

theorem occupiedSlots_pairwise (T : BlowupTower X Y) :
    (occupiedSlots T).Pairwise (· < ·) := by
  induction T with
  | refl => exact .nil
  | step T C π hπ ih =>
    by_cases h : C.Nonempty
    · simp only [occupiedSlots,if_pos h,List.pairwise_append]
      refine ⟨ih,by simp,?_⟩
      intro u hu v hv
      have hv' : v = T.length := by simpa using hv
      rw [hv']
      exact occupied_lt_length T ((mem_occupiedSlots T u).mp hu)
    · simpa [occupiedSlots,h] using ih

/-- The index in the occupied list is exactly the ordinal used to compare
slots across a physical overlap. -/
def occupiedOrdinalIso (T : BlowupTower X Y) :
    Fin (occupiedSlots T).length ≃o {i // Occupied T i} := by
  let f (i : Fin (occupiedSlots T).length) : {k // Occupied T k} :=
    ⟨(occupiedSlots T).get i,(mem_occupiedSlots T _).mp (List.mem_iff_get.mpr ⟨i,rfl⟩)⟩
  have hF : StrictMono f := fun i j h =>
    List.pairwise_iff_get.mp (occupiedSlots_pairwise T) i j h
  have hSurj : Function.Surjective f := by
    intro i
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp ((mem_occupiedSlots T i.val).mpr i.property)
    exact ⟨k,Subtype.ext hk⟩
  exact hF.orderIsoOfSurjective f hSurj

/-- Empty-aware physical overlap determines the unique increasing
bijection between the actual occupied raw slots. -/
def occupiedComparison
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {T : BlowupTower X Y} {S : BlowupTower A B} (h : EmptyAwareTowerIso φ T S ψ) :
    {i // Occupied T i} ≃o {i // Occupied S i} :=
  (occupiedOrdinalIso T).symm.trans ((Fin.castOrderIso (by
    rw [occupiedSlots_length,occupiedSlots_length,occupiedCount_emptyAware h])).trans
      (occupiedOrdinalIso S))

theorem occupied_orderIso_unique {T : BlowupTower X Y} {S : BlowupTower A B}
    (e f : {i // Occupied T i} ≃o {i // Occupied S i}) : e = f := by
  let u := occupiedOrdinalIso T
  have h : u.trans (e.trans (f.symm.trans u.symm)) = OrderIso.refl _ := Subsingleton.elim _ _
  ext x
  have hx := congrArg (fun g => g (u.symm x)) h
  change u.symm (f.symm (e (u (u.symm x)))) = u.symm x at hx
  rw [u.apply_symm_apply] at hx
  have hfx : f.symm (e x) = x := u.symm.injective hx
  exact congrArg Subtype.val (f.symm_apply_eq.mp hfx)

/-- All actual choices of terminal physical comparisons give the same
occupied ordinal match, and comparison matches compose on common sources. -/
theorem occupiedComparison_comp
    {P R : CMfd.{0} n}
    {T : BlowupTower X Y} {S : BlowupTower A B} {V : BlowupTower P R}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {φ' : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ P}
    {ψ' : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R}
    {φ'' : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ P}
    {ψ'' : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R}
    (h₁ : EmptyAwareTowerIso φ T S ψ) (h₂ : EmptyAwareTowerIso φ' S V ψ')
    (h₃ : EmptyAwareTowerIso φ'' T V ψ'') :
    (occupiedComparison h₁).trans (occupiedComparison h₂) = occupiedComparison h₃ :=
  occupied_orderIso_unique _ _

/-- The ordinal match into a literal restriction gives a chronological
embedding into the original tower's occupied slots. -/
def occupiedLiftOnOpen
    (U : Opens A) {T : BlowupTower X Y} (S : BlowupTower A B)
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S U)}
    (h : EmptyAwareTowerIso φ T (restrict U S) ψ) :
    {i // Occupied T i} ↪o {i // Occupied S i} :=
  (occupiedComparison h).toOrderEmbedding.trans
    (OrderEmbedding.ofStrictMono (fun i => ⟨i.val,occupied_of_restrict U S i.property⟩)
      (fun _ _ hlt => hlt))

theorem mem_range_occupiedLiftOnOpen
    (U : Opens A) {T : BlowupTower X Y} (S : BlowupTower A B)
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S U)}
    (h : EmptyAwareTowerIso φ T (restrict U S) ψ) (i : {i // Occupied S i}) :
    i ∈ range (occupiedLiftOnOpen U S h) ↔ Occupied (restrict U S) i.val := by
  constructor
  · rintro ⟨j,rfl⟩
    exact (occupiedComparison h j).property
  · intro hi
    obtain ⟨j,hj⟩ := (occupiedComparison h).surjective ⟨i.val,hi⟩
    exact ⟨j,Subtype.ext (congrArg (fun a : {k // Occupied (restrict U S) k} => a.val) hj)⟩


/-- Two chronological embeddings of one physical occupied list into the
same larger tower agree as soon as they have the same visible slots. -/
theorem occupied_orderEmbedding_unique_of_range {T : BlowupTower X Y} {S : BlowupTower A B}
    (e f : {i // Occupied T i} ↪o {i // Occupied S i}) (h : range e = range f) : e = f := by
  let fe (i : {i // Occupied T i}) : range e := ⟨e i,⟨i,rfl⟩⟩
  let ff (i : {i // Occupied T i}) : range e := ⟨f i,by rw [h]; exact ⟨i,rfl⟩⟩
  have he : Function.Surjective fe := by
    rintro ⟨x,⟨i,rfl⟩⟩
    exact ⟨i,rfl⟩
  have hf : Function.Surjective ff := by
    rintro ⟨x,hx⟩
    rw [h] at hx
    obtain ⟨i,rfl⟩ := hx
    exact ⟨i,rfl⟩
  let le := StrictMono.orderIsoOfSurjective fe (fun _ _ hij => e.strictMono hij) he
  let lf := StrictMono.orderIsoOfSurjective ff (fun _ _ hij => f.strictMono hij) hf
  let g := le.trans lf.symm
  have hg : g = OrderIso.refl _ := occupied_orderIso_unique _ _
  ext i
  have hi := congrArg (fun k => k i) hg
  change lf.symm (le i) = i at hi
  have hh := lf.symm_apply_eq.mp hi
  exact congrArg (fun z : range e => z.val.val) hh


/-- Projected source footprint of each literal physical raw slot. -/
def slotFootprint : {Y : CMfd.{0} n} → BlowupTower X Y → ℕ → Set X
  | _, .refl, _ => ∅
  | _, .step T C _ _, i => if i = T.length then T.proj '' C else slotFootprint T i

theorem slotFootprint_nonempty_iff (T : BlowupTower X Y) (i : ℕ) :
    (slotFootprint T i).Nonempty ↔ Occupied T i := by
  induction T with
  | refl => simp [slotFootprint,Occupied]
  | step T C π hπ ih =>
    by_cases hi : i = T.length
    · subst i
      have hp : ¬ Occupied T T.length := fun h => (Nat.lt_irrefl _) (occupied_lt_length T h)
      simp [slotFootprint,Occupied,hp]
    · simp [slotFootprint,Occupied,hi,ih]

/-- Physical raw slots retain exactly the footprint's literal trace. -/
theorem slotFootprint_restrict (T : BlowupTower X Y) (U : Opens X) (i : ℕ) :
    slotFootprint (restrict U T) i = (Subtype.val : U → X) ⁻¹' slotFootprint T i := by
  induction T with
  | refl => rfl
  | @step V W T C π hπ ih =>
    by_cases hi : i = T.length
    · have hri : i = (restrict U T).length := hi.trans (length_restrict U T).symm
      change (if i = (restrict U T).length then
        (restrict U T).proj '' ((Subtype.val : openPreimage T U → V) ⁻¹' C)
        else slotFootprint (restrict U T) i) = (Subtype.val : U → X) ⁻¹' _
      rw [if_pos hri,slotFootprint,if_pos hi]
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨y.val,hy,(proj_restrict U T y).symm⟩
      · rintro ⟨y,hy,hEq⟩
        have hyU : y ∈ openPreimage T U := by
          change T.proj y ∈ U
          rw [hEq]
          exact x.property
        exact ⟨⟨y,hyU⟩,hy,Subtype.ext ((proj_restrict U T ⟨y,hyU⟩).trans hEq)⟩
    · have hri : i ≠ (restrict U T).length := fun h => hi (h.trans (length_restrict U T))
      change (if i = (restrict U T).length then
        (restrict U T).proj '' ((Subtype.val : openPreimage T U → V) ⁻¹' C)
        else slotFootprint (restrict U T) i) = (Subtype.val : U → X) ⁻¹' _
      rw [if_neg hri,slotFootprint,if_neg hi]
      exact ih

theorem occupied_restrict_iff_slotFootprint_meets (T : BlowupTower X Y) (U : Opens X) (i : ℕ) :
    Occupied (restrict U T) i ↔ (slotFootprint T i ∩ (U : Set X)).Nonempty := by
  rw [← slotFootprint_nonempty_iff,slotFootprint_restrict]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z.val,hz,z.property⟩
  · rintro ⟨z,hz,hzU⟩
    exact ⟨⟨z,hzU⟩,hz⟩


/-- Ordinally ordered footprints of the occupied raw slots. -/
def occupiedFootprints (T : BlowupTower X Y) : List (Set X) :=
  (occupiedSlots T).map (slotFootprint T)

private theorem occupiedFootprints_step {C : Set Y} {π : B → Y} (T : BlowupTower X Y)
    (hπ : IsBlowupAlong n C π) :
    occupiedFootprints (.step T C π hπ) =
      occupiedFootprints T ++ if C.Nonempty then [T.proj '' C] else [] := by
  have hMap : (occupiedSlots T).map (slotFootprint (.step T C π hπ)) =
      (occupiedSlots T).map (slotFootprint T) := by
    apply List.map_congr_left
    intro i hi
    have hlt := occupied_lt_length T ((mem_occupiedSlots T i).mp hi)
    simp [slotFootprint,ne_of_lt hlt]
  unfold occupiedFootprints
  rw [occupiedSlots,List.map_append,hMap]
  by_cases h : C.Nonempty <;> simp [h,slotFootprint]

/-- Empty-aware comparison preserves the actual projected footprint of
every occupied occurrence in exact chronological order. -/
theorem occupiedFootprints_emptyAware
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {T : BlowupTower X Y} {S : BlowupTower A B} (h : EmptyAwareTowerIso φ T S ψ) :
    occupiedFootprints T = (occupiedFootprints S).map (φ ⁻¹' ·) := by
  induction h with
  | refl => rfl
  | @step Y B Z W T S ψ h C π hπ D ρ hρ χ hMap hC ih =>
    have hne : C.Nonempty ↔ D.Nonempty := by
      rw [← hC]
      exact ψ.surjective.nonempty_preimage
    rw [occupiedFootprints_step,occupiedFootprints_step,List.map_append,ih]
    by_cases hD : D.Nonempty
    · simp only [if_pos hD,if_pos (hne.mpr hD),List.map_cons,List.map_nil]
      congr 2
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        refine ⟨ψ y,?_,emptyAware_proj_comm h y⟩
        change y ∈ ψ ⁻¹' D
        rwa [hC]
      · rintro ⟨y,hy,he⟩
        refine ⟨ψ.symm y,?_,φ.injective ?_⟩
        · rw [← hC]
          change ψ (ψ.symm y) ∈ D
          rwa [ψ.apply_symm_apply]
        · change φ (T.proj (ψ.symm y)) = φ x
          rwa [← emptyAware_proj_comm h,ψ.apply_symm_apply]
    · simp [hD,not_congr hne |>.mpr hD]
  | leftEmpty h hρ e he ih => simpa [occupiedFootprints_step] using ih
  | rightEmpty h hρ e he ih => simpa [occupiedFootprints_step] using ih


/-- The canonical ordinal correspondence matches the exact projected
centre footprint of each actual occupied occurrence. -/
theorem slotFootprint_occupiedComparison
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {T : BlowupTower X Y} {S : BlowupTower A B} (h : EmptyAwareTowerIso φ T S ψ)
    (i : {i // Occupied T i}) :
    slotFootprint T i.val = φ ⁻¹' slotFootprint S (occupiedComparison h i).val := by
  let k := (occupiedOrdinalIso T).symm i
  let hLen : (occupiedSlots T).length = (occupiedSlots S).length := by
    rw [occupiedSlots_length,occupiedSlots_length,occupiedCount_emptyAware h]
  let j : Fin (occupiedSlots S).length := Fin.cast hLen k
  have hOrd : occupiedOrdinalIso T k = i := (occupiedOrdinalIso T).apply_symm_apply i
  have hOrd' : occupiedOrdinalIso S j = occupiedComparison h i := rfl
  have hk : (occupiedSlots T).get k = i.val := congrArg Subtype.val hOrd
  have hj : (occupiedSlots S).get j = (occupiedComparison h i).val := congrArg Subtype.val hOrd'
  have hL := congrArg (fun L : List (Set X) => L[k.val]?) (occupiedFootprints_emptyAware h)
  unfold occupiedFootprints at hL
  simp only [List.getElem?_map] at hL
  rw [List.getElem?_eq_getElem k.isLt] at hL
  have hj' : k.val < (occupiedSlots S).length := j.isLt
  rw [List.getElem?_eq_getElem hj'] at hL
  change some (slotFootprint T ((occupiedSlots T).get k)) =
    some (φ ⁻¹' slotFootprint S ((occupiedSlots S).get j)) at hL
  rw [hk,hj] at hL
  exact Option.some.inj hL

/-- Corresponding occupied slots remain visible on exactly the same
matched smaller opens. This is the range equality needed when composing
nested physical matches through a common literal restriction. -/
theorem occupiedComparison_visibility
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {T : BlowupTower X Y} {S : BlowupTower A B} (h : EmptyAwareTowerIso φ T S ψ)
    (U : Opens X) (V : Opens A) (hUV : (U : Set X) = φ ⁻¹' (V : Set A))
    (i : {i // Occupied T i}) :
    Occupied (restrict U T) i.val ↔ Occupied (restrict V S) (occupiedComparison h i).val := by
  rw [occupied_restrict_iff_slotFootprint_meets,occupied_restrict_iff_slotFootprint_meets,
    slotFootprint_occupiedComparison h i,hUV,← preimage_inter]
  exact φ.surjective.nonempty_preimage


/-- Ordered raw-slot inclusion along the literal restriction. -/
def occupiedRestrictionEmbedding (U : Opens X) (T : BlowupTower X Y) :
    {i // Occupied (restrict U T) i} ↪o {i // Occupied T i} :=
  OrderEmbedding.ofStrictMono (fun i => ⟨i.val,occupied_of_restrict U T i.property⟩)
    (fun _ _ hlt => hlt)

/-- Matching occupied slots commutes with any further matched literal
restriction. The restricted comparison can be any actual empty-aware
comparison between those restricted towers. -/
theorem occupiedComparison_restrict_natural
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {T : BlowupTower X Y} {S : BlowupTower A B} (h : EmptyAwareTowerIso φ T S ψ)
    (U : Opens X) (V : Opens A) (hUV : (U : Set X) = φ ⁻¹' (V : Set A))
    {φ₀ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V}
    {ψ₀ : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage S V)}
    (h₀ : EmptyAwareTowerIso φ₀ (restrict U T) (restrict V S) ψ₀) :
    occupiedLiftOnOpen V S h₀ =
      (occupiedRestrictionEmbedding U T).trans (occupiedComparison h).toOrderEmbedding := by
  apply occupied_orderEmbedding_unique_of_range
  ext j
  rw [mem_range_occupiedLiftOnOpen V S h₀]
  constructor
  · intro hj
    obtain ⟨i,rfl⟩ := (occupiedComparison h).surjective j
    have hi := (occupiedComparison_visibility h U V hUV i).mpr hj
    exact ⟨⟨i.val,hi⟩, by change occupiedComparison h _ = _; congr⟩
  · rintro ⟨i,rfl⟩
    exact (occupiedComparison_visibility h U V hUV (occupiedRestrictionEmbedding U T i)).mp i.property


end
end Hironaka.HironakaG8OccupiedSlotComparison
