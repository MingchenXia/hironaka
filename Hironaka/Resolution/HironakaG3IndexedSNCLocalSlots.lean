import Hironaka.Resolution.HironakaG3REmbeddedGlobalSNC
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary
import Hironaka.Resolution.HironakaActualIndexedBoundaryContinuation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedSNCLocalSlots
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation

/-- An injective match to actual local SNC slots supplies indexed coordinates. -/
theorem indexed_coordinates_of_local_slots {n : ℕ} {Z : CMfd.{0} n} {ι : Type*}
    (F : ι → Set Z) (x : Z) (U : Opens Z) (hxU : x ∈ U) (E : List (Set Z))
    (hE : IsSNCDivisor n (E.map ((Subtype.val : U → Z) ⁻¹' ·)))
    (hSlot : ∀ a, x ∈ F a → ∃ p : Fin (E.map ((Subtype.val : U → Z) ⁻¹' ·)).length,
      (E.map ((Subtype.val : U → Z) ⁻¹' ·)).get p = (Subtype.val : U → Z) ⁻¹' F a)
    (hUnique : ∀ a b, x ∈ F a → x ∈ F b →
      (Subtype.val : U → Z) ⁻¹' F a = (Subtype.val : U → Z) ⁻¹' F b → a = b) :
    ∃ S : ι → Finset (Fin n), IsCoordinateFamilyAt n F S x ∧
      (∀ a, x ∈ F a → (S a).card = 1) ∧ Set.InjOn S {a | x ∈ F a} := by
  obtain ⟨S,⟨Φ,hsrc,hzero,hcoord⟩,hcard,hinj⟩ := hE.2 ⟨x,hxU⟩
  let S' : ι → Finset (Fin n) := fun a => if ha : x ∈ F a then S (hSlot a ha).choose else ∅
  have hS' : ∀ a (ha : x ∈ F a), S' a = S (hSlot a ha).choose := fun a ha => dif_pos ha
  have hget : ∀ a (ha : x ∈ F a),
      (E.map ((Subtype.val : U → Z) ⁻¹' ·)).get (hSlot a ha).choose = (Subtype.val : U → Z) ⁻¹' F a :=
    fun a ha => (hSlot a ha).choose_spec
  refine ⟨S',?_,?_,?_⟩
  · apply (NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff (x := (⟨x,hxU⟩ : U))).mp
    refine ⟨Φ,hsrc,hzero,fun a ha y hy hyΦ => ?_⟩
    have ha' : x ∈ F a := ha
    rw [hS' a ha']
    have h := hcoord (hSlot a ha').choose (by beta_reduce; rw [hget a ha']; exact ha) hy hyΦ
    beta_reduce at h
    rw [hget a ha'] at h
    exact h
  · intro a ha
    rw [hS' a ha]
    exact hcard _ (by rw [hget a ha]; exact ha)
  · intro a ha b hb hab
    have ha' : x ∈ F a := ha
    have hb' : x ∈ F b := hb
    rw [hS' a ha',hS' b hb'] at hab
    have hp := hinj (by rw [Set.mem_ofPred_eq,hget a ha']; exact ha')
      (by rw [Set.mem_ofPred_eq,hget b hb']; exact hb') hab
    have heq : (Subtype.val : U → Z) ⁻¹' F a = (Subtype.val : U → Z) ⁻¹' F b := by
      rw [← hget a ha',← hget b hb',hp]
    exact hUnique a b ha' hb' heq

/-- Local injective finite slot charts and local finiteness yield global indexed SNC. -/
theorem indexed_snc_of_local_slots {n : ℕ} {Z : CMfd.{0} n} {ι : Type*}
    (F : ι → Set Z) (hLF : LocallyFinite F) (hClosed : ∀ a, IsClosed (F a))
    (hLocal : ∀ x : Z, ∃ (U : Opens Z) (E : List (Set Z)), x ∈ U ∧
      IsSNCDivisor n (E.map ((Subtype.val : U → Z) ⁻¹' ·)) ∧
      (∀ a, x ∈ F a → ∃ p : Fin (E.map ((Subtype.val : U → Z) ⁻¹' ·)).length,
        (E.map ((Subtype.val : U → Z) ⁻¹' ·)).get p = (Subtype.val : U → Z) ⁻¹' F a) ∧
      (∀ a b, x ∈ F a → x ∈ F b →
        (Subtype.val : U → Z) ⁻¹' F a = (Subtype.val : U → Z) ⁻¹' F b → a = b)) :
    IsLocallyFiniteSNCDivisor n F := by
  refine ⟨hLF,hClosed,?_⟩
  intro x
  obtain ⟨U,E,hxU,hE,hSlot,hUnique⟩ := hLocal x
  exact indexed_coordinates_of_local_slots F x U hxU E hE hSlot hUnique
/-- Matching the boundary traces to a local NC list transfers carrier NC. -/
theorem indexed_nc_of_local_slots {n : ℕ} {Z : CMfd.{0} n} {ι : Type*}
    (C : Set Z) (F : ι → Set Z)
    (hLocal : ∀ x ∈ C, ∃ (U : Opens Z) (E : List (Set Z)), x ∈ U ∧
      HasNormalCrossings n ((Subtype.val : U → Z) ⁻¹' C) (E.map ((Subtype.val : U → Z) ⁻¹' ·)) ∧
      (∀ a, x ∈ F a → ∃ p : Fin (E.map ((Subtype.val : U → Z) ⁻¹' ·)).length,
        (E.map ((Subtype.val : U → Z) ⁻¹' ·)).get p = (Subtype.val : U → Z) ⁻¹' F a)) :
    HasNormalCrossingsWithBoundary C F := by
  intro x hx
  obtain ⟨U,E,hxU,hNC,hSlot⟩ := hLocal x hx
  obtain ⟨S₀,S,⟨Φ,hsrc,hzero,hcoord⟩,hcard⟩ := hNC ⟨x,hxU⟩ hx
  let S' : ι → Finset (Fin n) := fun a => if ha : x ∈ F a then S (hSlot a ha).choose else ∅
  have hS' : ∀ a (ha : x ∈ F a), S' a = S (hSlot a ha).choose := fun a ha => dif_pos ha
  have hget : ∀ a (ha : x ∈ F a),
      (E.map ((Subtype.val : U → Z) ⁻¹' ·)).get (hSlot a ha).choose = (Subtype.val : U → Z) ⁻¹' F a :=
    fun a ha => (hSlot a ha).choose_spec
  refine ⟨S₀,S',?_,?_⟩
  · apply (NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff (x := (⟨x,hxU⟩ : U))).mp
    refine ⟨Φ,hsrc,hzero,fun o ho y hy hyΦ => ?_⟩
    cases o with
    | none => exact hcoord none ho hy hyΦ
    | some a =>
      have ha : x ∈ F a := ho
      simp only [Option.elim_some]
      rw [hS' a ha]
      have hh := hcoord (some (hSlot a ha).choose) (by simp only [Option.elim_some]; rw [hget a ha]; exact ho) hy hyΦ
      simp only [Option.elim_some] at hh
      rw [hget a ha] at hh
      exact hh
  · intro a ha
    rw [hS' a ha]
    exact hcard _ (by rw [hget a ha]; exact ha)

end
end Hironaka.HironakaG3IndexedSNCLocalSlots
