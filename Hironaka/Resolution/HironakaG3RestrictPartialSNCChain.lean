import Hironaka.Resolution.HironakaG3REmbeddedGlobalSNC
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3RestrictPartialSNCChain
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaG3REmbeddedGlobalSNC MaxLocusLocal

private theorem filter_preimage_subtype {M : Type*} (Q : Set M) (L : List (Set M))
    (hL : ∀ H ∈ L, H ⊆ Q) :
    (L.map ((Subtype.val : Q → M) ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
      (L.filter (fun H => decide H.Nonempty)).map ((Subtype.val : Q → M) ⁻¹' ·) := by
  induction L with
  | nil => rfl
  | cons H L ih =>
    have hHQ : H ⊆ Q := hL H (by simp)
    have hTail : ∀ A ∈ L, A ⊆ Q := fun A hA => hL A (by simp [hA])
    have hh : ((Subtype.val : Q → M) ⁻¹' H).Nonempty ↔ H.Nonempty := by
      constructor
      · rintro ⟨x,hx⟩; exact ⟨x,hx⟩
      · rintro ⟨x,hx⟩; exact ⟨⟨x,hHQ hx⟩,hx⟩
    by_cases hne : H.Nonempty <;> simp [hh,hne,ih hTail]

/-- Restrict a compatible chain covering an open to an actual SNC exhaustion there. -/
theorem restrict_partial_snc_chain {n : ℕ} {Z : CMfd.{0} n} (Q : Opens Z)
    (V : ℕ → Opens Z) (B : ℕ → List (Set Z))
    (hVQ : ∀ k, V k ≤ Q)
    (hMono : ∀ {j k : ℕ}, j ≤ k → (V j : Set Z) ⊆ V k)
    (hCover : (⋃ k, (V k : Set Z)) = (Q : Set Z))
    (hSub : ∀ {k : ℕ} {H : Set Z}, H ∈ B k → H ⊆ V k)
    (hSNC : ∀ k, IsSNCDivisor n ((B k).map ((Subtype.val : V k → Z) ⁻¹' ·)))
    (hNested : ∀ {j k : ℕ}, j ≤ k →
      ((B k).map (· ∩ (V j : Set Z))).filter (fun H => decide H.Nonempty) =
        (B j).filter (fun H => decide H.Nonempty)) :
    ∃ Ex : SNCExhaustion (CMfd.of (n := n) Q),
      (∀ k, Ex.W k = nestedOpens Q (V k)) ∧
      (∀ k, Ex.B k = (B k).map ((Subtype.val : Q → Z) ⁻¹' ·)) := by
  let F : Set Z → Set Q := fun H => (Subtype.val : Q → Z) ⁻¹' H
  have hFilter (L : List (Set Z)) (hL : ∀ H ∈ L, H ⊆ (Q : Set Z)) :
      (L.map F).filter (fun H => decide H.Nonempty) = (L.filter (fun H => decide H.Nonempty)).map F :=
    filter_preimage_subtype Q L hL
  have hListQ (k : ℕ) : ∀ H ∈ B k, H ⊆ (Q : Set Z) := fun H hH => (hSub hH).trans (hVQ k)
  let Ex : SNCExhaustion (CMfd.of (n := n) Q) := {
    W := fun k => nestedOpens Q (V k)
    B := fun k => (B k).map F
    mono := fun {j k} hjk x hx => hMono hjk hx
    cover := fun x => by
      have hx : (x : Z) ∈ ⋃ k, (V k : Set Z) := by rw [hCover]; exact x.property
      obtain ⟨k,hk⟩ := mem_iUnion.mp hx
      exact ⟨k,hk⟩
    sub := fun {k H} hH => by
      obtain ⟨H',hH',rfl⟩ := List.mem_map.mp hH
      exact fun x hx => hSub hH' hx
    snc := fun k => by
      let β := nestedOpensDiffeo (n := n) (hVQ k)
      have heq : ((B k).map F).map ((Subtype.val : nestedOpens Q (V k) → Q) ⁻¹' ·) =
          (((B k).map ((Subtype.val : V k → Z) ⁻¹' ·)).map (β ⁻¹' ·)) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro H _
        rfl
      rw [heq]
      exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff β).mpr (hSNC k)
    nested := fun {j k} hjk => by
      have hmap : ((B k).map F).map (· ∩ (nestedOpens Q (V j) : Set Q)) =
          ((B k).map (· ∩ (V j : Set Z))).map F := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro H _
        ext x
        rfl
      rw [hmap,hFilter _ (by
        intro H hH
        obtain ⟨H',hH',rfl⟩ := List.mem_map.mp hH
        exact inter_subset_left.trans (hListQ k H' hH')),
        hNested hjk,← hFilter _ (hListQ j)] }
  exact ⟨Ex,fun _ => rfl,fun _ => rfl⟩
end
end Hironaka.HironakaG3RestrictPartialSNCChain
