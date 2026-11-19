import Mathlib.Order.WellFoundedSet
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.NodupEquivFin

/-!+# Actual upward diagrams have no infinite reverse-inclusion bad sequence

Source-first proof: `hironaka-upward-diagram-well-quasi-order-20261101.tex`.
The dimension induction uses actual stabilized slices and Higman's lemma;
no vertex bound, supplied stabilization or well-foundedness premise is used.
-/

set_option autoImplicit false

namespace Hironaka.HironakaUpwardDiagramWellQuasiOrder

noncomputable section

open Set OrderDual

/-- Actual upward subsets of the finite exponent space, including the empty set. -/
abbrev Diagram (n : ℕ) := {s : Set (Fin n → ℕ) // IsUpperSet s}

private def slice {n : ℕ} (D : Diagram (n+1)) (k : ℕ) : Diagram n := by
  refine ⟨{a : Fin n → ℕ | Fin.cons k a ∈ D.val}, ?_⟩
  intro a b hab ha
  exact D.property (Fin.cons_le_cons.mpr ⟨le_rfl, hab⟩) ha

private theorem slice_antitone {n : ℕ} (D : Diagram (n+1)) :
    Antitone (fun k => toDual (slice D k)) := by
  intro i j hij a ha
  exact D.property (Fin.cons_le_cons.mpr ⟨hij, le_rfl⟩) ha

private theorem list_wellQuasiOrdered {α : Type*} [Preorder α]
    (h : WellQuasiOrdered ((· ≤ ·) : α → α → Prop)) :
    WellQuasiOrdered (List.SublistForall₂ ((· ≤ ·) : α → α → Prop)) := by
  intro f
  have hp := Set.partiallyWellOrderedOn_of_wellQuasiOrdered h Set.univ
  have hl := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ (· ≤ ·) hp
  exact hl.exists_lt (f := f) (fun _ _ _ => Set.mem_univ _)

private theorem embedding_index_le {p q : ℕ} (f : Fin p ↪o Fin q) :
    ∀ i : Fin p, i.val ≤ (f i).val := by
  have h : ∀ k (hk : k < p), k ≤ (f ⟨k,hk⟩).val := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < p := by omega
      have hlt := f.strictMono (show (⟨k,hk'⟩ : Fin p) < ⟨k+1,hk⟩ from by simp)
      have hi := ih hk'
      change (f ⟨k,hk'⟩).val < (f ⟨k+1,hk⟩).val at hlt
      omega
  exact fun i => h i.val i.isLt

private theorem prefix_le_of_sublist {α : Type*} [Preorder α]
    (A B : ℕ → α) (p q : ℕ) (hB : Antitone B)
    (h : List.SublistForall₂ (· ≤ ·) (List.ofFn fun i : Fin p => A i.val)
      (List.ofFn fun i : Fin q => B i.val)) :
    ∀ k < p, A k ≤ B k := by
  obtain ⟨l, hAl, hlB⟩ := List.sublistForall₂_iff.mp h
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hlB
  intro k hk
  have hkp : k < (List.ofFn fun i : Fin p => A i.val).length := by simpa using hk
  have hkl : k < l.length := by rw [← hAl.length_eq]; exact hkp
  have hA := hAl.get hkp hkl
  have hget := hf ⟨k,hkl⟩
  have hidx := embedding_index_le f ⟨k,hkl⟩
  have hAB : A k ≤ B (f ⟨k,hkl⟩).val := by
    simpa only [List.get_eq_getElem, List.getElem_ofFn] using hA.trans_eq hget
  exact hAB.trans (hB hidx)

/-- The actual upward diagrams in any fixed finite dimension are well quasi
ordered by reverse inclusion. Stabilization and list encodings are produced. -/
theorem upward_diagram_wellQuasiOrdered (n : ℕ) :
    WellQuasiOrdered (fun A B : Diagram n => B.val ⊆ A.val) := by
  classical
  induction n with
  | zero =>
    intro seq
    let origin : Fin 0 → ℕ := fun i => Fin.elim0 i
    obtain ⟨i,j,hij,h⟩ := Finite.wellQuasiOrdered ((· = ·) : Bool → Bool → Prop)
      (fun k => decide (origin ∈ (seq k).val))
    refine ⟨i,j,hij,?_⟩
    intro a ha
    have heq : a = origin := Subsingleton.elim _ _
    subst a
    exact of_decide_eq_true (h.trans (decide_eq_true ha))
  | succ n ih =>
    have : WellQuasiOrderedLE (Diagram n)ᵒᵈ := ⟨ih⟩
    have hs : ∀ D : Diagram (n+1), ∃ N, ∀ k, N ≤ k → slice D N = slice D k := by
      intro D
      exact WellFoundedLT.antitone_chain_condition (α := (Diagram n)ᵒᵈ)
        (f := fun k => toDual (slice D k)) (slice_antitone D)
    choose cut hcut using hs
    have hterminal (D : Diagram (n+1)) (k : ℕ) :
        (slice D k).val ⊆ (slice D (cut D)).val := by
      by_cases hk : k ≤ cut D
      · exact slice_antitone D hk
      · rw [hcut D k (by omega)]
    let code (D : Diagram (n+1)) : List (Diagram n)ᵒᵈ × (Diagram n)ᵒᵈ :=
      (List.ofFn fun i : Fin (cut D) => toDual (slice D i.val), toDual (slice D (cut D)))
    have hl := list_wellQuasiOrdered (α := (Diagram n)ᵒᵈ) ih
    have : IsPreorder (List (Diagram n)ᵒᵈ) (List.SublistForall₂ (· ≤ ·)) :=
      { refl := fun _ => refl _, trans := fun _ _ _ h₁ h₂ => _root_.trans h₁ h₂ }
    have hp := hl.prod ih
    intro seq
    obtain ⟨i,j,hij,hprefix,htail⟩ := hp (fun k => code (seq k))
    refine ⟨i,j,hij,?_⟩
    intro a ha
    let k : ℕ := a 0
    let b : Fin n → ℕ := Fin.tail a
    have ha' : b ∈ (slice (seq j) k).val := by simpa [slice,k,b] using ha
    have hmem : b ∈ (slice (seq i) k).val := by
      by_cases hk : k < cut (seq i)
      · have hle := prefix_le_of_sublist
          (fun t => toDual (slice (seq i) t)) (fun t => toDual (slice (seq j) t))
          (cut (seq i)) (cut (seq j)) (slice_antitone (seq j)) hprefix k hk
        exact hle ha'
      · have hborn : b ∈ (slice (seq j) (cut (seq j))).val := hterminal (seq j) k ha'
        have hsource : b ∈ (slice (seq i) (cut (seq i))).val := htail hborn
        rw [hcut (seq i) k (by omega)] at hsource
        exact hsource
    simpa [slice,k,b] using hmem

end
end Hironaka.HironakaUpwardDiagramWellQuasiOrder
