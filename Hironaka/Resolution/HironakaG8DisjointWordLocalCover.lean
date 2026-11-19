import Hironaka.Resolution.HironakaG8IndexedDisjointSwap

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8DisjointWordLocalCover
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG8OccupiedSlotComparison HironakaG8IndexedDisjointSwap
  G3UniverseEmptyAwareCore

variable {n : ℕ} {B F G H : CMfd.{0} n}

/-- A projected raw footprint is closed because the preceding projection is proper. -/
theorem isClosed_slotFootprint (T : BlowupTower B F) (i : ℕ) :
    IsClosed (slotFootprint T i) := by
  induction T with
  | refl => exact isClosed_empty
  | step T C π hπ ih =>
    rw [slotFootprint]
    split
    · exact (HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap _ hπ.1.1
    · exact ih

private theorem avoids_mono {U V : Opens B} (hUV : U ≤ V) (A : ℕ → Set B)
    {σ : ℕ ≃ ℕ} {w : List ℕ} (hV : OpenAvoidsSwapPairs V A σ w) :
    OpenAvoidsSwapPairs U A σ w := by
  induction w generalizing σ with
  | nil => trivial
  | cons i w ih =>
    obtain ⟨hPair,hTail⟩ := hV
    exact ⟨hPair.elim (fun h => Or.inl (h.mono_left hUV))
      (fun h => Or.inr (h.mono_left hUV)),ih hTail⟩

/-- At any point a finite word of disjoint exchanges of closed footprints
has one open on which at least one footprint of each exchange is absent. -/
theorem exists_open_avoiding_disjoint_word (A : ℕ → Set B) (hClosed : ∀ j, IsClosed (A j))
    {σ : ℕ ≃ ℕ} {w : List ℕ} (hWord : IsDisjointSwapWord A σ w) (x : B) :
    ∃ U : Opens B, x ∈ U ∧ OpenAvoidsSwapPairs U A σ w := by
  induction w generalizing σ with
  | nil => exact ⟨⊤,trivial,trivial⟩
  | cons i w ih =>
    obtain ⟨_,hDisj,hTail⟩ := hWord
    obtain ⟨V,hxV,hV⟩ := ih hTail
    have hPair : ∃ U : Opens B, x ∈ U ∧
        (Disjoint (U : Set B) (A (σ i)) ∨ Disjoint (U : Set B) (A (σ (i+1)))) := by
      classical
      by_cases hxi : x ∈ A (σ i)
      · let U : Opens B := ⟨(A (σ (i+1)))ᶜ,(hClosed _).isOpen_compl⟩
        exact ⟨U,fun hx => Set.disjoint_left.mp hDisj hxi hx,
          Or.inr disjoint_compl_left⟩
      · let U : Opens B := ⟨(A (σ i))ᶜ,(hClosed _).isOpen_compl⟩
        exact ⟨U,hxi,Or.inl disjoint_compl_left⟩
    obtain ⟨U,hxU,hU⟩ := hPair
    refine ⟨U ⊓ V,⟨hxU,hxV⟩,?_,avoids_mono inf_le_right A hV⟩
    exact hU.elim (fun h => Or.inl (h.mono_left (fun _ hx => hx.1)))
      (fun h => Or.inr (h.mono_left (fun _ hx => hx.1)))

/-- Two realized disjoint words on the same finite tower are locally
compared by the exact conjugation of their chosen terminal maps. -/
theorem local_comparison_of_disjoint_word_readbacks
    (T : BlowupTower B F) (R : BlowupTower B G) (S : BlowupTower B H)
    (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G)
    (f : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ H)
    (w v : List ℕ)
    (hW : IsDisjointSwapWord (slotFootprint T) (Equiv.refl ℕ) w)
    (hV : IsDisjointSwapWord (slotFootprint T) (Equiv.refl ℕ) v)
    (hR : ∀ U : Opens B, OpenAvoidsSwapPairs U (slotFootprint T) (Equiv.refl ℕ) w →
      ∃ eU : CMfd.of (n := n) (openPreimage T U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
        (∀ y, (eU y).val = e y.val) ∧
        EmptyAwareTowerIso (Diffeomorph.refl _ _ _) (restrict U T) (restrict U R) eU)
    (hS : ∀ U : Opens B, OpenAvoidsSwapPairs U (slotFootprint T) (Equiv.refl ℕ) v →
      ∃ fU : CMfd.of (n := n) (openPreimage T U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S U),
        (∀ y, (fU y).val = f y.val) ∧
        EmptyAwareTowerIso (Diffeomorph.refl _ _ _) (restrict U T) (restrict U S) fU)
    (x : B) :
    ∃ U : Opens B, x ∈ U ∧
      ∃ gU : CMfd.of (n := n) (openPreimage R U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S U),
        (∀ y, (gU y).val = f (e.symm y.val)) ∧
        EmptyAwareTowerIso (Diffeomorph.refl _ _ _) (restrict U R) (restrict U S) gU := by
  obtain ⟨U,hxU,hU⟩ := exists_open_avoiding_disjoint_word _ (isClosed_slotFootprint T) hW x
  obtain ⟨V,hxV,hV'⟩ := exists_open_avoiding_disjoint_word _ (isClosed_slotFootprint T) hV x
  obtain ⟨eU,heU,hE⟩ := hR (U ⊓ V) (avoids_mono inf_le_left _ hU)
  obtain ⟨fU,hfU,hF⟩ := hS (U ⊓ V) (avoids_mono inf_le_right _ hV')
  refine ⟨U ⊓ V,⟨hxU,hxV⟩,eU.symm.trans fU,?_,?_⟩
  · intro y
    change (fU (eU.symm y)).val = _
    rw [hfU]
    have h := heU (eU.symm y)
    rw [eU.apply_symm_apply] at h
    apply congrArg f
    apply e.injective
    change e (eU.symm y).val = e (e.symm y.val)
    rw [e.apply_symm_apply]
    exact h.symm
  · let O : Opens B := U ⊓ V
    let I := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (↥O) ∞
    have hh := G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.symm hE) hF
    change EmptyAwareTowerIso (I.symm.trans I) (restrict O R) (restrict O S) (eU.symm.trans fU) at hh
    have hId : I.symm.trans I = I := by ext y; rfl
    rw [hId] at hh
    exact hh

end Hironaka.HironakaG8DisjointWordLocalCover
