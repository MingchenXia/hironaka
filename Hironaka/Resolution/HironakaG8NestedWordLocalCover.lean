import Hironaka.Resolution.HironakaG8FixedGeometricWordReadback
import Hironaka.Resolution.HironakaG8FixedNestedOpenReadback
import Hironaka.Resolution.HironakaG8DisjointWordLocalCover

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NestedWordLocalCover

open BlowupTowers BlowupTowerTransforms MaxLocusLocal MarkedIdeals
  G3UniverseEmptyAwareCore HironakaG8NestedVisibleWordLift HironakaG8GeometricIndexedWord
  HironakaG8FixedGeometricWordReadback HironakaG8FixedNestedOpenReadback
  HironakaG8DisjointWordLocalCover HironakaG8IndexedDisjointSwap HironakaG8OccupiedSlotComparison

private theorem restrict_avoids {n : ℕ} {X : CMfd.{0} n} {U V : Opens X}
    (hUV : U ≤ V) (A : ℕ → Set X) {σ : ℕ ≃ ℕ} {w : List ℕ}
    (h : OpenAvoidsSwapPairs V A σ w) : OpenAvoidsSwapPairs U A σ w := by
  induction w generalizing σ with
  | nil => trivial
  | cons i w ih =>
      obtain ⟨hPair,hTail⟩ := h
      exact ⟨hPair.elim (fun h => Or.inl (h.mono_left hUV))
        (fun h => Or.inr (h.mono_left hUV)),ih hTail⟩

/-- Every geometric move records nonemptiness and disjointness at the
relevant source slots, so the realized word already carries avoidance data. -/
theorem geometric_word_isDisjoint {n : ℕ} {B : CMfd.{0} n} (W : Set B) (M : MarkedIdeal n B)
    (A : ℕ → Set B) {word : List ℕ} {L R : TowerAt B}
    (h : RealizedWord (GeometricIndexedMove W M) word L R)
    (σ : ℕ ≃ ℕ) (hFoot : ∀ j, slotFootprint L.2 j = A (σ j)) :
    IsDisjointSwapWord A σ word := by
  induction h generalizing σ with
  | nil => trivial
  | @cons i word L S R hMove _ ih =>
      obtain ⟨hi,hDisj,hOcc,_,hNext⟩ := hMove.1
      have hStep (j : ℕ) : slotFootprint S.2 j = A (((Equiv.swap i (i+1)).trans σ) j) :=
        (hNext j).trans (hFoot _)
      refine ⟨?_,?_,ih _ hStep⟩
      · simpa only [hFoot] using hOcc (i+1) hi
      · simpa only [hFoot] using hDisj

variable {n : ℕ} {X : CMfd.{0} n} {U V : Opens X}
local notation "BU" => CMfd.of (n := n) U
local notation "BV" => CMfd.of (n := n) V

/-- Local comparisons use the same two fixed sorting maps on every avoiding
subopen and agree pointwise with their conjugation of the original map. -/
theorem nested_words_local_cover
    {L L' : TowerAt BU} {R R' : TowerAt BV}
    (WL : Set BU) (WR : Set BV) (ML : MarkedIdeal n BU) (MR : MarkedIdeal n BV)
    {w v : List ℕ}
    (hL : RealizedWord (GeometricIndexedMove WL ML) w L L')
    (hR : RealizedWord (GeometricIndexedMove WR MR) v R R')
    (e : BU ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (nestedOpens V U))
    (he : ∀ x : U, (e x).val.val = x.val)
    (f : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage R.2 (nestedOpens V U)))
    (h : EmptyAwareTowerIso e L.2 (restrict (nestedOpens V U) R.2) f) :
    ∃ (a : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ L'.1)
      (b : R.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R'.1),
      L'.2.proj ∘ a = L.2.proj ∧ R'.2.proj ∘ b = R.2.proj ∧
      ∀ x : U, ∃ O : Opens X, x.val ∈ O ∧ O ≤ U ∧ O ≤ V ∧
        OpenAvoidsSwapPairs (nestedOpens U O) (slotFootprint L.2) (Equiv.refl ℕ) w ∧
        OpenAvoidsSwapPairs (nestedOpens V O) (slotFootprint R.2) (Equiv.refl ℕ) v ∧
        ∃ g : CMfd.of (n := n) (nestedOpens U O) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
            CMfd.of (n := n) (nestedOpens V O),
          (∀ z : nestedOpens U O, (g z).val.val = z.val.val) ∧
          ∃ k : CMfd.of (n := n) (openPreimage L'.2 (nestedOpens U O))
              ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
            CMfd.of (n := n) (openPreimage R'.2 (nestedOpens V O)),
            (∀ y, (k y).val = b (f (a.symm y.val)).val) ∧
            EmptyAwareTowerIso g (restrict (nestedOpens U O) L'.2) (restrict (nestedOpens V O) R'.2) k := by
  obtain ⟨a,ha,_,hA⟩ := fixed_geometric_word_readback WL ML (slotFootprint L.2) hL
    (Equiv.refl ℕ) (fun _ => rfl)
  obtain ⟨b,hb,_,hB⟩ := fixed_geometric_word_readback WR MR (slotFootprint R.2) hR
    (Equiv.refl ℕ) (fun _ => rfl)
  refine ⟨a,b,ha,hb,?_⟩
  intro x
  have hw := geometric_word_isDisjoint WL ML (slotFootprint L.2) hL
    (Equiv.refl ℕ) (fun _ => rfl)
  have hv := geometric_word_isDisjoint WR MR (slotFootprint R.2) hR
    (Equiv.refl ℕ) (fun _ => rfl)
  obtain ⟨P,hxP,hP⟩ := exists_open_avoiding_disjoint_word _ (isClosed_slotFootprint L.2) hw x
  obtain ⟨Q,hxQ,hQ⟩ := exists_open_avoiding_disjoint_word _ (isClosed_slotFootprint R.2) hv (e x).val
  let PX : Opens X := ⟨(Subtype.val : U → X) '' (P : Set U),
    U.isOpen.isOpenMap_subtype_val _ P.isOpen⟩
  let QX : Opens X := ⟨(Subtype.val : V → X) '' (Q : Set V),
    V.isOpen.isOpenMap_subtype_val _ Q.isOpen⟩
  let O := PX ⊓ QX
  have hOU : O ≤ U := fun _ hz => by
    obtain ⟨u,_,rfl⟩ := hz.1
    exact u.property
  have hOV : O ≤ V := fun _ hz => by
    obtain ⟨u,_,rfl⟩ := hz.2
    exact u.property
  have hOP : nestedOpens U O ≤ P := by
    intro u hu
    obtain ⟨z,hz,heq⟩ := hu.1
    exact (Subtype.ext heq : z = u) ▸ hz
  have hOQ : nestedOpens V O ≤ Q := by
    intro u hu
    obtain ⟨z,hz,heq⟩ := hu.2
    exact (Subtype.ext heq : z = u) ▸ hz
  have hAvoidL := restrict_avoids hOP _ hP
  have hAvoidR := restrict_avoids hOQ _ hQ
  obtain ⟨aO,haO,hAO⟩ := hA _ hAvoidL
  obtain ⟨bO,hbO,hBO⟩ := hB _ hAvoidR
  exact ⟨O,⟨⟨x,hxP,rfl⟩,⟨(e x).val,hxQ,he x⟩⟩,hOU,hOV,hAvoidL,hAvoidR,
    sorted_nested_common_subopen L.2 R.2 L'.2 R'.2 hOU e he f h a b aO bO haO hbO hAO hBO⟩

end Hironaka.HironakaG8NestedWordLocalCover
