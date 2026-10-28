import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyFinite
import TranscendentalNakamaye.Pending.HironakaActualLocallyFiniteBlowupLimitGeometry

/-! Compact escape produces genuine local finiteness of actual centre images.
No canonicality, fair selection or resolution scheduler is constructed.
Blueprint: `hironaka-disjoint-compact-exhaustion-escape.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology
universe u
namespace TranscendentalNakamaye.Pending.HironakaDisjointCompactExhaustionEscape
noncomputable section
variable {Q : Type*} [TopologicalSpace Q]

theorem locallyFinite_iff_exhaustion_escape (K : CompactExhaustion Q) (F : ℕ → Set Q) :
    LocallyFinite F ↔ ∀ m, ∃ N, ∀ i, N ≤ i → Disjoint (F i) (K m) := by
  constructor
  · intro h m
    obtain ⟨B,hB⟩:=(h.finite_nonempty_inter_compact (K.isCompact m)).bddAbove
    refine ⟨B+1,fun i hi => disjoint_left.mpr ?_⟩
    intro x hxF hxK
    have hle : i ≤ B:=hB ⟨x,hxF,hxK⟩
    omega
  · intro h x
    obtain ⟨m,hm⟩:=K.exists_mem_nhds x
    obtain ⟨N,hN⟩:=h m
    refine ⟨K m,hm,(finite_Iio N).subset ?_⟩
    rintro i ⟨y,hyF,hyK⟩
    change i < N
    apply lt_of_not_ge
    intro hi
    exact disjoint_left.mp (hN i hi) hyF hyK

/-- The literal complement of the entire closed indexed tail. -/
def protectedOpen (K : CompactExhaustion Q) (F : ℕ → Set Q)
    (hclosed : ∀i,IsClosed (F i))
    (hescape : ∀m,∃N,∀i,N ≤ i → Disjoint (F i) (K m)) (N : ℕ) : Opens Q :=
  ⟨(⋃i : {i : ℕ // N ≤ i},F i)ᶜ,
    (((locallyFinite_iff_exhaustion_escape K F).mpr hescape).comp_injective
      Subtype.val_injective).isClosed_iUnion (fun i => hclosed i.val) |>.isOpen_compl⟩

theorem mem_protectedOpen (K : CompactExhaustion Q) (F : ℕ → Set Q)
    (hclosed : ∀i,IsClosed (F i))
    (hescape : ∀m,∃N,∀i,N ≤ i → Disjoint (F i) (K m)) (N : ℕ) (x : Q) :
    x ∈ protectedOpen K F hclosed hescape N ↔ ∀i,N ≤ i → x ∉ F i := by
  change (x ∉ ⋃i : {i : ℕ // N ≤ i},F i) ↔ _
  simp only [mem_iUnion,not_exists]
  exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i i.property⟩

theorem protectedOpen_mono (K : CompactExhaustion Q) (F : ℕ → Set Q)
    (hclosed : ∀i,IsClosed (F i))
    (hescape : ∀m,∃N,∀i,N ≤ i → Disjoint (F i) (K m)) :
    Monotone (protectedOpen K F hclosed hescape) := by
  intro N M hNM x hx
  rw [mem_protectedOpen] at hx ⊢
  exact fun i hi => hx i (hNM.trans hi)

theorem exists_compact_subset_protectedOpen (K : CompactExhaustion Q) (F : ℕ → Set Q)
    (hclosed : ∀i,IsClosed (F i))
    (hescape : ∀m,∃N,∀i,N ≤ i → Disjoint (F i) (K m)) {L : Set Q} (hL : IsCompact L) :
    ∃N,L ⊆ protectedOpen K F hclosed hescape N := by
  obtain ⟨m,hm⟩:=K.exists_superset_of_isCompact hL
  obtain ⟨N,hN⟩:=hescape m
  refine ⟨N,fun x hx => (mem_protectedOpen K F hclosed hescape N x).mpr ?_⟩
  intro i hi hxF
  exact disjoint_left.mp (hN i hi) hxF (hm hx)

theorem protectedOpen_cover (K : CompactExhaustion Q) (F : ℕ → Set Q)
    (hclosed : ∀i,IsClosed (F i))
    (hescape : ∀m,∃N,∀i,N ≤ i → Disjoint (F i) (K m)) (x : Q) :
    ∃N,x ∈ protectedOpen K F hclosed hescape N := by
  obtain ⟨N,hN⟩:=exists_compact_subset_protectedOpen K F hclosed hescape
    (L:={x}) isCompact_singleton
  exact ⟨N,hN (mem_singleton x)⟩

open FirstPass FirstPass.HolomorphicIdealSheaves BlowupTowers ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteBlowupLimitGeometry
variable {n : ℕ} {X : CMfd.{u} n}

theorem actual_centres_locallyFinite (s : GrowingSeq X) (K : CompactExhaustion X)
    (hescape : ∀m,∃N,∀i,N ≤ i → Disjoint (centreImage s i) (K m)) :
    LocallyFinite (centreImage s) :=
  (locallyFinite_iff_exhaustion_escape K (centreImage s)).mpr hescape

theorem actual_centres_compact_protected (s : GrowingSeq X) (K : CompactExhaustion X)
    (hescape : ∀m,∃N,∀i,N ≤ i → Disjoint (centreImage s i) (K m))
    {L : Set X} (hL : IsCompact L) :
    ∃N,L ⊆ actualStableOpen s (actual_centres_locallyFinite s K hescape) N :=
  exists_compact_subset_actualStableOpen s (actual_centres_locallyFinite s K hescape) hL

theorem protectedOpen_actual_eq (s : GrowingSeq X) (K : CompactExhaustion X)
    (hescape : ∀m,∃N,∀i,N ≤ i → Disjoint (centreImage s i) (K m)) (N : ℕ) :
    protectedOpen K (centreImage s) (isClosed_centreImage s) hescape N =
      actualStableOpen s (actual_centres_locallyFinite s K hescape) N := rfl

/-- On the original ordinary second-countable locally compact base, the
exhaustion is supplied internally by topology; local finiteness is an output. -/
theorem actual_centres_choice_escape [LocallyCompactSpace X] [SecondCountableTopology X]
    (s : GrowingSeq X)
    (hescape : ∀ m, ∃ N, ∀ i, N ≤ i →
      Disjoint (centreImage s i) (CompactExhaustion.choice X m)) :
    LocallyFinite (centreImage s) ∧
      ∀ (L : Set X), IsCompact L → ∃ (N : ℕ) (U : Opens X),
        L ⊆ U ∧ (∀ i, N ≤ i → Disjoint (centreImage s i) (U : Set X)) := by
  have hLF:=actual_centres_locallyFinite s (CompactExhaustion.choice X) hescape
  refine ⟨hLF,fun L hL => ?_⟩
  obtain ⟨N,hN⟩:=exists_compact_subset_actualStableOpen s hLF hL
  refine ⟨N,actualStableOpen s hLF N,hN,fun i hi => disjoint_left.mpr ?_⟩
  intro x hxF hxU
  exact (mem_actualStableOpen s hLF N x).mp hxU i hi hxF

end
end TranscendentalNakamaye.Pending.HironakaDisjointCompactExhaustionEscape
