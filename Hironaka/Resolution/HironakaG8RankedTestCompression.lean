import Hironaka.Resolution.HironakaG8RankOccupiedAnnotation
import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareOpenRestriction

/-! Empty-free actual TEST compression with inherited event ranks. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8RankedTestCompression
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters HironakaG8EmptyAwareTestTransport
  HironakaG8CofinalOccupiedAncestry HironakaG8RankOccupiedAnnotation
  HironakaG8RankedEmptyPadding HironakaG8OccupiedSlotComparison
  HironakaG3EmptyAwareHistory G3UniverseEmptyAwareOpenRestriction BlowupTowerIsomorphism
  HironakaSharpActualCurveEmptyPadding MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal

variable {n : ℕ} {X Y A B : CMfd.{0} n}

theorem occupied_of_empty_free (T : BlowupTower X Y)
    (h : StageCentres (fun _ C => C.Nonempty) T) :
    ∀ i : Fin T.length, Occupied T i.val := by
  induction T with
  | refl => exact fun i => Fin.elim0 i
  | step T C π hπ ih =>
    intro i
    by_cases he : i.val = T.length
    · exact Or.inr ⟨he,h.2⟩
    · have hi := i.isLt
      change i.val < T.length+1 at hi
      exact Or.inl (ih h.1 ⟨i.val,by omega⟩)

/-- With no empty raw steps, raw indices and occupied indices agree
literally, in their original order. -/
def rawOccupiedIso (T : BlowupTower X Y)
    (h : StageCentres (fun _ C => C.Nonempty) T) :
    Fin T.length ≃o {i // Occupied T i} := by
  let f (i : Fin T.length) : {k // Occupied T k} :=
    ⟨i.val,occupied_of_empty_free T h i⟩
  have hMono : StrictMono f := fun _ _ hij => hij
  have hSurj : Function.Surjective f := fun i =>
    ⟨⟨i.val,occupied_lt_length T i.property⟩,Subtype.ext rfl⟩
  exact hMono.orderIsoOfSurjective f hSurj

@[simp] theorem rawOccupiedIso_val (T : BlowupTower X Y)
    (h : StageCentres (fun _ C => C.Nonempty) T) (i : Fin T.length) :
    (rawOccupiedIso T h i).val = i.val := rfl

/-- The raw clock of an empty-free compression reads the occupied
clock of the original physical tower. -/
def compressedRawOccupiedIso
    {Q : BlowupTower X A} {T : BlowupTower X Y}
    {e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hQ : StageCentres (fun _ C => C.Nonempty) Q)
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T e) :
    Fin Q.length ≃o {i // Occupied T i} :=
  (rawOccupiedIso Q hQ).trans (occupiedComparison h)

theorem slotFootprint_compressedRawOccupiedIso
    {Q : BlowupTower X A} {T : BlowupTower X Y}
    {e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hQ : StageCentres (fun _ C => C.Nonempty) Q)
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T e)
    (i : Fin Q.length) :
    slotFootprint Q i.val = slotFootprint T (compressedRawOccupiedIso hQ h i).val := by
  simpa only [compressedRawOccupiedIso,OrderIso.trans_apply,rawOccupiedIso_val,
    Diffeomorph.coe_refl,preimage_id] using slotFootprint_occupiedComparison h (rawOccupiedIso Q hQ i)

/-- The physical compression retains the original endpoint and its
compared occupied event ranks, together with exact original TEST. -/
structure RankedTestCompression (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (rank : {k // Occupied T k} → ℕ) where
  target : CMfd.{0} n
  tower : BlowupTower X target
  endpoint : target ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y
  comparison : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) tower T endpoint
  occupied : StageCentres (fun _ C => C.Nonempty) tower
  test : IsGeoTestTower M tower
  clock : ℕ
  decoration : RankedTower X tower clock
  rank_eq : ∀ p : {k // Occupied tower k},
    assignedSlot decoration p.val = rank (occupiedComparison comparison p)

/-- Every actual well-formed TEST chart admits the rank decoration after
its internally constructed physical empty-step compression. -/
theorem exists_ranked_test_compression (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (rank : {k // Occupied T k} → ℕ) (hRank : StrictMono rank) :
    Nonempty (RankedTestCompression M T rank) := by
  obtain ⟨Z,Q,χ,hOcc,_,hCmp,hTest⟩ := test_empty_free_compression M hM T
  obtain ⟨k,D,hD⟩ := exists_rankedTower_of_occupied_ranks Q
    (occupied_of_empty_free Q hOcc) (rank ∘ occupiedComparison hCmp)
    (hRank.comp (occupiedComparison hCmp).strictMono)
  exact ⟨⟨Z,Q,χ,hCmp,hOcc,hTest.mpr hT,k,D,hD⟩⟩

private theorem emptyAware_append_real_identity
    {T S : BlowupTower X Y}
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T S
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞)) (k : ℕ) :
    EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      (T.append (identityEmptyTail Y k)) S (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hb := EmptyAwareTowerIso.leftEmpty ih BlowupExistenceCodimOne.isBlowupAlong_id_empty
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) (fun _ => rfl)
    simpa only [Diffeomorph.refl_trans,identityEmptyTail,BlowupTower.append_step] using hb

private theorem ranked_pad_emptyAware {T : BlowupTower X Y} {k : ℕ} (D : RankedTower X T k) :
    EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) D.pad T
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) := by
  induction D with
  | refl => exact .refl
  | @step V W T i r D hi C π hπ ih =>
    exact .step (emptyAware_append_real_identity ih (r-i)) hπ hπ
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) W ∞) (fun _ => rfl) rfl

/-- Padding an actual rank decoration retains the original TEST. -/
theorem test_ranked_through (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {T : BlowupTower X Y} (hT : IsGeoTestTower M T) {k : ℕ}
    (D : RankedTower X T k) (N : ℕ) : IsGeoTestTower M (D.through N) := by
  let e := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have h := emptyAware_append_real_identity (ranked_pad_emptyAware D) (N-k)
  have hTest := (isGeoTestTower_iff_of_emptyAware M hM e h).mpr hT
  have hId : MarkedIdeal.pullback e M = M := ContactCanonicalAlong.pullback_id M hM.isCoherent
  rwa [hId] at hTest

/-- Compressing each literal nested chart and padding by a common event
rank produces the strict comparison. Original TEST is retained in each
compression; no original raw slot assignment is needed. -/
theorem strict_nested_overlap_after_test_compression
    {M : MarkedIdeal n X} {N : MarkedIdeal n A}
    {T : BlowupTower X Y} {S : BlowupTower A B}
    {rankT : {k // Occupied T k} → ℕ} {rankS : {k // Occupied S k} → ℕ}
    (dT : RankedTestCompression M T rankT) (dS : RankedTestCompression N S rankS)
    (V : Opens A)
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S V)}
    (h : EmptyAwareTowerIso φ T (restrict V S) ψ)
    (hRank : ∀ p, rankT p = rankS (occupiedLiftOnOpen V S h p))
    (k : ℕ) (hT : dT.clock ≤ k) (hS : dS.clock ≤ k) :
    ∃ χ : dT.target ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (dS.decoration.through k) V),
      IsTowerIso φ (dT.decoration.through k) (restrict V (dS.decoration.through k)) χ := by
  have hLeft := G3UniverseEmptyAwareCore.trans dT.comparison h
  have hRight := emptyAware_open_restriction dS.comparison V
  have hNew := G3UniverseEmptyAwareCore.trans hLeft (G3UniverseEmptyAwareCore.symm hRight)
  have hRB : occupiedLiftOnOpen V S hRight =
      (occupiedRestrictionEmbedding V dS.tower).trans
        (occupiedComparison dS.comparison).toOrderEmbedding :=
    occupiedComparison_restrict_natural dS.comparison V V rfl hRight
  have hRanks : ∀ p : {k // Occupied dT.tower k},
      assignedSlot dT.decoration p.val =
        assignedSlot dS.decoration (occupiedLiftOnOpen V dS.tower hNew p).val := by
    intro p
    have hOld := congrArg (fun u : {k // Occupied dT.tower k} ≃o
      {k // Occupied (restrict V S) k} => u p)
      (occupiedComparison_comp dT.comparison h hLeft)
    have hComp := congrArg (fun u : {k // Occupied dT.tower k} ≃o
      {k // Occupied (restrict V S) k} => u p)
      (occupiedComparison_comp hNew hRight hLeft)
    have hVis := congrArg (fun u : {k // Occupied (restrict V dS.tower) k} ↪o
      {k // Occupied S k} => u (occupiedComparison hNew p)) hRB
    have hOld' : occupiedComparison h (occupiedComparison dT.comparison p) =
        occupiedComparison hRight (occupiedComparison hNew p) := hOld.trans hComp.symm
    have hMatch : occupiedLiftOnOpen V S h (occupiedComparison dT.comparison p) =
        occupiedComparison dS.comparison (occupiedLiftOnOpen V dS.tower hNew p) := by
      calc
        _ = occupiedLiftOnOpen V S hRight (occupiedComparison hNew p) :=
          Subtype.ext (congrArg (fun x : {k // Occupied (restrict V S) k} => x.val) hOld')
        _ = _ := hVis
    calc
      _ = rankT (occupiedComparison dT.comparison p) := dT.rank_eq p
      _ = rankS (occupiedLiftOnOpen V S h (occupiedComparison dT.comparison p)) := hRank _
      _ = rankS (occupiedComparison dS.comparison (occupiedLiftOnOpen V dS.tower hNew p)) :=
        congrArg rankS hMatch
      _ = _ := (dS.rank_eq _).symm
  obtain ⟨χ,hχ⟩ := strict_padded_nested_overlap_of_agreeing_occupied_slots
    dT.decoration dS.decoration V hNew hRanks k hT hS
  exact ⟨χ,BlowupTowerSplitIso.IsTowerIso.congr_base hχ (Φ' := φ) (fun _ => rfl)⟩


end
end Hironaka.HironakaG8RankedTestCompression
