import Hironaka.Resolution.HironakaActualIteratedRelativeNormalHistory

/-! Compatibility of normal flags with ambient shifts and recursive depth padding. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Hironaka.HironakaG1NormalValueMaps

open Set

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantExt
  CanonicalCentres MonomialInvariant
  HironakaActualSectionBoundaryDimension HironakaOriginalFamilyDepthStability
  HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaDisjointCoherentNormalRecoding HironakaActualIteratedRelativeNormalHistory

private theorem dimensionValue_add (a b : ℕ) (v : WithBot Val) :
    dimensionValue b (dimensionValue a v) = dimensionValue (a + b) v := by
  change WithBot.map (dimensionKey b) (WithBot.map (dimensionKey a) v) = _
  rw [WithBot.map_map]
  congr 1
  funext x
  simp only [Function.comp_apply, dimensionKey, ofLex_toLex, Nat.add_assoc]

private theorem stepDimensionMap_comp {α β γ : Type} (f : β → γ) (g : α → β)
    (v : ℕ ×ₗ WithTop α) :
    stepDimensionMap f (stepDimensionMap g v) = stepDimensionMap (f ∘ g) v := by
  simp only [stepDimensionMap, ofLex_toLex, WithTop.map_map]

private theorem generalDimensionMap_comp {α β γ : Type} (a b : ℕ)
    (f : β → γ) (g : α → β) (v : ℕ ×ₗ (WithBot Val ⊕ₗ WithTop α)) :
    generalDimensionMap b f (generalDimensionMap a g v) =
      generalDimensionMap (a + b) (f ∘ g) v := by
  unfold generalDimensionMap
  simp only [ofLex_toLex]
  cases ofLex (ofLex v).2 with
  | inl w => simp only [Sum.map_inl, dimensionValue_add]
  | inr w => simp only [Sum.map_inr, WithTop.map_map]

/-- Changing ambient dimension twice gives the sum of the shifts at fixed recursive depth. -/
theorem sameIndexMap_add (a b : ℕ) : ∀ (q : ℕ) (v : ValTy q),
    sameIndexMap b q (sameIndexMap a q v) = sameIndexMap (a + b) q v
  | 0, _ => rfl
  | q + 1, v => by
      change generalDimensionMap b (stepDimensionMap (sameIndexMap b q))
        (generalDimensionMap a (stepDimensionMap (sameIndexMap a q)) v) = _
      rw [generalDimensionMap_comp]
      have hStep : stepDimensionMap (sameIndexMap b q) ∘
          stepDimensionMap (sameIndexMap a q) =
          stepDimensionMap (sameIndexMap (a + b) q) := by
        funext w
        rw [Function.comp_apply, stepDimensionMap_comp,
          show sameIndexMap b q ∘ sameIndexMap a q = sameIndexMap (a + b) q from
            funext (sameIndexMap_add a b q)]
      rw [hStep]
      rfl

/-- A recursive depth change commutes with a dimension shift, even when their sizes differ. -/
theorem depthPadMap_commutes_sameIndexMap (h t : ℕ) :
    ∀ (q : ℕ) (v : ValTy q),
      depthPadMap h q (sameIndexMap t q v) = sameIndexMap t (h + q) (depthPadMap h q v)
  | 0, v => by
      cases h with
      | zero => rfl
      | succ h =>
        change _ = generalDimensionMap t (stepDimensionMap (sameIndexMap t h)) (seedDimension (h + 1) v)
        rfl
  | q + 1, v => by
      change generalDimensionMap 0 (stepDimensionMap (depthPadMap h q))
          (generalDimensionMap t (stepDimensionMap (sameIndexMap t q)) v) =
        generalDimensionMap t (stepDimensionMap (sameIndexMap t (h + q)))
          (generalDimensionMap 0 (stepDimensionMap (depthPadMap h q)) v)
      rw [generalDimensionMap_comp, generalDimensionMap_comp, Nat.add_zero, Nat.zero_add]
      have hMap : depthPadMap h q ∘ sameIndexMap t q =
          sameIndexMap t (h + q) ∘ depthPadMap h q :=
        funext (depthPadMap_commutes_sameIndexMap h t q)
      have hStep : stepDimensionMap (depthPadMap h q) ∘ stepDimensionMap (sameIndexMap t q) =
          stepDimensionMap (sameIndexMap t (h + q)) ∘ stepDimensionMap (depthPadMap h q) := by
        funext w
        simp only [Function.comp_apply, stepDimensionMap_comp, hMap]
      rw [hStep]

private theorem depthPadMap_initialEmbedding (h q : ℕ) (v : ValTy q) :
    depthPadMap h (q + 1) (initialEmbedding q v) =
      initialEmbedding (h + q) (depthPadMap h q v) := by
  rfl

/-- Padding before or after an actual one-coordinate normal increment has the same value. -/
theorem depthPadMap_normal_increment (h q : ℕ) (v : ValTy q) :
    depthPadMap h (q + 1) (initialEmbedding q (sameIndexMap 1 q v)) =
      initialEmbedding (h + q) (sameIndexMap 1 (h + q) (depthPadMap h q v)) := by
  rw [depthPadMap_initialEmbedding, depthPadMap_commutes_sameIndexMap]

private theorem cast_normal_increment {a b : ℕ} (e : a = b) (v : ValTy a) :
    cast (congrArg ValTy (congrArg Nat.succ e)) (initialEmbedding a (sameIndexMap 1 a v)) =
      initialEmbedding b (sameIndexMap 1 b (cast (congrArg ValTy e) v)) := by
  cases e
  rfl

/-- The comparison for an actual finite normal flag is independent of when the
original recursive depth bound is enlarged. The cast only reassociates the depths. -/
theorem depthPadMap_iteratedValueEmbedding (h q r : ℕ) (v : ValTy q) :
    cast (congrArg ValTy (Nat.add_assoc h q r).symm)
        (depthPadMap h (q + r) (iteratedValueEmbedding q r v)) =
      iteratedValueEmbedding (h + q) r (depthPadMap h q v) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [iteratedValueEmbedding, iteratedValueEmbedding]
      refine (congrArg (cast (congrArg ValTy (Nat.add_assoc h q (r + 1)).symm))
        (depthPadMap_normal_increment h (q + r) (iteratedValueEmbedding q r v))).trans ?_
      have hCast : (Nat.add_assoc h q (r + 1)).symm =
          congrArg Nat.succ (Nat.add_assoc h q r).symm := Subsingleton.elim _ _
      rw [hCast]
      exact (cast_normal_increment (Nat.add_assoc h q r).symm
        (depthPadMap h (q + r) (iteratedValueEmbedding q r v))).trans
          (congrArg (fun w => initialEmbedding ((h + q) + r)
            (sameIndexMap 1 ((h + q) + r) w)) ih)

/-- Lift an actual canonical normal-flag comparison to a larger recursive bound
on both original histories. Neither history or its point map has to be rebuilt. -/
theorem paddedCanonicalNormalFlag {n m : ℕ} {X Y : CMfd.{0} n} {A B : CMfd.{0} m}
    (hn : 0 < n) (hm : 0 < m) (h q r : ℕ)
    (M : MarkedIdeal n X) (L : MarkedIdeal m A)
    (hM : IsInvDomain q M) (hL : IsInvDomain (q + r) L)
    (T : BlowupTower X Y) (P : BlowupTower A B) (j : Y → B)
    (hCanT : IsCanonical M ((invFamily hn q).inv M) T)
    (hCanP : IsCanonical L ((invFamily hm (q + r)).inv L) P)
    (hCos : ∀ y ∈ (geoTransformAlong M T).cosupp, j y ∈ (geoTransformAlong L P).cosupp)
    (hVal : ∀ y ∈ (geoTransformAlong M T).cosupp,
      (invFamily hm (q + r)).inv L P (j y) =
        iteratedValueEmbedding q r ((invFamily hn q).inv M T y)) :
    IsCanonical M ((invFamily hn (h + q)).inv M) T ∧
      IsCanonical L ((invFamily hm (h + (q + r))).inv L) P ∧
      ∀ y ∈ (geoTransformAlong M T).cosupp,
        cast (congrArg ValTy (Nat.add_assoc h q r).symm)
            ((invFamily hm (h + (q + r))).inv L P (j y)) =
          iteratedValueEmbedding (h + q) r ((invFamily hn (h + q)).inv M T y) := by
  obtain ⟨hCanT', hValT'⟩ := original_family_depth_stability hn h q M hM T hCanT
  obtain ⟨hCanP', hValP'⟩ := original_family_depth_stability hm h (q + r) L hL P hCanP
  refine ⟨hCanT', hCanP', fun y hy => ?_⟩
  rw [hValP' (j y) (hCos y hy), hVal y hy, hValT' y hy]
  exact depthPadMap_iteratedValueEmbedding h q r _

private theorem strictMono_castValTy {a b : ℕ} (e : a = b) :
    StrictMono (cast (congrArg ValTy e)) := by
  cases e
  exact strictMono_id

/-- At enlarged depth, the actual map of normal-flag endpoints reflects strict
and weak order and equality on the cosupport, and carries the full maximum locus. -/
theorem paddedCanonicalNormalFlag_comparisons {n m : ℕ}
    {X Y : CMfd.{0} n} {A B : CMfd.{0} m}
    (hn : 0 < n) (hm : 0 < m) (h q r : ℕ)
    (M : MarkedIdeal n X) (L : MarkedIdeal m A)
    (hM : IsInvDomain q M) (hL : IsInvDomain (q + r) L)
    (T : BlowupTower X Y) (P : BlowupTower A B) (j : Y → B)
    (hCanT : IsCanonical M ((invFamily hn q).inv M) T)
    (hCanP : IsCanonical L ((invFamily hm (q + r)).inv L) P)
    (hImage : j '' (geoTransformAlong M T).cosupp = (geoTransformAlong L P).cosupp)
    (hVal : ∀ y ∈ (geoTransformAlong M T).cosupp,
      (invFamily hm (q + r)).inv L P (j y) =
        iteratedValueEmbedding q r ((invFamily hn q).inv M T y)) :
    let S := (geoTransformAlong M T).cosupp
    let D := (geoTransformAlong L P).cosupp
    let f := (invFamily hn (h + q)).inv M T
    let g := (invFamily hm (h + (q + r))).inv L P
    (∀ y ∈ S, ∀ z ∈ S,
      (g (j y) < g (j z) ↔ f y < f z) ∧
      (g (j y) ≤ g (j z) ↔ f y ≤ f z) ∧
      (g (j y) = g (j z) ↔ f y = f z)) ∧
    ResolutionDriver.maxLocus g D = j '' ResolutionDriver.maxLocus f S := by
  let S := (geoTransformAlong M T).cosupp
  let D := (geoTransformAlong L P).cosupp
  have hCos : ∀ y ∈ S, j y ∈ D := by
    intro y hy
    change j y ∈ (geoTransformAlong L P).cosupp
    rw [← hImage]
    exact mem_image_of_mem j hy
  obtain ⟨_, _, hValue⟩ :=
    paddedCanonicalNormalFlag hn hm h q r M L hM hL T P j hCanT hCanP hCos hVal
  let f := (invFamily hn (h + q)).inv M T
  let g := (invFamily hm (h + (q + r))).inv L P
  have hCast := strictMono_castValTy (Nat.add_assoc h q r).symm
  have hFlag := strictMono_iteratedValueEmbedding (h + q) r
  have hCompare : ∀ y ∈ S, ∀ z ∈ S,
      (g (j y) < g (j z) ↔ f y < f z) ∧
      (g (j y) ≤ g (j z) ↔ f y ≤ f z) ∧
      (g (j y) = g (j z) ↔ f y = f z) := by
    intro y hy z hz
    refine ⟨hCast.lt_iff_lt.symm.trans ?_, hCast.le_iff_le.symm.trans ?_,
      hCast.injective.eq_iff.symm.trans ?_⟩
    · exact (hValue y hy) ▸ (hValue z hz) ▸ hFlag.lt_iff_lt
    · exact (hValue y hy) ▸ (hValue z hz) ▸ hFlag.le_iff_le
    · exact (hValue y hy) ▸ (hValue z hz) ▸ hFlag.injective.eq_iff
  refine ⟨hCompare, ?_⟩
  ext b
  constructor
  · intro hb
    obtain ⟨y, hy, rfl⟩ : b ∈ j '' S := hImage ▸ hb.1
    exact ⟨y, ⟨hy, fun z hz => (hCompare z hz y hy).2.1.mp (hb.2 (j z) (hCos z hz))⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hCos y hy.1, fun b hb => ?_⟩
    obtain ⟨z, hz, rfl⟩ : b ∈ j '' S := hImage ▸ hb
    exact (hCompare z hz y hy.1).2.1.mpr (hy.2 z hz)

end Hironaka.HironakaG1NormalValueMaps
