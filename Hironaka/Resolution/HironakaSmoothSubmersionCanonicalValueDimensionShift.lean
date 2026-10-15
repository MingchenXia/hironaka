/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionAllBranchHistory
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Invariant.MonomialInvariantEmptyMember
/-! # Actual ambient shifts on original recursive value types

Adding the actual fibre dimension to the first original monomial key
coordinate retains every whole colex index and gives the exact original
gammaAlong formula on actual smooth test histories. Strict maps on every
UNCHANGED original ValTy are constructed recursively. Comparing actual
whole invFamily values along arbitrary smooth histories remains further
work; no such value certificate or old definition change is introduced.
Complete mathematics preceded proofs in `Mathematics.tex`.
Blueprint: `hironaka-smooth-submersion-canonical-value-dimension-shift-extension.tex`.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionCanonicalValueDimensionShift
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MonomialInvariant MonomialInvariantEmptyMember CanonicalCentres DivisorExponentAlong BlowupTowers
  MonomialCaseAlong MonomialCase MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowerTransforms
  HironakaSmoothSubmersionMonomialOrdering HironakaSmoothSubmersionRelativeMonomial
  HironakaSmoothSubmersionCoefficientIdeals NormalCrossings

def dimensionKey (t : ℕ) (v : Val) : Val :=
  toLex ((ofLex v).1+t,(ofLex v).2)

theorem strictMono_dimensionKey (t : ℕ) : StrictMono (dimensionKey t) := by
  intro a b hab
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases Prod.Lex.toLex_lt_toLex.mp hab with h | ⟨h,h'⟩
  · exact Or.inl (Nat.add_lt_add_right h t)
  · exact Or.inr ⟨congrArg (fun x => x+t) h,h'⟩

def dimensionValue (t : ℕ) : WithBot Val → WithBot Val := WithBot.map (dimensionKey t)

theorem strictMono_dimensionValue (t : ℕ) : StrictMono (dimensionValue t) :=
  (strictMono_dimensionKey t).withBot_map

theorem dimensionKey_key (n t : ℕ) (a : ℕ → ℕ) (K : Finset ℕ) (hK : K.card ≤ n) :
    dimensionKey t (key n a K) = key (n+t) a K := by
  unfold dimensionKey key
  simp only [ofLex_toLex]
  rw [show n+t-K.card = n-K.card+t by omega]

/-- The whole original feasible maximum has the exact ambient dimension
shift, including bottom, and every actual indexed colex member set. -/
theorem inv_dimension_shift (n t : ℕ) (S : Finset ℕ) (a : ℕ → ℕ) (d : ℕ)
    (hS : S.card ≤ n) : inv (n+t) S a d = dimensionValue t (inv n S a d) := by
  classical
  have himage : (feasible S a d).image (key (n+t) a) =
      ((feasible S a d).image (key n a)).image (dimensionKey t) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro K hK
    exact (dimensionKey_key n t a K
      ((Finset.card_le_card (mem_feasible.mp hK).1).trans hS)).symm
  unfold inv
  rw [himage,max_image_of_monotone (strictMono_dimensionKey t).monotone]
  rfl

/-- The original actual smooth map and original coherent SNC data supply
all cardinality and fibre-dimension bounds internally for exact gamma. -/
theorem gammaAlong_preimage_dimension_shift {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m}
    {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) (N : Set X) (E : List (Set X))
    (hE : IsSNCDivisor n E) (d : ℕ) (y : Y) :
    gammaAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d y =
      dimensionValue (m-n) (gammaAlong n N I E d (f y)) := by
  rw [gammaAlong_preimage_dictionary hf hI N E d y]
  have hdim : m = n+(m-n) := (Nat.add_sub_of_le (dimension_le_of_submersionAt (hf.isSubmersionAt y))).symm
  change inv m (memberIdx E (f y)) (expDataAlong n N I E (f y)) d =
    dimensionValue (m-n) (inv n (memberIdx E (f y)) (expDataAlong n N I E (f y)) d)
  conv_lhs => rw [hdim]
  exact inv_dimension_shift n (m-n) _ _ d (MonomialCase.card_memberIdx_le E hE (f y))

/-- The strict depth-zero seed; it does not assert a nonvacuous comparison
of actual invariants on a dimension-zero cosupport. -/
def seedDimension : (t : ℕ) → ℕ → ValTy t
  | 0 => id
  | _t+1 => fun x => toLex (x,toLex (Sum.inl (⊥ : WithBot Val)))

theorem strictMono_seedDimension : ∀ t : ℕ, StrictMono (seedDimension t)
  | 0 => strictMono_id
  | _+1 => by
    intro a b hab
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)

def stepDimensionMap {α β : Type*} (f : α → β) (v : ℕ ×ₗ WithTop α) : ℕ ×ₗ WithTop β :=
  toLex ((ofLex v).1,WithTop.map f (ofLex v).2)

theorem strictMono_stepDimensionMap {α β : Type*} [LinearOrder α] [LinearOrder β]
    {f : α → β} (hf : StrictMono f) : StrictMono (stepDimensionMap f) := by
  intro a b hab
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases Prod.Lex.toLex_lt_toLex.mp hab with h | ⟨h,h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,hf.withTop_map h'⟩

def generalDimensionMap {α β : Type*} (t : ℕ) (f : α → β)
    (v : ℕ ×ₗ (WithBot Val ⊕ₗ WithTop α)) : ℕ ×ₗ (WithBot Val ⊕ₗ WithTop β) :=
  toLex ((ofLex v).1,toLex (Sum.map (dimensionValue t) (WithTop.map f) (ofLex (ofLex v).2)))

theorem strictMono_generalDimensionMap {α β : Type*} [LinearOrder α] [LinearOrder β]
    (t : ℕ) {f : α → β} (hf : StrictMono f) : StrictMono (generalDimensionMap t f) := by
  have hs : ∀ a b : WithBot Val ⊕ WithTop α, toLex a < toLex b →
      toLex (Sum.map (dimensionValue t) (WithTop.map f) a) <
        toLex (Sum.map (dimensionValue t) (WithTop.map f) b) := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        exact Sum.Lex.inl_lt_inl_iff.mpr
          ((strictMono_dimensionValue t) (Sum.Lex.inl_lt_inl_iff.mp hab))
      | inr b => exact Sum.Lex.inl_lt_inr _ _
    | inr a =>
      cases b with
      | inl b => exact False.elim (Sum.Lex.not_inr_lt_inl hab)
      | inr b =>
        exact Sum.Lex.inr_lt_inr_iff.mpr
          (hf.withTop_map (Sum.Lex.inr_lt_inr_iff.mp hab))
  intro a b hab
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases Prod.Lex.toLex_lt_toLex.mp hab with h | ⟨h,h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,hs _ _ h'⟩

/-- Explicit fibre-dimension maps on the UNCHANGED original recursive
value types. Actual whole-family smooth comparison is a further theorem. -/
def familyDimensionMap (t : ℕ) : (k : ℕ) → ValTy k → ValTy (t+k)
  | 0 => seedDimension t
  | k+1 => generalDimensionMap t (stepDimensionMap (familyDimensionMap t k))

theorem strictMono_familyDimensionMap (t : ℕ) :
    ∀ k : ℕ, StrictMono (familyDimensionMap t k)
  | 0 => strictMono_seedDimension t
  | k+1 => strictMono_generalDimensionMap t
      (strictMono_stepDimensionMap (strictMono_familyDimensionMap t k))

def familyDimensionEmbedding (t k : ℕ) : ValTy k ↪o ValTy (t+k) :=
  OrderEmbedding.ofStrictMono (familyDimensionMap t k) (strictMono_familyDimensionMap t k)

theorem familyDimensionMap_comparisons (t k : ℕ) (v w : ValTy k) :
    (familyDimensionMap t k v < familyDimensionMap t k w ↔ v < w) ∧
    (familyDimensionMap t k v ≤ familyDimensionMap t k w ↔ v ≤ w) ∧
    (familyDimensionMap t k v = familyDimensionMap t k w ↔ v = w) :=
  ⟨(strictMono_familyDimensionMap t k).lt_iff_lt,
    (strictMono_familyDimensionMap t k).le_iff_le,
    (strictMono_familyDimensionMap t k).injective.eq_iff⟩

/-- At every actual original test stage, the entire literal gamma has its
exact ambient shift; original test data supply all stage conditions. -/
theorem IsActualTowerPullback.gammaAlong_stage_dimension_shift
    {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : HironakaSmoothSubmersionCartesianTower.IsActualTowerPullback f Q T g)
    (M : MarkedIdeals.MarkedIdeal n X) (hM : M.IsWellFormed)
    (hT : M.IsGeoTestTower T) (z : D') :
    MonomialCaseAlong.gammaAlong m
      (geoTransformAlong (markedPullback (m := m) f M) Q).N
      (geoTransformAlong (markedPullback (m := m) f M) Q).ideal
      (geoTransformAlong (markedPullback (m := m) f M) Q).E
      (geoTransformAlong (markedPullback (m := m) f M) Q).d z =
      dimensionValue (m-n) (MonomialCaseAlong.gammaAlong n
        (geoTransformAlong M T).N
        (geoTransformAlong M T).ideal
        (geoTransformAlong M T).E
        (geoTransformAlong M T).d (g z)) := by
  have hMT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT
  rw [(HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
    h M hM hT).2]
  exact gammaAlong_preimage_dimension_shift h.isSubmersion hMT.isCoherent _ _ hMT.isSNCDivisor _ z

end
end Hironaka.HironakaSmoothSubmersionCanonicalValueDimensionShift
