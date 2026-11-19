import Hironaka.Resolution.HironakaOriginalActualEmptyNormalization
import Hironaka.Resolution.HironakaOriginalInvariantEmptyInsertion
import Hironaka.Resolution.HironakaG8NativeCommonMarkRank
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison
import Hironaka.Resolution.HironakaG8NativeSimultaneousCentre

/-! Rank comparison along two native windows at the same empty-history clock. -/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NativeUniformClockRank

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaG8LocalHistory HironakaOriginalActualEmptyNormalization HironakaOriginalInteriorEmptyHistory
  HironakaOriginalRecursiveBoundaryHistoryMap HironakaOriginalInvariantEmptyInsertion
  HironakaHolomorphicJetChartInvariance HironakaOriginalBoundaryEmptyFilterComparison
  MonomialInvariantEmptyMember

variable {n : ℕ} {X A B Y : CMfd.{0} n}

/-- Deletion of one real empty blowup, with the physical tower,
exact terminal cosupport and the whole chronological value shift. -/
structure EmptyStageReadout (hn : 0 < n) (k : ℕ) (M : MarkedIdeal n X)
    (H : BlowupTower X A) (π : B → A) (hπ : IsBlowupAlong n (∅ : Set A) π)
    (S : BlowupTower B Y) where
  target : CMfd.{0} n
  tail : BlowupTower A target
  back : target ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y
  same_length : tail.length = S.length
  physical : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
    (interiorEmptyHistory H tail) ((H.step ∅ π hπ).append S) back
  canonical : IsCanonical M ((invFamily hn k).inv M) (H.append tail)
  support : (geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp =
    back.symm ⁻¹' (geoTransformAlong M (H.append tail)).cosupp
  value : ∀ y ∈ (geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp,
    (invFamily hn k).inv M ((H.step ∅ π hπ).append S) y =
      recursiveHistoryShift k (M.E.length + H.length) ((invFamily hn k).inv M (H.append tail) (back.symm y))
  resolves : IsGeoResolution M ((H.step ∅ π hπ).append S) ↔ IsGeoResolution M (H.append tail)

/-- The actual canonical native window supplies all fields of the deletion. -/
theorem exists_empty_stage_readout (hn : 0 < n) (k : ℕ) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (H : BlowupTower X A) (π : B → A) (hπ : IsBlowupAlong n (∅ : Set A) π)
    (S : BlowupTower B Y)
    (hCan : IsCanonical M ((invFamily hn k).inv M) ((H.step ∅ π hπ).append S)) :
    Nonempty (EmptyStageReadout hn k M H π hπ S) := by
  obtain ⟨Y',S',χ,hLength,hPhysical,hCanonical,hSupport,hValue,hResolution⟩ :=
    original_recursive_family_actual_empty_deletion hn k M hM H π hπ S hCan
  exact ⟨⟨Y',S',χ,hLength,hPhysical,hCanonical,hSupport,hValue,hResolution⟩⟩

/-- Removing the same empty chronological slot in two independently
restricted native records preserves all comparisons of their active
values. Their actual empty maps and suffixes may be different. -/
theorem empty_stage_readout_comparisons (hn : 0 < n) (k : ℕ)
    {M : MarkedIdeal n X} {H : BlowupTower X A} {π : B → A}
    {hπ : IsBlowupAlong n (∅ : Set A) π} {S : BlowupTower B Y}
    (D : EmptyStageReadout hn k M H π hπ S)
    {X' A' B' Y' : CMfd.{0} n}
    {M' : MarkedIdeal n X'} {H' : BlowupTower X' A'} {π' : B' → A'}
    {hπ' : IsBlowupAlong n (∅ : Set A') π'} {S' : BlowupTower B' Y'}
    (D' : EmptyStageReadout hn k M' H' π' hπ' S')
    (hClock : M.E.length + H.length = M'.E.length + H'.length)
    {y : Y} (hy : y ∈ (geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp)
    {y' : Y'} (hy' : y' ∈ (geoTransformAlong M' ((H'.step ∅ π' hπ').append S')).cosupp) :
    let v := (invFamily hn k).inv M ((H.step ∅ π hπ).append S) y
    let w := (invFamily hn k).inv M' ((H'.step ∅ π' hπ').append S') y'
    let v₀ := (invFamily hn k).inv M (H.append D.tail) (D.back.symm y)
    let w₀ := (invFamily hn k).inv M' (H'.append D'.tail) (D'.back.symm y')
    (v < w ↔ v₀ < w₀) ∧ (v ≤ w ↔ v₀ ≤ w₀) ∧ (v = w ↔ v₀ = w₀) := by
  dsimp only
  rw [D.value y hy,D'.value y' hy',hClock]
  have hMono := strictMono_recursiveHistoryShift k (M'.E.length + H'.length)
  exact ⟨hMono.lt_iff_lt,hMono.le_iff_le,hMono.injective.eq_iff⟩

section InitialSlots

variable {G : Type}

open Classical

/-- The full ambient boundary is read on a native window before any
global empty slots are removed. -/
abbrev withMappedBoundary (M : MarkedIdeal n X) (f : Set G → Set X) (L : List (Set G)) :
    MarkedIdeal n X :=
  {M with E := L.map f}

private theorem mapped_insert_empty (M : MarkedIdeal n X) (f : Set G → Set X) (hf : f ∅ = ∅)
    (L : List (Set G)) (j : ℕ) :
    withMappedBoundary M f (L.insertIdx j ∅) = insertEmpty j (withMappedBoundary M f L) := by
  change ({M with E := (L.insertIdx j ∅).map f} : MarkedIdeal n X) =
    {M with E := (L.map f).insertIdx j ∅}
  rw [List.map_insertIdx,hf]

/-- Filtering only globally empty initial slots preserves the original
canonical history before or after restriction to a native window. -/
theorem canonical_mapped_global_empty_filter_iff (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (f : Set G → Set X) (hf : f ∅ = ∅) (L : List (Set G))
    (T : BlowupTower X Y) :
    let M₀ := withMappedBoundary M f (L.filter (fun B => decide B.Nonempty))
    let M₁ := withMappedBoundary M f L
    IsCanonical M₀ ((invFamily hn k).inv M₀) T ↔ IsCanonical M₁ ((invFamily hn k).inv M₁) T := by
  apply Iff.of_eq
  refine filter_value_of_empty_insertion
    (fun E => IsCanonical (withMappedBoundary M f E) ((invFamily hn k).inv (withMappedBoundary M f E)) T) ?_ L
  intro E j hj
  rw [mapped_insert_empty M f hf E j]
  exact propext (isCanonical_invFamily_insertEmpty_iff hn k (withMappedBoundary M f E)
    (by simpa only [List.length_map] using hj) T)

/-- The active cosupport is preserved when only the globally empty
initial slots are filtered on a literal native window. -/
theorem mapped_global_empty_filter_cosupp (M : MarkedIdeal n X) (f : Set G → Set X) (hf : f ∅ = ∅)
    (L : List (Set G)) (T : BlowupTower X Y) :
    (geoTransformAlong (withMappedBoundary M f (L.filter (fun B => decide B.Nonempty))) T).cosupp =
      (geoTransformAlong (withMappedBoundary M f L) T).cosupp := by
  refine filter_value_of_empty_insertion
    (fun E => (geoTransformAlong (withMappedBoundary M f E) T).cosupp) ?_ L
  intro E j hj
  rw [mapped_insert_empty M f hf E j]
  exact cosupp_geoTransformAlong_insertEmpty (withMappedBoundary M f E)
    (by simpa only [List.length_map] using hj) T

/-- All windows use the same global initial slot mask. The resulting
uniform clock change preserves strict cross-window order even when
different additional slots are empty on the individual windows. -/
theorem mapped_global_empty_filter_order_iff (hn : 0 < n) (k : ℕ)
    {X' Y' : CMfd.{0} n} (P : MarkedIdeal n X) (Q : MarkedIdeal n X')
    (f : Set G → Set X) (g : Set G → Set X') (hf : f ∅ = ∅) (hg : g ∅ = ∅)
    (L : List (Set G)) (T : BlowupTower X Y) (S : BlowupTower X' Y') (y : Y) (z : Y') :
    let L₀ := L.filter (fun B => decide B.Nonempty)
    ((invFamily hn k).inv (withMappedBoundary P f L₀) T y <
      (invFamily hn k).inv (withMappedBoundary Q g L₀) S z) ↔
    ((invFamily hn k).inv (withMappedBoundary P f L) T y <
      (invFamily hn k).inv (withMappedBoundary Q g L) S z) := by
  apply Iff.of_eq
  refine filter_value_of_empty_insertion (fun E =>
    (invFamily hn k).inv (withMappedBoundary P f E) T y <
      (invFamily hn k).inv (withMappedBoundary Q g E) S z) ?_ L
  intro E j hj
  rw [mapped_insert_empty P f hf E j,mapped_insert_empty Q g hg E j]
  exact propext (invFamily_insertEmpty_comparisons hn k (withMappedBoundary P f E)
    (by simpa only [List.length_map] using hj) T y (withMappedBoundary Q g E)
    (by simpa only [List.length_map] using hj) S z).1

end InitialSlots

section SimultaneousStages

open TopologicalSpace HironakaG8NativeSimultaneousCentre HironakaStageCenters

variable {I : Type} {U : I → Opens X}
variable {P Q : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))}
variable {k : ℕ} {Λ Λ' : Type} [LinearOrder Λ] [LinearOrder Λ']
variable {R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ}
variable {S : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ'}

/-- Strict order comparison across all active windows transports the
entire simultaneous maximum centre, even when the two value types differ. -/
theorem simultaneousCentre_of_same_order {T : BlowupTower X Y} {C : Set Y} {m : Λ}
    (hC : C.Nonempty) (h : NativeSimultaneousCentre R U P T C m)
    (hSupport : ∀ i, (geoTransformAlong (P i) (restrict (U i) T)).cosupp =
      (geoTransformAlong (Q i) (restrict (U i) T)).cosupp)
    (hOrder : ∀ i j (x : openPreimage T (U i)) (y : openPreimage T (U j)),
      x ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      y ∈ (geoTransformAlong (P j) (restrict (U j) T)).cosupp →
      (R.inv (P i) (restrict (U i) T) x < R.inv (P j) (restrict (U j) T) y ↔
        S.inv (Q i) (restrict (U i) T) x < S.inv (Q j) (restrict (U j) T) y)) :
    ∃ m', NativeSimultaneousCentre S U Q T C m' := by
  obtain ⟨q,hq⟩ := hC
  obtain ⟨j,hj⟩ := h.covered q hq
  let y : openPreimage T (U j) := ⟨q,hj⟩
  have hy := (Set.ext_iff.mp (h.trace j) y).mp hq
  refine ⟨S.inv (Q j) (restrict (U j) T) y,h.covered,?_,?_⟩
  · intro i x hx
    have hxP := hSupport i ▸ hx
    rw [← not_lt]
    intro hlt
    have hOld := (hOrder j i y x hy.1 hxP).mpr hlt
    exact (not_lt_of_ge (h.upper i x hxP)) (hy.2 ▸ hOld)
  · intro i
    ext x
    change _ ∈ C ↔
      x ∈ (geoTransformAlong (Q i) (restrict (U i) T)).cosupp ∧
        S.inv (Q i) (restrict (U i) T) x = S.inv (Q j) (restrict (U j) T) y
    rw [← hSupport i]
    change x ∈ (Subtype.val : openPreimage T (U i) → Y) ⁻¹' C ↔ _
    rw [h.trace]
    change (_ ∧ _) ↔ (_ ∧ _)
    refine and_congr_right fun hx => ?_
    rw [← hy.2]
    simp only [le_antisymm_iff, ← not_lt]
    exact and_congr (not_congr (hOrder j i y x hy.1 hx))
      (not_congr (hOrder i j x y hx hy.1))

/-- A shared cross-window order recoding at every actual prefix
preserves the retained simultaneous-stage certificate of the literal tower. -/
theorem simultaneousStages_of_same_order
    (hSupport : ∀ {Y' : CMfd.{0} n} (T : BlowupTower X Y') i,
      (geoTransformAlong (P i) (restrict (U i) T)).cosupp =
        (geoTransformAlong (Q i) (restrict (U i) T)).cosupp)
    (hOrder : ∀ {Y' : CMfd.{0} n} (T : BlowupTower X Y') i j
      (x : openPreimage T (U i)) (y : openPreimage T (U j)),
      x ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
      y ∈ (geoTransformAlong (P j) (restrict (U j) T)).cosupp →
      (R.inv (P i) (restrict (U i) T) x < R.inv (P j) (restrict (U j) T) y ↔
        S.inv (Q i) (restrict (U i) T) x < S.inv (Q j) (restrict (U j) T) y))
    (T : BlowupTower X Y) (h : NativeSimultaneousStages R U P T) :
    NativeSimultaneousStages S U Q T := by
  induction T with
  | refl => trivial
  | step T C p hp ih =>
    refine ⟨ih h.1,?_⟩
    by_cases hEmpty : C = ∅
    · exact Or.inl hEmpty
    · obtain ⟨m,hm⟩ := h.2.resolve_left hEmpty
      exact Or.inr (simultaneousCentre_of_same_order (Set.nonempty_iff_ne_empty.mpr hEmpty)
        hm (hSupport T) (hOrder T))

end SimultaneousStages

end
end Hironaka.HironakaG8NativeUniformClockRank
