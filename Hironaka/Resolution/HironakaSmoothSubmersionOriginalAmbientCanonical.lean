/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalRecursiveFamily
/-! Literal ambient canonical invariants under actual smooth pullback.

The unchanged original family is specialized using genuine dimension equality
only at actual source points. Whole canonical histories include ambient-zero
and empty-source cases. Complete four-node mathematics preceded these proofs.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalAmbientCanonical
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaSmoothSubmersionOriginalZeroFamilyHistory
  HironakaSmoothSubmersionOriginalRecursiveFamily
  HironakaSmoothSubmersionMonomialOrdering
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- Only the actual positive ambient definition is unfolded. -/
theorem canonicalInvariant_eq_invFamily (hn : 0 < n) :
    canonicalInvariant.{u} n = invFamily hn n := by
  cases n with
  | zero => omega
  | succ n => rfl

/-- Arithmetic transport retains the unchanged recursively ordered value type. -/
def ambientDimensionMap (hnm : n ≤ m) (v : ValTy n) : ValTy m :=
  cast (congrArg ValTy (Nat.sub_add_cancel hnm)) (familyDimensionMap (m-n) n v)

private theorem strictMono_valTy_cast {a b : ℕ} (hab : a = b) :
    StrictMono (cast (congrArg ValTy hab)) := by
  subst b
  exact strictMono_id

theorem strictMono_ambientDimensionMap (hnm : n ≤ m) :
    StrictMono (ambientDimensionMap hnm) :=
  (strictMono_valTy_cast (Nat.sub_add_cancel hnm)).comp (strictMono_familyDimensionMap (m-n) n)

theorem ambientDimensionMap_comparisons (hnm : n ≤ m) (v w : ValTy n) :
    (ambientDimensionMap hnm v < ambientDimensionMap hnm w ↔ v < w) ∧
    (ambientDimensionMap hnm v ≤ ambientDimensionMap hnm w ↔ v ≤ w) ∧
    (ambientDimensionMap hnm v = ambientDimensionMap hnm w ↔ v = w) :=
  ⟨(strictMono_ambientDimensionMap hnm).lt_iff_lt,
    (strictMono_ambientDimensionMap hnm).le_iff_le,
    (strictMono_ambientDimensionMap hnm).injective.eq_iff⟩

private theorem cast_invFamily_value (hm : 0 < m) {a b : ℕ} (hab : a = b)
    (M : MarkedIdeal m Y) (Q : BlowupTower Y D') (z : D') :
    cast (congrArg ValTy hab) ((invFamily hm a).inv M Q z) =
      (invFamily hm b).inv M Q z := by
  subst b
  rfl

/-- Ambient bounds are proved at actual source points, including an empty source. -/
theorem original_ambient_domain_pullback
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    IsInvDomain m (markedPullback (m := m) f M) := by
  have hd := isInvDomain_markedPullback_submersion hf M hM
  refine ⟨hd.isWellFormed,?_,hd.one_le_d,hd.isNonzeroAlongAt⟩
  intro y hy
  have hnm := dimension_le_of_submersionAt (hf.isSubmersionAt y)
  have he : n+(m-n)=m := Nat.add_sub_of_le hnm
  rw [he] at hd
  exact hd.dimLE y hy

private theorem actual_base_submersion (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

/-- Original zero-dimensional domain and canonicality force every actual centre empty. -/
theorem original_ambient_canonical_empty_of_dim_zero (M : MarkedIdeal n X)
    (hM : IsInvDomain 0 M) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower X D),
      IsCanonical M ((canonicalInvariant n).inv M) T → IsEmptyTower T := by
  intro D T
  induction T with
  | refl => exact fun _ => trivial
  | step T C π hπ ih =>
    intro hcan
    obtain ⟨hcanT,hC⟩ := hcan
    refine ⟨ih hcanT,?_⟩
    rcases hC with hC | hC
    · exact hC
    · have hD : IsInvDomain n M :=
        ⟨hM.isWellFormed,fun x hx => by
          obtain ⟨j,hj,hreg⟩ := hM.dimLE x hx
          exact ⟨j,hj.trans (Nat.zero_le n),hreg⟩,
          hM.one_le_d,hM.isNonzeroAlongAt⟩
      have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
        (canonicalInvariant n).isInvValue hD T hcanT
      have he := ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T ht
      rw [hC,he]
      ext z
      simp only [ResolutionDriver.maxLocus,mem_ofPred_eq,notMem_empty,false_and]

/-- A point in any actual centre would project to a point of the empty original source. -/
theorem original_empty_source_history [IsEmpty Y] :
    ∀ {D' : CMfd.{u} m} (Q : BlowupTower Y D'), IsEmptyTower Q := by
  intro D' Q
  induction Q with
  | refl => trivial
  | step Q C π hπ ih =>
    exact ⟨ih,eq_empty_iff_forall_notMem.mpr fun z _ => isEmptyElim (Q.proj z)⟩

/-- The actual submersion proves the empty source rather than a false dimension bound. -/
theorem original_source_empty_of_dimension_drop
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hnm : ¬ n ≤ m) : IsEmpty Y :=
  ⟨fun y => hnm (dimension_le_of_submersionAt (hf.isSubmersionAt y))⟩

/-- Whole literal ambient canonicality, with genuine zero and empty-source branches. -/
theorem IsActualTowerPullback.original_ambient_canonical
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hcan : IsCanonical M ((canonicalInvariant n).inv M) T) :
    IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) Q := by
  by_cases hnm : n ≤ m
  · cases n with
    | zero =>
      have he := original_ambient_canonical_empty_of_dim_zero M hM T hcan
      exact ResolutionInvariantExt.isCanonical_of_isEmptyTower _ _ Q
        (IsActualTowerPullback.empty_history h he)
    | succ n =>
      have hn : 0 < n+1 := Nat.succ_pos n
      have hm : 0 < m := hn.trans_le hnm
      have ht : IsCanonical M ((invFamily hn (n+1)).inv M) T := by
        simpa only [canonicalInvariant_eq_invFamily hn] using hcan
      have hc := (IsActualTowerPullback.original_recursive_family hn hm h M hM ht).1
      rw [Nat.sub_add_cancel hnm] at hc
      simpa only [canonicalInvariant_eq_invFamily hm] using hc
  · have := original_source_empty_of_dimension_drop (actual_base_submersion h) hnm
    exact ResolutionInvariantExt.isCanonical_of_isEmptyTower _ _ Q (original_empty_source_history Q)

/-- Every actual point supplies the true ambient dimension inequality internally. -/
theorem IsActualTowerPullback.original_ambient_value
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (z : D') (hz : g z ∈ (geoTransformAlong M T).cosupp) :
    (canonicalInvariant m).inv (markedPullback (m := m) f M) Q z =
      ambientDimensionMap (dimension_le_of_submersionAt
        ((actual_base_submersion h).isSubmersionAt (Q.proj z)))
        ((canonicalInvariant n).inv M T (g z)) := by
  have hnm := dimension_le_of_submersionAt
    ((actual_base_submersion h).isSubmersionAt (Q.proj z))
  cases n with
  | zero =>
    have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
      (canonicalInvariant 0).isInvValue hM T hcan
    rw [ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T ht] at hz
    exact False.elim hz
  | succ n =>
    have hn : 0 < n+1 := Nat.succ_pos n
    have hm : 0 < m := hn.trans_le hnm
    have ht : IsCanonical M ((invFamily hn (n+1)).inv M) T := by
      simpa only [canonicalInvariant_eq_invFamily hn] using hcan
    have hv := (IsActualTowerPullback.original_recursive_family hn hm h M hM ht).2 z hz
    rw [canonicalInvariant_eq_invFamily hm,canonicalInvariant_eq_invFamily hn]
    unfold ambientDimensionMap
    rw [← cast_invFamily_value hm (Nat.sub_add_cancel hnm) _ Q z,hv]

/-- BOTH actual ambient terminal histories are supplied from compact target input alone. -/
theorem exists_original_smooth_ambient_canonical_resolution [CompactSpace X]
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ∃ (D : CMfd.{u} n) (T : BlowupTower X D)
      (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      IsActualTowerPullback f Q T g ∧ Q.length = T.length ∧
      IsInvDomain m (markedPullback (m := m) f M) ∧
      IsCanonical (markedPullback (m := m) f M)
        ((canonicalInvariant m).inv (markedPullback (m := m) f M)) Q ∧
      IsGeoResolution (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q = markedPullback (m := m) g (geoTransformAlong M T) ∧
      (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp = g ⁻¹' (geoTransformAlong M T).cosupp := by
  obtain ⟨D,T,hcan,hres⟩ :=
    ResolutionInvariantSeq.exists_isGeoResolution_isCanonical (canonicalInvariant n) hM
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  obtain ⟨hqt,hrecord⟩ := IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hres.1
  have hcs := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hres.1
  have hqr : IsGeoResolution (markedPullback (m := m) f M) Q := by
    refine ⟨hqt,?_⟩
    rw [hcs,hres.2,preimage_empty]
  exact ⟨D,T,D',Q,g,hcan,hres,h,h.length_eq,original_ambient_domain_pullback hf M hM,
    IsActualTowerPullback.original_ambient_canonical h M hM hcan,hqr,hrecord,hcs⟩

end
end Hironaka.HironakaSmoothSubmersionOriginalAmbientCanonical
