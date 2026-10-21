/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSubmersionHSNeighborhoods
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalAmbientCanonical
import Hironaka.Resolution.HironakaSmoothSubmersionRegularityReflection
import Hironaka.Resolution.HironakaOriginalFullValueVariationLocus

/-! The SAME original canonical history under genuine smooth basechange:
FULL-R plus ALL existing HS profiles, actual neighborhoods and literal bad set.
No noncanonical preparation or coefficient-transform closure is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalCanonicalSmoothTupleVariation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaOriginalSubmersionHSNeighborhoods
  HironakaOriginalSmoothSubmersionIntrinsicHS HironakaOriginalFullValueVariationLocus
  HironakaHolomorphicJetChartInvariance
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- Genuine regularity and genuine reflection retain the ACTUAL free dimension. -/
theorem actual_submersion_carrier_regular_iff {n r : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]
    {f : Y → X} (y : Y)
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f y)
    (S : Set X) (q : ℕ) :
    RegularAtDim (n := n+r) (f ⁻¹' S) y (q+r) ↔ RegularAtDim (n := n) S (f y) q := by
  constructor
  · intro hh
    have h := (HironakaSmoothSubmersionRegularityReflection.regularAtDim_of_preimage_submersion hf hh).2
    simpa only [Nat.add_sub_cancel_left,Nat.add_sub_cancel] using h
  · intro hh
    have h := regularAtDim_preimage_submersion hf hh
    simpa only [Nat.add_sub_cancel_left] using h

/-- The literal ORIGINAL full current invariant and EVERY entire original ambient HS profile. -/
def originalCurrentFullHSTuple {n : ℕ} {X D : CMfd.{u} n} {ι : Type v}
    (M : MarkedIdeal n X) (T : BlowupTower X D) (A : ι → GermIdeal n D) (x : D) :
    ValTy n × (ι → ℕ → ℕ) :=
  ((canonicalInvariant n).inv M T x,fun i ℓ => hilbertSamuelAt (A i) x ℓ)

/-- True original ambient carrier neighborhoods of the SAME entire tuple. -/
def originalCurrentFullHSTupleLocallyConstant {n : ℕ} {X D : CMfd.{u} n} {ι : Type v}
    (M : MarkedIdeal n X) (T : BlowupTower X D) (A : ι → GermIdeal n D) (S : Set D) (x : D) : Prop :=
  ∃ U : Set D,IsOpen U ∧ x ∈ U ∧ ∀ z ∈ S ∩ U,
    originalCurrentFullHSTuple M T A z=originalCurrentFullHSTuple M T A x

/-- Literal nonsmooth-or-nonconstant subset, without a bad-locus certificate. -/
def originalCurrentFullHSTupleBad {n : ℕ} {X D : CMfd.{u} n} {ι : Type v}
    (M : MarkedIdeal n X) (T : BlowupTower X D) (A : ι → GermIdeal n D) (S : Set D) (q : ℕ) : Set D :=
  actualValueVariationLocus (n := n) (originalCurrentFullHSTuple M T A) S q

section ActualHistory
variable {n r : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} (n+r)} {ι : Type v}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- Actual ORIGINAL value embedding and actual full HS product reflection
prove BOTH tuple equality directions, before transporting neighborhoods. -/
theorem actual_original_canonical_full_hs_tuple_eq_iff
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (A : ι → GermIdeal n D) (hA : ∀ i,(A i).IsCoherent)
    (p q : D') (hp : g p ∈ (geoTransformAlong M T).cosupp)
    (hq : g q ∈ (geoTransformAlong M T).cosupp) :
    originalCurrentFullHSTuple (markedPullback (m := n+r) f M) Q
      (fun i => GermIdeal.pullback (m := n+r) g (A i)) p=
      originalCurrentFullHSTuple (markedPullback (m := n+r) f M) Q
        (fun i => GermIdeal.pullback (m := n+r) g (A i)) q ↔
      originalCurrentFullHSTuple M T A (g p)=originalCurrentFullHSTuple M T A (g q) := by
  have hv : ∀ z,g z ∈ (geoTransformAlong M T).cosupp →
      (canonicalInvariant (n+r)).inv (markedPullback (m := n+r) f M) Q z=
        ambientDimensionMap (Nat.le_add_right n r) ((canonicalInvariant n).inv M T (g z)) := by
    intro z hz
    exact HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_value h M hM hcan z hz
  have hs := h.isSubmersion
  constructor
  · intro heq
    apply Prod.ext
    · have hh := congrArg Prod.fst heq
      change (canonicalInvariant (n+r)).inv _ Q p=(canonicalInvariant (n+r)).inv _ Q q at hh
      rw [hv p hp,hv q hq] at hh
      exact (strictMono_ambientDimensionMap (Nat.le_add_right n r)).injective hh
    · funext i ℓ
      exact (hilbertSamuelAt_original_submersion_entire_profile_eq_iff hs (A i) (hA i) p q).mp
        (fun k => congrArg (fun a => a.2 i k) heq) ℓ
  · intro heq
    apply Prod.ext
    · change (canonicalInvariant (n+r)).inv _ Q p=(canonicalInvariant (n+r)).inv _ Q q
      rw [hv p hp,hv q hq]
      exact congrArg (ambientDimensionMap (Nat.le_add_right n r)) (congrArg Prod.fst heq)
    · funext i ℓ
      exact (hilbertSamuelAt_original_submersion_entire_profile_eq_iff hs (A i) (hA i) p q).mpr
        (fun k => congrArg (fun a => a.2 i k) heq) ℓ

/-- The actual stage submersion constructs BOTH true original ambient
neighborhood directions for ANY carrier inside the SAME target cosupport. -/
theorem actual_original_canonical_full_hs_tuple_localConst_iff
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (A : ι → GermIdeal n D) (hA : ∀ i,(A i).IsCoherent)
    (S : Set D) (hS : S ⊆ (geoTransformAlong M T).cosupp) (y : D') (hy : g y ∈ S) :
    originalCurrentFullHSTupleLocallyConstant M T A S (g y) ↔
      originalCurrentFullHSTupleLocallyConstant (markedPullback (m := n+r) f M) Q
        (fun i => GermIdeal.pullback (m := n+r) g (A i)) (g ⁻¹' S) y := by
  have hG := original_submersion_carrier_function_localConst_iff h.isSubmersion.contMDiff y
    (h.isSubmersion.isSubmersionAt y) (originalCurrentFullHSTuple M T A) S
  constructor
  · intro hh
    obtain ⟨V,hVo,hyV,hv⟩ := hG.mp hh
    refine ⟨V,hVo,hyV,?_⟩
    intro z hz
    exact (actual_original_canonical_full_hs_tuple_eq_iff h M hM hcan A hA z y (hS hz.1) (hS hy)).mpr (hv z hz)
  · rintro ⟨V,hVo,hyV,hv⟩
    exact hG.mpr ⟨V,hVo,hyV,fun z hz =>
      (actual_original_canonical_full_hs_tuple_eq_iff h M hM hcan A hA z y (hS hz.1) (hS hy)).mp (hv z hz)⟩

/-- True regularity shift and BOTH neighborhood directions prove the EXACT
literal whole-tuple bad-set preimage on ANY actual target cosupport subset. -/
theorem actual_original_canonical_full_hs_tuple_bad_eq_preimage
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (A : ι → GermIdeal n D) (hA : ∀ i,(A i).IsCoherent)
    (S : Set D) (hS : S ⊆ (geoTransformAlong M T).cosupp) (q : ℕ) :
    originalCurrentFullHSTupleBad (markedPullback (m := n+r) f M) Q
      (fun i => GermIdeal.pullback (m := n+r) g (A i)) (g ⁻¹' S) (q+r)=
      g ⁻¹' originalCurrentFullHSTupleBad M T A S q := by
  ext y
  change (g y ∈ S ∧ ¬(RegularAtDim (n := n+r) (g ⁻¹' S) y (q+r) ∧
    originalCurrentFullHSTupleLocallyConstant _ Q _ (g ⁻¹' S) y)) ↔
      g y ∈ S ∧ ¬(RegularAtDim (n := n) S (g y) q ∧ originalCurrentFullHSTupleLocallyConstant M T A S (g y))
  constructor
  · rintro ⟨hy,hbad⟩
    refine ⟨hy,fun hh => hbad ⟨?_,?_⟩⟩
    · exact (actual_submersion_carrier_regular_iff y (h.isSubmersion.isSubmersionAt y) S q).mpr hh.1
    · exact (actual_original_canonical_full_hs_tuple_localConst_iff h M hM hcan A hA S hS y hy).mp hh.2
  · rintro ⟨hy,hbad⟩
    refine ⟨hy,fun hh => hbad ⟨?_,?_⟩⟩
    · exact (actual_submersion_carrier_regular_iff y (h.isSubmersion.isSubmersionAt y) S q).mp hh.1
    · exact (actual_original_canonical_full_hs_tuple_localConst_iff h M hM hcan A hA S hS y hy).mpr hh.2

end ActualHistory

/-- ONLY original smooth basechange, domain and SAME original canonical target
history construct the actual source prefix and every true tuple bad-set pullback. -/
theorem exists_original_canonical_smooth_full_tuple_variation {n r : ℕ}
    {X D : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {ι : Type v} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (T : BlowupTower X D)
    (hcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (A : ι → GermIdeal n D) (hA : ∀ i,(A i).IsCoherent) :
    ∃ (D' : CMfd.{u} (n+r)) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      Q.length=T.length ∧ (∀ z,T.proj (g z)=f (Q.proj z)) ∧
      IsInvDomain (n+r) (markedPullback (m := n+r) f M) ∧
      IsCanonical (markedPullback (m := n+r) f M)
        ((canonicalInvariant (n+r)).inv (markedPullback (m := n+r) f M)) Q ∧
      IsGeoTestTower (markedPullback (m := n+r) f M) Q ∧
      geoTransformAlong (markedPullback (m := n+r) f M) Q=markedPullback (m := n+r) g (geoTransformAlong M T) ∧
      (geoTransformAlong (markedPullback (m := n+r) f M) Q).cosupp=g ⁻¹' (geoTransformAlong M T).cosupp ∧
      ∀ S : Set D,S ⊆ (geoTransformAlong M T).cosupp →
        (∀ y : D',g y ∈ S →
          (originalCurrentFullHSTupleLocallyConstant M T A S (g y) ↔
            originalCurrentFullHSTupleLocallyConstant (markedPullback (m := n+r) f M) Q
              (fun i => GermIdeal.pullback (m := n+r) g (A i)) (g ⁻¹' S) y)) ∧
        ∀ q : ℕ,originalCurrentFullHSTupleBad (markedPullback (m := n+r) f M) Q
          (fun i => GermIdeal.pullback (m := n+r) g (A i)) (g ⁻¹' S) (q+r)=
          g ⁻¹' originalCurrentFullHSTupleBad M T A S q := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (canonicalInvariant n).isInvValue hM T hcan
  obtain ⟨hqt,hrecord⟩ := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed ht
  have hcs := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed ht
  have hqcan := HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_canonical
    h M hM hcan
  refine ⟨D',Q,g,h,h.isSubmersion,h.length_eq,h.proj_comm,
    original_ambient_domain_pullback hf M hM,hqcan,hqt,hrecord,hcs,?_⟩
  intro S hS
  exact ⟨fun y hy => actual_original_canonical_full_hs_tuple_localConst_iff h M hM hcan A hA S hS y hy,
    fun q => actual_original_canonical_full_hs_tuple_bad_eq_preimage h M hM hcan A hA S hS q⟩

end
end Hironaka.HironakaOriginalCanonicalSmoothTupleVariation
