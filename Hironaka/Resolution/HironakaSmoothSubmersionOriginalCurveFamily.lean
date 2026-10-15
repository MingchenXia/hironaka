/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.SharpGeometryExact
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGeneralFamilyLeaves
/-! Complete actual original bound-one smooth family comparison, and its
canonical history transfer. Complete mathematics preceded proofs in Mathematics.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalCurveFamily
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail GeneralValue MaxOrderValue
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionNonmonomialHistory
  HironakaSmoothSubmersionHistoricalControlledTail HironakaSmoothSubmersionHistoricalCompanionMasks
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaSmoothSubmersionActualFamilyMonomialLeaf
  HironakaSmoothSubmersionOriginalGeneralFamilyLeaves
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

theorem original_curve_step_one_special (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 0) M) T)
    (y : D) (hy : y ∈ (geoTransformAlong M T).cosupp) : IsSpecial M T y := by
  by_contra hns
  obtain ⟨ht,_,hcos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn 0) M hM hmax hn T hcan
  have hc := (Seq.StepOneBridge.isCanonical_iff (invFamily hn 0) M hM hmax hn T).mp hcan
  have hybar : y ∈ (geoTransformAlong (barMarked M) T).cosupp := hcos.symm ▸ hy
  have hd := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical M (k := 1)
    (invFamily hn 0) hM.isWellFormed hM.one_le_d hn hmax hM.dimLE T ht hc y hybar hns
  obtain ⟨hp,hdom,hcanJ,hcosJ⟩ := hd
  have htJ := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn 0).isInvValue hdom _ hcanJ
  have he := ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hdom _ htJ
  rw [he] at hcosJ
  exact hcosJ

theorem IsActualTowerPullback.actual_curve_family_value (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (hcan : IsCanonical M ((invFamily hn 1).inv M) T)
    (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp) :
    (invFamily hm ((m-n)+1)).inv (markedPullback (m := m) f M) Q z =
      familyDimensionMap (m-n) 1 ((invFamily hn 1).inv M T (g z)) := by
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn 1).isInvValue hM T hcan
  by_cases hzero : nmOrd (geoTransformAlong M T) (g z) = 0
  · exact (IsActualTowerPullback.actual_family_monomial_leaf hn hm h M hM ht z hzero).2
  let o := nmOrd (geoTransformAlong M T) (g z)
  have ho : 0 < o := Nat.pos_of_ne_zero hzero
  let F := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {B : CMfd.{u} n}
    (S : BlowupTower A B) (y : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn 0) J S y
  have hF : IsMaxOrderValue n 1 F := StepOneSeq.isMaxOrderValue_stepOneInvM (k := 1) (invFamily hn 0) hn
  have hc : IsCanonical M (genInv F M) T := hcan
  have hd := GeneralCanonicalTail.hasGenLowerData_of_isCanonical F hF hn hM T ht hc (g z) hy o rfl ho
  obtain ⟨hp,hdom,hmax,hcanP,hcosP⟩ := hd
  let r := regimeRun (OrdRegime M o) T (g z)
  let U := ordMask (geoTransformAlong M (head T r)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) o
  let P := compAt M o (head T r)
  let P' := compAt (markedPullback (m := m) f M) o (head Q r)
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  change IsInvDomain 1 P at hdom
  change IsMaximalOrderAlong P.N P.ideal P.d at hmax
  change IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 0) P) L at hcanP
  have hsp := original_curve_step_one_special hn P hdom hmax hcanP _ hcosP
  obtain ⟨p,q,hrecord,hqcoord,hrestr⟩ := IsActualTowerPullback.exists_actual_historical_tail hn h M hM ht r o
  change markedPullback (m := m) p P = P' at hrecord
  change IsActualTowerPullback p L' L q at hrestr
  obtain ⟨a,hhead,htail⟩ := IsActualTowerPullback.simultaneous_split h r
  have hheadT := ((isGeoTestTower_iff_head_tail M T r).mp ht).1
  have hpre : (V : Set (split Q r).1) = a ⁻¹' (U : Set (split T r).1) :=
    IsActualTowerPullback.order_mask_dictionary hn hhead M hM hheadT o
  have hp' : (tail Q r).proj z ∈ V := by
    change (tail Q r).proj z ∈ (V : Set (split Q r).1)
    rw [hpre]
    change a ((tail Q r).proj z) ∈ U
    rw [← htail.proj_comm z]
    exact hp
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  have hq : q z' = (⟨g z,hp⟩ : openPreimage (tail T r) U) := Subtype.ext (hqcoord z')
  have hspq : IsSpecial P L (q z') := by rw [hq];exact hsp
  have hv := original_special_step_one_value hn hm hrestr P hdom hmax hcanP z' hspq
  rw [hrecord,hq] at hv
  have hord' : nmOrd (geoTransformAlong (markedPullback (m := m) f M) Q) z = o :=
    IsActualTowerPullback.orderAt_dictionary hn h M hM ht z
  have hrun : regimeRun (OrdRegime (markedPullback (m := m) f M) o) Q z = r :=
    IsActualTowerPullback.fixed_order_regime_run hn h M hM ht o z
  change genInv (fun {A} J {B} S y => Seq.StepOneValueMasked.stepOneInvM
      (X := A) (invFamily hm (m-n)) J (Y := B) S y) (markedPullback (m := m) f M) Q z =
    generalDimensionMap (m-n) (stepDimensionMap (familyDimensionMap (m-n) 0))
      (genInv F M T (g z))
  unfold generalDimensionMap genInv genSecond
  rw [hord',show nmOrd (geoTransformAlong M T) (g z) = o from rfl,
    if_neg (ne_of_gt ho),hrun,genLowerValue_eq_of_mem _ _ hp',genLowerValue_eq_of_mem _ _ hp]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr,WithTop.map_coe]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy (m-n)) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy (m-n))))))) hv

private theorem actual_visible_curve_maximum (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (hcan : IsCanonical M ((invFamily hn 1).inv M) T)
    (hvisible : (g ⁻¹' ResolutionDriver.maxLocus ((invFamily hn 1).inv M T)
      (geoTransformAlong M T).cosupp).Nonempty) :
    ResolutionDriver.maxLocus ((invFamily hm ((m-n)+1)).inv (markedPullback (m := m) f M) Q)
      (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp =
    g ⁻¹' ResolutionDriver.maxLocus ((invFamily hn 1).inv M T) (geoTransformAlong M T).cosupp := by
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn 1).isInvValue hM T hcan
  have hcs := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed ht
  obtain ⟨w,hw⟩ := hvisible
  change g w ∈ (geoTransformAlong M T).cosupp ∧
    ∀ x ∈ (geoTransformAlong M T).cosupp, (invFamily hn 1).inv M T x ≤ (invFamily hn 1).inv M T (g w) at hw
  ext z
  change (z ∈ (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp ∧
      ∀ v ∈ (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp,
        (invFamily hm ((m-n)+1)).inv (markedPullback (m := m) f M) Q v ≤
        (invFamily hm ((m-n)+1)).inv (markedPullback (m := m) f M) Q z) ↔
    (g z ∈ (geoTransformAlong M T).cosupp ∧
      ∀ x ∈ (geoTransformAlong M T).cosupp, (invFamily hn 1).inv M T x ≤ (invFamily hn 1).inv M T (g z))
  rw [hcs]
  constructor
  · rintro ⟨hz,hmax⟩
    refine ⟨hz,fun x hx => (hw.2 x hx).trans ?_⟩
    have hle := hmax w hw.1
    rw [IsActualTowerPullback.actual_curve_family_value hn hm h M hM hcan w hw.1,
      IsActualTowerPullback.actual_curve_family_value hn hm h M hM hcan z hz] at hle
    exact (strictMono_familyDimensionMap (m-n) 1).le_iff_le.mp hle
  · rintro ⟨hz,hmax⟩
    refine ⟨hz,?_⟩
    intro v hv
    rw [IsActualTowerPullback.actual_curve_family_value hn hm h M hM hcan v hv,
      IsActualTowerPullback.actual_curve_family_value hn hm h M hM hcan z hz]
    exact (strictMono_familyDimensionMap (m-n) 1).monotone (hmax (g v) hv)

theorem IsActualTowerPullback.original_curve_family_canonical (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (hcan : IsCanonical M ((invFamily hn 1).inv M) T) :
    IsCanonical (markedPullback (m := m) f M)
      ((invFamily hm ((m-n)+1)).inv (markedPullback (m := m) f M)) Q := by
  induction h with
  | refl => trivial
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    obtain ⟨hc,hC⟩ := hcan
    refine ⟨ih hc,?_⟩
    rcases hC with hC | hC
    · left
      rw [hC,preimage_empty]
    · by_cases he : g ⁻¹' C = ∅
      · exact Or.inl he
      · have hv : (g ⁻¹' ResolutionDriver.maxLocus ((invFamily hn 1).inv M T)
            (geoTransformAlong M T).cosupp).Nonempty := by
          rw [← hC]
          exact nonempty_iff_ne_empty.mpr he
        exact Or.inr (by rw [hC,actual_visible_curve_maximum hn hm h M hM hc hv])

theorem exists_original_smooth_curve_family_resolution [CompactSpace X]
    (hn : 0 < n) (hm : 0 < m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) :
    ∃ (D : CMfd.{u} n) (T : BlowupTower X D)
      (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsCanonical M ((invFamily hn 1).inv M) T ∧ IsGeoResolution M T ∧
      IsActualTowerPullback f Q T g ∧ Q.length = T.length ∧
      IsInvDomain ((m-n)+1) (markedPullback (m := m) f M) ∧
      IsCanonical (markedPullback (m := m) f M)
        ((invFamily hm ((m-n)+1)).inv (markedPullback (m := m) f M)) Q ∧
      IsGeoResolution (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q = markedPullback (m := m) g (geoTransformAlong M T) ∧
      (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp = g ⁻¹' (geoTransformAlong M T).cosupp := by
  obtain ⟨D,T,hcan,hres⟩ := ResolutionInvariantSeq.exists_isGeoResolution_isCanonical (invFamily hn 1) hM
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  have hd : IsInvDomain ((m-n)+1) (markedPullback (m := m) f M) := by
    simpa only [Nat.add_comm] using isInvDomain_markedPullback_submersion hf M hM
  obtain ⟨hqt,hrecord⟩ := IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hres.1
  have hcs := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hres.1
  have hqr : IsGeoResolution (markedPullback (m := m) f M) Q := by
    refine ⟨hqt,?_⟩
    rw [hcs,hres.2,preimage_empty]
  exact ⟨D,T,D',Q,g,hcan,hres,h,h.length_eq,hd,
    IsActualTowerPullback.original_curve_family_canonical hn hm h M hM hcan,hqr,hrecord,hcs⟩
end
end Hironaka.HironakaSmoothSubmersionOriginalCurveFamily
