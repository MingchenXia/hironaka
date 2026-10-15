/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalContactHistory
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalPositiveCurveLower
/-! Genuine original zero-contact lower and common source mask producers.
Complete Mathematics.tex preceded proofs. Source lower canonicity/value
remain internally constructed obligations of the full depth induction. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalZeroContactLower
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked StepOneLowerDomain HomogenizedIdealAlong
  ContactStageKept TangentDirectionAlong HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionOriginalContactHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

theorem original_zero_common_contact_mask_geometry
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hd : 1 ≤ M.d)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (ht : IsGeoTestTower (barMarked M) T)
    (z : D') (hy : g z ∈ (geoTransformAlong (barMarked M) T).cosupp)
    (hl : level M T (g z) = 0) (hns : ¬ IsSpecial M T (g z)) :
    let r := regimeRun (stepRegime M 0) T (g z)
    let w := (tangentChoice M (T.proj (g z))).2
    let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
    regimeRun (stepRegime (markedPullback (m := m) f M)
      (level (markedPullback (m := m) f M) Q z)) Q z = r ∧
    IsTangentDirectionAlong (markedPullback (m := m) f M).N
      (markedPullback (m := m) f M).ideal (markedPullback (m := m) f M).d
      (f ⁻¹' (tangentChoice M (T.proj (g z))).1) (w ∘ f) ∧
    ∃ (a : (split Q r).1 → (split T r).1) (V : Opens (split Q r).1)
      (p : V → U) (q : openPreimage (tail Q r) V → openPreimage (tail T r) U),
      IsActualTowerPullback f (head Q r) (head T r) a ∧
      IsActualTowerPullback a (tail Q r) (tail T r) g ∧
      (V : Set (split Q r).1) = a ⁻¹' (U : Set (split T r).1) ∧
      (tail Q r).proj z ∈ V ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      (∀ b, (q b : D) = g (b : D')) ∧
      (V : Set (split Q r).1) ⊆ (head Q r).proj ⁻¹'
        (f ⁻¹' (tangentChoice M (T.proj (g z))).1) ∧
      (∀ F ∈ origMembers (markedPullback (m := m) f M) (head Q r), Disjoint (V : Set (split Q r).1) F) ∧
      markedPullback (m := m) p (lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))) =
        contactMarkedKept (markedPullback (m := m) f M) (w ∘ f) (head Q r) V ∧
      IsActualTowerPullback p (restrict V (tail Q r)) (restrict U (tail T r)) q := by
  dsimp only
  obtain ⟨hr,hu,a,V,p,q,hh,hs,hV,hpV,hpSmooth,_hpcoord,hqcoord,hrecord,hR⟩ :=
    IsActualTowerPullback.exists_selected_original_zero_contact_diagram h M hM hd hmax ht z hy hl hns
  let r := regimeRun (stepRegime M 0) T (g z)
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  have htarget (b : (split Q r).1) (hb : b ∈ V) : a b ∈ maskB M (head T r) ((tail T r).proj (g z)) := by
    change a b ∈ (U : Set (split T r).1)
    change b ∈ (V : Set (split Q r).1) at hb
    rw [hV] at hb
    exact hb
  have hbase : (head T r).proj ((tail T r).proj (g z)) = T.proj (g z) :=
    (congrFun (proj_eq_comp T r) (g z)).symm
  have hWU : (V : Set (split Q r).1) ⊆ (head Q r).proj ⁻¹'
      (f ⁻¹' (tangentChoice M (T.proj (g z))).1) := by
    intro b hb
    change f ((head Q r).proj b) ∈ (tangentChoice M (T.proj (g z))).1
    rw [← hh.proj_comm b]
    have hx := (interior_subset (htarget b hb)).1
    rwa [hbase] at hx
  have htH := ((isGeoTestTower_iff_head_tail (barMarked M) T r).mp ht).1
  have hWE : ∀ F ∈ origMembers (markedPullback (m := m) f M) (head Q r), Disjoint (V : Set (split Q r).1) F := by
    intro F hF
    rw [IsActualTowerPullback.bar_original_members_dictionary hh M hM htH] at hF
    obtain ⟨F0,hF0,rfl⟩ := List.mem_map.mp hF
    exact Set.disjoint_left.mpr fun b hb hbF => (interior_subset (htarget b hb)).2.1 F0 hF0 hbF
  exact ⟨hr,hu,a,V,p,q,hh,hs,hV,hpV,hpSmooth,hqcoord,hWU,hWE,hrecord,hR⟩

theorem original_zero_canonical_lower_diagram (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M) T)
    (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hns : ¬ IsSpecial M T (g z)) (hl : level M T (g z) = 0) :
    let r := regimeRun (stepRegime M 0) T (g z)
    let w := (tangentChoice M (T.proj (g z))).2
    let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
    let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
    let L := restrict U (tail T r)
    ∃ (hp : (tail T r).proj (g z) ∈ U) (a : (split Q r).1 → (split T r).1)
      (V : Opens (split Q r).1) (hp' : (tail Q r).proj z ∈ V)
      (p : V → U) (q : openPreimage (tail Q r) V → openPreimage (tail T r) U),
      let J' := contactMarkedKept (markedPullback (m := m) f M) (w ∘ f) (head Q r) V
      let L' := restrict V (tail Q r)
      IsTangentDirectionAlong (markedPullback (m := m) f M).N
        (markedPullback (m := m) f M).ideal (markedPullback (m := m) f M).d
        (f ⁻¹' (tangentChoice M (T.proj (g z))).1) (w ∘ f) ∧
      IsActualTowerPullback f (head Q r) (head T r) a ∧
      (V : Set (split Q r).1) = a ⁻¹' (U : Set (split T r).1) ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      markedPullback (m := m) p J = J' ∧ IsActualTowerPullback p L' L q ∧
      q (⟨z,hp'⟩ : openPreimage (tail Q r) V) = (⟨g z,hp⟩ : openPreimage (tail T r) U) ∧
      (V : Set (split Q r).1) ⊆ (head Q r).proj ⁻¹'
        (f ⁻¹' (tangentChoice M (T.proj (g z))).1) ∧
      (∀ F ∈ origMembers (markedPullback (m := m) f M) (head Q r), Disjoint (V : Set (split Q r).1) F) ∧
      IsInvDomain (k+1) J ∧ IsCanonical J ((invFamily hn (k+1)).inv J) L ∧
      (⟨g z,hp⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong J L).cosupp ∧
      IsInvDomain ((m-n)+k+1) J' ∧ IsGeoTestTower J' L' ∧
      (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' L').cosupp := by
  dsimp only
  obtain ⟨ht,_,hcos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)) M hM hmax hn T hcan
  have hc := (Seq.StepOneBridge.isCanonical_iff (invFamily hn (k+1)) M hM hmax hn T).mp hcan
  have hybar : g z ∈ (geoTransformAlong (barMarked M) T).cosupp := hcos.symm ▸ hy
  have hD := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical M (k := k+2)
    (invFamily hn (k+1)) hM.isWellFormed hM.one_le_d hn hmax hM.dimLE T ht hc (g z) hybar hns
  rw [hl] at hD
  obtain ⟨hp,hdom,hcanJ,hcosJ⟩ := hD
  obtain ⟨_hr,hu,a,V,p,q,hh,_hs,hV,hp',hpSmooth,hqcoord,hWU,hWE,hrecord,hR⟩ :=
    original_zero_common_contact_mask_geometry h M hM.isWellFormed hM.one_le_d hmax ht z hybar hl hns
  let r := regimeRun (stepRegime M 0) T (g z)
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
  let L := restrict U (tail T r)
  let J' := contactMarkedKept (markedPullback (m := m) f M)
    ((tangentChoice M (T.proj (g z))).2 ∘ f) (head Q r) V
  let L' := restrict V (tail Q r)
  simp only [show k+2-1=k+1 by omega] at hdom
  change IsInvDomain (k+1) J at hdom
  change markedPullback (m := m) p J = J' at hrecord
  change IsActualTowerPullback p L' L q at hR
  have hq : q (⟨z,hp'⟩ : openPreimage (tail Q r) V) = (⟨g z,hp⟩ : openPreimage (tail T r) U) :=
    Subtype.ext (hqcoord (⟨z,hp'⟩ : openPreimage (tail Q r) V))
  have htJ : IsGeoTestTower J L := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)).isInvValue hdom L hcanJ
  have hd' : IsInvDomain ((m-n)+k+1) J' := by
    have hd := isInvDomain_markedPullback_submersion hpSmooth J hdom
    have hh : IsInvDomain ((k+1)+(m-n)) J' := hrecord ▸ hd
    convert hh using 1
    omega
  have hqt : IsGeoTestTower J' L' :=
    hrecord ▸ (IsActualTowerPullback.relative_marked_dictionary hR J hdom.isWellFormed htJ).1
  have hqcos : (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' L').cosupp := by
    have hcs : (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈
        (geoTransformAlong (markedPullback (m := m) p J) L').cosupp := by
      rw [IsActualTowerPullback.relative_cosupport_dictionary hR J hdom.isWellFormed htJ]
      change q (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J L).cosupp
      rw [hq]
      exact hcosJ
    exact hrecord ▸ hcs
  exact ⟨hp,a,V,hp',p,q,hu,hh,hV,hpSmooth,hrecord,hR,hq,hWU,hWE,hdom,hcanJ,hcosJ,hd',hqt,hqcos⟩
end
end Hironaka.HironakaSmoothSubmersionOriginalZeroContactLower
