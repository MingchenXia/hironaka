/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionPositiveLowerHistory
import Hironaka.Resolution.HironakaSmoothSubmersionTangentContact
/-! # The original chosen contact model on actual smooth histories

Whole strict carriers and coefficient records commute with actual Cartesian
histories. The actual original zero mask, chosen original direction, smooth
restricted maps and whole selected remaining histories are produced from
original maximal-order zero/nonspecial data. The source common contact record
explicitly uses the transported original choice. Comparing its invariant
with the independently chosen source contact remains an obligation.
Mathematics was written before proofs in `Mathematics.tex`.
Blueprint: `hironaka-smooth-submersion-original-contact-history-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalContactHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HomogenizedGlueingTower HomogenizedIdealAlong CoefficientIdealRestriction
  StepOneValue StepOneValueMasked StepOneLowerDomain ContactStageKept
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeDifferentialIdeals
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionControlledTransform HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionAllBranchHistory HironakaSmoothSubmersionHistoricalCompanionMasks
  HironakaSmoothSubmersionHistoricalControlledTail HironakaSmoothSubmersionContactParameterCharts
  HironakaSmoothSubmersionContactParameterCoefficientIdeals HironakaSmoothSubmersionTangentContact
  TangentDirectionAlong StepOneRegime GermIdealOrder CodimOneSupportAlong
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

private theorem IsActualTowerPullback.base_submersion
    (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

theorem IsActualTowerPullback.strictAlong_preimage
    (h : IsActualTowerPullback f Q T g) (B : Set X) :
    strictAlong Q (f ⁻¹' B) = g ⁻¹' strictAlong T B := by
  induction h with
  | refl => rfl
  | step h hg hπ hρ ih =>
    rw [strictAlong_step,strictAlong_step,ih]
    exact (geoStrictTransform_actual_preimage hg hπ hρ _).symm

theorem IsActualTowerPullback.whole_contact_record
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (w : X → ℂ) :
    withN (coeffMarkedAlong (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q))
        (strictAlong Q ((markedPullback (m := m) f M).N ∩ {y | (w ∘ f) y = 0})) =
      markedPullback (m := m) g
        (withN (coeffMarkedAlong (geoTransformAlong (barMarked M) T))
          (strictAlong T (M.N ∩ {x | w x = 0}))) := by
  have hMT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked M hM) T hT
  have hcarrier : (markedPullback (m := m) f M).N ∩ {y | (w ∘ f) y = 0} =
      f ⁻¹' (M.N ∩ {x | w x = 0}) := rfl
  rw [(IsActualTowerPullback.bar_stage_dictionary h M hM hT).2,
    ← pullback_coeffMarkedAlong h.isSubmersion _ hMT.isCoherent hMT.isClosedSubmanifold_N,
    hcarrier,IsActualTowerPullback.strictAlong_preimage h]
  rfl

/-- The actual full preimage open and smooth restricted map, retaining
the entire original contact record and original stage coordinates. -/
theorem IsActualTowerPullback.exists_original_contact_open_record
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (w : X → ℂ) (U : Opens D) :
    ∃ (V : Opens D') (p : V → U),
      (V : Set D') = g ⁻¹' (U : Set D) ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      (∀ z, (p z : D) = g (z : D')) ∧
      markedPullback (m := m) p (contactMarkedKept M w T U) =
        contactMarkedKept (markedPullback (m := m) f M) (w ∘ f) Q V := by
  let V : Opens D' := ⟨g ⁻¹' (U : Set D),U.isOpen.preimage h.isSubmersion.contMDiff.continuous⟩
  have hVU : MapsTo g V U := fun _ hz => hz
  let p : V → U := restrictedOpenMap V U hVU
  have hp := restrictedOpenMap_isSubmersion h.isSubmersion V U hVU
  let J := withN (coeffMarkedAlong (geoTransformAlong (barMarked M) T))
    (strictAlong T (M.N ∩ {x | w x = 0}))
  have hc : J.ideal.IsCoherent := isCoherent_restrictedCoeff M hM.isCoherent
    hM.isClosedSubmanifold_N w T hT
  refine ⟨V,p,rfl,hp,fun _ => rfl,?_⟩
  change markedPullback (m := m) p
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → D) J) =
    MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : V → D')
      (withN (coeffMarkedAlong (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q))
        (strictAlong Q ((markedPullback (m := m) f M).N ∩ {y | (w ∘ f) y = 0})))
  rw [IsActualTowerPullback.whole_contact_record h M hM hT w]
  change markedPullback (m := m) p
      (markedPullback (m := n) (Subtype.val : U → D) J) =
    markedPullback (m := m) (Subtype.val : V → D') (markedPullback (m := m) g J)
  rw [← whole_parameter_markedPullback_comp (X := D) (Y := CMfd.of (n := n) U)
      (Z := CMfd.of (n := m) V) (f := (Subtype.val : U → D)) (g := p)
      contMDiff_subtype_val hp.contMDiff J hc,
    ← whole_parameter_markedPullback_comp (X := D) (Y := D')
      (Z := CMfd.of (n := m) V) (f := g) (g := (Subtype.val : V → D'))
      h.isSubmersion.contMDiff contMDiff_subtype_val J hc]
  rfl

/-- Original contact records and actual entire restricted tails at any
actual split. The preimage open and both maps are constructed internally. -/
theorem IsActualTowerPullback.exists_split_original_contact_diagram
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower (barMarked M) T) (w : X → ℂ)
    (j : ℕ) (U : Opens (split T j).1) :
    ∃ (a : (split Q j).1 → (split T j).1) (V : Opens (split Q j).1)
      (p : V → U) (q : openPreimage (tail Q j) V → openPreimage (tail T j) U),
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      IsActualTowerPullback a (tail Q j) (tail T j) g ∧
      (V : Set (split Q j).1) = a ⁻¹' (U : Set (split T j).1) ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      (∀ z, (p z : (split T j).1) = a (z : (split Q j).1)) ∧
      (∀ z, (q z : D) = g (z : D')) ∧
      markedPullback (m := m) p (contactMarkedKept M w (head T j) U) =
        contactMarkedKept (markedPullback (m := m) f M) (w ∘ f) (head Q j) V ∧
      IsActualTowerPullback p (restrict V (tail Q j)) (restrict U (tail T j)) q := by
  obtain ⟨a,hhead,htail⟩ := IsActualTowerPullback.simultaneous_split h j
  have hheadT := ((isGeoTestTower_iff_head_tail (barMarked M) T j).mp hT).1
  obtain ⟨V,p₀,hV,hp₀,hpcoord,hrecord⟩ :=
    IsActualTowerPullback.exists_original_contact_open_record hhead M hM hheadT w U
  obtain ⟨p,q,hp,hq,hR⟩ := IsActualTowerPullback.exists_actual_open_restriction htail U V hV
  have hpSame : p₀=p := by
    funext z
    exact Subtype.ext ((hpcoord z).trans (hp z).symm)
  subst p₀
  exact ⟨a,V,p,q,hhead,htail,hV,hp₀,hp,hq,hrecord,hR⟩

/-- The actual nonspecial zero branch produces the original chosen contact
model and WHOLE selected restricted Cartesian histories. The source record
uses the transported original choice explicitly; no independent-choice
mask or value comparison is asserted. -/
theorem IsActualTowerPullback.exists_selected_original_zero_contact_diagram
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hd : 1 ≤ M.d)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (hT : IsGeoTestTower (barMarked M) T)
    (z : D') (hz : g z ∈ (geoTransformAlong (barMarked M) T).cosupp)
    (hlevel : level M T (g z) = 0) (hsp : ¬ IsSpecial M T (g z)) :
    let r := regimeRun (stepRegime M 0) T (g z)
    let u := (tangentChoice M (T.proj (g z))).2
    let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
    regimeRun (stepRegime (markedPullback (m := m) f M)
      (level (markedPullback (m := m) f M) Q z)) Q z = r ∧
    TangentDirectionAlong.IsTangentDirectionAlong (markedPullback (m := m) f M).N
      (markedPullback (m := m) f M).ideal (markedPullback (m := m) f M).d
      (f ⁻¹' (tangentChoice M (T.proj (g z))).1) (u ∘ f) ∧
    ∃ (a : (split Q r).1 → (split T r).1) (V : Opens (split Q r).1)
      (p : V → U) (q : openPreimage (tail Q r) V → openPreimage (tail T r) U),
      IsActualTowerPullback f (head Q r) (head T r) a ∧
      IsActualTowerPullback a (tail Q r) (tail T r) g ∧
      (V : Set (split Q r).1) = a ⁻¹' (U : Set (split T r).1) ∧
      (tail Q r).proj z ∈ V ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      (∀ b, (p b : (split T r).1) = a (b : (split Q r).1)) ∧
      (∀ b, (q b : D) = g (b : D')) ∧
      markedPullback (m := m) p
        (lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))) =
        contactMarkedKept (markedPullback (m := m) f M) (u ∘ f) (head Q r) V ∧
      IsActualTowerPullback p (restrict V (tail Q r)) (restrict U (tail T r)) q := by
  dsimp only
  let r := regimeRun (stepRegime M 0) T (g z)
  let u := (tangentChoice M (T.proj (g z))).2
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  have hf := IsActualTowerPullback.base_submersion h
  obtain ⟨hxU,hu⟩ := tangentChoice_spec M (exists_tangent_of_mem_cosupp M hM hd hmax T hT hz)
  have hselected := stepRegime_and_mem_cosupp_head M hM T hT hz hsp
  rw [hlevel] at hselected
  obtain ⟨hreg,hcos⟩ := hselected
  have hheadT := ((isGeoTestTower_iff_head_tail (barMarked M) T r).mp hT).1
  have hZ : (tail T r).proj (g z) ∉ codimOnePartAlong
      (geoTransformAlong (barMarked M) (head T r)).N
      (geoTransformAlong (barMarked M) (head T r)).ideal
      (geoTransformAlong (barMarked M) (head T r)).d := by
    intro hm
    exact hreg.2 (Or.inl ⟨hreg.1,hm⟩)
  have hpU : (tail T r).proj (g z) ∈ U := mem_maskB M hM hd hmax (head T r) hheadT hcos hreg.1 hZ
  have hbase : (head T r).proj ((tail T r).proj (g z)) = T.proj (g z) :=
    (congrFun (proj_eq_comp T r) (g z)).symm
  obtain ⟨a,V,p,q,hhead,htail,hV,hp,hpcoord,hqcoord,hrecord,hR⟩ :=
    IsActualTowerPullback.exists_split_original_contact_diagram h M hM hT u r U
  have hzV : (tail Q r).proj z ∈ V := by
    change (tail Q r).proj z ∈ (V : Set (split Q r).1)
    rw [hV]
    change a ((tail Q r).proj z) ∈ (U : Set (split T r).1)
    rw [← htail.proj_comm z]
    exact hpU
  have htarget : contactMarkedKept M u (head T r) U =
      lowerMarkedM M 0 (head T r) ((tail T r).proj (g z)) := by
    unfold lowerMarkedM lowerMarkedB
    rw [hbase]
    rfl
  rw [htarget] at hrecord
  refine ⟨?_,isTangentDirectionAlong_preimage hf hM.isCoherent hM.isClosedSubmanifold_N hu,
    a,V,p,q,hhead,htail,hV,hzV,hp,hpcoord,hqcoord,hrecord,hR⟩
  rw [IsActualTowerPullback.bar_level_dictionary h M hM hT z,hlevel]
  exact IsActualTowerPullback.all_stepRegime_run h M hM hT 0 z

end
end Hironaka.HironakaSmoothSubmersionOriginalContactHistory
