/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionHistoricalCompanionMasks
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaSmoothSubmersionHistoricalControlledTail
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec InvDomainTowerAlong
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionRelativePartsCompanion HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionNonmonomialHistory
  HironakaSmoothSubmersionHistoricalCompanionMasks HironakaSmoothSubmersionContactParameterCharts
  HironakaSmoothSubmersionContactParameterCoefficientIdeals HironakaSmoothSubmersionBlowupLift
  NonmonomialOrderTail CompanionRebase GeneralValue HironakaGeneralThreeNonspecialAnalyticLoci
  BlowupRestrictOpen MarkedIdealRestrictOpen NonmonomialOrderCanonical NonmonomialOrderRegime StepOneRegime
noncomputable section
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

theorem IsActualTowerPullback.step_of_actual_square
    (h : IsActualTowerPullback f Q T g)
    (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g)
    {Z : CMfd.{u} n} {Z' : CMfd.{u} m} {C : Set D} {C' : Set D'}
    {π : Z → D} {ρ : Z' → D'}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m C' ρ)
    (hC : C' = g ⁻¹' C) (b : Z' → Z)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ b)
    (hsquare : π ∘ b = g ∘ ρ) :
    IsActualTowerPullback f (.step Q C' ρ hρ) (.step T C π hπ) b := by
  subst C'
  rw [actualLift_unique hg hπ hρ b hb hsquare]
  exact IsActualTowerPullback.step h hg hπ hρ

theorem IsActualTowerPullback.openPreimage_dictionary
    (h : IsActualTowerPullback f Q T g) (U : Opens X) (V : Opens Y)
    (hV : (V : Set Y) = f ⁻¹' (U : Set X)) :
    (openPreimage Q V : Set D') = g ⁻¹' (openPreimage T U : Set D) := by
  ext z
  change Q.proj z ∈ (V : Set Y) ↔ T.proj (g z) ∈ (U : Set X)
  rw [hV]
  exact Iff.of_eq (congrArg (fun x => x ∈ (U : Set X)) (h.proj_comm z).symm)

theorem IsActualTowerPullback.exists_actual_open_restriction
    (h : IsActualTowerPullback f Q T g) (U : Opens X) (V : Opens Y)
    (hV : (V : Set Y) = f ⁻¹' (U : Set X)) :
    ∃ (p : V → U) (q : openPreimage Q V → openPreimage T U),
      (∀ z, (p z : X) = f (z : Y)) ∧
      (∀ z, (q z : D) = g (z : D')) ∧
      IsActualTowerPullback p (restrict V Q) (restrict U T) q := by
  have hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f := by
    induction h with
    | refl hf => exact hf
    | step _ _ _ _ ih => exact ih
  have hVU : MapsTo f V U := by intro z hz;rw [hV] at hz;exact hz
  let p : V → U := restrictedOpenMap V U hVU
  have hp := restrictedOpenMap_isSubmersion hf V U hVU
  induction h with
  | refl hf => exact ⟨p,p,fun _ => rfl,fun _ => rfl,IsActualTowerPullback.refl hp⟩
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    obtain ⟨p₀,q₀,hp₀,hq₀,hR⟩ := ih
    have hpSame : p₀ = p := by funext z;exact Subtype.ext (hp₀ z)
    subst p₀
    let A := openPreimage Q V
    let B := openPreimage T U
    let A' := openPreimage (.step Q (g ⁻¹' C) ρ hρ) V
    let B' := openPreimage (.step T C π hπ) U
    let πR : B' → B := fun z => ⟨π z.val,z.property⟩
    let ρR : A' → A := fun z => ⟨ρ z.val,z.property⟩
    have hπR : IsBlowupAlong n ((Subtype.val : B → D) ⁻¹' C) πR :=
      isBlowupAlong_restrict hπ B (B.isOpen.preimage hπ.contMDiff.continuous)
    have hρR : IsBlowupAlong m ((Subtype.val : A → D') ⁻¹' (g ⁻¹' C)) ρR :=
      isBlowupAlong_restrict hρ A (A.isOpen.preimage hρ.contMDiff.continuous)
    have hCR : ((Subtype.val : A → D') ⁻¹' (g ⁻¹' C)) =
        q₀ ⁻¹' ((Subtype.val : B → D) ⁻¹' C) := by
      ext z
      change g z.val ∈ C ↔ (q₀ z).val ∈ C
      rw [hq₀ z]
    have hmap : MapsTo (actualLift hg hπ hρ) A' B' := by
      intro z hz
      change z ∈ (openPreimage (.step Q (g ⁻¹' C) ρ hρ) V : Set Z') at hz
      rw [IsActualTowerPullback.openPreimage_dictionary
        (IsActualTowerPullback.step h hg hπ hρ) U V hV] at hz
      exact hz
    let q : A' → B' := restrictedOpenMap A' B' hmap
    have hq : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ q :=
      (restrictedOpenMap_isSubmersion (IsActualTowerPullback.step h hg hπ hρ).isSubmersion A' B' hmap).contMDiff
    have hsq : πR ∘ q = q₀ ∘ ρR := by
      funext z
      apply Subtype.ext
      change π (actualLift hg hπ hρ z.val) = (q₀ (ρR z)).val
      rw [hq₀ (ρR z)]
      exact congrFun (actualLift_proj_comm hg hπ hρ) z.val
    refine ⟨p,q,fun _ => rfl,fun _ => rfl,?_⟩
    exact IsActualTowerPullback.step_of_actual_square
      (Z := CMfd.of (n := n) B') (Z' := CMfd.of (n := m) A')
      (π := πR) (ρ := ρR) hR hR.isSubmersion hπR hρR hCR q hq hsq

theorem IsActualTowerPullback.exists_actual_restricted_marked_dictionary
    (h : IsActualTowerPullback f Q T g) (U : Opens X) (V : Opens Y)
    (hV : (V : Set Y) = f ⁻¹' (U : Set X)) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hT : IsGeoTestTower M T) :
    ∃ (p : V → U) (q : openPreimage Q V → openPreimage T U),
      (∀ z, (p z : X) = f (z : Y)) ∧
      (∀ z, (q z : D) = g (z : D')) ∧
      IsActualTowerPullback p (restrict V Q) (restrict U T) q ∧
      IsGeoTestTower (markedPullback (m := m) p
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M)) (restrict V Q) ∧
      geoTransformAlong (markedPullback (m := m) p
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M)) (restrict V Q) =
        markedPullback (m := m) q (geoTransformAlong
          (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)) ∧
      (geoTransformAlong (markedPullback (m := m) p
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M)) (restrict V Q)).cosupp =
        q ⁻¹' (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp ∧
      ∀ i : ℕ, ∃ b : (split (restrict V Q) i).1 → (split (restrict U T) i).1,
        IsActualTowerPullback p (head (restrict V Q) i) (head (restrict U T) i) b ∧
        IsGeoTestTower (markedPullback (m := m) p
          (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M)) (head (restrict V Q) i) ∧
        geoTransformAlong (markedPullback (m := m) p
          (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M)) (head (restrict V Q) i) =
          markedPullback (m := m) b (geoTransformAlong
            (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M) (head (restrict U T) i)) ∧
        (geoTransformAlong (markedPullback (m := m) p
          (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M)) (head (restrict V Q) i)).cosupp =
          b ⁻¹' (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M) (head (restrict U T) i)).cosupp := by
  obtain ⟨p,q,hp,hq,hR⟩ := IsActualTowerPullback.exists_actual_open_restriction h U V hV
  have hTU := isGeoTestTower_restrict U hM.isClosedSubmanifold_N hM.isCoherent T hT
  have hMU := IsWellFormed.pullback_val hM U
  obtain ⟨hQ,hwhole⟩ := IsActualTowerPullback.relative_marked_dictionary hR _ hMU hTU
  have hcos := IsActualTowerPullback.relative_cosupport_dictionary hR _ hMU hTU
  refine ⟨p,q,hp,hq,hR,hQ,hwhole,hcos,?_⟩
  intro i
  obtain ⟨b,hb⟩ := hR.head i
  have hTi := ((isGeoTestTower_iff_head_tail
    (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) i).mp hTU).1
  obtain ⟨hQi,hwholei⟩ := IsActualTowerPullback.relative_marked_dictionary hb _ hMU hTi
  have hcosi := IsActualTowerPullback.relative_cosupport_dictionary hb _ hMU hTi
  exact ⟨b,hb,hQi,hwholei,hcosi⟩


theorem IsActualTowerPullback.exists_actual_historical_tail
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (j o : ℕ) :
    let U := ordMask (geoTransformAlong M (head T j)) o
    let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q j)) o
    ∃ (p : V → U) (q : openPreimage (tail Q j) V → openPreimage (tail T j) U),
      markedPullback (m := m) p (compAt M o (head T j)) =
        compAt (markedPullback (m := m) f M) o (head Q j) ∧
      (∀ z, (q z : D) = g (z : D')) ∧
      IsActualTowerPullback p (restrict V (tail Q j)) (restrict U (tail T j)) q := by
  dsimp only
  let U := ordMask (geoTransformAlong M (head T j)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q j)) o
  obtain ⟨a,hhead,htail⟩ := IsActualTowerPullback.simultaneous_split h j
  have hTH := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hmask : (V : Set (split Q j).1) = a ⁻¹' (U : Set (split T j).1) :=
    IsActualTowerPullback.order_mask_dictionary hn hhead M hM hTH o
  obtain ⟨p,q,hp,hq,hR⟩ := IsActualTowerPullback.exists_actual_open_restriction htail U V hmask
  obtain ⟨p',_,hp',hcomp⟩ := IsActualTowerPullback.exists_actual_masked_companion hn hhead M hM hTH o
  have hpp : p' = p := by funext z;exact Subtype.ext ((hp' z).trans (hp z).symm)
  subst p'
  exact ⟨p,q,hcomp,hq,hR⟩

private def HistoricalTailAtIndices (M : MarkedIdeal n X) (Q : BlowupTower Y D')
    (T : BlowupTower X D) (g : D' → D) (os ot js jt : ℕ) : Prop :=
  let U := ordMask (geoTransformAlong M (head T jt)) ot
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q js)) os
  ∃ (p : V → U) (q : openPreimage (tail Q js) V → openPreimage (tail T jt) U),
    markedPullback (m := m) p (compAt M ot (head T jt)) =
      compAt (markedPullback (m := m) f M) os (head Q js) ∧
    (∀ w, (q w : D) = g (w : D')) ∧
    IsActualTowerPullback p (restrict V (tail Q js)) (restrict U (tail T jt)) q

private def OwnHistoricalTailAt (M : MarkedIdeal n X) (Q : BlowupTower Y D')
    (T : BlowupTower X D) (g : D' → D) (z : D') : Prop :=
  HistoricalTailAtIndices (f := f) M Q T g (orderAt (markedPullback (m := m) f M) Q z)
    (orderAt M T (g z)) (runAt (markedPullback (m := m) f M) Q z) (runAt M T (g z))

theorem IsActualTowerPullback.exists_actual_own_historical_tail
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (z : D') :
    OwnHistoricalTailAt (f := f) M Q T g z := by
  have ho := IsActualTowerPullback.orderAt_dictionary hn h M hM hT z
  have hr := IsActualTowerPullback.runAt_dictionary hn h M hM hT z
  unfold OwnHistoricalTailAt HistoricalTailAtIndices
  rw [hr,ho]
  exact IsActualTowerPullback.exists_actual_historical_tail hn h M hM hT (runAt M T (g z)) (orderAt M T (g z))

variable {Λ : Type v} [LinearOrder Λ]

theorem IsActualTowerPullback.exists_historical_controlled_tail
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (hT : IsGeoTestTower M T)
    (F : ∀ {A : CMfd.{u} n}, BlowupTower X A → A → Λ)
    (hF : OrdMonotone M F) (hcan : IsCanonical M F T)
    (y : D) (o : ℕ) (ho : 1 ≤ o) :
    let j := regimeRun (OrdRegime M o) T y
    let U := ordMask (geoTransformAlong M (head T j)) o
    let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q j)) o
    ∃ (p : V → U) (q : openPreimage (tail Q j) V → openPreimage (tail T j) U),
      markedPullback (m := m) p (compAt M o (head T j)) =
        compAt (markedPullback (m := m) f M) o (head Q j) ∧
      (∀ z, (q z : D) = g (z : D')) ∧
      IsActualTowerPullback p (restrict V (tail Q j)) (restrict U (tail T j)) q ∧
      IsGeoTestTower (compAt M o (head T j)) (restrict U (tail T j)) ∧
      IsGeoTestTower (compAt (markedPullback (m := m) f M) o (head Q j)) (restrict V (tail Q j)) ∧
      geoTransformAlong (compAt (markedPullback (m := m) f M) o (head Q j)) (restrict V (tail Q j)) =
        markedPullback (m := m) q (geoTransformAlong (compAt M o (head T j)) (restrict U (tail T j))) ∧
      (geoTransformAlong (compAt (markedPullback (m := m) f M) o (head Q j)) (restrict V (tail Q j))).cosupp =
        q ⁻¹' (geoTransformAlong (compAt M o (head T j)) (restrict U (tail T j))).cosupp ∧
      ∀ i : ℕ, ∃ b : (split (restrict V (tail Q j)) i).1 → (split (restrict U (tail T j)) i).1,
        IsActualTowerPullback p (head (restrict V (tail Q j)) i) (head (restrict U (tail T j)) i) b ∧
        IsGeoTestTower (compAt (markedPullback (m := m) f M) o (head Q j)) (head (restrict V (tail Q j)) i) ∧
        geoTransformAlong (compAt (markedPullback (m := m) f M) o (head Q j)) (head (restrict V (tail Q j)) i) =
          markedPullback (m := m) b (geoTransformAlong (compAt M o (head T j)) (head (restrict U (tail T j)) i)) ∧
        (geoTransformAlong (compAt (markedPullback (m := m) f M) o (head Q j)) (head (restrict V (tail Q j)) i)).cosupp =
          b ⁻¹' (geoTransformAlong (compAt M o (head T j)) (head (restrict U (tail T j)) i)).cosupp := by
  dsimp only
  let j := regimeRun (OrdRegime M o) T y
  let U := ordMask (geoTransformAlong M (head T j)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q j)) o
  have hTH := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  obtain ⟨p,q,hcomp,hq,hR⟩ := IsActualTowerPullback.exists_actual_historical_tail hn h M hM hT j o
  have hTT := isGeoTestTower_companion_tail_of_canonical hn hM hF ho T hT hcan y
  change IsGeoTestTower (compAt M o (head T j)) (restrict U (tail T j)) at hTT
  have hHeadDomain := isInvDomain_geoTransformAlong hM (head T j) hTH
  have hMaskDomain := isInvDomain_pullback_val U hHeadDomain
  have hCompDomain := InvDomainCompanion.isInvDomain_companionAlong (X := CMfd.of (n := n) U) hn hMaskDomain ho
  change IsInvDomain k (compAt M o (head T j)) at hCompDomain
  obtain ⟨hQT,hmark⟩ := IsActualTowerPullback.relative_marked_dictionary hR _ hCompDomain.isWellFormed hTT
  have hcos := IsActualTowerPullback.relative_cosupport_dictionary hR _ hCompDomain.isWellFormed hTT
  rw [hcomp] at hQT hmark hcos
  refine ⟨p,q,hcomp,hq,hR,hTT,hQT,hmark,hcos,?_⟩
  intro i
  obtain ⟨b,hb⟩ := hR.head i
  have hTTi := ((isGeoTestTower_iff_head_tail (compAt M o (head T j)) (restrict U (tail T j)) i).mp hTT).1
  obtain ⟨hQi,hwhole⟩ := IsActualTowerPullback.relative_marked_dictionary hb _ hCompDomain.isWellFormed hTTi
  have hcosi := IsActualTowerPullback.relative_cosupport_dictionary hb _ hCompDomain.isWellFormed hTTi
  rw [hcomp] at hQi hwhole hcosi
  exact ⟨b,hb,hQi,hwhole,hcosi⟩

private def HistoricalControlledTailAtIndices (M : MarkedIdeal n X) (Q : BlowupTower Y D')
    (T : BlowupTower X D) (g : D' → D) (os ot js jt : ℕ) : Prop :=
    let U := ordMask (geoTransformAlong M (head T jt)) ot
    let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q js)) os
    ∃ (p : V → U) (q : openPreimage (tail Q js) V → openPreimage (tail T jt) U),
      markedPullback (m := m) p (compAt M ot (head T jt)) =
        compAt (markedPullback (m := m) f M) os (head Q js) ∧
      (∀ z, (q z : D) = g (z : D')) ∧
      IsActualTowerPullback p (restrict V (tail Q js)) (restrict U (tail T jt)) q ∧
      IsGeoTestTower (compAt M ot (head T jt)) (restrict U (tail T jt)) ∧
      IsGeoTestTower (compAt (markedPullback (m := m) f M) os (head Q js)) (restrict V (tail Q js)) ∧
      geoTransformAlong (compAt (markedPullback (m := m) f M) os (head Q js)) (restrict V (tail Q js)) =
        markedPullback (m := m) q (geoTransformAlong (compAt M ot (head T jt)) (restrict U (tail T jt))) ∧
      (geoTransformAlong (compAt (markedPullback (m := m) f M) os (head Q js)) (restrict V (tail Q js))).cosupp =
        q ⁻¹' (geoTransformAlong (compAt M ot (head T jt)) (restrict U (tail T jt))).cosupp ∧
      ∀ i : ℕ, ∃ b : (split (restrict V (tail Q js)) i).1 → (split (restrict U (tail T jt)) i).1,
        IsActualTowerPullback p (head (restrict V (tail Q js)) i) (head (restrict U (tail T jt)) i) b ∧
        IsGeoTestTower (compAt (markedPullback (m := m) f M) os (head Q js)) (head (restrict V (tail Q js)) i) ∧
        geoTransformAlong (compAt (markedPullback (m := m) f M) os (head Q js)) (head (restrict V (tail Q js)) i) =
          markedPullback (m := m) b (geoTransformAlong (compAt M ot (head T jt)) (head (restrict U (tail T jt)) i)) ∧
        (geoTransformAlong (compAt (markedPullback (m := m) f M) os (head Q js)) (head (restrict V (tail Q js)) i)).cosupp =
          b ⁻¹' (geoTransformAlong (compAt M ot (head T jt)) (head (restrict U (tail T jt)) i)).cosupp

private def OwnHistoricalControlledAt (M : MarkedIdeal n X) (Q : BlowupTower Y D')
    (T : BlowupTower X D) (g : D' → D) (z : D') : Prop :=
  HistoricalControlledTailAtIndices (f := f) M Q T g (orderAt (markedPullback (m := m) f M) Q z)
    (orderAt M T (g z)) (runAt (markedPullback (m := m) f M) Q z) (runAt M T (g z))

variable (L : ∀ {A : CMfd.{u} n}, MarkedIdeal n A → ∀ {B : CMfd.{u} n}, BlowupTower A B → B → Λ)

theorem IsActualTowerPullback.exists_own_historical_controlled_tail
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (hT : IsGeoTestTower M T)
    (hcan : IsCanonical M (genInv L M) T) (z : D')
    (ho : 1 ≤ orderAt M T (g z)) : OwnHistoricalControlledAt (f := f) M Q T g z := by
  have hord := IsActualTowerPullback.orderAt_dictionary hn h M hM hT z
  have hrun := IsActualTowerPullback.runAt_dictionary hn h M hM hT z
  unfold OwnHistoricalControlledAt HistoricalControlledTailAtIndices
  rw [hrun,hord]
  exact IsActualTowerPullback.exists_historical_controlled_tail hn h M hM hT
    (genInv L M) (ordMonotone_genInv L M) hcan (g z) (orderAt M T (g z)) ho

theorem exists_original_only_historical_controlled_tails
    (hn : 0 < n)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) (hcan : IsCanonical M (genInv L M) T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      Q.length = T.length ∧
      HironakaSmoothSubmersionOrderedChoiceBaseChange.HolomorphicSquarePullback f g Q.proj T.proj ∧
      ∀ z : D', (OwnHistoricalTailAt (f := f) M Q T g z ∧
        (1 ≤ orderAt M T (g z) → OwnHistoricalControlledAt (f := f) M Q T g z)) := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  refine ⟨D',Q,g,h,h.isSubmersion,h.length_eq,h.universal,?_⟩
  intro z
  exact ⟨IsActualTowerPullback.exists_actual_own_historical_tail hn h M hM hT z,
    fun ho => IsActualTowerPullback.exists_own_historical_controlled_tail L hn h M hM hT hcan z ho⟩

end
end Hironaka.HironakaSmoothSubmersionHistoricalControlledTail
