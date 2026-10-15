/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalContactRemainderSmoothNaturality
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalContactHistory
/-! Actual original-only smooth lower diagrams. Real selected opens and maps
are constructed internally. The source contact uses the transported ORIGINAL
choice; independently chosen source-contact comparison is not asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalActualSmoothLowerDiagram
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ContactStageKept
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain TangentDirectionAlong
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderTestTower
  HironakaOriginalNoncanonicalRemainderPresentation HironakaOriginalContactRemainderSmoothNaturality
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionContactParameterCharts HironakaSmoothSubmersionContactParameterCoefficientIdeals
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionOriginalContactHistory
  HironakaSmoothSubmersionCartesianTower HironakaStepOneSpecialAnalyticLoci
  HironakaSmoothSubmersionHistoricalCompanionMasks
open ResolutionInvariantSpec (IsInvDomain)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y : CMfd.{u} m}

/-- Actual selected complements and real submersion restriction supply the
ENTIRE lower marked diagram, with no caller open/map/equality certificate. -/
theorem exists_actual_remainder_open_smooth_diagram {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1 ≤ L.d) (b : ℕ) :
    let P := markedPullback (m := m) f L
    let G := remainderOpen L hN
    ∃ hPN : IsClosedSubmanifold m P.N,
      let G' := remainderOpen P hPN
      ∃ q : G' → G, (G' : Set Y)=f ⁻¹' (G : Set X) ∧
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ q ∧
        (∀ z,(q z : X)=f (z : Y)) ∧
        markedPullback (m := m) q (MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L b)) =
          MarkedIdeal.pullback (Subtype.val : G' → Y) (contactRemainderMarked P b) := by
  dsimp only
  let P := markedPullback (m := m) f L
  let G := remainderOpen L hN
  have hPN : IsClosedSubmanifold m P.N := isClosedSubmanifold_preimage_submersion hf hN
  let G' := remainderOpen P hPN
  have hSelected := selectedComponents_preimage_submersion hf L hN hI hd
  have hG : (G' : Set Y)=f ⁻¹' (G : Set X) := by
    change (selectedComponents (n := m) P.N P.cosupp)ᶜ=
      f ⁻¹' (selectedComponents (n := n) L.N L.cosupp)ᶜ
    rw [hSelected]
    rfl
  have hMaps : MapsTo f G' G := fun z hz => (Set.ext_iff.mp hG z).mp hz
  let q : G' → G := restrictedOpenMap G' G hMaps
  have hq := restrictedOpenMap_isSubmersion hf G' G hMaps
  have hR := contactRemainderMarked_markedPullback hf L hN hI hd b
  let R := contactRemainderMarked L b
  have hcR : R.ideal.IsCoherent := hI
  refine ⟨hPN,q,hG,hq,fun _ => rfl,?_⟩
  change markedPullback (m := m) q (markedPullback (m := n) (Subtype.val : G → X) R) =
    markedPullback (m := m) (Subtype.val : G' → Y) (contactRemainderMarked P b)
  rw [←hR]
  rw [←whole_parameter_markedPullback_comp (X := X) (Y := CMfd.of (n := n) G)
      (Z := CMfd.of (n := m) G') contMDiff_subtype_val hq.contMDiff R hcR,
    ←whole_parameter_markedPullback_comp (X := X) (Y := Y)
      (Z := CMfd.of (n := m) G') hf.contMDiff contMDiff_subtype_val R hcR]
  rfl

/-- ONLY genuine original inputs internally choose the actual smooth source
history and nonzero lower diagram, including the true source dimension shift. -/
theorem exists_original_test_actual_smooth_lower_diagram :
    ∀ {f : Y → X}
    (_hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (_hM : IsInvDomain (k+2) M)
    (_hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (_hT : IsGeoTestTower M T)
    (y : D) (_hy : y ∈ (geoTransformAlong M T).cosupp),
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q=markedPullback (m := m) g (geoTransformAlong M T) ∧
      let w := (tangentChoice M (T.proj y)).2
      ∃ U : Opens X,(U : Set X)=(tangentChoice M (T.proj y)).1 ∧ T.proj y ∈ U ∧
        IsTangentDirectionAlong M.N M.ideal M.d U w ∧
        let V := openPreimage T U
        let L := contactMarkedKept M w T V
        ∃ hLN : IsClosedSubmanifold n L.N,L.ideal.IsCoherent ∧
          let G := remainderOpen (X := CMfd.of (n := n) V) L hLN
          let A := MarkedIdeal.pullback (Subtype.val : G → V) (contactRemainderMarked L M.E.length)
          IsInvDomain (k+1) A ∧
          ∃ (V' : Opens D') (p : V' → V),
            (V' : Set D')=g ⁻¹' (V : Set D) ∧
            Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ p ∧
            (∀ z,(p z : D)=g (z : D')) ∧
            let P := markedPullback (m := m) p L
            P=contactMarkedKept (markedPullback (m := m) f M) (w ∘ f) Q V' ∧
            ∃ hPN : IsClosedSubmanifold m P.N,
              let G' := remainderOpen (X := CMfd.of (n := m) V') P hPN
              let B := MarkedIdeal.pullback (Subtype.val : G' → V') (contactRemainderMarked P M.E.length)
              ∃ q : G' → G, (G' : Set V')=p ⁻¹' (G : Set V) ∧
                Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ q ∧
                (∀ z,(q z : V)=p (z : V')) ∧
                markedPullback (m := m) q A=B ∧ IsInvDomain (k+1+(m-n)) B := by
  intro f hf M hM hmax T hT y hy
  obtain ⟨D',Q,g,hCart,hg,_hLen,_hSquare,hQ,hCurrent,_hw,_hCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed T hT
  obtain ⟨U,hU,hyU,hw,hLN,hI,hA,_hPoint⟩ :=
    exists_original_test_nonzero_contact_domain M hM hmax T hT y hy
  refine ⟨D',Q,g,hCart,hg,hQ,hCurrent,U,hU,hyU,hw,hLN,hI,hA,?_⟩
  let V := openPreimage T U
  let L := contactMarkedKept M (tangentChoice M (T.proj y)).2 T V
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 _).1.mpr hT
  obtain ⟨V',p,hV',hp,hpcoord,hContact⟩ :=
    IsActualTowerPullback.exists_original_contact_open_record hCart M hM.isWellFormed hBar
      (tangentChoice M (T.proj y)).2 V
  obtain ⟨hPN,q,hG',hq,hqcoord,hLower⟩ := exists_actual_remainder_open_smooth_diagram
    (X := CMfd.of (n := n) V) (Y := CMfd.of (n := m) V') hp L hLN hI
      (ContactIndependenceAlong.one_le_coeffMarkedAlong_d _) M.E.length
  have hSource := isInvDomain_markedPullback_submersion hq _ hA
  rw [hLower] at hSource
  exact ⟨V',p,hV',hp,hpcoord,hContact,hPN,q,hG',hq,hqcoord,hLower,hSource⟩

end
end Hironaka.HironakaOriginalActualSmoothLowerDiagram
