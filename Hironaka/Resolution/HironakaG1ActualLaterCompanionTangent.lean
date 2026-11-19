import Hironaka.Resolution.HironakaG1ActualLaterOrderRun
import Hironaka.Resolution.HironakaG1LaterPositiveMaskContact
import Hironaka.Resolution.HironakaG8E4cCompanion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ActualLaterCompanionTangent
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain GeneralValue
  CompanionRebase CompanionReductionAlong NonmonomialOrderTail
  HironakaG1ActualLaterOrderRun HironakaG1LaterSelectedActualOrder
  HironakaG1LaterPositiveMaskContact HironakaG1PositiveNormalPhase
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualOpenZeroSectionDifferentials HironakaActualOpenTangentDescent
  InvDomainMemberRestriction InvDomainTowerAlong BoundaryCount RelativePrincipalizationSpan
  TangentDirectionAlong ContactEquivalenceAlong DerivativeIdealAlong DerivativeIdealAlongEtale
  HironakaActualRawCompanionNaturality HironakaG8E4cCompanion MarkedIdealOperationsAlong RestrictedIdealExtension RestrictLeCalculus MarkedIdealOperationsAlong.MarkedIdeal
open HomogenizedGlueingTower (strictAlong)
open HomogenizedGlueingLiftAlong HironakaActualRelativeNormalGeometry

private theorem hol {m : ℕ} {X : CMfd.{0} m} {K : MarkedIdeal m X}
    (hK : K.ideal.IsCoherent) :
    ∀ x f, K.ideal.mem x f → HolomorphicAt m f x :=
  fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK hf

set_option maxHeartbeats 1600000 in
/-- A window with zero retained exponents and a window of prescribed
normal contact give a genuine tangent to the literal initial companion. -/
theorem initial_companion_tangent_of_windows {m k : ℕ} {Y : CMfd.{0} m}
    (hm : 0 < m) (K : MarkedIdeal m Y) (hK : K.IsWellFormed)
    {O W V : Opens Y} (hWO : W ≤ O) (u : Y → ℂ)
    (hL : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → Y) K))
    (hW : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → Y) K))
    (hFactor : let Lw := MarkedIdeal.pullback (Subtype.val : W → Y) K
      companionOf m Lw Lw.d = (⟨Lw.N, Lw.E, restrictOn m Lw.N Lw.ideal, Lw.d⟩ :
        MarkedIdeal m (CMfd.of (n := m) W)))
    (hTan : IsTangentDirectionAlong K.N K.ideal K.d V u) :
    let A := CMfd.of (n := m) O
    let L : MarkedIdeal m A := MarkedIdeal.pullback (Subtype.val : O → Y) K
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let J := compAt L L.d (.refl : BlowupTower A A)
    let f : C → Y := fun z => z.val.val
    IsTangentDirectionAlong J.N J.ideal J.d (f ⁻¹' ((W : Set Y) ∩ V)) (u ∘ f) := by
  intro A L C J f
  let Lw : MarkedIdeal m (CMfd.of (n := m) W) := MarkedIdeal.pullback (Subtype.val : W → Y) K
  let Jw := companionOf m Lw Lw.d
  let J₀ := companionOf m L L.d
  have hJ₀ : J₀.IsWellFormed := companion_wf (A := L) (o := L.d) hL hm hL.one_le_d
  have hJw : Jw.IsWellFormed := companion_wf (A := Lw) (o := Lw.d) hW hm hW.one_le_d
  have htW := isTangentDirectionAlong_pullback
    (fun z : W => ⟨_, isLocalInverseAt_val (n := m) W z⟩) (hol hK.isCoherent) hTan
  have htJw : IsTangentDirectionAlong Jw.N Jw.ideal Jw.d
      ((Subtype.val : W → Y) ⁻¹' (V : Set Y)) (u ∘ (Subtype.val : W → Y)) := by
    unfold Jw
    rw [hFactor]
    exact ⟨htW.isOpen, fun z hz =>
      iterDerivIdealAlong_mono (N := Lw.N) (le_restrictOn hW.isWellFormed.isCoherent)
        (Lw.d - 1) z _ (htW.mem z hz), htW.multiplicity_one⟩
  let W₀ := MaxLocusLocal.nestedOpens O W
  let e := MaxLocusLocal.nestedOpensDiffeo (n := m) hWO
  have hA : MarkedIdeal.pullback (Subtype.val : W₀ → O) J₀ = MarkedIdeal.pullback e Jw := by
    rw [show J₀ = companionOf m L L.d from rfl,
      pullback_val_companionOf (M := A) (𝔪 := L) hm hL.isWellFormed hL.isNonzeroAlongAt W₀ L.d,
      MaxLocusLocal.pullback_val_pullback_val hK.isCoherent hWO]
    exact (pullback_diffeo_companionOf hm e (𝔪 := Lw) hW.isWellFormed hW.isNonzeroAlongAt Lw.d).symm
  have htW₀ := isTangentDirectionAlong_pullback
    (fun z : W₀ => ⟨e.symm, isLocalInverseAt_diffeo e z⟩) (hol hJw.isCoherent) htJw
  change IsTangentDirectionAlong (MarkedIdeal.pullback e Jw).N
    (MarkedIdeal.pullback e Jw).ideal (MarkedIdeal.pullback e Jw).d
    {z : W₀ | z.val.val ∈ V} ((u ∘ (Subtype.val : O → Y)) ∘ (Subtype.val : W₀ → O)) at htW₀
  rw [← hA] at htW₀
  have htO := isTangentDirectionAlong_of_open_pullback J₀.N hJ₀.isClosedSubmanifold_N J₀.ideal
    hJ₀.isCoherent J₀.d W₀ {z : W₀ | z.val.val ∈ V} (u ∘ (Subtype.val : O → Y)) htW₀
  have him : (Subtype.val : W₀ → O) '' {z : W₀ | z.val.val ∈ V} =
      (Subtype.val : O → Y) ⁻¹' ((W : Set Y) ∩ V) := by
    ext z
    exact ⟨fun ⟨w, hw, heq⟩ => heq ▸ ⟨w.property, hw⟩,
      fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩⟩
  rw [him] at htO
  have htC := isTangentDirectionAlong_pullback
    (fun z : C => ⟨_, isLocalInverseAt_val (n := m) C z⟩) (hol hJ₀.isCoherent) htO
  have hJ : MarkedIdeal.pullback (Subtype.val : C → O) J₀ = J := by
    exact pullback_val_companionOf (M := A) (𝔪 := L) hm hL.isWellFormed hL.isNonzeroAlongAt C L.d
  change IsTangentDirectionAlong (MarkedIdeal.pullback (Subtype.val : C → O) J₀).N
    (MarkedIdeal.pullback (Subtype.val : C → O) J₀).ideal
    (MarkedIdeal.pullback (Subtype.val : C → O) J₀).d
    (f ⁻¹' ((W : Set Y) ∩ V)) (u ∘ f) at htC
  rwa [hJ] at htC

set_option maxHeartbeats 1800000 in
/-- The actual first order companion of the later positive lower tail has
a local normal direction at its initial anchor. Its zero trace there is
the pullback of the upper strict section, on the literal order mask. -/
theorem exists_actual_later_initial_order_companion_tangent {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let J := compAt L L.d (.refl : BlowupTower A A)
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    let f : C → _ := fun z => z.val.val
    ∃ hp : p ∈ O, ∃ hq : (⟨p, hp⟩ : O) ∈ C,
      ∃ (W : Set C) (u : _ → ℂ),
        (⟨⟨p, hp⟩, hq⟩ : C) ∈ W ∧ u p = 0 ∧
        IsInvDomain (k + 1) J ∧
        IsTangentDirectionAlong J.N J.ideal J.d W (u ∘ f) ∧
        J.N ∩ {z : C | u (f z) = 0} ∩ W = J.N ∩ f ⁻¹' D ∩ W := by
  intro X P r H S p O A L C J D f
  let R := invFamily (Nat.succ_pos n) (k + 1)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  obtain ⟨hBarTest, hTest, hCos⟩ :=
    Seq.StepOneBridge.isGeoTestTower_of_isCanonical R P hP hMax (Nat.succ_pos n) T hCan
  obtain ⟨hReg, hpBar⟩ :=
    stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarTest (hCos.symm ▸ hy) hNS
  rw [hLevel] at hReg hpBar
  have hHeadTest := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  obtain ⟨W, _, hpW, hWO, hW, _, _, hFactor, _⟩ :=
    exists_later_selected_actual_normal_order Q hQ H hHeadTest p hpBar hReg.1 hReg.2
  have hpP := ((HironakaG8HomStable.bar_local_any_boundary P hP).wEquiv.2 H).2 hHeadTest ▸ hpBar
  obtain ⟨V, _, u, hpV, hpD, _, _, _, hTanV, hTrace⟩ :=
    later_positive_mask_contact Q hQ H hHeadTest p hpP hReg.1 hReg.2
  obtain ⟨_, _, _, _, hpO, hpL, hL, _, _⟩ :=
    original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
  obtain ⟨hp, _, _, hq, hJ, _, _, _, _⟩ :=
    original_upper_positive_successor_at_initial_order_companion Q hQ T hCan y hy hLevel hNS
  let B := geoTransformAlong (barMarked P) H
  let K := memberRestrict B (membersThrough B.E (origMembers P H) p)
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked P hP.isWellFormed) H
      ((isGeoTestTower_iff_head_tail (barMarked P) T r).mp hBarTest).1
  have hK : K.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hB _
  have htV := isTangentDirectionAlong_of_open_pullback K.N hK.isClosedSubmanifold_N K.ideal
    hK.isCoherent K.d V univ u hTanV
  have him : (Subtype.val : V → _) '' (univ : Set V) = (V : Set _) := by
    ext z
    exact ⟨fun ⟨w, _, hw⟩ => hw ▸ w.property, fun hz => ⟨⟨z, hz⟩, trivial, rfl⟩⟩
  rw [him] at htV
  have htJ := initial_companion_tangent_of_windows (Nat.succ_pos n) K hK hWO u hL hW hFactor htV
  have hpC : (⟨p, hp⟩ : O) ∈ C := by
    convert hq using 1
    exact Subtype.ext (proj_restrict O S ⟨y, hp⟩).symm
  have hpN : (⟨p, hpV⟩ : V) ∈ (MarkedIdeal.pullback (Subtype.val : V → _) K).N := by
    exact L.cosupp_subset_N hpL
  have hpu : u p = 0 :=
    ((Set.ext_iff.mp hTrace (⟨p, hpV⟩ : V)).mpr ⟨hpN, hpD⟩).2
  let Ω : Set C := {z | f z ∈ W ∧ f z ∈ V}
  have ht : IsTangentDirectionAlong J.N J.ideal J.d Ω (u ∘ f) := htJ
  refine ⟨hp, hpC, Ω, u, ⟨hpW, hpV⟩, hpu, hJ, ht, ?_⟩
  ext z
  have hCarrier : z ∈ J.N ↔ f z ∈ K.N := by
    change z ∈ (companionOf (n + 1) _ L.d).N ↔ _
    simp only [companionOf, companionAlong_N, geoTransformAlong_refl]
    rfl
  constructor
  · rintro ⟨⟨hz, hu⟩, hw⟩
    have hz' := (Set.ext_iff.mp hTrace (⟨f z, hw.2⟩ : V)).mp ⟨hCarrier.mp hz, hu⟩
    exact ⟨⟨hz, hz'.2⟩, hw⟩
  · rintro ⟨⟨hz, hd⟩, hw⟩
    have hz' := (Set.ext_iff.mp hTrace (⟨f z, hw.2⟩ : V)).mpr ⟨hCarrier.mp hz, hd⟩
    exact ⟨⟨hz, hz'.2⟩, hw⟩

end
end Hironaka.HironakaG1ActualLaterCompanionTangent
