import Hironaka.Resolution.HironakaG1LaterOrderMaskSupportedLocal
import Hironaka.Resolution.HironakaG8LocalContactStage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterOrderMaskNonfactor
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec
  CompanionRebase CompanionReductionAlong GeneralValue NonmonomialOrderTail
  HironakaG8LocalContactStage HironakaG8E4cCompanion ContactRepresentative
  RestrictedIdealExtension MarkedIdealOperationsAlong.MarkedIdeal InvDomainTowerAlong
  RelativePrincipalizationSpan GermIdealPullbackCalculus

private theorem re_pullback_diffeo {n : ℕ} {X Y : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    {L J : MarkedIdeal n Y} (h : RestrictEquiv L J)
    (hL : L.ideal.IsCoherent) (hJ : J.ideal.IsCoherent) :
    RestrictEquiv (MarkedIdeal.pullback e L) (MarkedIdeal.pullback e J) := by
  apply restrictEquiv_pullback_map e.contMDiff h hL hJ rfl rfl _ rfl rfl rfl rfl
  change L.E.map (e ⁻¹' ·) = J.E.map (e ⁻¹' ·)
  rw [h.E_eq]

set_option maxHeartbeats 900000 in
/-- A local restricted comparison persists on the corresponding open
inside another mask, with the exact nested pullbacks of both records. -/
theorem restrictEquiv_on_nested_window {n : ℕ} {X : CMfd.{0} n}
    (L J : MarkedIdeal n X) (hL : L.ideal.IsCoherent) (hJ : J.ideal.IsCoherent)
    (C W : Opens X)
    (h : RestrictEquiv (MarkedIdeal.pullback (Subtype.val : W → X) L)
      (MarkedIdeal.pullback (Subtype.val : W → X) J)) :
    let V := MaxLocusLocal.nestedOpens C W
    RestrictEquiv
      (MarkedIdeal.pullback (Subtype.val : V → C) (MarkedIdeal.pullback (Subtype.val : C → X) L))
      (MarkedIdeal.pullback (Subtype.val : V → C) (MarkedIdeal.pullback (Subtype.val : C → X) J)) := by
  intro V
  let N := C ⊓ W
  let A := CMfd.of (n := n) W
  have hNW : N ≤ W := inf_le_right
  have hNC : N ≤ C := inf_le_left
  have hAlias : V = MaxLocusLocal.nestedOpens C N := by
    ext z
    exact ⟨fun hz => ⟨z.property, hz⟩, fun hz => hz.2⟩
  have hv : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : A → X) := contMDiff_subtype_val
  have h₁ := restrictEquiv_pullback_val (MaxLocusLocal.nestedOpens W N) h
    (isCoherent_pullback hv hL) (isCoherent_pullback hv hJ)
  let e := MaxLocusLocal.nestedOpensDiffeo (n := n) hNW
  have he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : MaxLocusLocal.nestedOpens W N → W) := contMDiff_subtype_val
  have h₂ := re_pullback_diffeo e.symm h₁
    (isCoherent_pullback he (isCoherent_pullback hv hL))
    (isCoherent_pullback he (isCoherent_pullback hv hJ))
  rw [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hL hNW,
    MaxLocusLocal.pullback_symm_nestedOpensDiffeo hJ hNW] at h₂
  rw [hAlias, MaxLocusLocal.pullback_val_pullback_val hL hNC,
    MaxLocusLocal.pullback_val_pullback_val hJ hNC]
  have hv' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : N → X) := contMDiff_subtype_val
  exact re_pullback_diffeo (MaxLocusLocal.nestedOpensDiffeo (n := n) hNC) h₂
    (isCoherent_pullback hv' hL) (isCoherent_pullback hv' hJ)

set_option maxHeartbeats 900000 in
/-- Where the true-mark companion equals the carrier restriction, the same
restricted comparison holds on the corresponding part of its literal order mask. -/
theorem initial_companion_restrictEquiv_on_nonfactor_window {n k : ℕ}
    (hn : 0 < n) {X : CMfd.{0} n} (L : MarkedIdeal n X) (hL : IsInvDomain k L)
    (W : Opens X)
    (hFactor : let Lw := MarkedIdeal.pullback (Subtype.val : W → X) L
      companionOf n Lw Lw.d = (⟨Lw.N, Lw.E, restrictOn n Lw.N Lw.ideal, Lw.d⟩ :
        MarkedIdeal n (CMfd.of (n := n) W))) :
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower X X)) L.d
    let V := MaxLocusLocal.nestedOpens C W
    let J := compAt L L.d (.refl : BlowupTower X X)
    RestrictEquiv
      (MarkedIdeal.pullback (Subtype.val : V → C) (MarkedIdeal.pullback (Subtype.val : C → X) L))
      (MarkedIdeal.pullback (Subtype.val : V → C) J) := by
  intro C V J
  let F := companionOf n L L.d
  let Lw : MarkedIdeal n (CMfd.of (n := n) W) := MarkedIdeal.pullback (Subtype.val : W → X) L
  have hF : F.IsWellFormed := companion_wf hL hn hL.one_le_d
  have hW : IsInvDomain k Lw := isInvDomain_pullback_val W hL
  have hEq : MarkedIdeal.pullback (Subtype.val : C → X) F = J :=
    pullback_val_companionOf hn hL.isWellFormed hL.isNonzeroAlongAt C L.d
  have h : RestrictEquiv Lw (MarkedIdeal.pullback (Subtype.val : W → X) F) := by
    rw [show F = companionOf n L L.d from rfl,
      pullback_val_companionOf hn hL.isWellFormed hL.isNonzeroAlongAt W L.d]
    change RestrictEquiv Lw (companionOf n Lw Lw.d)
    rw [hFactor]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hW.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  rw [← hEq]
  exact restrictEquiv_on_nested_window L F hL.isWellFormed.isCoherent hF.isCoherent C W h

set_option maxHeartbeats 1000000 in
/-- A nonfactor window in the ambient upper stage compares the initial
companion with its literal selected record on the corresponding order window. -/
theorem initial_companion_restrictEquiv_of_ambient_nonfactor {n k : ℕ} {Y : CMfd.{0} n}
    (hn : 0 < n) (K : MarkedIdeal n Y) (hK : K.ideal.IsCoherent)
    {O W : Opens Y} (hWO : W ≤ O)
    (hL : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → Y) K))
    (hW : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → Y) K))
    (hFactor : let Lw := MarkedIdeal.pullback (Subtype.val : W → Y) K
      companionOf n Lw Lw.d = (⟨Lw.N, Lw.E, restrictOn n Lw.N Lw.ideal, Lw.d⟩ :
        MarkedIdeal n (CMfd.of (n := n) W))) :
    let A := CMfd.of (n := n) O
    let L : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : O → Y) K
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let V := MaxLocusLocal.nestedOpens C (MaxLocusLocal.nestedOpens O W)
    let J := compAt L L.d (.refl : BlowupTower A A)
    RestrictEquiv
      (MarkedIdeal.pullback (Subtype.val : V → C) (MarkedIdeal.pullback (Subtype.val : C → A) L))
      (MarkedIdeal.pullback (Subtype.val : V → C) J) := by
  intro A L C V J
  let F := companionOf n L L.d
  let W₀ := MaxLocusLocal.nestedOpens O W
  let Lw : MarkedIdeal n (CMfd.of (n := n) W) := MarkedIdeal.pullback (Subtype.val : W → Y) K
  let Jw := companionOf n Lw Lw.d
  let e := MaxLocusLocal.nestedOpensDiffeo (n := n) hWO
  have hF : F.IsWellFormed := companion_wf (A := L) hL hn hL.one_le_d
  have hJw : Jw.IsWellFormed := companion_wf (A := Lw) hW hn hW.one_le_d
  have hBase : RestrictEquiv Lw Jw := by
    unfold Jw
    rw [hFactor]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hW.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  have hEq : MarkedIdeal.pullback (Subtype.val : C → A) F = J :=
    pullback_val_companionOf (M := A) (𝔪 := L) hn hL.isWellFormed hL.isNonzeroAlongAt C L.d
  have hL₀ : MarkedIdeal.pullback (Subtype.val : W₀ → O) L = MarkedIdeal.pullback e Lw :=
    MaxLocusLocal.pullback_val_pullback_val hK hWO
  have hF₀ : MarkedIdeal.pullback (Subtype.val : W₀ → O) F = MarkedIdeal.pullback e Jw := by
    rw [show F = companionOf n L L.d from rfl,
      pullback_val_companionOf (M := A) (𝔪 := L) hn hL.isWellFormed hL.isNonzeroAlongAt W₀ L.d, hL₀]
    exact (pullback_diffeo_companionOf hn e (𝔪 := Lw) hW.isWellFormed hW.isNonzeroAlongAt Lw.d).symm
  have h₀ : RestrictEquiv (MarkedIdeal.pullback (Subtype.val : W₀ → O) L)
      (MarkedIdeal.pullback (Subtype.val : W₀ → O) F) := by
    rw [hL₀, hF₀]
    exact re_pullback_diffeo e hBase hW.isWellFormed.isCoherent hJw.isCoherent
  rw [← hEq]
  exact restrictEquiv_on_nested_window L F hL.isWellFormed.isCoherent hF.isCoherent C W₀ h₀

end
end Hironaka.HironakaG1LaterOrderMaskNonfactor
