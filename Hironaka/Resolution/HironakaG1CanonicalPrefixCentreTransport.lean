import Hironaka.Resolution.HironakaG11PresClassTransport
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenPullback

/-!
# Whole canonical centre ideals at the same actual prefix

Full initial presentation class data and an actual current-prefix structural
isomorphism give current cosupport/value transport. No full-carrier or empty-
boundary assumption is used, and values are never recomputed at the identity
tower after transforming the record. The resulting canonical centre equality
is consumed by the held entire native ideal/open-pullback dictionaries.

Blueprint FIRST: `hironaka-g1-canonical-prefix-centre-transport.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1CanonicalPrefixCentreTransport

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdealBiholomorphism ResolutionInvariantSeq
  HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n k : ℕ} {Λ : Type*} [LinearOrder Λ]

/-- The canonical level centre on the ACTUAL current open of the SAME prefix. -/
def centreTrace (R : ResolutionInvariant.{0} n k Λ)
    {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (U : Opens X) (lam : Λ) : Set (openPreimage T U) :=
  {p | (p : Y) ∈ (geoTransformAlong M T).cosupp ∧ R.inv M T (p : Y) = lam}

private def nativeOverlapIso {V V' : CMfd.{0} n}
    (e : V' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) V' ≅
      ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) V where
  hom := ChartedSpace.locallyRingedSpaceMap e e.contMDiff
  inv := ChartedSpace.locallyRingedSpaceMap e.symm e.symm.contMDiff
  hom_inv_id := by
    rw [← ChartedSpace.locallyRingedSpace_comp]
    have h : (e.symm ∘ e : V' → V') = id := funext e.symm_apply_apply
    simpa only [h] using ChartedSpace.locallyRingedSpace_id 𝓘(ℂ, ComplexModel n) V'
  inv_hom_id := by
    rw [← ChartedSpace.locallyRingedSpace_comp]
    have h : (e ∘ e.symm : V → V) = id := funext e.apply_symm_apply
    simpa only [h] using ChartedSpace.locallyRingedSpace_id 𝓘(ℂ, ComplexModel n) V

private theorem nativeOverlap_isOpenImmersion {V V' : CMfd.{0} n}
    (e : V' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V) :
    LocallyRingedSpace.IsOpenImmersion (ChartedSpace.locallyRingedSpaceMap e e.contMDiff) := by
  have : IsIso (ChartedSpace.locallyRingedSpaceMap e e.contMDiff) := by
    change IsIso (nativeOverlapIso e).hom
    infer_instance
  infer_instance

section Overlap

variable (B : BMInvariant n (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  {X X' : CMfd.{0} n} {M : MarkedIdeal n X} {N : MarkedIdeal n X'}
  (U : Opens X) (U' : Opens X')
  (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
  (hM : IsInvDomain k M) (hN : IsInvDomain k N)
  (hEq : LocWPEquiv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) M))
    (MarkedIdeal.pullback (Subtype.val : U' → X') N))
  (hd : M.d = N.d)
  (hE : (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) M)).E =
    (MarkedIdeal.pullback (Subtype.val : U' → X') N).E)
  (hdim : SameCarrierDim
    (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) M))
    (MarkedIdeal.pullback (Subtype.val : U' → X') N))
  (hexp : ExpAgree
    (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) M))
    (MarkedIdeal.pullback (Subtype.val : U' → X') N))
  {Y Y' : CMfd.{0} n} {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
  (hcan : IsCanonical M (B.toResolutionInvariant.inv M) T)
  (hcan' : IsCanonical N (B.toResolutionInvariant.inv N) T')
  (χ : CMfd.of (n := n) (openPreimage T' U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
    CMfd.of (n := n) (openPreimage T U))
  (hiso : IsTowerIso Φ (restrict U' T') (restrict U T) χ)

include hM hN hEq hd hE hdim hexp hcan hcan' hiso

/-- Current values/cosupports agree along the SAME actual canonical prefixes.
All initial divisor members and their data remain present in hE/hexp and T/T'. -/
theorem cosupp_value_transport (p : openPreimage T' U') :
    ((((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong M T).cosupp ↔
        (p : Y') ∈ (geoTransformAlong N T').cosupp) ∧
      (((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong M T).cosupp →
        B.toResolutionInvariant.inv N T' p = B.toResolutionInvariant.inv M T (χ p))) := by
  let R := B.toResolutionInvariant
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let A := MarkedIdeal.pullback Φ MU
  let D := MarkedIdeal.pullback (Subtype.val : U' → X') N
  have hMU : IsInvDomain k MU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hA : IsInvDomain k A := InvDomainTowerAlong.isInvDomain_pullback Φ hMU
  have hD : IsInvDomain k D := InvDomainTowerAlong.isInvDomain_pullback_val U' hN
  have hcanU : IsCanonical MU (R.inv MU) (restrict U T) :=
    Seq.ResolutionInvariantExt.isCanonical_restrict R hM U T hcan
  have hcanA : IsCanonical A (R.inv A) (restrict U' T') :=
    Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hMU Φ hiso hcanU
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM T hcan
  have ht' := R.isInvValue.isGeoTestTower_of_isCanonical hN T' hcan'
  have hUt := R.isInvValue.isGeoTestTower_of_isCanonical hMU (restrict U T) hcanU
  have hAt := R.isInvValue.isGeoTestTower_of_isCanonical hA (restrict U' T') hcanA
  have hcosU := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent U T ht
  have hcosU' := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hN.isWellFormed.isClosedSubmanifold_N hN.isWellFormed.isCoherent U' T' ht'
  have hcosA : (geoTransformAlong A (restrict U' T')).cosupp =
      χ ⁻¹' (geoTransformAlong MU (restrict U T)).cosupp :=
    IsTowerIso.cosupp_geoTransformAlong Φ hMU.isWellFormed.isClosedSubmanifold_N
      hMU.isWellFormed.isCoherent hiso hUt
  have hcosAD : (geoTransformAlong A (restrict U' T')).cosupp =
      (geoTransformAlong D (restrict U' T')).cosupp :=
    ((LocEquiv.wEquiv hEq).2 (restrict U' T')).2 hAt
  have hleft : ((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong M T).cosupp ↔
      p ∈ (geoTransformAlong A (restrict U' T')).cosupp := by
    rw [hcosA, mem_preimage, hcosU]
    rfl
  have hright : p ∈ (geoTransformAlong D (restrict U' T')).cosupp ↔
      (p : Y') ∈ (geoTransformAlong N T').cosupp := by
    rw [hcosU']
    rfl
  have hmid : p ∈ (geoTransformAlong A (restrict U' T')).cosupp ↔
      p ∈ (geoTransformAlong D (restrict U' T')).cosupp := by rw [hcosAD]
  refine ⟨hleft.trans (hmid.trans hright), ?_⟩
  intro hp
  have hpA := hleft.mp hp
  have hpN := hright.mp (hcosAD ▸ hpA)
  have hχU : χ p ∈ (geoTransformAlong MU (restrict U T)).cosupp := by
    rw [hcosA] at hpA
    exact hpA
  have hval := B.classFunctorial.inv_eq A D hA hD hEq hd hE hdim hexp
    (restrict U' T') hcanA p hpA
  rw [← R.isInvValue.restrictOpen N hN U' T' hcan' p hpN,
    ← R.isInvValue.restrictOpen M hM U T hcan (χ p) hp, ← hval]
  exact R.isInvValue.towerIso Φ MU hMU (restrict U' T') (restrict U T)
    χ hiso hcanU p hχU

/-- The ACTUAL prefix level centres agree under the full current overlap map. -/
theorem centre_preimage_eq (lam : Λ) :
    χ ⁻¹' centreTrace B.toResolutionInvariant M T U lam =
      centreTrace B.toResolutionInvariant N T' U' lam := by
  ext p
  have h := cosupp_value_transport B U U' Φ hM hN hEq hd hE hdim hexp hcan hcan' χ hiso p
  constructor
  · rintro ⟨hp, hv⟩
    exact ⟨h.1.mp hp, (h.2 hp).trans hv⟩
  · rintro ⟨hp, hv⟩
    have hpM := h.1.mpr hp
    exact ⟨hpM, (h.2 hpM).symm.trans hv⟩

variable (lam : Λ)

local notation "Z₁" => ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) (openPreimage T U)
local notation "Z₂" => ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) (openPreimage T' U')
local notation "C₁" => centreTrace B.toResolutionInvariant M T U lam
local notation "C₂" => centreTrace B.toResolutionInvariant N T' U' lam
local notation "jχ" => ChartedSpace.locallyRingedSpaceMap χ χ.contMDiff

/-- Equality in the SAME native structure-sheaf unit submodule, not merely
an equality of supports or an unspecified ideal isomorphism. -/
theorem centre_submodule_eq :
    nativePulledIdealSubmodule jχ (intrinsicReducedCentreIdealModule Z₁ C₁)
      (intrinsicReducedCentreIdealInclusion Z₁ C₁) = intrinsicReducedCentreSubmodule Z₂ C₂ := by
  have : LocallyRingedSpace.IsOpenImmersion jχ := nativeOverlap_isOpenImmersion χ
  rw [openImmersion_pulled_submodule_eq]
  apply congrArg (intrinsicReducedCentreSubmodule Z₂)
  change χ ⁻¹' C₁ = C₂
  exact centre_preimage_eq B U U' Φ hM hN hEq hd hE hdim hexp hcan hcan' χ hiso lam

/-- The whole canonical-centre ideal comparison is built from the actual
native submodule equality; its section maps preserve every actual section. -/
def centreIdealIso :
    nativePulledIdealModule jχ (intrinsicReducedCentreIdealModule Z₁ C₁)
      (intrinsicReducedCentreIdealInclusion Z₁ C₁) ≅ intrinsicReducedCentreIdealModule Z₂ C₂ := by
  let h := centre_submodule_eq B U U' Φ hM hN hEq hd hE hdim hexp hcan hcan' χ hiso lam
  exact
    { hom := ⟨PresheafOfModules.Submodule.homOfLE h.le⟩
      inv := ⟨PresheafOfModules.Submodule.homOfLE h.ge⟩
      hom_inv_id := by ext V s; rfl
      inv_hom_id := by ext V s; rfl }

/-- The FULL native scalar/inclusion triangle of the forward comparison. -/
theorem centreIdealIso_hom_comp_inclusion :
    (centreIdealIso B U U' Φ hM hN hEq hd hE hdim hexp hcan hcan' χ hiso lam).hom ≫
      intrinsicReducedCentreIdealInclusion Z₂ C₂ =
        nativePulledIdealInclusion jχ (intrinsicReducedCentreIdealModule Z₁ C₁)
          (intrinsicReducedCentreIdealInclusion Z₁ C₁) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι
    (centre_submodule_eq B U U' Φ hM hN hEq hd hE hdim hexp hcan hcan' χ hiso lam).le

/-- The inverse FULL native scalar/inclusion triangle. -/
theorem centreIdealIso_inv_comp_inclusion :
    (centreIdealIso B U U' Φ hM hN hEq hd hE hdim hexp hcan hcan' χ hiso lam).inv ≫
      nativePulledIdealInclusion jχ (intrinsicReducedCentreIdealModule Z₁ C₁)
        (intrinsicReducedCentreIdealInclusion Z₁ C₁) =
          intrinsicReducedCentreIdealInclusion Z₂ C₂ := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι
    (centre_submodule_eq B U U' Φ hM hN hEq hd hE hdim hexp hcan hcan' χ hiso lam).ge

/-- ENTIRE original section ideals agree on every actual current open. -/
theorem centre_sectionIdeal_eq (V : Opens (Z₂).toTopCat) :
    nativePulledIdealSectionIdeal jχ (intrinsicReducedCentreIdealModule Z₁ C₁)
      (intrinsicReducedCentreIdealInclusion Z₁ C₁) V = intrinsicReducedCentreSectionIdeal Z₂ C₂ V := by
  have : LocallyRingedSpace.IsOpenImmersion jχ := nativeOverlap_isOpenImmersion χ
  rw [openImmersion_pulled_sectionIdeal_eq]
  apply congrArg (fun C => intrinsicReducedCentreSectionIdeal Z₂ C V)
  change χ ⁻¹' C₁ = C₂
  exact centre_preimage_eq B U U' Φ hM hN hEq hd hE hdim hexp hcan hcan' χ hiso lam

/-- The SAME entire original inclusion-stalk image, at every current point. -/
theorem centre_stalkIdeal_eq (p : Z₂) :
    nativePulledIdealStalkIdeal jχ (intrinsicReducedCentreIdealModule Z₁ C₁)
      (intrinsicReducedCentreIdealInclusion Z₁ C₁) p = intrinsicCentreStalkRange Z₂ C₂ p := by
  have : LocallyRingedSpace.IsOpenImmersion jχ := nativeOverlap_isOpenImmersion χ
  rw [openImmersion_pulled_stalkIdeal_eq]
  apply congrArg (fun C => intrinsicCentreStalkRange Z₂ C p)
  change χ ⁻¹' C₁ = C₂
  exact centre_preimage_eq B U U' Φ hM hN hEq hd hE hdim hexp hcan hcan' χ hiso lam

end Overlap

end
end Hironaka.HironakaG1CanonicalPrefixCentreTransport
