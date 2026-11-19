import Hironaka.Resolution.HironakaG3RWindowTangentTransfer

/-! # O7a′, node N2b at level 0: the window lower data from the lower data of the restriction

Lane G3 (run 0080, round 6).  Blueprint: `hironaka-g3-r-window-lower-data.tex`.
Plan: `work/hironaka-resume-20261111/G3/O7A-PRIME-PLAN.md` (§7, N2b).

`HironakaG3RWindowLowerValue.lowerValueL_zero_restrict_window` (O7a′-1 at level `0`) needs, besides the lower data `hD'` on
the side of `𝔍|_U`, the base-side WINDOW canonicity `hcanW`.  Here `hcanW` is removed: it is derived from `hD'` on a smaller
window around the point.

* `pullback_symm_pullback_of_isCoherent`, **`isInvDomain_isCanonical_of_isTowerIso_symm`** (generic): domain and canonicity
  transport BACK along an isomorphism of towers (property (6) read from the pulled-back side).
* **`isInvDomain_isCanonical_contactMarkedKept_of_restrict`**: the reverse of the held
  `ContactStageKept.inv_contactMarkedKept_restrict` followed by `inv_contactMarkedKept_isTowerIso`: canonicity of Step 1bb's
  lower marked ideal (divisor kept, tangent direction `w ∘ ι`) on a window of the side of `𝔍|_U` gives canonicity of the base
  lower marked ideal (tangent direction `w`) on the corresponding window of the base.
* `lowerValueL_zero_restrict_window_of_le`: O7a′-1 at level `0` with the window an ARBITRARY open `V ⊆ mask ∩ T₀⁻¹U`
  containing the image of the point (the held window `windowB` is the largest choice).
* **`lowerValueL_zero_restrict_of_lowerData`** (N2b at level `0`): property (5) of Step 1bb's lower value, given only the lower
  data `hD'` of `𝔍|_U`, the mask and domain of the global lower marked ideal, `LocalLaw R` and the global test tower:
  the `U`-side canonicity is moved to the base tangent direction on the common window by N2a
  (`HironakaG3RWindowTangentTransfer.isCanonical_contactMarkedKept_tangent_transfer`) and transported back to the base.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG3RWindowLowerData

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  BlowupTowerIsomorphism ResolutionInvariantExt StepOneTangentChange ContactStageKept
  StepOneValue StepOneLowerDomain StepOneValueMasked MarkedIdealOperationsAlong.MarkedIdeal
  InvDomainMemberRestriction InvDomainRebase StepOneNearby BoundaryCount
  ContactLowerValue MemberRestrictTowerIso HironakaG3RWindowLowerValue
open HomogenizedGlueingTower (strictAlong)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Transport back along an isomorphism of towers -/

section Back

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Pulling back along `Φ` and then along `Φ⁻¹` is the identity** (coherent ideal). -/
theorem pullback_symm_pullback_of_isCoherent {X X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {P : MarkedIdeal n X} (hP : P.ideal.IsCoherent) :
    MarkedIdeal.pullback Φ.symm (MarkedIdeal.pullback Φ P) = P := by
  obtain ⟨N, E, I, d⟩ := P
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
  · exact MarkedIdealTowerTransport.symm_preimage_preimage Φ N
  · exact MarkedIdealTowerTransport.map_symm_preimage_map_preimage Φ E
  · show GermIdeal.pullback (m := n) Φ.symm (GermIdeal.pullback (m := n) Φ I) = I
    rw [← GermIdealTotalTransform.pullback_comp Φ.contMDiff Φ.symm.contMDiff hP]
    have hid : (Φ : X' → X) ∘ Φ.symm = id := funext fun y => Φ.apply_symm_apply y
    rw [hid]
    exact BlowupControlledTransform.pullback_id hP

/-- **Domain and canonicity transport back along an isomorphism of towers**: if `T' ≅ T` over `Φ`, `Φ^*𝔪` lies in the domain
and `T'` is a canonical segment of it, then `𝔪` lies in the domain and `T` is a canonical segment of it (coherent ideal). -/
theorem isInvDomain_isCanonical_of_isTowerIso_symm (R : ResolutionInvariant.{u, v} n k Λ) {X X' : CMfd.{u} n}
    {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.ideal.IsCoherent) (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (hdom' : IsInvDomain k (MarkedIdeal.pullback Φ 𝔪)) {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'}
    {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ)
    (hcan' : IsCanonical (MarkedIdeal.pullback Φ 𝔪) (R.inv (MarkedIdeal.pullback Φ 𝔪)) T') :
    IsInvDomain k 𝔪 ∧ IsCanonical 𝔪 (R.inv 𝔪) T := by
  have e := pullback_symm_pullback_of_isCoherent Φ h𝔪
  have h1 := InvDomainTowerAlong.isInvDomain_pullback Φ.symm hdom'
  have h2 := isCanonical_of_isTowerIso R hdom' Φ.symm hiso.symm hcan'
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

end Back

/-! ### From the side of `𝔍|_U` back to the base -/

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Step 1bb's lower marked ideal: domain and canonicity from the side of `𝔍|_U` back to the base** (the reverse of
`inv_contactMarkedKept_restrict` followed by `inv_contactMarkedKept_isTowerIso`): let `T₀' ≅ T₀|_U` over `id_U` (last-stage
map `χ₀`) and `T₁' ≅ T₁|_{T₀⁻¹U}` over `χ₀`, `T₀` a multiple test blow-up of `J̄`, `V ⊆ T₀⁻¹U` open and `W'` the open of the
last stage of `T₀'` corresponding to `V`.  If the lower marked ideal of `𝔍|_U` with the tangent direction `w ∘ ι` on `W'` lies
in the domain and `T₁'|_{W'}` is a canonical segment of it, then `contactMarkedKept 𝔍 w T₀ V` lies in the domain and `T₁|_V`
is a canonical segment of it. -/
theorem isInvDomain_isCanonical_contactMarkedKept_of_restrict (R : ResolutionInvariant.{u, v} n k Λ)
    (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₀ Z Y₀' Z' : CMfd.{u} n} {T₀ : BlowupTower X Y₀}
    {T₁ : BlowupTower Y₀ Z} {T₀' : BlowupTower (CMfd.of (n := n) U) Y₀'}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₀ U)}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) T₀' (restrict U T₀) χ₀)
    {T₁' : BlowupTower Y₀' Z'}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ U))}
    (hχ : IsTowerIso χ₀ T₁' (restrict (openPreimage T₀ U) T₁) χ) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀)
    (w : X → ℂ) {V : Opens Y₀} (hVU : V ≤ openPreimage T₀ U) {W' : Opens Y₀'}
    (hW' : ∀ q, q ∈ W' ↔ χ₀ q ∈ MaxLocusLocal.nestedOpens (openPreimage T₀ U) V)
    (hdom' : IsInvDomain k (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) T₀' W'))
    (hcan' : IsCanonical (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) T₀' W')
      (R.inv (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) T₀' W'))
      (restrict W' T₁')) :
    IsInvDomain k (contactMarkedKept 𝔍 w T₀ V) ∧
      IsCanonical (contactMarkedKept 𝔍 w T₀ V) (R.inv (contactMarkedKept 𝔍 w T₀ V)) (restrict V T₁) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍U : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).IsWellFormed :=
    MarkedIdealRestrictOpen.IsWellFormed.pullback_val h𝔍 U
  have hbarU : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) :=
    barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  have hT₀U : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀) := by
    rw [hbarU]
    exact isGeoTestTower_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  -- (A) from `T₀'` to `T₀|_U`
  have eA := contactMarkedKept_isTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
    h𝔍U.isCoherent h𝔍U.isClosedSubmanifold_N hd hiso hT₀U (w ∘ Subtype.val) W'
    (MaxLocusLocal.nestedOpens (openPreimage T₀ U) V)
    (diffeoOpens χ₀ W' (MaxLocusLocal.nestedOpens (openPreimage T₀ U) V) hW') fun _ => rfl
  have hpbU : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) = MarkedIdeal.pullback (Subtype.val : U → X) 𝔍 :=
    ContactCanonicalAlong.pullback_id _ h𝔍U.isCoherent
  rw [hpbU] at eA
  have eA' : contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) T₀' W' =
      MarkedIdeal.pullback (diffeoOpens χ₀ W' (MaxLocusLocal.nestedOpens (openPreimage T₀ U) V) hW')
        (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) (restrict U T₀)
          (MaxLocusLocal.nestedOpens (openPreimage T₀ U) V)) := eA
  have hξ := isTowerIso_restrictOpens hW' hχ (isTowerIso_mem_openPreimage_iff hχ hW')
  rw [eA'] at hdom' hcan'
  have hcohA : (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) (restrict U T₀)
      (MaxLocusLocal.nestedOpens (openPreimage T₀ U) V)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff _ h𝔍U.isCoherent h𝔍U.isClosedSubmanifold_N (w ∘ Subtype.val) (restrict U T₀) hT₀U)
  obtain ⟨hdomA, hcanA⟩ := isInvDomain_isCanonical_of_isTowerIso_symm R hcohA _ hdom' hξ hcan'
  -- (B) from `T₀|_U` to `T₀`
  rw [contactMarkedKept_restrict U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd T₀ hT₀ w hVU] at hdomA hcanA
  have hcohB : (contactMarkedKept 𝔍 w T₀ V).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff 𝔍 h𝔍.isCoherent h𝔍.isClosedSubmanifold_N w T₀ hT₀)
  exact isInvDomain_isCanonical_of_isTowerIso_symm R hcohB _ hdomA
    (MaxLocusLocal.isTowerIso_restrict_nestedOpens (X := Y₀) hVU T₁) hcanA

end Restrict

/-! ### O7a′-1 at level `0` with an arbitrary window -/

section Window

variable {X : CMfd.{u} n} (U : Opens X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **O7a′-1 at level `0` with an arbitrary window** (`lowerValueL_zero_restrict_window` with `windowB` replaced by any open `V`
of the stage `T₀` with `V ⊆ mask ∩ T₀⁻¹U` containing the image of the point): the base window canonicity is asked only on
`V`.  The held proof, `windowB` replaced by `V` (it uses the window only through `inv_eq_restrict_nestedOpens_of_localLaw`,
which accepts any smaller open set). -/
theorem lowerValueL_zero_restrict_window_of_le (R : ResolutionInvariant.{u, v} n k Λ) (hLL : LocalLaw R) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) {Y₀ Z Y₀' Z' : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Z}
    {T₀' : BlowupTower (CMfd.of (n := n) U) Y₀'}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₀ U)}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) T₀' (restrict U T₀) χ₀)
    {T₁' : BlowupTower Y₀' Z'}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ U))}
    (hχ : IsTowerIso χ₀ T₁' (restrict (openPreimage T₀ U) T₁) χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁))
    {p' : Z'} (hp : ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈
      (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp)
    (hD' : LowerDataL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) 0 T₀' T₁' p')
    (hmask : T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈
      lowerMask 𝔍 0 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))
    (hdom : IsInvDomain k (lowerMarkedM 𝔍 0 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z))))
    {V : Opens Y₀} (hVW : V ≤ maskB 𝔍 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))
    (hVU : V ≤ openPreimage T₀ U) (hyV : T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈ V)
    (hcanV : IsCanonical (contactMarkedKept 𝔍
        (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).2 T₀ V)
      (R.inv (contactMarkedKept 𝔍
        (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).2 T₀ V))
      (restrict V T₁)) :
    lowerValueL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) 0 T₀' T₁' p' =
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍U : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val h𝔍 U
  have hJU := isWellFormed_barMarked (X := CMfd.of (n := n) U) _ h𝔍U
  have hbarU : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) :=
    barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  -- the restricted towers
  have hT₀U : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T₀) := by
    rw [hbarU]
    exact isGeoTestTower_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hgU : geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T₀) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (geoTransformAlong (barMarked 𝔍) T₀) := by
    rw [hbarU]
    exact geoTransformAlong_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hRU : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁)) := by
    refine (isGeoTestTower_append_iff _ _ _).mpr ⟨hT₀U, ?_⟩
    rw [hgU]
    exact isGeoTestTower_restrict (openPreimage T₀ U) hNT hcT T₁ hT₁
  have hcosR : χ p' ∈ (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁))).cosupp := by
    rw [geoTransformAlong_append, hgU,
      ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hNT hcT (openPreimage T₀ U) T₁ hT₁, mem_preimage,
      ← geoTransformAlong_append]
    exact hp
  -- along the isomorphism over `id_U`
  have hiso' := hiso.append hχ
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) =
      barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) :=
    ContactCanonicalAlong.pullback_id _ hJU.isCoherent
  have hT' : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (T₀'.append T₁') := by
    have h1 := (IsTowerIso.isGeoTestTower_iff _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso').mpr hRU
    rwa [hpb] at h1
  have hp' : p' ∈ (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (T₀'.append T₁')).cosupp := by
    have h1 := IsTowerIso.cosupp_geoTransformAlong _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso' hRU
    rw [hpb] at h1
    rw [h1]
    exact hcosR
  -- the images of `p'` and `χ p'`
  have hy : χ₀ (T₁'.proj p') = (restrict (openPreimage T₀ U) T₁).proj (χ p') := hχ.proj_comm p'
  have hy' : (((restrict (openPreimage T₀ U) T₁).proj (χ p') : openPreimage T₀ U) : Y₀) =
      T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := proj_restrict _ T₁ (χ p')
  -- the data on the side of `𝔍`: the mask `W` of `χ p'` and the tangent direction `w` chosen at its base point
  have h := hmask
  have hxw : T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) ∈
      (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).1 :=
    (interior_subset h).1
  have hw := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hxw
  set W : Opens Y₀ := maskB 𝔍 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) with hWdef
  set w : X → ℂ := (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).2
    with hwdef
  set Uw : Set X := (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).1
    with hUwdef
  -- (1) shrink the mask to its part over `U`
  have hcoh := isCoherent_restrictedCoeff 𝔍 h𝔍.isCoherent h𝔍.isClosedSubmanifold_N w T₀ hT₀
  have hdom₁ : IsInvDomain k (contactMarkedKept 𝔍 w T₀ V) := isInvDomain_restrict_nestedOpens hcoh hVW hdom
  have hcan₁ : IsCanonical (contactMarkedKept 𝔍 w T₀ V) (R.inv (contactMarkedKept 𝔍 w T₀ V)) (restrict V T₁) := hcanV
  have hpV : T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈ V := hyV
  have hcos₁ : (⟨((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z), hpV⟩ : openPreimage T₁ V) ∈
      (geoTransformAlong (contactMarkedKept 𝔍 w T₀ V) (restrict V T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
      ⟨Uw, hw.isOpen⟩ hw T₀ T₁ hT V fun y hy => (interior_subset (hVW hy)).1).2]
    exact hp
  have hcosW : (⟨((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z), MaxLocusLocal.openPreimage_mono T₁ hVW hpV⟩ :
      openPreimage T₁ W) ∈ (geoTransformAlong (contactMarkedKept 𝔍 w T₀ W) (restrict W T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
      ⟨Uw, hw.isOpen⟩ hw T₀ T₁ hT W fun y hy => (interior_subset hy).1).2]
    exact hp
  have hv1 := inv_eq_restrict_nestedOpens_of_localLaw R hLL hcoh hVW hdom T₁ hcan₁ ⟨_, hpV⟩ hcos₁ hcosW
  -- (2) restrict to `U`
  obtain ⟨-, hcan₂, hval₂⟩ := inv_contactMarkedKept_restrict U R h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd T₀ hT₀ w
    hVU hdom₁ T₁ hcan₁
  have hdom₂ := (inv_contactMarkedKept_restrict U R h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd T₀ hT₀ w
    hVU hdom₁ T₁ hcan₁).1
  set W₂ : Opens (CMfd.of (n := n) (openPreimage T₀ U)) := MaxLocusLocal.nestedOpens (openPreimage T₀ U) V with hW₂def
  have hq₂ : χ p' ∈ openPreimage (restrict (openPreimage T₀ U) T₁) W₂ := by
    show (((restrict (openPreimage T₀ U) T₁).proj (χ p') : openPreimage T₀ U) : Y₀) ∈ V
    rw [hy']
    exact hpV
  obtain ⟨hcosiff, hv2⟩ := hval₂ ⟨χ p', hq₂⟩ ⟨_, hpV⟩ rfl
  have hcos₂ := hcosiff.mpr hcos₁
  have hv2' := hv2 hcos₁
  -- (3) along the isomorphism over `id_U`
  set W' : Opens Y₀' := ⟨χ₀ ⁻¹' (W₂ : Set (CMfd.of (n := n) (openPreimage T₀ U))),
    W₂.isOpen.preimage χ₀.continuous⟩ with hW'def
  have hW' : ∀ q, q ∈ W' ↔ χ₀ q ∈ W₂ := fun _ => Iff.rfl
  obtain ⟨hdom₃, hcan₃, hval₃⟩ := inv_contactMarkedKept_isTowerIso
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) R h𝔍U.isCoherent h𝔍U.isClosedSubmanifold_N hd hiso
    hT₀U (w ∘ Subtype.val) hW' hχ hdom₂ hcan₂
  have hpbU : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) = MarkedIdeal.pullback (Subtype.val : U → X) 𝔍 :=
    ContactCanonicalAlong.pullback_id _ h𝔍U.isCoherent
  rw [hpbU] at hdom₃ hcan₃ hval₃
  have hpW' : T₁'.proj p' ∈ W' := by
    show χ₀ (T₁'.proj p') ∈ W₂
    rw [hy]
    exact hq₂
  have hv3 := hval₃ ⟨p', hpW'⟩ ⟨χ p', hq₂⟩ rfl hcos₂
  -- (4) the anchor for `𝔍|_U` with `w ∘ ι` on `W'`
  have hu : IsTangentDirectionAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).ideal (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).d
      ((Subtype.val : U → X) ⁻¹' Uw) (w ∘ Subtype.val) :=
    ContactMarkedCanonical.isTangentDirectionAlong_comp_val U h𝔍.isCoherent hw
  have hproj : ∀ q, (((T₀'.proj q : CMfd.of (n := n) U) : U) : X) = T₀.proj ((χ₀ q : openPreimage T₀ U) : Y₀) := by
    intro q
    have e : T₀'.proj q = (restrict U T₀).proj (χ₀ q) := hiso.proj_comm q
    rw [e, proj_restrict]
  have hW'U : (W' : Set Y₀') ⊆ T₀'.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' Uw) := by
    intro q hq
    have h1 : ((χ₀ q : openPreimage T₀ U) : Y₀) ∈ V := hq
    show (((T₀'.proj q : CMfd.of (n := n) U) : U) : X) ∈ Uw
    rw [hproj]
    exact (interior_subset (hVW h1)).1
  have hW'E : ∀ H ∈ origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀', Disjoint (W' : Set Y₀') H := by
    intro H hH
    have e := origMembers_isTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) _ h𝔍U hd hiso hT₀U
    rw [hpbU, origMembers_restrict U 𝔍 h𝔍 hd hT₀, List.map_map] at e
    rw [e] at hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    refine Set.disjoint_left.mpr fun q hq hqH => ?_
    have h1 : ((χ₀ q : openPreimage T₀ U) : Y₀) ∈ V := hq
    exact (interior_subset (hVW h1)).2.1 H₀ hH₀ hqH
  have key := lowerValueL_zero_eq (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) h𝔍U hd T₀' T₁' hT' hu W' hW'U hW'E
    hdom₃ hcan₃ hpW' hp' hD'
  rw [key, lowerValueL_eq_of_mem R 𝔍 _ h]
  congr 1
  exact hv3.trans (hv2'.trans hv1)

end Window

/-! ### N2b at level `0`: no base window canonicity -/

section LowerData

variable {X : CMfd.{u} n} (U : Opens X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **O7a′, node N2b at level `0`: property (5) of Step 1bb's lower value from the lower data of `𝔍|_U` alone.**  As
`HironakaG3RWindowLowerValue.lowerValueL_zero_restrict_window`, WITHOUT the base-side window canonicity `hcanW`: the inputs
are the lower data `hD'` on the side of `𝔍|_U`, the mask and the domain of the global lower marked ideal at the image of the
point, the window-local law `LocalLaw R` of the lower invariant and the global test tower `T₀ T₁` of `J̄`.  Proof: on the
window `W''` of the side of `𝔍|_U` cut out by its own mask and by the base mask over `U`, the canonicity of `hD'` (tangent
direction chosen for `𝔍|_U`) restricts to `W''` (`MaxLocusLocal.restrict_nestedOpens`) and passes to the tangent direction
`w ∘ ι` chosen for `𝔍` (N2a, `isCanonical_contactMarkedKept_tangent_transfer`); it is carried back to the base window `V`
corresponding to `W''` (`isInvDomain_isCanonical_contactMarkedKept_of_restrict`), and `lowerValueL_zero_restrict_window_of_le`
applies with that window. -/
theorem lowerValueL_zero_restrict_of_lowerData (R : ResolutionInvariant.{u, v} n k Λ) (hLL : LocalLaw R)
    (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₀ Z Y₀' Z' : CMfd.{u} n} {T₀ : BlowupTower X Y₀}
    {T₁ : BlowupTower Y₀ Z} {T₀' : BlowupTower (CMfd.of (n := n) U) Y₀'}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₀ U)}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) T₀' (restrict U T₀) χ₀)
    {T₁' : BlowupTower Y₀' Z'}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ U))}
    (hχ : IsTowerIso χ₀ T₁' (restrict (openPreimage T₀ U) T₁) χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁))
    {p' : Z'} (hp : ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈
      (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp)
    (hD' : LowerDataL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) 0 T₀' T₁' p')
    (hmask : T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈
      lowerMask 𝔍 0 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))
    (hdom : IsInvDomain k (lowerMarkedM 𝔍 0 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))) :
    lowerValueL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) 0 T₀' T₁' p' =
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍U : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).IsWellFormed :=
    MarkedIdealRestrictOpen.IsWellFormed.pullback_val h𝔍 U
  have hJU := isWellFormed_barMarked (X := CMfd.of (n := n) U) _ h𝔍U
  have hbarU : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) :=
    barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    T₀ hT₀
  have hT₀U : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀) := by
    rw [hbarU]
    exact isGeoTestTower_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hgU : geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (geoTransformAlong (barMarked 𝔍) T₀) := by
    rw [hbarU]
    exact geoTransformAlong_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hRU : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁)) := by
    refine (isGeoTestTower_append_iff _ _ _).mpr ⟨hT₀U, ?_⟩
    rw [hgU]
    exact isGeoTestTower_restrict (openPreimage T₀ U) hNT hcT T₁ hT₁
  have hiso' := hiso.append hχ
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) =
      barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) :=
    ContactCanonicalAlong.pullback_id _ hJU.isCoherent
  have hT' : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (T₀'.append T₁') := by
    have h1 := (IsTowerIso.isGeoTestTower_iff _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso').mpr hRU
    rwa [hpb] at h1
  have hT₀' := ((isGeoTestTower_append_iff _ T₀' T₁').mp hT').1
  have hpbU : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) = MarkedIdeal.pullback (Subtype.val : U → X) 𝔍 :=
    ContactCanonicalAlong.pullback_id _ h𝔍U.isCoherent
  -- the images of `p'` and `χ p'`
  have hy : χ₀ (T₁'.proj p') = (restrict (openPreimage T₀ U) T₁).proj (χ p') := hχ.proj_comm p'
  have hy' : (((restrict (openPreimage T₀ U) T₁).proj (χ p') : openPreimage T₀ U) : Y₀) =
      T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := proj_restrict _ T₁ (χ p')
  have hproj : ∀ q, (((T₀'.proj q : CMfd.of (n := n) U) : U) : X) = T₀.proj ((χ₀ q : openPreimage T₀ U) : Y₀) := by
    intro q
    have e : T₀'.proj q = (restrict U T₀).proj (χ₀ q) := hiso.proj_comm q
    rw [e, proj_restrict]
  -- the base tangent direction `w` at the image of `χ p'`
  have hxw : T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) ∈
      (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).1 :=
    (interior_subset hmask).1
  have hw := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hxw
  set y : Y₀ := T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) with hydef
  set w : X → ℂ := (tangentChoice 𝔍 (T₀.proj y)).2 with hwdef
  set Uw : Set X := (tangentChoice 𝔍 (T₀.proj y)).1 with hUwdef
  -- the data of `𝔍|_U` at `p'`
  obtain ⟨h', hdom', hcan', hcos'⟩ := hD'
  have hxu : T₀'.proj (T₁'.proj p') ∈
      (tangentChoice (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (T₀'.proj (T₁'.proj p'))).1 :=
    (interior_subset h').1
  have hu := StepOneCompare.tangentChoice_spec_of_mem (X := CMfd.of (n := n) U)
    (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) hxu
  set u : CMfd.of (n := n) U → ℂ :=
    (tangentChoice (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (T₀'.proj (T₁'.proj p'))).2 with hudef
  set U₁ : Set (CMfd.of (n := n) U) :=
    (tangentChoice (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (T₀'.proj (T₁'.proj p'))).1 with hU₁def
  set M' : Opens Y₀' := maskB (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀' (T₁'.proj p')
    with hM'def
  have hdomM' : IsInvDomain k (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) u T₀' M') := hdom'
  have hcanM' : IsCanonical (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) u T₀' M')
      (R.inv (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) u T₀' M')) (restrict M' T₁') := hcan'
  -- the windows
  set W₁ : Opens Y₀ := maskB 𝔍 T₀ y ⊓ openPreimage T₀ U with hW₁def
  have hW₁U : W₁ ≤ openPreimage T₀ U := inf_le_right
  set Ww : Opens Y₀' := ⟨χ₀ ⁻¹' (MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁ :
      Set (CMfd.of (n := n) (openPreimage T₀ U))),
    (MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁).isOpen.preimage χ₀.continuous⟩ with hWwdef
  have hWw : ∀ q, q ∈ Ww ↔ χ₀ q ∈ MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁ := fun _ => Iff.rfl
  set W'' : Opens Y₀' := M' ⊓ Ww with hW''def
  -- the base-side lower marked ideal (tangent direction `w`) on `W''`: domain
  have hcoh := isCoherent_restrictedCoeff 𝔍 h𝔍.isCoherent h𝔍.isClosedSubmanifold_N w T₀ hT₀
  have hdom₁ : IsInvDomain k (contactMarkedKept 𝔍 w T₀ W₁) := isInvDomain_restrict_nestedOpens hcoh inf_le_left hdom
  have hdom₂ : IsInvDomain k (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val)
      (restrict U T₀) (MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁)) := by
    rw [contactMarkedKept_restrict U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd T₀ hT₀ w hW₁U]
    exact InvDomainTowerAlong.isInvDomain_pullback _ hdom₁
  have hdomWw : IsInvDomain k (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val)
      T₀' Ww) := by
    have e := contactMarkedKept_isTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      h𝔍U.isCoherent h𝔍U.isClosedSubmanifold_N hd hiso hT₀U (w ∘ Subtype.val) Ww
      (MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁)
      (diffeoOpens χ₀ Ww (MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁) hWw) fun _ => rfl
    rw [hpbU] at e
    have e' : contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) T₀' Ww =
        MarkedIdeal.pullback (diffeoOpens χ₀ Ww (MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁) hWw)
          (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) (restrict U T₀)
            (MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁)) := e
    rw [e']
    exact InvDomainTowerAlong.isInvDomain_pullback _ hdom₂
  have hcohw := isCoherent_restrictedCoeff (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) h𝔍U.isCoherent
    h𝔍U.isClosedSubmanifold_N (w ∘ Subtype.val) T₀' hT₀'
  have hdomv : IsInvDomain k (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val)
      T₀' W'') := isInvDomain_restrict_nestedOpens hcohw inf_le_right hdomWw
  -- the `U`-side lower marked ideal (tangent direction `u`) on `W''`: domain and canonicity
  have hcohu := isCoherent_restrictedCoeff (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) h𝔍U.isCoherent
    h𝔍U.isClosedSubmanifold_N u T₀' hT₀'
  obtain ⟨hdomu, hcanu, -⟩ := MaxLocusLocal.restrict_nestedOpens R hcohu (inf_le_left : W'' ≤ M') hdomM' T₁' hcanM'
  -- N2a: from `u` to `w ∘ ι` on `W''`
  have hv : IsTangentDirectionAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).ideal (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).d
      ((Subtype.val : U → X) ⁻¹' Uw) (w ∘ Subtype.val) :=
    ContactMarkedCanonical.isTangentDirectionAlong_comp_val U h𝔍.isCoherent hw
  have hW''U₁ : (W'' : Set Y₀') ⊆ T₀'.proj ⁻¹' U₁ := fun z hz => (interior_subset hz.1).1
  have hW''Uw : (W'' : Set Y₀') ⊆ T₀'.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' Uw) := by
    intro q hq
    have h1 : ((χ₀ q : openPreimage T₀ U) : Y₀) ∈ W₁ := hq.2
    show (((T₀'.proj q : CMfd.of (n := n) U) : U) : X) ∈ Uw
    rw [hproj]
    exact (interior_subset h1.1).1
  have hW''E : ∀ H ∈ origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀',
      Disjoint (W'' : Set Y₀') H := fun H hH =>
    Set.disjoint_left.mpr fun z hz hzH => (interior_subset hz.1).2.1 H hH hzH
  have hcanv := HironakaG3RWindowTangentTransfer.isCanonical_contactMarkedKept_tangent_transfer
    (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) h𝔍U hd hu hv T₀' W'' hW''U₁ hW''Uw hW''E hdomu hdomv T₁' hT'
    hcanu
  -- the base window `V` corresponding to `W''`
  set V : Opens Y₀ := ⟨Subtype.val '' (χ₀.symm ⁻¹' (W'' : Set Y₀')),
    (openPreimage T₀ U).isOpen.isOpenMap_subtype_val _ (W''.isOpen.preimage χ₀.symm.continuous)⟩ with hVdef
  have hVU : V ≤ openPreimage T₀ U := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hW''V : ∀ q, q ∈ W'' ↔ χ₀ q ∈ MaxLocusLocal.nestedOpens (openPreimage T₀ U) V := by
    intro q
    constructor
    · intro hq
      refine ⟨χ₀ q, ?_, rfl⟩
      show χ₀.symm (χ₀ q) ∈ W''
      rw [χ₀.symm_apply_apply]
      exact hq
    · rintro ⟨r, hr, hrq⟩
      have hr' : r = χ₀ q := Subtype.ext hrq
      have hr'' : χ₀.symm r ∈ W'' := hr
      rw [hr', χ₀.symm_apply_apply] at hr''
      exact hr''
  have hVW : V ≤ maskB 𝔍 T₀ y := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : χ₀ (χ₀.symm r) ∈ MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁ := (hr : χ₀.symm r ∈ W'').2
    rw [χ₀.apply_symm_apply] at h1
    exact (h1 : (r : Y₀) ∈ W₁).1
  have hpW'' : T₁'.proj p' ∈ W'' := by
    refine ⟨h', ?_⟩
    show χ₀ (T₁'.proj p') ∈ MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁
    rw [hy]
    show (((restrict (openPreimage T₀ U) T₁).proj (χ p') : openPreimage T₀ U) : Y₀) ∈ W₁
    rw [hy']
    exact ⟨hmask, (χ p').2⟩
  have hyV : y ∈ V := by
    refine ⟨χ₀ (T₁'.proj p'), ?_, ?_⟩
    · show χ₀.symm (χ₀ (T₁'.proj p')) ∈ W''
      rw [χ₀.symm_apply_apply]
      exact hpW''
    · rw [hy, hy']
  -- back to the base, then the window form of O7a′-1
  obtain ⟨-, hcanV⟩ := isInvDomain_isCanonical_contactMarkedKept_of_restrict U R 𝔍 h𝔍 hd hiso hχ hT₀ w hVU hW''V
    hdomv hcanv
  exact lowerValueL_zero_restrict_window_of_le U R hLL 𝔍 h𝔍 hd hiso hχ hT hp ⟨h', hdom', hcan', hcos'⟩ hmask hdom
    hVW hVU hyV hcanV

end LowerData

end

end Hironaka.HironakaG3RWindowLowerData
