import Hironaka.Resolution.HironakaG8DomainExponents
import Hironaka.Resolution.HironakaG8LocalContactStage
import Hironaka.Resolution.HironakaG8LocalTransport

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boundary exponents of Bierstone--Milman's lower coefficient ideals for two tangent directions (G8 lane, run 0080, round 6)

Blueprint: `hironaka-g8-resume-stage-exponents.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c (module 6
`TangentIndepBM`, item (iv) `ExpAgree`), lane G11B's inbox item I-1348 (b).

For two tangent directions `u` (on `U`) and `u'` (on `U'`) of `(𝔍.ideal|_N, d)` and a test tower `T₀` of `𝔍`, the lower
coefficient ideals `contactCoeffBM 𝔍 u T₀` and `contactCoeffBM 𝔍 u' T₀` (lane G11B, `HironakaG11InvBMLower`) have the same ideal,
the same mark and the same (born) boundary, and different carriers (the strict transforms of the two hypersurfaces of
maximal contact).  **Their boundary exponents agree on every open `O` of the stage over `U ∩ U'` at the cosupport points where
both are nonzero along their carriers** — in particular on every `O` on which both restrictions are in the native domain:

* `base_contact_two`: the base objects (BM's `𝒞_W(𝔍_∅)` on the two hypersurfaces, on `W = U ∩ U'`) are well formed, `LocWPEquiv`
  and have carriers of the same dimension (lane G8 r5);
* **`expAgree_stage_contactCoeffBM_two`**: the pointwise form (hypothesis: nonzero along the carriers at the cosupport points
  of `O`);
* **`expAgree_stage_contactCoeffBM_two_of_isInvDomain`**: the form consumed by `ClassFunctorialFor.inv_eq` (hypothesis: both
  restrictions to `O` in `IsInvDomain`).

Proof: the stage-local P6 (`HironakaG8DomainExponents.expAgreeAt_geoTransformAlong_of_domain`, empty initial boundary) along
`T₀|_W` for the base objects, then the restricted equivalences of `HironakaG11InvBMStage.restrictEquiv_stage_contactCoeffBM`
and locality of exponents.  Sorry-free.  Universe `0`.  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8StageExponents

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.DivisorExponentAlong Hironaka.HomogenizedIdealAlong
  Hironaka.HomogenizedIdealAlongTower Hironaka.MarkedIdealOperationsAlong
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.CoefficientIdealRestriction Hironaka.CoefficientIdealAlongRestrictionTower
  Hironaka.ContactEquivalenceAlong Hironaka.TangentDirectionAlong
  Hironaka.RestrictedIdealWeight Hironaka.NormalCrossings
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalContact
  Hironaka.HironakaG8DomainExponents
open Hironaka.HironakaStepOneZeroContactRemainderGlueing (isNonzeroAlongAt_pullback_val_iff)
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree)

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n} {𝔍 : MarkedIdeal n X} {Y₀ : CMfd.{0} n}

/-- **The base objects for two tangent directions** (lane G8 r5): on an open `W ⊆ U ∩ U'`, BM's `𝒞_W(𝔍_∅)` restricted to the two
hypersurfaces of maximal contact are well formed, `LocWPEquiv`, and have carriers of the same dimension on the cosupport. -/
theorem base_contact_two (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U U' : Set X} {u u' : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u')
    (W : Opens X) (hWU : (W : Set X) ⊆ U) (hWU' : (W : Set X) ⊆ U') :
    (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0}))).IsWellFormed ∧
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u' x = 0}))).IsWellFormed ∧
      LocWPEquiv (X := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0})))
        (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u' x = 0}))) ∧
      SameCarrierDim (X := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0})))
        (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u' x = 0}))) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) := contMDiff_subtype_val
  have huW := IsTangentDirectionAlong.mono_open hu W.isOpen hWU
  have hu'W := IsTangentDirectionAlong.mono_open hu' W.isOpen hWU'
  have hW0 : LocWPEquiv (X := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0})))
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u' x = 0}))) :=
    locWPEquiv_contact_two_directions (emptyBoundary 𝔍) hN h𝔞 hd hu hu' W hWU hWU'
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN W
  have hcU : (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞
  have hreg : ∀ {w : X → ℂ}, IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d W w →
      IsClosedSubmanifold n ((Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | w y = 0})) ∧
      ∀ x ∈ (Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | w y = 0}), ∃ k,
        RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' 𝔍.N) x k ∧
        RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | w y = 0})) x (k - 1) := by
    intro w hw
    have hwU := isTangentDirectionAlong_pullback_val W hhol hw
    have h1 := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) W)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)) hNU hcU hwU
    rw [preimage_val_contact_eq W] at h1
    refine ⟨h1, fun x hx => ?_⟩
    have hx' : x ∈ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).N ∩
        {x : W | (w ∘ Subtype.val) x = 0} ∩ univ := by
      rw [preimage_val_contact_eq W]; exact hx
    obtain ⟨k, hk, hk'⟩ := IsTangentDirectionAlong.regularAtDim_contact
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcU) hNU hwU hx'
    rw [preimage_val_contact_eq W] at hk'
    exact ⟨k, hk, hk'⟩
  obtain ⟨hS, hSd⟩ := hreg huW
  obtain ⟨hS', hSd'⟩ := hreg hu'W
  have hcohA := GermIdealPullbackCalculus.isCoherent_pullback hval hwfc.isCoherent
  refine ⟨⟨hS, hcohA, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hS⟩,
    ⟨hS', hcohA, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hS'⟩, hW0, ?_⟩
  intro x hx j
  have hxB := hW0.cosupp_eq_base ▸ hx
  obtain ⟨k, hk, hkS⟩ := hSd x (MarkedIdeal.cosupp_subset_N _ hx)
  obtain ⟨k', hk', hkS'⟩ := hSd' x (MarkedIdeal.cosupp_subset_N _ hxB)
  have hkk : k = k' := RegularPointDimension.eq_of_regularAtDim hk hk'
  show RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | u y = 0})) x j ↔
    RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | u' y = 0})) x j
  constructor
  · intro hj
    rw [← RegularPointDimension.eq_of_regularAtDim hkS hj, hkk]; exact hkS'
  · intro hj
    rw [← RegularPointDimension.eq_of_regularAtDim hkS' hj, ← hkk]; exact hkS

/-- **P6 for the lower coefficient ideals of two tangent directions, pointwise form**: for tangent directions `u` on `U` and
`u'` on `U'`, a test tower `T₀` of `𝔍` and an open `O` of the stage over `U ∩ U'`, if both lower coefficient ideals are nonzero
along their carriers at the cosupport points of `O`, their restrictions to `O` have the same boundary exponents on the
cosupport. -/
theorem expAgree_stage_contactCoeffBM_two (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U U' : Set X} {u u' : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u')
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔍 T₀) (O : Opens Y₀) (hOU : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U)
    (hOU' : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U')
    (hnz : ∀ y ∈ O, y ∈ (contactCoeffBM 𝔍 u T₀).cosupp →
      IsNonzeroAlongAt (contactCoeffBM 𝔍 u T₀).N (contactCoeffBM 𝔍 u T₀).ideal y ∧
        IsNonzeroAlongAt (contactCoeffBM 𝔍 u' T₀).N (contactCoeffBM 𝔍 u' T₀).ideal y) :
    ExpAgree (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM 𝔍 u T₀))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM 𝔍 u' T₀)) := by
  let W : Opens X := ⟨U ∩ U', hu.isOpen.inter hu'.isOpen⟩
  have hWU : (W : Set X) ⊆ U := inter_subset_left
  have hWU' : (W : Set X) ⊆ U' := inter_subset_right
  have huW : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d (W : Set X) u := IsTangentDirectionAlong.mono_open hu W.isOpen hWU
  have hu'W : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d (W : Set X) u' :=
    IsTangentDirectionAlong.mono_open hu' W.isOpen hWU'
  obtain ⟨hwfA, hwfB, hAB, hdim⟩ := base_contact_two h𝔍 hd hu hu' W hWU hWU'
  obtain ⟨hTs, hRE⟩ := restrictEquiv_stage_contactCoeffBM h𝔍 hd W huW T₀ hT₀
  obtain ⟨-, hRE'⟩ := restrictEquiv_stage_contactCoeffBM h𝔍 hd W hu'W T₀ hT₀
  have hdA : 1 ≤ (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0}))).d :=
    ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary 𝔍)
  have hkey := expAgreeAt_geoTransformAlong_of_domain hAB hwfA hwfB hdA rfl hdim
    (fun x _ _ _ => expAgreeAt_of_E_nil rfl x) (restrict W T₀) hTs
  -- coherence of the two lower coefficient ideals
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ (isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀)
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have hcL : (contactCoeffBM 𝔍 u T₀).ideal.IsCoherent := hcTc
  have hcL' : (contactCoeffBM 𝔍 u' T₀).ideal.IsCoherent := hcTc
  have hholL := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL
  have hholL' := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL'
  refine (expAgree_iff_forall_expAgreeAt (Y := CMfd.of (n := n) O)).mpr fun p => ?_
  rw [expAgreeAt_pullback_val_iff hholL hholL' O p]
  have hpV : (p : Y₀) ∈ openPreimage T₀ W := ⟨hOU p.2, hOU' p.2⟩
  rw [← expAgreeAt_pullback_val_iff hholL hholL' (openPreimage T₀ W) ⟨p, hpV⟩]
  intro H hH hy hyH
  have hpc : (p : Y₀) ∈ (contactCoeffBM 𝔍 u T₀).cosupp := by
    have h1 := cosupp_pullback_val (contactCoeffBM 𝔍 u T₀) hholL (openPreimage T₀ W)
    have h2 : (⟨p, hpV⟩ : openPreimage T₀ W) ∈
        (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ W → Y₀) (contactCoeffBM 𝔍 u T₀)).cosupp := hy
    rw [h1] at h2
    exact h2
  obtain ⟨nz1, nz2⟩ := hnz p p.2 hpc
  have hyA := hRE.cosupp_eq ▸ hy
  have hyAN := MarkedIdeal.cosupp_subset_N _ hyA
  have hcosAB := (hAB.geoTransformAlong (restrict W T₀) hTs).cosupp_eq_base
  have hyBN := MarkedIdeal.cosupp_subset_N _ (hcosAB ▸ hyA)
  have nzA := (isNonzeroAlongAt_iff_of_restrictEquiv hRE hyAN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL (openPreimage T₀ W) ⟨p, hpV⟩).mpr nz1)
  have nzB := (isNonzeroAlongAt_iff_of_restrictEquiv hRE' hyBN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL' (openPreimage T₀ W) ⟨p, hpV⟩).mpr nz2)
  exact expAgreeAt_of_restrictEquiv hRE hRE' (hkey _ hyA nzA nzB) H hH hy hyH

/-- **P6 for the lower coefficient ideals of two tangent directions, in the form consumed by `ClassFunctorialFor.inv_eq`**: if the
restrictions to an open `O` of the stage over `U ∩ U'` of both lower coefficient ideals are in the native domain (any `k`, `k'`),
they have the same boundary exponents on the cosupport. -/
theorem expAgree_stage_contactCoeffBM_two_of_isInvDomain (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U U' : Set X}
    {u u' : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u)
    (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u') (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔍 T₀)
    (O : Opens Y₀) (hOU : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U) (hOU' : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U') {k k' : ℕ}
    (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM 𝔍 u T₀)))
    (hdom' : IsInvDomain k' (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM 𝔍 u' T₀))) :
    ExpAgree (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM 𝔍 u T₀))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM 𝔍 u' T₀)) := by
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ (isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀)
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have hcL : (contactCoeffBM 𝔍 u T₀).ideal.IsCoherent := hcTc
  have hcL' : (contactCoeffBM 𝔍 u' T₀).ideal.IsCoherent := hcTc
  have hholL := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL
  have hholL' := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL'
  -- the two restrictions to `O` have the same cosupport
  let W : Opens X := ⟨U ∩ U', hu.isOpen.inter hu'.isOpen⟩
  have hOV : O ≤ openPreimage T₀ W := fun y hy => ⟨hOU hy, hOU' hy⟩
  have hLV := HironakaG8LocalContactStage.locWPEquiv_stage_contactCoeffBM_two h𝔍 hd ⟨U, hu.isOpen⟩ T₀ hT₀
    (U' := ⟨U', hu'.isOpen⟩) hu hu' W inter_subset_left inter_subset_right
  have hLO := HironakaG8LocalTransport.locWPEquiv_restrict_of_le hcL hcL' hOV hLV
  have hcos := hLO.cosupp_eq_base
  refine expAgree_stage_contactCoeffBM_two h𝔍 hd hu hu' T₀ hT₀ O hOU hOU' fun y hy hyc => ?_
  have hyc' : (⟨y, hy⟩ : O) ∈ (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM 𝔍 u T₀)).cosupp := by
    rw [cosupp_pullback_val _ hholL O]
    exact hyc
  have hyc'' := hcos ▸ hyc'
  exact ⟨(isNonzeroAlongAt_pullback_val_iff hcL O ⟨y, hy⟩).mp
      (hdom.isNonzeroAlongAt _ (MarkedIdeal.cosupp_subset_N _ hyc')),
    (isNonzeroAlongAt_pullback_val_iff hcL' O ⟨y, hy⟩).mp
      (hdom'.isNonzeroAlongAt _ (MarkedIdeal.cosupp_subset_N _ hyc''))⟩

end

end Hironaka.HironakaG8StageExponents
