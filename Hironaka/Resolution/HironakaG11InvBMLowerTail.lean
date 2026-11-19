import Hironaka.Resolution.HironakaG11InvBMLowerDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The tails of Bierstone--Milman's lower marked ideal of level `0` on open sets (repair (B'), plan module 5, level 0)

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` (module 5).
Source: Bierstone--Milman 2008, §5 Step I.A ("a resolution of singularities of `𝒞_U(I)` is a resolution of `I|_U`": the test
blowings-up and cosupports correspond, Corollary 4.2), Step I.B (the transforms `𝒞_{q}`); Włodarczyk 2005 Lemma `le:cf`.

An equivalence of marked ideals quantifies over the towers of its own base and does not pass to smaller opens, so, as in
`ContactStageTail` for the W-family, the tails are proved for the given segment: for `T₀ T₁` a multiple test blow-up of
`J̄ = 𝓒_N(𝓗_N(𝔍))` (`𝔍` well formed, `d ≥ 1`), a tangent direction `u` on `U` and ANY open `W ⊆ T₀⁻¹U` of the stage `T₀`:

* `cosupp_tail_subset_strictAlong_BM` (**Giraud along the tails**): along every multiple test blow-up `T` of
  `𝓒_N(𝔍_∅)_{T₀}`, the cosupport over `W` lies in the strict transform of `(N ∩ V(u))_{T₀}`;
* **`isGeoTestTower_tail_contactCoeffBM`**: `T₁|_W` is a multiple test blow-up of `contactCoeffBM 𝔍 u T₀|_W`, and along it the
  cosupport is the trace of `cosupp J̄_{T₀ T₁}` (equivalently of `𝔍_{T₀ T₁}`);
* `isGeoTestTower_tail_lowerBM_zero`: the same for `lowerBM 𝔍 0 T₀ y₀` on its mask (`maskB ⊆ T₀⁻¹U`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11InvBMLowerTail

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.MarkedIdealEquivalence Hironaka.MarkedIdealEquivalence.MarkedIdeal
  Hironaka.HomogenizedIdealAlong Hironaka.HomogenizedIdealAlongTower
  Hironaka.CoefficientIdealRestriction Hironaka.CoefficientIdealAlongRestrictionTower
  Hironaka.TangentDirectionAlong Hironaka.ContactStageInvDomain
  Hironaka.MaximalContactAlongTower Hironaka.MemberInterTowerAlong
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG11InvBMLowerDomain
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_restrict)
open Hironaka.MemberInterLocusAlong (strictAlong_append)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)

noncomputable section

variable {n : ℕ}

section Tail

variable {X : CMfd.{u} n} {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ}
  (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
  (hT₀ : IsGeoTestTower (coeffEmptyBM 𝔍) T₀) (W : Opens Y₀) (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U)

include h𝔍 hd hu hT₀ hWU in
/-- **Giraud along the tails, for Bierstone--Milman's coefficient ideal**: along every multiple test blow-up `T` of
`𝓒_N(𝔍_∅)_{T₀}`, the cosupport over `W ⊆ T₀⁻¹U` lies in the strict transform of `(N ∩ V(u))_{T₀}`. -/
theorem cosupp_tail_subset_strictAlong_BM {Z : CMfd.{u} n} (T : BlowupTower Y₀ Z) (C : Set Z)
    (hT : IsGeoTestTower (geoTransformAlong (coeffEmptyBM 𝔍) T₀) T)
    (hC : (geoTransformAlong (geoTransformAlong (coeffEmptyBM 𝔍) T₀) T).IsAdmissibleCentre C) :
    C ∩ T.proj ⁻¹' (W : Set Y₀) ⊆ strictAlong T (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})) := by
  intro z ⟨hzC, hzW⟩
  have hTT : IsGeoTestTower (coeffEmptyBM 𝔍) (T₀.append T) := (isGeoTestTower_append_iff _ T₀ T).mpr ⟨hT₀, hT⟩
  have hTe : IsGeoTestTower (emptyBoundary 𝔍) (T₀.append T) :=
    (coeffAlong_tower (emptyBoundary 𝔍) h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd (T₀.append T)).1.mp hTT
  have hzc : z ∈ (geoTransformAlong (emptyBoundary 𝔍) (T₀.append T)).cosupp := by
    rw [cosupp_geoTransformAlong_emptyBoundary, ← cosupp_geoTransformAlong_coeffEmptyBM h𝔍 hd _ hTe,
      geoTransformAlong_append]
    exact hC.2.1 hzC
  have hzU : (T₀.append T).proj z ∈ U := by
    rw [BlowupTower.proj_append]
    exact hWU hzW
  have h1 := cosupp_subset_strictAlong_along (emptyBoundary 𝔍) h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd hu
    (T₀.append T) hTe ⟨hzc, hzU⟩
  rw [← strictAlong_append]
  exact strictAlong_mono (T₀.append T) (fun x hx => hx.1) h1

include h𝔍 hd hu hT₀ hWU in
/-- **The tails of Bierstone--Milman's coefficient ideal on maximal contact, on an open `W ⊆ T₀⁻¹U`**: for every multiple
test blow-up `T₁` of `𝓒_N(𝔍_∅)_{T₀}` (e.g. the tail of a multiple test blow-up `T₀ T₁` of `J̄`), `T₁|_W` is a multiple test
blow-up of `contactCoeffBM 𝔍 u T₀|_W`, and along it the cosupport is the trace of `cosupp (𝔍_∅)_{T₀ T₁} = cosupp 𝔍_{T₀ T₁}`. -/
theorem isGeoTestTower_tail_contactCoeffBM {Z : CMfd.{u} n} (T₁ : BlowupTower Y₀ Z)
    (hT₁ : IsGeoTestTower (geoTransformAlong (coeffEmptyBM 𝔍) T₀) T₁) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → Y₀) (contactCoeffBM 𝔍 u T₀)) (restrict W T₁) ∧
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) (contactCoeffBM 𝔍 u T₀)) (restrict W T₁)).cosupp =
        (Subtype.val : openPreimage T₁ W → Z) ⁻¹' (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → Y₀) := contMDiff_subtype_val
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀
  have hT₀e : IsGeoTestTower (emptyBoundary 𝔍) T₀ := (coeffAlong_tower (emptyBoundary 𝔍) hN h𝔞 hd T₀).1.mp hT₀
  have hA : IsClosedSubmanifold n ((Subtype.val : W → Y₀) ⁻¹' strictAlong T₀ (𝔍.N ∩ {x | u x = 0})) :=
    isClosedSubmanifold_strictAlong_stage_of_le (emptyBoundary 𝔍) hN h𝔞 hd U hu T₀ hT₀e W hWU
  have hAN : strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ⊆ (geoTransformAlong (coeffEmptyBM 𝔍) T₀).N := by
    rw [HomogenizedGlueingTower.N_geoTransformAlong]
    exact strictAlong_mono T₀ (fun x hx => hx.1)
  have hNW : IsClosedSubmanifold n
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (coeffEmptyBM 𝔍) T₀)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNT W
  have hcW : (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (coeffEmptyBM 𝔍) T₀)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval hcT
  have hR := isGeoTestTower_restrict (𝔪 := geoTransformAlong (coeffEmptyBM 𝔍) T₀) W hNT hcT T₁ hT₁
  have hC : CentresIn ((Subtype.val : W → Y₀) ⁻¹' strictAlong T₀ (𝔍.N ∩ {x | u x = 0})) (restrict W T₁) :=
    centresIn_restrict_of_forall (geoTransformAlong (coeffEmptyBM 𝔍) T₀) W
      (fun T C hT hCa => cosupp_tail_subset_strictAlong_BM h𝔍 hd U hu T₀ hT₀ W hWU T C hT hCa) T₁ hT₁
  obtain ⟨hTs, -, -, -, -, -, hRE⟩ := restrict_tower_along (X := CMfd.of (n := n) W)
    (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (coeffEmptyBM 𝔍) T₀)) hNW hcW hA
    (preimage_mono hAN) (restrict W T₁) hR hC
  refine ⟨hTs, ?_⟩
  have hRE' := hRE.cosupp_eq
  change (geoTransformAlong (withN (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (coeffEmptyBM 𝔍) T₀))
    ((Subtype.val : W → Y₀) ⁻¹' strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))) (restrict W T₁)).cosupp = _
  rw [hRE', geoTransformAlong_restrict W hNT hcT T₁ hT₁, strictAlong_restrict W T₁]
  obtain ⟨-, hcTT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hNT hcT T₁ hT₁
  change (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ W → Z)
    (withN (geoTransformAlong (geoTransformAlong (coeffEmptyBM 𝔍) T₀) T₁)
      (strictAlong T₁ (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))))).cosupp = _
  rw [cosupp_pullback_val (withN (geoTransformAlong (geoTransformAlong (coeffEmptyBM 𝔍) T₀) T₁)
      (strictAlong T₁ (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))))
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcTT)]
  ext p
  simp only [mem_preimage]
  have hTT : IsGeoTestTower (coeffEmptyBM 𝔍) (T₀.append T₁) := (isGeoTestTower_append_iff _ T₀ T₁).mpr ⟨hT₀, hT₁⟩
  have hTTe : IsGeoTestTower (emptyBoundary 𝔍) (T₀.append T₁) :=
    (coeffAlong_tower (emptyBoundary 𝔍) hN h𝔞 hd (T₀.append T₁)).1.mp hTT
  have hpU : (T₀.append T₁).proj (p : Z) ∈ U := by
    rw [BlowupTower.proj_append]
    exact hWU p.2
  have key := cosupp_contactCoeffBM_iff (𝔍 := emptyBoundary 𝔍) (isWellFormed_emptyBoundary h𝔍) hd U hu (T₀.append T₁)
    hTTe hpU
  rw [contactCoeffBM, geoTransformAlong_append, strictAlong_append, cosupp_geoTransformAlong_emptyBoundary] at key
  exact key

/-- **The tails of Bierstone--Milman's lower marked ideal of level `0`**: along a multiple test blow-up `T₀ T₁` of `J̄`
(`𝔍` well formed, `d ≥ 1`, of maximal order), at a point `y₀` of the cosupport at the stage `T₀` (where a tangent direction
exists), `T₁` restricted to the mask `maskBM 𝔍 0 T₀ y₀` is a multiple test blow-up of `lowerBM 𝔍 0 T₀ y₀`, and along it the
cosupport is the trace of `cosupp 𝔍_{T₀ T₁}`. -/
theorem isGeoTestTower_tail_lowerBM_zero {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₀ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Z)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) :
    IsGeoTestTower (lowerBM 𝔍 0 T₀ y₀) (restrict (maskBM 𝔍 0 T₀ y₀) T₁) ∧
      (geoTransformAlong (lowerBM 𝔍 0 T₀ y₀) (restrict (maskBM 𝔍 0 T₀ y₀) T₁)).cosupp =
        (Subtype.val : openPreimage T₁ (maskBM 𝔍 0 T₀ y₀) → Z) ⁻¹' (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp := by
  have hTa : IsGeoTestTower 𝔍 (T₀.append T₁) := isGeoTestTower_of_barMarked h𝔍 hd _ hT
  have hTc : IsGeoTestTower (coeffEmptyBM 𝔍) (T₀.append T₁) :=
    isGeoTestTower_coeffEmptyBM h𝔍 hd _ (isGeoTestTower_emptyBoundary 𝔍 _ hTa)
  obtain ⟨hT₀c, hT₁c⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hTc
  have hT₀J := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  obtain ⟨hxU, hU⟩ := StepOneLowerDomain.tangentChoice_spec 𝔍
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀J hy₀)
  exact isGeoTestTower_tail_contactCoeffBM h𝔍 hd ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ hU T₀ hT₀c
    (maskB 𝔍 T₀ y₀) (fun z hz => (interior_subset hz).1) T₁ hT₁c

end Tail

end

end Hironaka.HironakaG11InvBMLowerTail
