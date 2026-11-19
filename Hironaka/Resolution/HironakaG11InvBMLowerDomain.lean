import Hironaka.Resolution.HironakaG11InvBMStage

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's lower marked ideal of level `0` lies in the domain (repair (B'), plan module 4, level 0)

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` (module 4).
Source: Bierstone--Milman 2008, §5 Step I (the marked ideal `𝒞_U(I_∅)` on the hypersurface of maximal contact `P` has
dimension `dim N - 1`; its transforms are marked ideals of the same dimension); Włodarczyk 2005, Step 1bb (after the
codimension-one components have been blown up).  The analogue of `ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le`
for Bierstone--Milman's coefficient ideal (transformed, not re-formed; divisor: the members born along `T₀`).

* `cosupp_contactCoeffBM_iff`: over `U`, the cosupport of `contactCoeffBM 𝔍 u T₀` is that of `𝔍_{T₀}` (pointwise form of
  `HironakaG11InvBMStage.cosupp_stage_contactCoeffBM`);
* **`isInvDomain_contactCoeffBM_of_le`**: for `𝔍` well formed with `d ≥ 1` and `dim N ≤ k`, a tangent direction `u` on an
  open `U`, a multiple test blow-up `T₀` of `J̄`, and an open `W ⊆ T₀⁻¹U` on which no point of `(N ∩ V(u))_{T₀}` lies in the
  codimension-one part `Z₁(J̄_{T₀})`, the restriction of `contactCoeffBM 𝔍 u T₀` to `W` lies in `IsInvDomain (k - 1)`;
* **`mem_maskBM_and_isInvDomain_lowerBM_zero`**: at a point `y₀` of the cosupport in the regime of level `0` (marked ideal of
  maximal order), `y₀` lies in its mask and `lowerBM 𝔍 0 T₀ y₀` lies in `IsInvDomain (k - 1)`.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11InvBMLowerDomain

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.MarkedIdealEquivalence Hironaka.MarkedIdealEquivalence.MarkedIdeal
  Hironaka.HomogenizedIdealAlong Hironaka.HomogenizedIdealAlongTower
  Hironaka.CoefficientIdealRestriction Hironaka.CodimOneSupportAlong
  Hironaka.ContactEquivalenceAlong Hironaka.TangentDirectionAlong
  Hironaka.ContactEquivalenceStage Hironaka.ContactStageInvDomain
  Hironaka.MaximalContactAlongTower Hironaka.NormalCrossings
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
open Hironaka.HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open Hironaka.ResolutionInvariantSpec (DimLE IsInvDomain)
open Hironaka.ContactIndependenceAlong (one_le_coeffMarkedAlong_d)

noncomputable section

variable {n : ℕ}

section Domain

variable {X : CMfd.{u} n} {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ}
  (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)

include h𝔍 hd hu in
/-- **Over `U`, the cosupport of `contactCoeffBM 𝔍 u T₀` is that of `𝔍_{T₀}`** (`T₀` a multiple test blow-up of `𝔍`). -/
theorem cosupp_contactCoeffBM_iff (hT₀ : IsGeoTestTower 𝔍 T₀) {y : Y₀} (hyU : T₀.proj y ∈ U) :
    y ∈ (contactCoeffBM 𝔍 u T₀).cosupp ↔ y ∈ (geoTransformAlong 𝔍 T₀).cosupp := by
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ (isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀)
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong h𝔍.isClosedSubmanifold_N
    h𝔍.isCoherent T₀ hT₀
  have h := cosupp_stage_contactCoeffBM h𝔍 hd U hu T₀ hT₀
  rw [cosupp_pullback_val (contactCoeffBM 𝔍 u T₀) (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcTc),
    cosupp_pullback_val _ (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT)] at h
  have hyV : y ∈ openPreimage T₀ U := hyU
  exact Set.ext_iff.mp h ⟨y, hyV⟩

include h𝔍 hd hu in
/-- **Bierstone--Milman's coefficient ideal on maximal contact at the stage `T₀` lies in the domain on every open
`W ⊆ T₀⁻¹U` off `Z₁(J̄_{T₀})`**: for `𝔍` well formed with `d ≥ 1` and `dim N ≤ k`, `u` a tangent direction of `(𝔞|_N, d)` on
`U`, `T₀` a multiple test blow-up of `J̄ = 𝓒_N(𝓗_N(𝔍))`, and `W ⊆ T₀⁻¹U` open with no point of `(N ∩ V(u))_{T₀} ∩ W` in the
codimension-one part `Z₁(J̄_{T₀})`, `contactCoeffBM 𝔍 u T₀|_W` lies in `IsInvDomain (k - 1)`. -/
theorem isInvDomain_contactCoeffBM_of_le {k : ℕ} (hk : DimLE n 𝔍.N k) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀)
    (W : Opens Y₀) (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U)
    (hZ : ∀ y ∈ W, y ∈ strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) →
      y ∉ codimOnePartAlong (geoTransformAlong (barMarked 𝔍) T₀).N (geoTransformAlong (barMarked 𝔍) T₀).ideal
        (geoTransformAlong (barMarked 𝔍) T₀).d) :
    IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : W → Y₀) (contactCoeffBM 𝔍 u T₀)) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol𝔍 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  have hJN : IsClosedSubmanifold n (barMarked 𝔍).N := hN
  have hJc : (barMarked 𝔍).ideal.IsCoherent := isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hWJ := coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd
  have hT₀a : IsGeoTestTower 𝔍 T₀ := (hWJ.2 T₀).1.mp hT₀
  have hT₀e := isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀a
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ hT₀e
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have hholc := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcTc
  -- Giraud at the stage `T₀` over `U`
  have hGir : ∀ z ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp, T₀.proj z ∈ U →
      z ∈ strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) := by
    intro z hz hzU
    rw [(hWJ.2 T₀).2 hT₀] at hz
    exact MemberInterTowerAlong.strictAlong_mono T₀ (fun x hx => hx.1) (cosupp_subset_strictAlong_along 𝔍 hN h𝔞 hd hu T₀ hT₀a ⟨hz, hzU⟩)
  refine ⟨⟨isClosedSubmanifold_strictAlong_stage_of_le 𝔍 hN h𝔞 hd U hu T₀ hT₀a W hWU,
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcTc,
    (IsWellFormed.pullback_val (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfc T₀ hT₀c) W).isSNCDivisor,
    ?_⟩, fun y hy => ?_, ?_, fun y hy => ?_⟩
  · -- transversality: all members of the divisor are born along `T₀`, from centres in the strict transforms of `N ∩ V(u)`
    have hA : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {x | u x = 0})) := by
      have h1 := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) U)
        (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U)
        (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞)
        (isTangentDirectionAlong_pullback_val U hhol𝔍 hu)
      have hset : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N ∩ {x : U | (u ∘ Subtype.val) x = 0} ∩ univ =
          (Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {x | u x = 0}) := by
        ext y
        simp [MarkedIdeal.pullback]
      rw [hset] at h1
      exact h1
    have hcent : ∀ {Z : CMfd.{u} n} (T : BlowupTower X Z) (C : Set Z),
        IsGeoTestTower (coeffEmptyBM 𝔍) T →
        (geoTransformAlong (coeffEmptyBM 𝔍) T).IsAdmissibleCentre C →
        C ∩ T.proj ⁻¹' (U : Set X) ⊆ strictAlong T (𝔍.N ∩ {x | u x = 0}) := by
      intro Z T C hT hC z hz
      have hTe : IsGeoTestTower (emptyBoundary 𝔍) T :=
        (coeffAlong_tower (emptyBoundary 𝔍) hN h𝔞 hd T).1.mp hT
      have hzc : z ∈ (geoTransformAlong (emptyBoundary 𝔍) T).cosupp := by
        rw [cosupp_geoTransformAlong_emptyBoundary, ← cosupp_geoTransformAlong_coeffEmptyBM h𝔍 hd T hTe]
        exact hC.2.1 hz.1
      exact MemberInterTowerAlong.strictAlong_mono T (fun x hx => hx.1)
        (cosupp_subset_strictAlong_along (emptyBoundary 𝔍) hN h𝔞 hd hu T hTe ⟨hzc, hz.2⟩)
    have hD := CodimOneAdmissibleAlong.isTransverse_drop_E_inter_preimage _ hwfc U hA hcent T₀ hT₀c
    have hlen : (coeffEmptyBM 𝔍).E.length = 0 := rfl
    rw [hlen, List.drop_zero] at hD
    have hD' : IsTransverse n (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ (W : Set Y₀))
        (geoTransformAlong (coeffEmptyBM 𝔍) T₀).E := by
      refine CodimOneAdmissibleAlong.isTransverse_of_forall_eventually fun x hx => ?_
      refine ⟨strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' (U : Set X), ⟨hx.1, hWU hx.2⟩, ?_, hD⟩
      filter_upwards [W.isOpen.mem_nhds hx.2] with y hyW
      exact ⟨fun h => ⟨h.1, hWU h.2⟩, fun h => ⟨h.1, hyW⟩⟩
    have h2 := NormalCrossingsInvariance.isTransverse_preimage (NormalCrossingsInvariance.pullsBackCoordinates_val W) hD'
    have hset : (Subtype.val : W → Y₀) ⁻¹' (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ (W : Set Y₀)) =
        (Subtype.val : W → Y₀) ⁻¹' strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) := by
      ext p
      exact ⟨fun h => h.1, fun h => ⟨h, p.2⟩⟩
    rw [hset] at h2
    exact h2
  · -- dimension
    obtain ⟨j, hj1, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔍 hN h𝔞 hd U hu T₀ hT₀a (hWU y.2) hy
    obtain ⟨j', hj'k, hj'⟩ := InvDomainTowerAlong.dimLE_geoTransformAlong hN h𝔞 hk T₀ hT₀a y hj1.2.1
    have hjj := RegularPointDimension.eq_of_regularAtDim hj1 hj'
    exact ⟨j, by omega, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj⟩
  · -- the mark
    show 1 ≤ (contactCoeffBM 𝔍 u T₀).d
    rw [contactCoeffBM_d]
    exact one_le_coeffMarkedAlong_d (emptyBoundary 𝔍)
  · -- nonvanishing along the carrier: off `Z₁`, as for the W-family (TN3's lemma), with the cosupport of the stage
    have hN𝔍J : (geoTransformAlong 𝔍 T₀).N = (geoTransformAlong (barMarked 𝔍) T₀).N := by
      rw [N_geoTransformAlong, N_geoTransformAlong]
      rfl
    obtain ⟨j, hj1, hj⟩ := exists_regularAtDim_strictAlong_stage 𝔍 hN h𝔞 hd U hu T₀ hT₀a (hWU y.2) hy
    rw [hN𝔍J] at hj1
    refine CodimOnePartTowerAlong.isNonzeroAlongAt_of_notMem_codimOnePartAlong
      (N := (Subtype.val : W → Y₀) ⁻¹' (geoTransformAlong (barMarked 𝔍) T₀).N)
      (𝔞 := GermIdeal.pullback (m := n) (Subtype.val : W → Y₀) (geoTransformAlong (barMarked 𝔍) T₀).ideal)
      (μ := (geoTransformAlong (barMarked 𝔍) T₀).d) (ν := (geoTransformAlong (coeffEmptyBM 𝔍) T₀).d) (k := j)
      (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcTc)
      (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj1)
      (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hj) (Eventually.of_forall fun z hz => ?_)
      (Eventually.of_forall fun z hz => ?_) ?_
    · have hz' : z ∈ (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (barMarked 𝔍) T₀)).cosupp := hz
      rw [cosupp_pullback_val _ hhol W] at hz'
      exact hGir z hz' (hWU z.2)
    · have hz' : z ∈ (MarkedIdeal.pullback (Subtype.val : W → Y₀) (contactCoeffBM 𝔍 u T₀)).cosupp := hz
      rw [cosupp_pullback_val (contactCoeffBM 𝔍 u T₀) hholc W] at hz'
      have h1 := (cosupp_contactCoeffBM_iff h𝔍 hd U hu T₀ hT₀a (hWU z.2)).mp hz'
      rw [← (hWJ.2 T₀).2 hT₀] at h1
      show z ∈ (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (barMarked 𝔍) T₀)).cosupp
      rw [cosupp_pullback_val _ hhol W]
      exact h1
    · rw [CodimOnePartCanonical.codimOnePartAlong_pullback_val _ hhol]
      exact hZ y y.2 hy

end Domain

/-! ### Level `0` of Bierstone--Milman's family -/

section LevelZero

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **Bierstone--Milman's lower marked ideal of level `0` lies in the domain**: for `𝔍` well formed with `d ≥ 1`, of maximal
order along `N` with `dim N ≤ k` (`0 < n`), along a multiple test blow-up `T₀` of `J̄`, at a point `y₀` of the cosupport in the
regime of level `0`, `y₀` lies in its mask `maskBM 𝔍 0 T₀ y₀ = maskB 𝔍 T₀ y₀` and `lowerBM 𝔍 0 T₀ y₀` lies in
`IsInvDomain (k - 1)`. -/
theorem mem_maskBM_and_isInvDomain_lowerBM_zero (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k : ℕ} (hk : DimLE n 𝔍.N k) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hreg : stepRegime 𝔍 0 T₀ y₀) :
    y₀ ∈ maskBM 𝔍 0 T₀ y₀ ∧ IsInvDomain (k - 1) (lowerBM 𝔍 0 T₀ y₀) := by
  refine ⟨mem_maskBM_of_stepRegime 𝔍 h𝔍 hd hn hmax T₀ hT₀ hy₀ hreg, ?_⟩
  obtain ⟨hxU, hU⟩ := StepOneLowerDomain.tangentChoice_spec 𝔍
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀)
  exact isInvDomain_contactCoeffBM_of_le h𝔍 hd ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ hU T₀ hk hT₀
    (maskB 𝔍 T₀ y₀) (fun z hz => (interior_subset hz).1) (fun z hz _ => (interior_subset hz).2.2)

end LevelZero

end

end Hironaka.HironakaG11InvBMLowerDomain
