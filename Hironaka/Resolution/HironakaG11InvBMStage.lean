import Hironaka.Resolution.HironakaG11InvBMLower
import Hironaka.Invariant.ContactStageInvDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's coefficient ideal on maximal contact at a stage (repair (B'), plan modules 4--5, the stage)

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` (modules 4, 5).
Source: Bierstone--Milman 2008, Corollary 4.2 (`I|_U` is equivalent to its coefficient ideal on a hypersurface of maximal
contact), §5 Step I.B (the transforms `𝒞_{q_k}` of `𝒞 = 𝒞_U(I_∅)`); Włodarczyk 2005, Lemmas `le:codim2`, `le:cf`, `le:S`.

For `𝔍` well formed with `d ≥ 1`, `u` a tangent direction of `(𝔍.ideal|_N, d)` along `N` on an open `U`, and `T₀` a multiple
test blow-up of `𝔍` (e.g. of `J̄ = 𝓒_N(𝓗_N(𝔍))`), over `V = T₀⁻¹U`:

* the divisor-free marked ideal `𝔍_∅` has the multiple test blow-ups of `𝔍` (fewer normal-crossing conditions) with the same
  transforms up to the divisor (`geoTransformAlong_emptyBoundary`, `isGeoTestTower_emptyBoundary`), and so does the
  coefficient ideal `𝓒_N(𝔍_∅)` (`isGeoTestTower_coeffEmptyBM`, `cosupp_geoTransformAlong_coeffEmptyBM`);
* **`restrictEquiv_stage_contactCoeffBM`**: `contactCoeffBM 𝔍 u T₀|_V` is restricted-equivalent to the transform along
  `T₀|_U` of Bierstone--Milman's `𝒞_U(𝔍_∅) = 𝓒_N(𝔍_∅)|_{N ∩ V(u)}` (restriction commutes with the transform, Włodarczyk
  `le:cf` along `N`: `CoefficientIdealAlongRestrictionTower.restrict_tower_along`);
* **`wEquiv_stage_contactCoeffBM`**: `(𝔍_∅)_{T₀}|_V ≃ contactCoeffBM 𝔍 u T₀|_V` (Bierstone--Milman Corollary 4.2 /
  Włodarczyk `le:codim2` on `U`, transported along `T₀|_U`);
* `cosupp_stage_contactCoeffBM`: hence `cosupp (contactCoeffBM 𝔍 u T₀)|_V = cosupp 𝔍_{T₀}|_V`.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11InvBMStage

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.MarkedIdealEquivalence Hironaka.MarkedIdealEquivalence.MarkedIdeal
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.HomogenizedIdealAlong Hironaka.HomogenizedIdealAlongTower
  Hironaka.CoefficientIdealRestriction
  Hironaka.CoefficientIdealAlongRestrictionTower
  Hironaka.ContactEquivalenceAlong Hironaka.TangentDirectionAlong
  Hironaka.NormalCrossings Hironaka.StepOneRegime
  Hironaka.HironakaG11InvBMLower
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_restrict)

noncomputable section

variable {n : ℕ}

/-! ### Forgetting the divisor -/

section Empty

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- `𝔍_∅` is `𝔍` with all members dropped. -/
theorem dropE_eq_emptyBoundary : ({ 𝔍 with E := 𝔍.E.drop 𝔍.E.length } : MarkedIdeal n X) = emptyBoundary 𝔍 := by
  rw [List.drop_length]
  rfl

/-- **The transforms of `𝔍_∅` are those of `𝔍` with the original members dropped.** -/
theorem geoTransformAlong_emptyBoundary {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    geoTransformAlong (emptyBoundary 𝔍) T =
      { geoTransformAlong 𝔍 T with E := (geoTransformAlong 𝔍 T).E.drop 𝔍.E.length } := by
  rw [← dropE_eq_emptyBoundary]
  exact geoTransformAlong_dropE 𝔍 le_rfl T

/-- **A multiple test blow-up of `𝔍` is one of `𝔍_∅`.** -/
theorem isGeoTestTower_emptyBoundary {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔍 T) :
    IsGeoTestTower (emptyBoundary 𝔍) T := by
  rw [← dropE_eq_emptyBoundary]
  exact isGeoTestTower_dropE 𝔍 le_rfl T hT

theorem cosupp_geoTransformAlong_emptyBoundary {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (emptyBoundary 𝔍) T).cosupp = (geoTransformAlong 𝔍 T).cosupp := by
  rw [geoTransformAlong_emptyBoundary]
  rfl

/-- The pullbacks of the transforms of `𝔍_∅` and of `𝔍` along any map have the same cosupport. -/
theorem cosupp_pullback_geoTransformAlong_emptyBoundary {Y : CMfd.{u} n} (T : BlowupTower X Y) {W : Type u}
    [TopologicalSpace W] [ChartedSpace (ComplexModel n) W] (φ : W → Y) :
    (MarkedIdeal.pullback φ (geoTransformAlong (emptyBoundary 𝔍) T)).cosupp =
      (MarkedIdeal.pullback φ (geoTransformAlong 𝔍 T)).cosupp := by
  rw [geoTransformAlong_emptyBoundary]
  rfl

variable {𝔍} (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
include h𝔍

theorem isWellFormed_emptyBoundary : (emptyBoundary 𝔍).IsWellFormed :=
  ⟨h𝔍.isClosedSubmanifold_N, h𝔍.isCoherent, isSNCDivisor_nil,
    isTransverse_nil_of_isClosedSubmanifold h𝔍.isClosedSubmanifold_N⟩

theorem isWellFormed_coeffEmptyBM : (coeffEmptyBM 𝔍).IsWellFormed :=
  ⟨h𝔍.isClosedSubmanifold_N,
    isCoherent_coeffMarkedAlong (𝔪 := emptyBoundary 𝔍) h𝔍.isCoherent h𝔍.isClosedSubmanifold_N, isSNCDivisor_nil,
    isTransverse_nil_of_isClosedSubmanifold h𝔍.isClosedSubmanifold_N⟩

include hd

/-- **A multiple test blow-up of `J̄ = 𝓒_N(𝓗_N(𝔍))` is one of `𝔍`** (`J̄ ≃ 𝔍`). -/
theorem isGeoTestTower_of_barMarked {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (StepOneValue.barMarked 𝔍) T) : IsGeoTestTower 𝔍 T :=
  ((coeff_homAlong_wEquiv 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd).2 T).1.mp hT

/-- **A multiple test blow-up of `𝔍_∅` is one of its coefficient ideal `𝓒_N(𝔍_∅)`.** -/
theorem isGeoTestTower_coeffEmptyBM {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (emptyBoundary 𝔍) T) :
    IsGeoTestTower (coeffEmptyBM 𝔍) T :=
  (coeffAlong_tower (emptyBoundary 𝔍) h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd T).1.mpr hT

/-- **Along it the cosupports of `𝓒_N(𝔍_∅)` are those of `𝔍`.** -/
theorem cosupp_geoTransformAlong_coeffEmptyBM {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (emptyBoundary 𝔍) T) :
    (geoTransformAlong (coeffEmptyBM 𝔍) T).cosupp = (geoTransformAlong 𝔍 T).cosupp := by
  show (geoTransformAlong (coeffMarkedAlong (emptyBoundary 𝔍)) T).cosupp = _
  rw [(coeffAlong_tower (emptyBoundary 𝔍) h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd T).2 hT,
    cosupp_geoTransformAlong_emptyBoundary]

end Empty

/-! ### The coefficient ideal on maximal contact at a stage -/

section Stage

variable {X : CMfd.{u} n} {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ}
  (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
  (hT₀ : IsGeoTestTower 𝔍 T₀)

/-- The hypersurface of maximal contact on `U`. -/
theorem preimage_val_contact_eq :
    (MarkedIdeal.pullback (Subtype.val : U → X) (emptyBoundary 𝔍)).N ∩ {x : U | (u ∘ Subtype.val) x = 0} ∩ univ =
      (Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {y | u y = 0}) := by
  ext y
  simp [MarkedIdeal.pullback, emptyBoundary]

include h𝔍 hd hu hT₀

/-- **Bierstone--Milman's `𝒞_{q}` at the stage `T₀`, over `V = T₀⁻¹U`**: the transform along `T₀|_U` of
`𝒞_U(𝔍_∅) = 𝓒_N(𝔍_∅)|_{N ∩ V(u)}` is a multiple test blow-up and is restricted-equivalent to `contactCoeffBM 𝔍 u T₀|_V`
(the transform of the coefficient ideal restricted to the strict transform of the hypersurface). -/
theorem restrictEquiv_stage_contactCoeffBM :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0})))
        (restrict U T₀) ∧
      RestrictEquiv (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
          (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0}))) (restrict U T₀))
        (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (contactCoeffBM 𝔍 u T₀)) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol := hol_of_isCoherent h𝔞
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : U → X) := contMDiff_subtype_val
  set 𝔪U := MarkedIdeal.pullback (Subtype.val : U → X) (emptyBoundary 𝔍) with h𝔪U
  have hNU : IsClosedSubmanifold n 𝔪U.N := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hcU : 𝔪U.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞
  have huU : IsTangentDirectionAlong 𝔪U.N 𝔪U.ideal 𝔪U.d univ (u ∘ Subtype.val) :=
    isTangentDirectionAlong_pullback_val U hhol hu
  have hS := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) U) (𝔪 := 𝔪U) hNU hcU huU
  have hSN : 𝔪U.N ∩ {x | (u ∘ Subtype.val) x = 0} ∩ univ ⊆ 𝔪U.N := fun x hx => hx.1.1
  have hT₀e := isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀
  have hTU : IsGeoTestTower 𝔪U (restrict U T₀) := isGeoTestTower_restrict (𝔪 := emptyBoundary 𝔍) U hN h𝔞 T₀ hT₀e
  have hcent := centresIn_contact_along (X := CMfd.of (n := n) U) 𝔪U hNU hcU hd huU (restrict U T₀) hTU
  obtain ⟨hTs, hRE, -⟩ := coeffAlong_restrict_tower (X := CMfd.of (n := n) U) 𝔪U hNU hcU hd hS hSN (restrict U T₀) hTU hcent
  have hcoeff : coeffMarkedAlong 𝔪U = MarkedIdeal.pullback (Subtype.val : U → X) (coeffEmptyBM 𝔍) :=
    (pullback_val_coeffMarkedAlong U (emptyBoundary 𝔍) h𝔞 hN hd).symm
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ hT₀e
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  rw [preimage_val_contact_eq U, hcoeff] at hTs hRE
  refine ⟨hTs, ?_⟩
  rw [geoTransformAlong_restrict U hwfc.isClosedSubmanifold_N hwfc.isCoherent T₀ hT₀c, strictAlong_restrict U T₀] at hRE
  exact hRE

/-- **Bierstone--Milman's Corollary 4.2 at the stage `T₀`**: over `V = T₀⁻¹U`, `(𝔍_∅)_{T₀}|_V` is equivalent to
`contactCoeffBM 𝔍 u T₀|_V`. -/
theorem wEquiv_stage_contactCoeffBM :
    WEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (geoTransformAlong (emptyBoundary 𝔍) T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (contactCoeffBM 𝔍 u T₀)) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol := hol_of_isCoherent h𝔞
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : U → X) := contMDiff_subtype_val
  have hT₀e := isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀
  have hTU := isGeoTestTower_restrict (𝔪 := emptyBoundary 𝔍) U hN h𝔞 T₀ hT₀e
  -- the contact equivalence on `U`, transported along `T₀|_U`
  have hW := (contact_wEquiv_open_along (emptyBoundary 𝔍) hN h𝔞 hd U hu).geoTransformAlong hTU
  rw [geoTransformAlong_restrict (𝔪 := emptyBoundary 𝔍) U hN h𝔞 T₀ hT₀e] at hW
  obtain ⟨hTs, hRE⟩ := restrictEquiv_stage_contactCoeffBM h𝔍 hd U hu T₀ hT₀
  -- coherence of the two sides of the restricted equivalence
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ hT₀e
  obtain ⟨hNTc, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have hcR : (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (contactCoeffBM 𝔍 u T₀)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcTc
  have hS : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {y | u y = 0})) := by
    have h1 := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) U)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) (emptyBoundary 𝔍))
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U)
      (GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞) (isTangentDirectionAlong_pullback_val U hhol hu)
    rwa [preimage_val_contact_eq U] at h1
  have hcS : (MarkedIdeal.pullback (Subtype.val : U → X)
      (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0}))).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval hwfc.isCoherent
  have hSN : (Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {y | u y = 0}) ⊆
      (MarkedIdeal.pullback (Subtype.val : U → X) (coeffEmptyBM 𝔍)).N := fun x hx => hx.1
  obtain ⟨-, -, -, hST, -, hcT, -⟩ := restrict_tower_along (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) (coeffEmptyBM 𝔍))
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U)
    (GermIdealPullbackCalculus.isCoherent_pullback hval hwfc.isCoherent) hS hSN (restrict U T₀)
    (isGeoTestTower_restrict U hwfc.isClosedSubmanifold_N hwfc.isCoherent T₀ hT₀c)
    (CoefficientIdealRestriction.centresIn_of_isGeoTestTower_withN (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) (coeffEmptyBM 𝔍)) ((Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {y | u y = 0}))
      (restrict U T₀) hTs)
  have hWR := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hRE (by
    show IsClosed (geoTransformAlong (withN (MarkedIdeal.pullback (Subtype.val : U → X) (coeffEmptyBM 𝔍))
      ((Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {y | u y = 0}))) (restrict U T₀)).N
    rw [N_geoTransformAlong_withN]
    exact hST.1) hcT hcR
  have hpb : MarkedIdeal.pullback (Subtype.val : U → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0})) =
      withN (MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong (emptyBoundary 𝔍)))
        ((Subtype.val : U → X) ⁻¹' ((emptyBoundary 𝔍).N ∩ {y | u y = 0})) := rfl
  rw [hpb] at hWR
  exact hW.trans hWR

/-- **The cosupport of `contactCoeffBM` at the stage `T₀`, over `V = T₀⁻¹U`, is that of `𝔍_{T₀}`.** -/
theorem cosupp_stage_contactCoeffBM :
    (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (contactCoeffBM 𝔍 u T₀)).cosupp =
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (geoTransformAlong 𝔍 T₀)).cosupp := by
  rw [← (wEquiv_stage_contactCoeffBM h𝔍 hd U hu T₀ hT₀).cosupp_eq]
  exact cosupp_pullback_geoTransformAlong_emptyBoundary 𝔍 T₀ _

end Stage

end

end Hironaka.HironakaG11InvBMStage
