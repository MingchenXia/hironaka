import Hironaka.Resolution.HironakaG8LocalContact
import Hironaka.Resolution.HironakaG11InvBMStage
import Hironaka.Resolution.HironakaG8SpecialLoci

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The local contact equivalence at a stage, for lane G11B's lower family (G8 lane, run 0080, round 5; P4 for (B'))

Blueprint: `hironaka-g8-resume-local-contact.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6b
(module 6, tangent change, and module 7 step (d2) need BM08 Cor 4.2 in `LocWPEquiv` form at a stage).

* `restrictEquiv_pullback_map`: restricted equivalence pulls back along holomorphic maps (any dimensions);
* **`locEquiv_of_restrictEquiv_closed`**: restricted-equivalent marked ideals with a closed submanifold as carrier and
  coherent ideals are locally equivalent (kinds without exceptional blowups; no condition on the boundary — the
  native-domain form is `HironakaG8LocalRestrictEquiv.locEquiv_of_restrictEquiv`);
* **`locWPEquiv_stage_contactCoeffBM`**: the strengthening of G11B's
  `HironakaG11InvBMStage.wEquiv_stage_contactCoeffBM` from `WEquiv` to `LocWPEquiv` (same sides): over
  `V = T₀⁻¹U`, `(𝔍_∅)_{T₀}|_V ≈ contactCoeffBM 𝔍 u T₀|_V`;
* **`locWPEquiv_stage_contactCoeffBM_two`**: for two tangent directions `u` (on `U`) and `u'` (on `U'`) and an open
  `W ⊆ U ∩ U'`, over `T₀⁻¹W`: `contactCoeffBM 𝔍 u T₀|_V ≈ contactCoeffBM 𝔍 u' T₀|_V` — BM08 §5 Step I.A, the input of
  G11B's module 6 (tangent change on overlaps of two anchors);
* **`sameCarrierDim_stage_contactCoeffBM_two`**: the two lower coefficient ideals have carriers of the same dimension
  on the cosupport (`HironakaG11InvBMClass.SameCarrierDim`, the other hypothesis of `ClassFunctorialFor`), from the base
  (both hypersurfaces of maximal contact have dimension `dim N - 1`) along `T₀|_W`
  (`HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong`); `sameCarrierDim_of_restrictEquiv`.

Sorry-free.  Universe-polymorphic.  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8LocalContactStage

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.MarkedIdealOperationsAlong Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.HomogenizedIdealAlong Hironaka.HomogenizedIdealAlongTower
  Hironaka.CoefficientIdealRestriction
  Hironaka.CoefficientIdealAlongRestrictionTower
  Hironaka.ContactEquivalenceAlong Hironaka.TangentDirectionAlong
  Hironaka.RestrictedIdealWeight
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalStable
  Hironaka.HironakaG8LocalContact Hironaka.NormalCrossings
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient)
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_restrict)
open scoped ProductComplexManifold

noncomputable section

/-! ### Restricted equivalence gives local equivalence -/

section RestrictEquivLoc

/-- **Restricted equivalence pulls back** along a holomorphic map (any dimensions). -/
theorem restrictEquiv_pullback_map {n m : ℕ} {M : CMfd.{u} n} {M' : CMfd.{u} m} {f : M' → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) {P Q : MarkedIdeal n M}
    (h : RestrictEquiv P Q) (hPc : P.ideal.IsCoherent) (hQc : Q.ideal.IsCoherent) {P' Q' : MarkedIdeal m M'}
    (hPN : P'.N = f ⁻¹' P.N) (hQN : Q'.N = f ⁻¹' Q.N) (hE : P'.E = Q'.E) (hPd : P'.d = P.d) (hQd : Q'.d = Q.d)
    (hPI : P'.ideal = GermIdeal.pullback (m := m) f P.ideal) (hQI : Q'.ideal = GermIdeal.pullback (m := m) f Q.ideal) :
    RestrictEquiv P' Q' := by
  refine ⟨by rw [hPN, hQN, h.N_eq], hE, by rw [hPd, hQd, h.d_eq], ?_, ?_⟩
  · rw [hPI, hQI, hPN]
    exact restrictLe_pullback_map hf (fun y hy => hy) hQc h.le
  · rw [hPI, hQI, hPN]
    exact restrictLe_pullback_map hf (fun y hy => hy) hPc h.ge

/-- The relation of the coinduction: restricted equivalence with a closed carrier and coherent ideals. -/
def ClosedRE {m : ℕ} {Y : CMfd.{u} m} (P Q : MarkedIdeal m Y) : Prop :=
  RestrictEquiv P Q ∧ IsClosedSubmanifold m P.N ∧ P.ideal.IsCoherent ∧ Q.ideal.IsCoherent

/-- **Restricted equivalence with a closed carrier and coherent ideals is stable** under the local test actions. -/
theorem isLocStable_closedRE (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} P Q => ClosedRE (m := m) (Y := Y) P Q) where
  E_eq h := h.1.E_eq.symm
  cosupp_eq h := h.1.cosupp_eq
  controlled := by
    intro m Y P Q h C Z π hπ hC
    obtain ⟨hRE, hN, hP, hQ⟩ := h
    have heq : P.geoTransform C π = Q.geoTransform C π := hRE.geoTransform_eq hN.1 hP hQ hπ.contMDiff
    have hcoh := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN hP hC hπ
    rw [← heq]
    exact ⟨RestrictEquiv.refl hcoh, isClosedSubmanifold_geoTransform_N hN hC hπ, hcoh, hcoh⟩
  projection := by
    intro _ m Y P Q h
    obtain ⟨hRE, hN, hP, hQ⟩ := h
    have hf := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1)
    have hEP : (projectionTest P).E = (projectionTest Q).E := by simp only [projectionTest, hRE.E_eq]
    refine ⟨restrictEquiv_pullback_map hf.contMDiff hRE hP hQ rfl rfl hEP rfl rfl rfl rfl,
      HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hN,
      GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hP,
      GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hQ⟩
  restrict := by
    intro m Y P Q h U
    obtain ⟨hRE, hN, hP, hQ⟩ := h
    have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ (Subtype.val : U → Y) := contMDiff_subtype_val
    refine ⟨restrictEquiv_pullback_map hval hRE hP hQ rfl rfl (by simp only [MarkedIdeal.pullback, hRE.E_eq]) rfl rfl
      rfl rfl, BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U,
      GermIdealPullbackCalculus.isCoherent_pullback hval hP, GermIdealPullbackCalculus.isCoherent_pullback hval hQ⟩

/-- **Restricted-equivalent marked ideals with a closed submanifold as carrier and coherent ideals are locally
equivalent** (kinds without exceptional blowups; no condition on the boundary). -/
theorem locEquiv_of_restrictEquiv_closed {κ : Kinds} (hexc : κ.exc = false) {n : ℕ} {X : CMfd.{u} n}
    {P Q : MarkedIdeal n X} (h : RestrictEquiv P Q) (hN : IsClosedSubmanifold n P.N) (hP : P.ideal.IsCoherent)
    (hQ : Q.ideal.IsCoherent) : LocEquiv κ P Q :=
  LocEquiv.of_isLocStable (isLocStable_closedRE κ) hexc ⟨h, hN, hP, hQ⟩

end RestrictEquivLoc

/-! ### At a stage of a test tower -/

section Stage

variable {n : ℕ} {X : CMfd.{u} n} {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (U : Opens X)
  {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
  (hT₀ : IsGeoTestTower 𝔍 T₀)

include h𝔍 hd hu hT₀

/-- **Bierstone--Milman's Corollary 4.2 at the stage `T₀`, local `s(i,ii)` form**: over `V = T₀⁻¹U`,
`(𝔍_∅)_{T₀}|_V` is `LocWPEquiv` to `contactCoeffBM 𝔍 u T₀|_V` (the strengthening of
`HironakaG11InvBMStage.wEquiv_stage_contactCoeffBM`, same sides). -/
theorem locWPEquiv_stage_contactCoeffBM :
    LocWPEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (geoTransformAlong (emptyBoundary 𝔍) T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (contactCoeffBM 𝔍 u T₀)) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol := hol_of_isCoherent h𝔞
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : U → X) := contMDiff_subtype_val
  have hT₀e := isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀
  have hTU := isGeoTestTower_restrict (𝔪 := emptyBoundary 𝔍) U hN h𝔞 T₀ hT₀e
  -- the local contact equivalence on `U`, transported along `T₀|_U`
  have hW := (locWPEquiv_contact_open_along (emptyBoundary 𝔍) hN h𝔞 hd U hu).geoTransformAlong (restrict U T₀) hTU
  rw [geoTransformAlong_restrict (𝔪 := emptyBoundary 𝔍) U hN h𝔞 T₀ hT₀e] at hW
  obtain ⟨hTs, hRE⟩ := restrictEquiv_stage_contactCoeffBM h𝔍 hd U hu T₀ hT₀
  -- coherence and closedness of the two sides of the restricted equivalence
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ hT₀e
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have hcR : (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (contactCoeffBM 𝔍 u T₀)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcTc
  have hS : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {y | u y = 0})) := by
    have h1 := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) U)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) (emptyBoundary 𝔍))
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U)
      (GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞) (isTangentDirectionAlong_pullback_val U hhol hu)
    rwa [preimage_val_contact_eq U] at h1
  have hSN : (Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {y | u y = 0}) ⊆
      (MarkedIdeal.pullback (Subtype.val : U → X) (coeffEmptyBM 𝔍)).N := fun x hx => hx.1
  obtain ⟨-, -, -, hST, -, hcT, -⟩ := restrict_tower_along (X := CMfd.of (n := n) U)
    (MarkedIdeal.pullback (Subtype.val : U → X) (coeffEmptyBM 𝔍))
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U)
    (GermIdealPullbackCalculus.isCoherent_pullback hval hwfc.isCoherent) hS hSN (restrict U T₀)
    (isGeoTestTower_restrict U hwfc.isClosedSubmanifold_N hwfc.isCoherent T₀ hT₀c)
    (CoefficientIdealRestriction.centresIn_of_isGeoTestTower_withN (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) (coeffEmptyBM 𝔍)) ((Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {y | u y = 0}))
      (restrict U T₀) hTs)
  have hNc : IsClosedSubmanifold n (geoTransformAlong (withN (MarkedIdeal.pullback (Subtype.val : U → X)
      (coeffEmptyBM 𝔍)) ((Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {y | u y = 0}))) (restrict U T₀)).N := by
    rw [N_geoTransformAlong_withN]
    exact hST
  have hWR := locEquiv_of_restrictEquiv_closed (κ := Kinds.wp) rfl hRE hNc hcT hcR
  have hpb : MarkedIdeal.pullback (Subtype.val : U → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0})) =
      withN (MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong (emptyBoundary 𝔍)))
        ((Subtype.val : U → X) ⁻¹' ((emptyBoundary 𝔍).N ∩ {y | u y = 0})) := rfl
  rw [hpb] at hWR
  exact hW.trans hWR

omit hu in
/-- **The tangent change at a stage** (BM08 §5 Step I.A; input of G11B's module 6): for tangent directions `u` on `U`
and `u'` on `U'` and an open `W ⊆ U ∩ U'`, over `T₀⁻¹W` the two lower coefficient ideals are `LocWPEquiv`:
`contactCoeffBM 𝔍 u T₀|_V ≈ contactCoeffBM 𝔍 u' T₀|_V`. -/
theorem locWPEquiv_stage_contactCoeffBM_two {U' : Opens X} {u' : X → ℂ}
    (hu₁ : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u')
    (W : Opens X) (hWU : (W : Set X) ⊆ U) (hWU' : (W : Set X) ⊆ U') :
    LocWPEquiv (X := CMfd.of (n := n) (openPreimage T₀ W))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ W → Y₀) (contactCoeffBM 𝔍 u T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ W → Y₀) (contactCoeffBM 𝔍 u' T₀)) := by
  have h1 := locWPEquiv_stage_contactCoeffBM h𝔍 hd W (IsTangentDirectionAlong.mono_open hu₁ W.isOpen hWU) T₀ hT₀
  have h2 := locWPEquiv_stage_contactCoeffBM h𝔍 hd W (IsTangentDirectionAlong.mono_open hu' W.isOpen hWU') T₀ hT₀
  exact h1.symm.trans h2

end Stage

/-! ### Carrier dimensions of the two lower coefficient ideals -/

section Two

variable {n : ℕ} {X : CMfd.{u} n} {𝔍 : MarkedIdeal n X} {Y₀ : CMfd.{u} n}

/-- **Carrier dimensions only see the restriction**: restricted equivalence on both sides preserves `SameCarrierDim`. -/
theorem sameCarrierDim_of_restrictEquiv {m : ℕ} {Y : CMfd.{u} m} {P Q P' Q' : MarkedIdeal m Y}
    (h : SameCarrierDim P Q) (hP : RestrictEquiv P P') (hQ : RestrictEquiv Q Q') : SameCarrierDim P' Q' := by
  intro x hx j
  rw [← hP.N_eq, ← hQ.N_eq]
  exact h x (by rw [hP.cosupp_eq]; exact hx) j

/-- **The two lower coefficient ideals have carriers of the same dimension** on the cosupport: for tangent directions
`u` on `U`, `u'` on `U'` and an open `W ⊆ U ∩ U'`, over `T₀⁻¹W`. -/
theorem sameCarrierDim_stage_contactCoeffBM_two (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U U' : Opens X}
    {u u' : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u)
    (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u') (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔍 T₀)
    (W : Opens X) (hWU : (W : Set X) ⊆ U) (hWU' : (W : Set X) ⊆ U') :
    SameCarrierDim (X := CMfd.of (n := n) (openPreimage T₀ W))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ W → Y₀) (contactCoeffBM 𝔍 u T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ W → Y₀) (contactCoeffBM 𝔍 u' T₀)) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol := hol_of_isCoherent h𝔞
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) := contMDiff_subtype_val
  have huW := IsTangentDirectionAlong.mono_open hu W.isOpen hWU
  have hu'W := IsTangentDirectionAlong.mono_open hu' W.isOpen hWU'
  obtain ⟨hTs, hRE⟩ := restrictEquiv_stage_contactCoeffBM h𝔍 hd W huW T₀ hT₀
  obtain ⟨-, hRE'⟩ := restrictEquiv_stage_contactCoeffBM h𝔍 hd W hu'W T₀ hT₀
  have hW0 : WEquiv (X := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0})))
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u' x = 0}))) :=
    (locWPEquiv_contact_two_directions (emptyBoundary 𝔍) hN h𝔞 hd hu hu' W hWU hWU').wEquiv
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN W
  have hcU : (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞
  -- the hypersurfaces of maximal contact on `W`
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
    obtain ⟨k, hk, hk'⟩ := IsTangentDirectionAlong.regularAtDim_contact (hol_of_isCoherent hcU) hNU hwU hx'
    rw [preimage_val_contact_eq W] at hk'
    exact ⟨k, hk, hk'⟩
  obtain ⟨hS, hSd⟩ := hreg huW
  obtain ⟨hS', hSd'⟩ := hreg hu'W
  have hcohA := GermIdealPullbackCalculus.isCoherent_pullback hval hwfc.isCoherent
  have hwfA : (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0}))).IsWellFormed :=
    ⟨hS, hcohA, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hS⟩
  have hwfB : (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u' x = 0}))).IsWellFormed :=
    ⟨hS', hcohA, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hS'⟩
  have hdim0 : SameCarrierDim (X := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0})))
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u' x = 0}))) := by
    intro x hx j
    have hxB := hW0.cosupp_eq ▸ hx
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
  have hT := HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong hwfA hwfB hW0 hdim0 (restrict W T₀) hTs
  exact sameCarrierDim_of_restrictEquiv hT hRE hRE'

end Two

end

end Hironaka.HironakaG8LocalContactStage
