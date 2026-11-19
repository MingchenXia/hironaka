import Hironaka.Resolution.HironakaG8LocalStable
import Hironaka.Resolution.HironakaG1TwoVertexWeakClass
import Hironaka.Resolution.HironakaG1ChosenCommonContactClassData
import Hironaka.Resolution.HironakaActualOriginalPowerTransform
import Hironaka.Resolution.HironakaG11PresLineState

/-! Quadratic reduction modulo restriction to the actual carrier. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1CarrierQuadraticReduction

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers IdealOrderArithmetic
  HironakaActualPowerBoundaryExponents BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong RestrictedIdealWeight RestrictLeCalculus
  ResolutionInvariantSpec HironakaActualOriginalPowerTransform HironakaG8LocalHistory
  HironakaG8LocalStable HironakaActualProjectionTestRecord GermIdealPullbackCalculus
open scoped ProductComplexManifold

/-- The two inequalities needed for a quadratic reduction on the true source
carrier. Both remain meaningful after controlled transforms. -/
structure CarrierQuadraticReduction {m : ℕ} {X : CMfd.{0} m} (P Q : MarkedIdeal m X) : Prop where
  carrier : P.N = Q.N
  boundary : Q.E = P.E
  mark : P.d = 2 * Q.d
  domain : ∃ k l : ℕ, IsInvDomain k P ∧ IsInvDomain l Q
  inclusion : RestrictLe P.N P.ideal (idealPow Q.ideal 2)
  product : RestrictLe P.N (idealPow Q.ideal 3) (P.ideal.mul Q.ideal)

/-- The normalized cosupport proof only needs inequalities on the carrier. -/
theorem CarrierQuadraticReduction.cosupp_eq {m : ℕ} {X : CMfd.{0} m}
    {P Q : MarkedIdeal m X} (h : CarrierQuadraticReduction P Q) : P.cosupp = Q.cosupp := by
  classical
  obtain ⟨_, _, hP, hQ⟩ := h.domain
  let N := P.N
  let I := Q.ideal
  let J := P.ideal
  let d := Q.d
  have hI := hQ.isWellFormed.isCoherent
  have hN := hP.isWellFormed.isClosedSubmanifold_N
  have hHol : ∀ x f, I.mem x f → HolomorphicAt m f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hI hf
  change cosupport m P.N J P.d = cosupport m Q.N I d
  rw [← h.carrier, h.mark]
  ext x
  constructor
  · intro hx
    by_contra hn
    have hex : ∃ j : ℕ, x ∉ cosupport m N I j := ⟨d, hn⟩
    let s := Nat.find hex
    have hs : x ∉ cosupport m N I s := Nat.find_spec hex
    have hs₀ : s ≠ 0 := by
      intro he
      rw [he, cosupport_zero hHol] at hs
      exact hs hx.1
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hs₀
    have hLess : j < s := by omega
    have hjd : j < d := by
      have hFind := Nat.find_min' hex hn
      change s ≤ d at hFind
      omega
    have hjIn : x ∈ cosupport m N I j := by
      by_contra hmiss
      exact (Nat.find_min hex hLess) hmiss
    have hProd : x ∈ cosupport m N (J.mul I) (2 * d + j) :=
      inter_cosupport_subset_cosupport_mul _ _ ⟨hx, hjIn⟩
    have hCube := cosupport_subset_of_restrictLe h.product (2 * d + j) hProd
    have hSharp : x ∈ cosupport m N (idealPow I 3) (3 * j + 1) :=
      cosupport_anti (by omega) hCube
    rw [cosupport_idealPow_mul_succ_eq_along (X := X) hN hI (by decide : 1 ≤ 3) j] at hSharp
    exact hs (hj ▸ hSharp)
  · intro hx
    have hPow := cosupport_subset_cosupport_idealPow d 2 hx
    have hTwo : x ∈ cosupport m N (idealPow I 2) (2 * d) := by
      simpa only [Nat.mul_comm] using hPow
    exact cosupport_subset_of_restrictLe h.inclusion _ hTwo

private theorem CarrierQuadraticReduction.controlled {m : ℕ} {X Y : CMfd.{0} m}
    {P Q : MarkedIdeal m X} (h : CarrierQuadraticReduction P Q) (C : Set X)
    (π : Y → X) (hπ : IsBlowupAlong m C π) (hCP : P.IsAdmissibleCentre C) :
    CarrierQuadraticReduction (P.geoTransform C π) (Q.geoTransform C π) := by
  obtain ⟨k, l, hP, hQ⟩ := h.domain
  have hCQ : Q.IsAdmissibleCentre C :=
    (HironakaG8MixedEquiv.isAdmissibleCentre_congr h.boundary.symm h.cosupp_eq C).mp hCP
  have hT : IsGeoTestTower P (.step .refl C π hπ) := ⟨trivial, hCP⟩
  have hU : IsGeoTestTower Q (.step .refl C π hπ) := ⟨trivial, hCQ⟩
  have hP' := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP (.step .refl C π hπ) hT
  have hQ' := InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ (.step .refl C π hπ) hU
  have h2 := original_power_transform Q hQ 2 (by decide) (.step .refl C π hπ) hU
  have h3 := original_power_transform Q hQ 3 (by decide) (.step .refl C π hπ) hU
  have hC2 : (powerMarked Q 2).IsAdmissibleCentre C := h2.1.2
  have hC3 : (powerMarked Q 3).IsAdmissibleCentre C := h3.1.2
  let B := MarkedIdealOperationsTransform.MarkedIdeal.mul P Q
  have hCB : B.IsAdmissibleCentre C :=
    MarkedIdealOperationsTransform.MarkedIdeal.IsAdmissibleCentre.mul h.carrier hCP hCQ
  have hB : B.ideal.IsCoherent := isCoherent_mul hP.isWellFormed.isCoherent hQ.isWellFormed.isCoherent
  have hm := h.mark
  have hPair : IsSubmanifoldPair P Q :=
    ⟨h.carrier, h.boundary.symm, hP.isWellFormed.isClosedSubmanifold_N,
      hP.isWellFormed.isCoherent, hQ.isWellFormed.isCoherent⟩
  have hB' := geoTransform_mul_restrictEquiv hPair hπ hCP hCQ
  have hN' : (P.geoTransform C π).N = (Q.geoTransform C π).N := by
    rw [geoTransform_N, geoTransform_N, h.carrier]
  refine ⟨hN', by simp only [geoTransform_E, h.boundary], h.mark, ⟨k, l, hP', hQ'⟩, ?_, ?_⟩
  · have hd : P.d = (powerMarked Q 2).d := by
      change P.d = Q.d * 2
      omega
    have hMon := HomogenizedIdealAlongTower.restrictLe_geoTransform_of_restrictLe
      (𝔫₁ := P) (𝔫₂ := powerMarked Q 2)
      hP.isWellFormed.isClosedSubmanifold_N h.carrier hd hP.isWellFormed.isCoherent
      (isCoherent_idealPow hQ.isWellFormed.isCoherent 2) hCP hC2 hπ h.inclusion
    have hNext : RestrictLe (Q.geoTransform C π).N
        ((powerMarked Q 2).geoTransform C π).ideal (idealPow (Q.geoTransform C π).ideal 2) := h2.2.le
    rw [← hN'] at hNext
    exact RestrictLe.trans hMon hNext
  · have hd : (powerMarked Q 3).d = B.d := by
      change Q.d * 3 = P.d + Q.d
      omega
    have hOld : RestrictLe (powerMarked Q 3).N (powerMarked Q 3).ideal B.ideal := by
      change RestrictLe Q.N (idealPow Q.ideal 3) (P.ideal.mul Q.ideal)
      rw [← h.carrier]
      exact h.product
    have hMon := HomogenizedIdealAlongTower.restrictLe_geoTransform_of_restrictLe
      (𝔫₁ := powerMarked Q 3) (𝔫₂ := B)
      hQ.isWellFormed.isClosedSubmanifold_N h.carrier.symm hd
      (isCoherent_idealPow hQ.isWellFormed.isCoherent 3) hB hC3 hCB hπ hOld
    have hStart : RestrictLe (Q.geoTransform C π).N (idealPow (Q.geoTransform C π).ideal 3)
        ((powerMarked Q 3).geoTransform C π).ideal := h3.2.ge
    have hMiddle : RestrictLe (Q.geoTransform C π).N ((powerMarked Q 3).geoTransform C π).ideal
        (B.geoTransform C π).ideal := hMon
    rw [← hN'] at hStart hMiddle
    exact RestrictLe.trans hStart (RestrictLe.trans hMiddle hB'.le)


private theorem CarrierQuadraticReduction.pullback_ideal_inequalities
    {m r : ℕ} {X : CMfd.{0} m} {Y : CMfd.{0} r}
    {P Q : MarkedIdeal m X} (h : CarrierQuadraticReduction P Q)
    {φ : Y → X} (hφ : ContMDiff 𝓘(ℂ, ComplexModel r) 𝓘(ℂ, ComplexModel m) ∞ φ)
    {W : Set Y} (hW : ∀ x ∈ W, φ x ∈ P.N) :
    let J := GermIdeal.pullback (m := r) φ P.ideal
    let I := GermIdeal.pullback (m := r) φ Q.ideal
    RestrictLe W J (idealPow I 2) ∧ RestrictLe W (idealPow I 3) (J.mul I) := by
  obtain ⟨_, _, hP, hQ⟩ := h.domain
  have hJ := hP.isWellFormed.isCoherent
  have hI := hQ.isWellFormed.isCoherent
  dsimp only
  rw [← HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hφ hI,
    ← HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hφ hI,
    ← HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hφ hJ hI]
  exact ⟨HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe hφ hW
    (hol_of_isCoherent (isCoherent_idealPow hI 2)) h.inclusion,
    HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe hφ hW
      (hol_of_isCoherent (isCoherent_mul hJ hI)) h.product⟩

/-- The restricted quadratic relation survives admissible blowups, line
products and restrictions to open subsets on actual invariant-domain carriers. -/
theorem isLocStable_carrierQuadraticReduction : IsLocStable.{0} Kinds.wp
    (fun {m} {X} P Q => CarrierQuadraticReduction (m := m) (X := X) P Q) where
  E_eq h := h.boundary
  cosupp_eq h := h.cosupp_eq
  controlled := by
    intro m X P Q h C Y π hπ hCP
    exact h.controlled (Y := Y) C π hπ hCP
  projection := by
    intro _ m X P Q h
    obtain ⟨k, l, hP, hQ⟩ := h.domain
    have hφ := ProductComplexManifold.contMDiff_fst (n := m) (m := 1) (X := X) (Y := ComplexModel 1)
    obtain ⟨hIncl, hProd⟩ := h.pullback_ideal_inequalities (Y := projectionAmbient X)
      hφ (W := (projectionTest P).N) (fun _ hx => hx)
    refine ⟨?_, HironakaG11PresLineState.projectionTest_E_congr h.boundary, h.mark,
      ⟨k + 1, l + 1, projection_test_isInvDomain P hP, projection_test_isInvDomain Q hQ⟩, hIncl, hProd⟩
    change Prod.fst ⁻¹' P.N = Prod.fst ⁻¹' Q.N
    rw [h.carrier]
  restrict := by
    intro m X P Q h U
    obtain ⟨k, l, hP, hQ⟩ := h.domain
    let φ : U → X := Subtype.val
    have hφ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ φ := contMDiff_subtype_val
    obtain ⟨hIncl, hProd⟩ := h.pullback_ideal_inequalities (Y := CMfd.of (n := m) U)
      hφ (W := φ ⁻¹' P.N) (fun _ hx => hx)
    refine ⟨?_, ?_, h.mark,
      ⟨k, l, InvDomainTowerAlong.isInvDomain_pullback_val U hP,
        InvDomainTowerAlong.isInvDomain_pullback_val U hQ⟩, hIncl, hProd⟩
    · change φ ⁻¹' P.N = φ ⁻¹' Q.N
      rw [h.carrier]
    · change Q.E.map (φ ⁻¹' ·) = P.E.map (φ ⁻¹' ·)
      rw [h.boundary]

/-- The quadratic compression has the same local test class as its reduction
on a proper closed carrier, with the same entire ordered boundary. -/
theorem locWPEquiv_of_carrierQuadraticReduction {m : ℕ} {X : CMfd.{0} m}
    {P Q : MarkedIdeal m X} (h : CarrierQuadraticReduction P Q) : LocWPEquiv P Q :=
  LocEquiv.of_isLocStable isLocStable_carrierQuadraticReduction rfl h


open HironakaActualCoherentWeightedCoefficientMarked HironakaG1TwoVertexWeakClass

private theorem weighted_pair_isCarrierReduction {m k : ℕ} {X : CMfd.{0} m}
    (N : Set X) (E : List (Set X)) (c : Fin 2 → X → ℂ)
    (hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (c i))
    (hSource : IsInvDomain k (⟨N, E, finiteFunctionIdeal c, 2⟩ : MarkedIdeal m X)) :
    CarrierQuadraticReduction
      (⟨N, E, weightedFunctionIdeal (fun _ => 2) c, 4⟩ : MarkedIdeal m X)
      ⟨N, E, finiteFunctionIdeal c, 2⟩ := by
  let P : MarkedIdeal m X := ⟨N, E, weightedFunctionIdeal (fun _ => 2) c, 4⟩
  let Q : MarkedIdeal m X := ⟨N, E, finiteFunctionIdeal c, 2⟩
  have hJ : P.ideal.IsCoherent := isCoherent_weightedFunctionIdeal _ c hc
  have hI : Q.ideal.IsCoherent := hSource.isWellFormed.isCoherent
  have hRed := quadratic_reduction_of_two_functions c hc
  have hCos : P.cosupp = Q.cosupp := cosupport_eq_of_quadratic_reduction
    hSource.isWellFormed.isClosedSubmanifold_N hI hRed.1 hRed.2 2
  have hP : IsInvDomain k P :=
    HironakaG1ChosenCommonContactClassData.isInvDomain_of_sameCarrier_cosupp P Q hSource hJ
      (by decide : 1 ≤ 4) rfl rfl hCos
  refine ⟨rfl, rfl, rfl, ⟨k, k, hP, hSource⟩, restrictLe_of_le (isCoherent_idealPow hI 2) hRed.1, ?_⟩
  change RestrictLe N (idealPow (finiteFunctionIdeal c) 3)
    ((weightedFunctionIdeal (fun _ => 2) c).mul (finiteFunctionIdeal c))
  rw [hRed.2]
  exact restrictLe_refl (isCoherent_idealPow hI 3)

/-- Two actual weight-two holomorphic generator pairs with the same whole
source ideal have the same tests on its given proper invariant-domain carrier. -/
theorem locWPEquiv_two_weight_two_functions_on_carrier {m k : ℕ} {X : CMfd.{0} m}
    (N : Set X) (E : List (Set X)) (c d : Fin 2 → X → ℂ)
    (hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (c i))
    (hd : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (d i))
    (hSpan : finiteFunctionIdeal (n := m) c = finiteFunctionIdeal d)
    (hSource : IsInvDomain k (⟨N, E, finiteFunctionIdeal c, 2⟩ : MarkedIdeal m X)) :
    LocWPEquiv (X := X) ⟨N, E, weightedFunctionIdeal (fun _ => 2) c, 4⟩
      ⟨N, E, weightedFunctionIdeal (fun _ => 2) d, 4⟩ := by
  have hSource' : IsInvDomain k (⟨N, E, finiteFunctionIdeal d, 2⟩ : MarkedIdeal m X) := by
    rw [← hSpan]
    exact hSource
  have ha := locWPEquiv_of_carrierQuadraticReduction (weighted_pair_isCarrierReduction N E c hc hSource)
  have hb := locWPEquiv_of_carrierQuadraticReduction (weighted_pair_isCarrierReduction N E d hd hSource')
  rw [← hSpan] at hb
  exact ha.trans hb.symm

end

end Hironaka.HironakaG1CarrierQuadraticReduction
