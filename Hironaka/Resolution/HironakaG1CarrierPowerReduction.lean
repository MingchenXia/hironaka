import Hironaka.Resolution.HironakaG8LocalStable
import Hironaka.Resolution.HironakaActualHistoricalNativeStageStep
import Hironaka.Resolution.HironakaG1UniformVertexReduction
import Hironaka.Resolution.HironakaActualHistoricalInitialAffineDictionary
import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon
import Hironaka.Resolution.HironakaG8LocalContactStage
import Hironaka.Resolution.HironakaG8LocalPower
import Hironaka.Resolution.HironakaActualOriginalPowerTransform
import Hironaka.Resolution.HironakaG11PresLineState

/-! Power reduction modulo restriction to the actual carrier. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1CarrierPowerReduction

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers IdealOrderArithmetic
  HironakaActualPowerBoundaryExponents BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong RestrictedIdealWeight RestrictLeCalculus
  ResolutionInvariantSpec HironakaActualOriginalPowerTransform HironakaG8LocalHistory
  HironakaG8LocalStable HironakaActualProjectionTestRecord GermIdealPullbackCalculus
open scoped ProductComplexManifold

/-- The two inequalities needed for a power reduction on the true source
carrier. Both remain meaningful after controlled transforms. -/
structure CarrierPowerReduction (e r : ℕ) {m : ℕ} {X : CMfd.{0} m} (P Q : MarkedIdeal m X) : Prop where
  exponent_pos : 1 ≤ e
  offset_pos : 1 ≤ r
  carrier : P.N = Q.N
  boundary : Q.E = P.E
  mark : P.d = e * Q.d
  domain : ∃ k l : ℕ, IsInvDomain k P ∧ IsInvDomain l Q
  inclusion : RestrictLe P.N P.ideal (idealPow Q.ideal e)
  product : RestrictLe P.N (idealPow Q.ideal (e + r)) (P.ideal.mul (idealPow Q.ideal r))

/-- The normalized cosupport proof only needs inequalities on the carrier. -/
theorem CarrierPowerReduction.cosupp_eq {m e r : ℕ} {X : CMfd.{0} m}
    {P Q : MarkedIdeal m X} (h : CarrierPowerReduction e r P Q) : P.cosupp = Q.cosupp := by
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
    have hProd : x ∈ cosupport m N (J.mul (idealPow I r)) (e * d + r * j) :=
      inter_cosupport_subset_cosupport_mul _ _ ⟨hx, by simpa only [Nat.mul_comm] using cosupport_subset_cosupport_idealPow j r hjIn⟩
    have hCube := cosupport_subset_of_restrictLe h.product (e * d + r * j) hProd
    have hSharp : x ∈ cosupport m N (idealPow I (e+r)) ((e+r) * j + 1) :=
      cosupport_anti (by
        have hdj := Nat.mul_le_mul_left e (Nat.succ_le_of_lt hjd)
        rw [Nat.mul_succ] at hdj
        rw [Nat.add_mul]
        have hp := h.exponent_pos
        omega) hCube
    rw [cosupport_idealPow_mul_succ_eq_along (X := X) hN hI (by have hp := h.exponent_pos; omega : 1 ≤ e + r) j] at hSharp
    exact hs (hj ▸ hSharp)
  · intro hx
    have hPow := cosupport_subset_cosupport_idealPow d e hx
    have hTwo : x ∈ cosupport m N (idealPow I e) (e * d) := by
      simpa only [Nat.mul_comm] using hPow
    exact cosupport_subset_of_restrictLe h.inclusion _ hTwo

private theorem CarrierPowerReduction.controlled {m e r : ℕ} {X Y : CMfd.{0} m}
    {P Q : MarkedIdeal m X} (h : CarrierPowerReduction e r P Q) (C : Set X)
    (π : Y → X) (hπ : IsBlowupAlong m C π) (hCP : P.IsAdmissibleCentre C) :
    CarrierPowerReduction e r (P.geoTransform C π) (Q.geoTransform C π) := by
  obtain ⟨k, l, hP, hQ⟩ := h.domain
  have hCQ : Q.IsAdmissibleCentre C :=
    (HironakaG8MixedEquiv.isAdmissibleCentre_congr h.boundary.symm h.cosupp_eq C).mp hCP
  have hT : IsGeoTestTower P (.step .refl C π hπ) := ⟨trivial, hCP⟩
  have hU : IsGeoTestTower Q (.step .refl C π hπ) := ⟨trivial, hCQ⟩
  have hP' := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP (.step .refl C π hπ) hT
  have hQ' := InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ (.step .refl C π hπ) hU
  have hAdd : 1 ≤ e + r := by have hp := h.exponent_pos; omega
  have hE := original_power_transform Q hQ e h.exponent_pos (.step .refl C π hπ) hU
  have hR := original_power_transform Q hQ r h.offset_pos (.step .refl C π hπ) hU
  have hER := original_power_transform Q hQ (e + r) hAdd (.step .refl C π hπ) hU
  have hCE : (powerMarked Q e).IsAdmissibleCentre C := hE.1.2
  have hCR : (powerMarked Q r).IsAdmissibleCentre C := hR.1.2
  have hCER : (powerMarked Q (e + r)).IsAdmissibleCentre C := hER.1.2
  let B := MarkedIdealOperationsTransform.MarkedIdeal.mul P (powerMarked Q r)
  have hCB : B.IsAdmissibleCentre C :=
    MarkedIdealOperationsTransform.MarkedIdeal.IsAdmissibleCentre.mul (𝔪₂ := powerMarked Q r) h.carrier hCP hCR
  have hB : B.ideal.IsCoherent := isCoherent_mul hP.isWellFormed.isCoherent
    (isCoherent_idealPow hQ.isWellFormed.isCoherent r)
  have hm := h.mark
  have hPair : IsSubmanifoldPair P (powerMarked Q r) :=
    ⟨h.carrier, h.boundary.symm, hP.isWellFormed.isClosedSubmanifold_N,
      hP.isWellFormed.isCoherent, isCoherent_idealPow hQ.isWellFormed.isCoherent r⟩
  have hB' := geoTransform_mul_restrictEquiv hPair hπ hCP hCR
  have hN' : (P.geoTransform C π).N = (Q.geoTransform C π).N := by
    rw [geoTransform_N, geoTransform_N, h.carrier]
  refine ⟨h.exponent_pos, h.offset_pos, hN', by simp only [geoTransform_E, h.boundary],
    h.mark, ⟨k, l, hP', hQ'⟩, ?_, ?_⟩
  · have hd : P.d = (powerMarked Q e).d := by
      change P.d = Q.d * e
      rw [hm, Nat.mul_comm]
    have hMon := HomogenizedIdealAlongTower.restrictLe_geoTransform_of_restrictLe
      (𝔫₁ := P) (𝔫₂ := powerMarked Q e)
      hP.isWellFormed.isClosedSubmanifold_N h.carrier hd hP.isWellFormed.isCoherent
      (isCoherent_idealPow hQ.isWellFormed.isCoherent e) hCP hCE hπ h.inclusion
    have hNext : RestrictLe (Q.geoTransform C π).N
        ((powerMarked Q e).geoTransform C π).ideal (idealPow (Q.geoTransform C π).ideal e) := hE.2.le
    rw [← hN'] at hNext
    exact RestrictLe.trans hMon hNext
  · have hd : (powerMarked Q (e + r)).d = B.d := by
      change Q.d * (e + r) = P.d + Q.d * r
      rw [hm, Nat.mul_add, Nat.mul_comm Q.d e]
    have hOld : RestrictLe (powerMarked Q (e + r)).N (powerMarked Q (e + r)).ideal B.ideal := by
      change RestrictLe Q.N (idealPow Q.ideal (e + r)) (P.ideal.mul (idealPow Q.ideal r))
      rw [← h.carrier]
      exact h.product
    have hMon := HomogenizedIdealAlongTower.restrictLe_geoTransform_of_restrictLe
      (𝔫₁ := powerMarked Q (e + r)) (𝔫₂ := B)
      hQ.isWellFormed.isClosedSubmanifold_N h.carrier.symm hd
      (isCoherent_idealPow hQ.isWellFormed.isCoherent _) hB hCER hCB hπ hOld
    have hStart : RestrictLe (Q.geoTransform C π).N (idealPow (Q.geoTransform C π).ideal (e + r))
        ((powerMarked Q (e + r)).geoTransform C π).ideal := hER.2.ge
    have hMiddle : RestrictLe (Q.geoTransform C π).N ((powerMarked Q (e + r)).geoTransform C π).ideal
        (B.geoTransform C π).ideal := hMon
    have hFactor : RestrictLe (Q.geoTransform C π).N ((powerMarked Q r).geoTransform C π).ideal
        (idealPow (Q.geoTransform C π).ideal r) := hR.2.le
    rw [← hN'] at hStart hMiddle hFactor
    have hPC : (P.geoTransform C π).ideal.IsCoherent := hP'.isWellFormed.isCoherent
    have hQC : (Q.geoTransform C π).ideal.IsCoherent := hQ'.isWellFormed.isCoherent
    have hEnd := restrictLe_mul (hol_of_isCoherent hPC) (hol_of_isCoherent (isCoherent_idealPow hQC r))
      (restrictLe_refl hPC) hFactor
    exact RestrictLe.trans hStart (RestrictLe.trans hMiddle (RestrictLe.trans hB'.le hEnd))


private theorem CarrierPowerReduction.pullback_ideal_inequalities
    {m s e r : ℕ} {X : CMfd.{0} m} {Y : CMfd.{0} s}
    {P Q : MarkedIdeal m X} (h : CarrierPowerReduction e r P Q)
    {φ : Y → X} (hφ : ContMDiff 𝓘(ℂ, ComplexModel s) 𝓘(ℂ, ComplexModel m) ∞ φ)
    {W : Set Y} (hW : ∀ x ∈ W, φ x ∈ P.N) :
    let J := GermIdeal.pullback (m := s) φ P.ideal
    let I := GermIdeal.pullback (m := s) φ Q.ideal
    RestrictLe W J (idealPow I e) ∧ RestrictLe W (idealPow I (e + r)) (J.mul (idealPow I r)) := by
  obtain ⟨_, _, hP, hQ⟩ := h.domain
  have hJ := hP.isWellFormed.isCoherent
  have hI := hQ.isWellFormed.isCoherent
  dsimp only
  rw [← HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hφ hI,
    ← HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hφ hI,
    ← HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hφ hI,
    ← HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hφ hJ (isCoherent_idealPow hI r)]
  exact ⟨HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe hφ hW
    (hol_of_isCoherent (isCoherent_idealPow hI e)) h.inclusion,
    HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe hφ hW
      (hol_of_isCoherent (isCoherent_mul hJ (isCoherent_idealPow hI r))) h.product⟩

/-- The restricted power reduction relation survives admissible blowups, line
products and restrictions to open subsets on actual invariant-domain carriers. -/
theorem isLocStable_carrierPowerReduction (e r : ℕ) : IsLocStable.{0} Kinds.wp
    (fun {m} {X} P Q => CarrierPowerReduction e r (m := m) (X := X) P Q) where
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
    refine ⟨h.exponent_pos, h.offset_pos, ?_, HironakaG11PresLineState.projectionTest_E_congr h.boundary, h.mark,
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
    refine ⟨h.exponent_pos, h.offset_pos, ?_, ?_, h.mark,
      ⟨k, l, InvDomainTowerAlong.isInvDomain_pullback_val U hP,
        InvDomainTowerAlong.isInvDomain_pullback_val U hQ⟩, hIncl, hProd⟩
    · change φ ⁻¹' P.N = φ ⁻¹' Q.N
      rw [h.carrier]
    · change Q.E.map (φ ⁻¹' ·) = P.E.map (φ ⁻¹' ·)
      rw [h.boundary]

/-- The power compression has the same local test class as its reduction
on a proper closed carrier, with the same entire ordered boundary. -/
theorem locWPEquiv_of_carrierPowerReduction {m e r : ℕ} {X : CMfd.{0} m}
    {P Q : MarkedIdeal m X} (h : CarrierPowerReduction e r P Q) : LocWPEquiv P Q :=
  LocEquiv.of_isLocStable (isLocStable_carrierPowerReduction e r) rfl h



/-- The common test class also follows when the offset is zero. In that case
the two restricted inclusions already identify the source power. -/
theorem locWPEquiv_of_restricted_power_reduction {m : ℕ} {X : CMfd.{0} m}
    {P Q : MarkedIdeal m X} {k l e r : ℕ} (he : 1 ≤ e)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : P.N = Q.N) (hE : Q.E = P.E) (hMark : P.d = e * Q.d)
    (hIncl : RestrictLe P.N P.ideal (idealPow Q.ideal e))
    (hProduct : RestrictLe P.N (idealPow Q.ideal (e + r)) (P.ideal.mul (idealPow Q.ideal r))) :
    LocWPEquiv P Q := by
  by_cases hr : r = 0
  · subst r
    rw [Nat.add_zero, idealPow_zero, mul_unitIdeal hP.isWellFormed.isCoherent] at hProduct
    have hp : RestrictEquiv P (powerMarked Q e) := by
      refine ⟨hN, hE.symm, ?_, hIncl, hProduct⟩
      change P.d = Q.d * e
      rw [hMark, Nat.mul_comm]
    have hClass := HironakaG8LocalContactStage.locEquiv_of_restrictEquiv_closed (κ := Kinds.wp)
      rfl hp hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent
      (isCoherent_idealPow hQ.isWellFormed.isCoherent e)
    exact hClass.trans (HironakaG8LocalPower.locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ he).symm
  · exact locWPEquiv_of_carrierPowerReduction
      ⟨he, Nat.one_le_iff_ne_zero.mpr hr, hN, hE, hMark, ⟨k, l, hP, hQ⟩, hIncl, hProduct⟩


open scoped Pointwise
open HironakaSmoothSubmersionGermIdealColon HironakaActualHistoricalInitialAffineDictionary
  IdealWeightProducts InvertibleIdealQuotient

/-- A coherent ideal product becomes the product of adapted holomorphic
germ ideals in any fixed source chart. -/
theorem adaptedIdeal_mul_exact {m : ℕ} {X : CMfd.{0} m}
    (I J : GermIdeal m X) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel m) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel m) x x) = 0) :
    adaptedIdeal (I.mul J) x Φ h0 = adaptedIdeal I x Φ h0 * adaptedIdeal J x Φ h0 := by
  obtain ⟨U, hU, hxU, a, c, hc, hGenC⟩ := hI x
  obtain ⟨V, hV, hxV, b, d, hd, hGenD⟩ := hJ x
  have hCh (i : Fin a) : HolomorphicAt m (c i) x :=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hc i) hxU
  have hDh (j : Fin b) : HolomorphicAt m (d j) x :=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hV (hd j) hxV
  have hCDh (k : Fin (a * b)) : HolomorphicAt m (mulFamily c d k) x :=
    (hCh (finProdFinEquiv.symm k).1).mul (hDh (finProdFinEquiv.symm k).2)
  rw [actual_native_adapted_ideal_of_whole_generation I x Φ h0 c hCh (hGenC x hxU),
    actual_native_adapted_ideal_of_whole_generation J x Φ h0 d hDh (hGenD x hxV)]
  have hGenCD := mem_mul_iff_isInSpanAt_mulFamily (hU.inter hV)
    (fun i => (hc i).mono inter_subset_left) (fun j => (hd j).mono inter_subset_right)
    (fun y hy => hGenC y hy.1) (fun y hy => hGenD y hy.2) (y := x) ⟨hxU, hxV⟩
  rw [actual_native_adapted_ideal_of_whole_generation (I.mul J) x Φ h0 _ hCDh hGenCD,
    Ideal.span_mul_span']
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    apply Set.mem_mul.mpr
    let ij := finProdFinEquiv.symm k
    refine ⟨_, ⟨ij.1, rfl⟩, _, ⟨ij.2, rfl⟩, ?_⟩
    exact (adaptedGerm_mul x Φ h0 _ _ (hDh ij.2) (hCh ij.1)).symm
  · intro hz
    obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    have hEq {u v : X → ℂ} (hu : HolomorphicAt m u x) (hv : HolomorphicAt m v x)
        (he : u = v) : adaptedGerm x Φ h0 u hu = adaptedGerm x Φ h0 v hv := by
      subst v
      rfl
    exact (hEq _ ((hCh i).mul (hDh j)) (funext (mulFamily_apply c d i j))).trans
      (adaptedGerm_mul x Φ h0 _ _ (hDh j) (hCh i))

/-- An original coherent whole power becomes the corresponding adapted
holomorphic germ power, in each fixed chart. -/
theorem adaptedIdeal_power_exact {m : ℕ} {X : CMfd.{0} m}
    (I : GermIdeal m X) (hI : I.IsCoherent)
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel m) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel m) x x) = 0) (e : ℕ) :
    adaptedIdeal (idealPow I e) x Φ h0 = adaptedIdeal I x Φ h0 ^ e := by
  induction e with
  | zero =>
    rw [idealPow_zero, pow_zero]
    rw [Ideal.one_eq_top, Ideal.eq_top_iff_one]
    have hOne := (mem_adaptedIdeal_iff (unitIdeal m X) isCoherent_unitIdeal x Φ h0
      (fun _ => 1) (holomorphicAt_const 1)).mpr (mem_unitIdeal_iff.mpr (isInSpanAt_self ⟨0, rfl⟩ (holomorphicAt_const 1)))
    exact hOne
  | succ e ih =>
    rw [idealPow_succ, adaptedIdeal_mul_exact _ _ (isCoherent_idealPow hI e) hI x Φ h0, ih, pow_succ]


open HironakaActualHistoricalNativeStageStep HironakaActualFixedInheritedSelector
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualWeightedCoefficientCompression HironakaActualNativeSourceChartComposition
  HironakaG1UniformVertexReduction

/-- A genuine equal-weight native point presentation determines the power
reduction inequalities for the original stalk, before restriction. -/
theorem uniformNative_stalk_powerReduction {m k : ℕ} {X : CMfd.{0} m}
    {V : Finset (Fin m →₀ ℕ)} [Nonempty V]
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (words : Fin k → CoordinateWord m)
    (w : ℕ) (hw : 0 < w) (hUniform : ∀ v : V, normalExponentDegree v.val = w)
    (W : Set X) (hW : (vanishingIdeal (n := m) W).IsCoherent)
    (P : MarkedIdeal m X) (hP : P.ideal.IsCoherent) (x : X)
    (hAt : ActualHistoricalNativePointPresentation S a words W P x) :
    let I := vanishingIdeal (n := m) W
    let e := weightedCommonMark (fun _ : V => w) / w
    let r := Fintype.card V * (e - 1)
    (∀ f, P.ideal.mem x f → (idealPow I e).mem x f) ∧
      (∀ f, (idealPow I (e + r)).mem x f → (P.ideal.mul (idealPow I r)).mem x f) := by
  intro I e r
  obtain ⟨Φ, hΦsrc, hΦ0, Γ, _, hSpan, hComp⟩ := hAt
  have hI : I.IsCoherent := hW
  have hIAdapt : adaptedIdeal I x Φ hΦ0 = Ideal.span (range Γ) := by
    have hRange : range (fun i => Γ (a i)) = range Γ := a.surjective.range_comp Γ
    rw [hRange] at hSpan
    exact ((actual_original_translated_flattened_vanishing_origin_eq_adapted x Φ hΦsrc hΦ0 W hW).symm).trans
      hSpan.symm
  have hUniformFun : (fun v : V => normalExponentDegree v.val) = fun _ => w := funext hUniform
  rw [hUniformFun] at hComp
  have hAlg := uniformCompression_mul_span_pow w Γ hw
  change weightedCompression (fun _ : V => w) Γ * (Ideal.span (range Γ)) ^ r =
    (Ideal.span (range Γ)) ^ (e + r) at hAlg
  have hLe : adaptedIdeal P.ideal x Φ hΦ0 ≤ adaptedIdeal (idealPow I e) x Φ hΦ0 := by
    rw [hComp, adaptedIdeal_power_exact I hI x Φ hΦ0, hIAdapt]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : Γ i ∈ Ideal.span (range Γ) := Ideal.subset_span ⟨i, rfl⟩
    exact Ideal.pow_mem_pow hi e
  have hEq : adaptedIdeal (P.ideal.mul (idealPow I r)) x Φ hΦ0 =
      adaptedIdeal (idealPow I (e + r)) x Φ hΦ0 := by
    rw [adaptedIdeal_mul_exact _ _ hP (isCoherent_idealPow hI r) x Φ hΦ0,
      adaptedIdeal_power_exact I hI x Φ hΦ0, adaptedIdeal_power_exact I hI x Φ hΦ0,
      hIAdapt, hComp]
    exact hAlg
  constructor
  · intro f hf
    have hHol := GermIdeal.IsCoherent.holomorphicAt_mem hP hf
    exact (mem_adaptedIdeal_iff _ (isCoherent_idealPow hI e) x Φ hΦ0 f hHol).mp
      (hLe ((mem_adaptedIdeal_iff _ hP x Φ hΦ0 f hHol).mpr hf))
  · intro f hf
    have hHol := GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_idealPow hI (e + r)) hf
    exact (mem_adaptedIdeal_iff _ (isCoherent_mul hP (isCoherent_idealPow hI r))
      x Φ hΦ0 f hHol).mp (hEq.symm ▸
        (mem_adaptedIdeal_iff _ (isCoherent_idealPow hI (e + r)) x Φ hΦ0 f hHol).mpr hf)

/-- Actual point presentations of uniform native weight supply the two
carrier-relative inclusions at the literal compression mark. -/
theorem restricted_powerReduction_of_uniformNative
    {m k l j : ℕ} {X : CMfd.{0} m} {V : Finset (Fin m →₀ ℕ)} [Nonempty V]
    (S : ActualFixedInheritedSelector V) (a : Fin j ≃ V) (words : Fin j → CoordinateWord m)
    (w : ℕ) (hw : 0 < w) (hUniform : ∀ v : V, normalExponentDegree v.val = w)
    (W : Set X) (P : MarkedIdeal m X) (hP : IsInvDomain k P)
    (hd : P.d = weightedCommonMark (fun _ : V => w))
    (hBase : IsInvDomain l (⟨P.N, P.E, vanishingIdeal (n := m) W, w⟩ : MarkedIdeal m X))
    (hAt : ∀ x ∈ P.N, ActualHistoricalNativePointPresentation S a words W P x) :
    let I := vanishingIdeal (n := m) W
    ∃ e r : ℕ, 1 ≤ e ∧ P.d = e * w ∧
      RestrictLe P.N P.ideal (idealPow I e) ∧
      RestrictLe P.N (idealPow I (e + r)) (P.ideal.mul (idealPow I r)) := by
  let I := vanishingIdeal (n := m) W
  let e := weightedCommonMark (fun _ : V => w) / w
  let r := Fintype.card V * (e - 1)
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have he : 1 ≤ e := compressionExponent_pos (fun _ : V => w) (fun _ => hw) v
  have hGamma : P.d = e * w := by
    rw [hd, Nat.mul_comm]
    exact (weight_mul_compressionExponent (fun _ : V => w) v).symm
  have hI : I.IsCoherent := hBase.isWellFormed.isCoherent
  have hPcoh := hP.isWellFormed.isCoherent
  have hStep (x : X) (hx : x ∈ P.N) :=
    uniformNative_stalk_powerReduction S a words w hw hUniform W hI P hPcoh x (hAt x hx)
  refine ⟨e, r, he, hGamma, ?_, ?_⟩
  · intro x hx f hf
    have hm := (hStep x hx).1 f hf
    exact IsInSpanAt.restrict (isInSpanAt_self hm
      (GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_idealPow hI e) hm))
  · intro x hx f hf
    have hm := (hStep x hx).2 f hf
    exact IsInSpanAt.restrict (isInSpanAt_self hm
      (GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_mul hPcoh (isCoherent_idealPow hI r)) hm))

/-- Uniform native weight and actual point presentations along the entire
carrier give the full weak test class of the uncompressed source. -/
theorem locWPEquiv_uniformNative_of_carrier_presentations
    {m k l j : ℕ} {X : CMfd.{0} m} {V : Finset (Fin m →₀ ℕ)} [Nonempty V]
    (S : ActualFixedInheritedSelector V) (a : Fin j ≃ V) (words : Fin j → CoordinateWord m)
    (w : ℕ) (hw : 0 < w) (hUniform : ∀ v : V, normalExponentDegree v.val = w)
    (W : Set X) (P : MarkedIdeal m X) (hP : IsInvDomain k P)
    (hd : P.d = weightedCommonMark (fun _ : V => w))
    (hBase : IsInvDomain l (⟨P.N, P.E, vanishingIdeal (n := m) W, w⟩ : MarkedIdeal m X))
    (hAt : ∀ x ∈ P.N, ActualHistoricalNativePointPresentation S a words W P x) :
    LocWPEquiv (X := X) P ⟨P.N, P.E, vanishingIdeal (n := m) W, w⟩ := by
  obtain ⟨e, r, he, hMark, hIncl, hProd⟩ :=
    restricted_powerReduction_of_uniformNative S a words w hw hUniform W P hP hd hBase hAt
  exact locWPEquiv_of_restricted_power_reduction (e := e) (r := r) he hP hBase
    rfl rfl hMark hIncl hProd


/-- Two native records may use different vertices, selectors, adapted charts
and true common marks. A shared positive generator weight and original
analytic source give the same local tests on their common carrier. -/
theorem locWPEquiv_of_independent_uniformNative_presentations
    {m k l d j j' : ℕ} {X : CMfd.{0} m}
    {V V' : Finset (Fin m →₀ ℕ)} [Nonempty V] [Nonempty V']
    (S : ActualFixedInheritedSelector V) (a : Fin j ≃ V) (words : Fin j → CoordinateWord m)
    (S' : ActualFixedInheritedSelector V') (a' : Fin j' ≃ V') (words' : Fin j' → CoordinateWord m)
    (w : ℕ) (hw : 0 < w) (hUniform : ∀ v : V, normalExponentDegree v.val = w)
    (hUniform' : ∀ v : V', normalExponentDegree v.val = w)
    (W : Set X) (P Q : MarkedIdeal m X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : P.N = Q.N) (hE : P.E = Q.E)
    (hd : P.d = weightedCommonMark (fun _ : V => w))
    (hd' : Q.d = weightedCommonMark (fun _ : V' => w))
    (hBase : IsInvDomain d (⟨P.N, P.E, vanishingIdeal (n := m) W, w⟩ : MarkedIdeal m X))
    (hAt : ∀ x ∈ P.N, ActualHistoricalNativePointPresentation S a words W P x)
    (hAt' : ∀ x ∈ Q.N, ActualHistoricalNativePointPresentation S' a' words' W Q x) :
    LocWPEquiv P Q := by
  have hBase' : IsInvDomain d (⟨Q.N, Q.E, vanishingIdeal (n := m) W, w⟩ : MarkedIdeal m X) := by
    rw [← hN, ← hE]
    exact hBase
  have hL := locWPEquiv_uniformNative_of_carrier_presentations S a words w hw hUniform W P hP hd hBase hAt
  have hR := locWPEquiv_uniformNative_of_carrier_presentations
    S' a' words' w hw hUniform' W Q hQ hd' hBase' hAt'
  rw [← hN, ← hE] at hR
  exact hL.trans hR.symm

end

end Hironaka.HironakaG1CarrierPowerReduction
