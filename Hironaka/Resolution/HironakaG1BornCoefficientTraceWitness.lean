import Hironaka.Resolution.HironakaG1AdvancingBornControlledTrace
import Hironaka.Resolution.HironakaG1AdvancingSupportPowerGap

/-! Finite local coefficient witnesses on the actual born divisor trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1BornCoefficientTraceWitness

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong StepOneValue TangentDirectionAlong CoefficientIdealRestriction ContactStageKept
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal InvDomainRebase
  HironakaG8LocalHistory HironakaG8GapNormalizedExponent HironakaG8DomainExponents
  HironakaG8LocalRestrictEquiv HironakaG1AdvancingBornControlledTrace
  RelativePrincipalizationSpan DivisorExponentAlong GermIdealOrder
open HomogenizedGlueingTower (strictAlong)

/-- Exact carrier-restricted initial coefficient inheritance supplies
initial normalized exponents automatically. At an offending born slot,
it suffices to exhibit local refreshed generators that restrict to
the actual controlled source coefficients on that trace. -/
theorem advancing_supported_canonical_of_finite_born_coefficient_witnesses {n k l : ℕ}
    (hn : 0 < n) {X Y : CMfd.{0} n} (K P : MarkedIdeal n X)
    (hK : IsInvDomain k K) (hP : IsInvDomain l P) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = P.N)
    (hExact : RestrictEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) P)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked K) H) (O : Opens Y) :
    let A := CMfd.of (n := n) O
    let C := withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})
    let D := contactMarkedKept K u H O
    let C' := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong C H)
    let P' := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong P H)
    (∀ F ∈ D.E, ∀ z ∈ D.cosupp, z ∈ F →
      (¬ ∃ i : Fin P.E.length, F = (Subtype.val : O → Y) ⁻¹' strictAlong H (P.E.get i)) →
      divExpAlong n D.N D.ideal F z = 0 → 0 < divExpAlong n P'.N P'.ideal F z →
      ∀ᶠ w in 𝓝 z, ∃ (r : ℕ) (s : Fin r → A → ℂ),
        (∀ g, D.ideal.mem w g → IsInSpanOnAt (n := n) (D.N ∩ F) (· ∈ range s) w g) ∧
        (∀ i, IsInSpanOnAt (n := n) (D.N ∩ F) (C'.ideal.mem w) w (s i))) →
    (∀ F ∈ D.E, ∀ z ∈ D.cosupp, z ∈ F →
      P'.d * divExpAlong n D.N D.ideal F z = D.d * divExpAlong n P'.N P'.ideal F z) ∧
    ∀ {Z : CMfd.{0} n} (T : BlowupTower A Z),
      IsCanonical D ((invFamily hn l).inv D) T ↔ IsCanonical P' ((invFamily hn l).inv P') T := by
  intro A C D C' P' hWitness
  have hCoh : C.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N
  have hBack : RestrictEquiv P C := ⟨hExact.N_eq.symm,hExact.E_eq.symm,hExact.d_eq.symm,
    hExact.N_eq ▸ hExact.ge,hExact.N_eq ▸ hExact.le⟩
  have hC := isInvDomain_of_restrictEquiv hP hBack hCoh
  have hL := locWPEquiv_of_restrictEquiv hC hP hExact
  have hGapC : HasCosupportGap C := by
    intro z _ hz
    change z ∈ cosupport n C.N (coeffMarkedAlong K).ideal (coeffMarkedAlong K).d
    rw [← HironakaActualCoefficientDivisorExponentGap.coefficient_restriction_cosupport_gap K
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d C.N (fun _ hx => hx.1)]
    exact hz
  have hGapP := HironakaG1AdvancingSupportPowerGap.cosupport_gap_of_restrictEquiv hBack hGapC
  have hInitial : ∀ F ∈ C.E, ∀ z ∈ C.cosupp, z ∈ F →
      P.d * divExpAlong n C.N C.ideal F z = C.d * divExpAlong n P.N P.ideal F z := by
    intro F _ z _ _
    rw [hExact.d_eq,divExpAlong_eq_of_restrictEquiv hExact]
  apply advancing_supported_canonical_of_born_controlled_trace hn K P hK hP u hu hTrace
    H hH O hC hL hGapP hInitial
  intro F hF z hz hzF hNew hD0 hPPos
  filter_upwards [hWitness F hF z hz hzF hNew hD0 hPPos] with w hw g hg
  obtain ⟨r,s,hGen,hS⟩ := hw
  refine IsInSpanOnAt.trans ?_ (hGen g hg)
  rintro _ ⟨i,rfl⟩
  exact hS i

#print axioms advancing_supported_canonical_of_finite_born_coefficient_witnesses

end Hironaka.HironakaG1BornCoefficientTraceWitness
