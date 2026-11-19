import Hironaka.Resolution.HironakaG1PositiveNormalPhase
import Hironaka.Invariant.ContactEquivalenceStage

/-! Current normal contact and its transfer to an actual positive selected cut. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterSelectedNormalTangent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism NormalCrossings ResolutionInvariantSpec HomogenizedIdealAlong
  IdealWeightPowers DerivativeIdealAlong DerivativeIdealAlongTransform TangentDirectionAlong
  CoefficientIdeal GiraudAlong CompanionReduction InvertibleIdealQuotient
  RelativePrincipalizationSpan InvDomainMemberRestriction InvDomainRebase
  ContactEquivalenceAlong ContactStageInvDomain
  StepOneValue StepOneValueMasked HironakaG8HomStable
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative
  HironakaG1PositiveNormalPhase HironakaG1RecursiveMemberValueTransport
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
open HomogenizedGlueingTower (strictAlong)

private theorem successive_powers_at_tangent_field {n : ℕ} {Y : CMfd.{0} n}
    {N : Set Y} {J : GermIdeal n Y} {u : Y → ℂ} {x : Y}
    (e : ComplexChart n Y) (ξ : Fin n → Y → ℂ) (hξ : IsTangentField N e ξ x)
    (hu : HolomorphicAt n u x) (hOne : fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1) :
    ∀ j r, J.mem x (fun z => u z ^ (r + j)) →
      (iterDerivIdealAlong N J j).mem x (fun z => u z ^ r)
  | 0, _, h => h
  | j + 1, r, h => by
    have hExp : r + 1 + j = r + (j + 1) := by omega
    have hPrev := successive_powers_at_tangent_field e ξ hξ hu hOne j (r + 1) (by rwa [hExp])
    have hGen : DerivGenAlong N (iterDerivIdealAlong N J j) x
        (fieldDeriv e ξ (fun z => u z ^ (r + 1))) :=
      Or.inr (Or.inr ⟨e, ξ, _, hξ, hPrev, rfl⟩)
    have hPow := fieldDeriv_pow (ξ := ξ) hξ.mem_source hu r
    have hCoef : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    have hEq : (fun z => ((r : ℂ) + 1)⁻¹ *
        fieldDeriv e ξ (fun w => u w ^ (r + 1)) z) =ᶠ[𝓝 x] fun z => u z ^ r := by
      filter_upwards [hPow, hOne] with z hz hzOne
      rw [hz, hzOne, mul_one, ← mul_assoc, inv_mul_cancel₀ hCoef, one_mul]
    exact isInSpanAt_of_eq_mul hGen (holomorphicAt_pow_of hu r)
      (holomorphicAt_const (((r : ℂ) + 1)⁻¹)) hEq.symm

/-- A later upper test stage has an actual local tangent for the current bar
record. Its zero locus on the current carrier is the literal strict
transform of the original normal section in that carrier. -/
theorem later_normal_bar_contact {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H)
    {x : Y} (hx : x ∈ (geoTransformAlong (barMarked (properNormalMarked Q)) H).N) :
    let P := properNormalMarked Q
    let B := geoTransformAlong (barMarked P) H
    ∃ (V : Opens Y) (u : Y → ℂ), x ∈ V ∧
      IsTangentDirectionAlong B.N B.ideal B.d V u ∧
      B.N ∩ {z | u z = 0} ∩ V =
        strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0}) ∩ V := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let A := barMarked (X := X) P
  have hP := properNormalMarked_isInvDomain Q hQ
  have hA := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hATest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  obtain ⟨V, hxV, _, u, hu, hZero⟩ :=
    ContactEquivalenceStage.exists_isTangentDirectionAlong_stage
      (X := X) A hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent hA.one_le_d
      (⊤ : Opens X) (bar_normal_tangent Q hQ) H hATest hx trivial
  exact ⟨V, u, hxV, hu, hZero⟩

/-- The top relative derivative of the current record contributes a power at
the full coefficient mark. A field in a simultaneous chart tangent to the
selected carrier can differentiate that power back to the coordinate. -/
theorem selected_tangent_of_current_contact {n : ℕ} {X : CMfd.{0} n}
    (B : MarkedIdeal n X) (hB : B.IsWellFormed) (hd : 0 < B.d)
    (I : Finset (Fin B.E.length)) (V : Opens X) (u : X → ℂ)
    (hu : IsTangentDirectionAlong B.N B.ideal B.d V u)
    (hField : ∀ x ∈ V, ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField (memberRestrict B I).N e ξ x ∧
        fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1) :
    let K := memberRestrict B I
    IsTangentDirectionAlong K.N K.ideal K.d V u := by
  intro K
  have hK : 0 < K.d := one_le_memberRestrict_d B I
  refine ⟨V.isOpen, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, ξ, hξ, hOne⟩ := hField x hx
    have hMem := hu.mem x hx
    have hHol : HolomorphicAt n u x := holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg) (B.d - 1) x u hMem
    let i := B.d - 1
    let a := sumExp (fun j => B.d - j) B.d i
    have hi : i < B.d := by dsimp [i]; omega
    have hOneMark : B.d - i = 1 := by dsimp [i]; omega
    have hCoeff : K.d = a := by
      change (Finset.range B.d).prod (fun j => B.d - j) = a
      have h := mul_sumExp (fun j => B.d - j) hi
      simpa only [hOneMark, one_mul] using h.symm
    have hPower : K.ideal.mem x (fun z => u z ^ K.d) := by
      change IsInSpanAt (n := n) (fun f => ∃ j, j < B.d ∧
        (idealPow (iterDerivIdealAlong B.N B.ideal j) (sumExp (fun m => B.d - m) B.d j)).mem x f) x _
      rw [hCoeff]
      exact isInSpanAt_self ⟨i, hi, HomogenizedIdeal.pow_mem_idealPow hMem hHol a⟩
        (holomorphicAt_pow_of hHol a)
    have hSum : 1 + (K.d - 1) = K.d := by omega
    simpa only [pow_one] using successive_powers_at_tangent_field e ξ hξ hHol hOne
      (K.d - 1) 1 (by simpa only [hSum] using hPower)
  · intro x hx _
    obtain ⟨e, ξ, hξ, hOne⟩ := hField x hx
    exact ⟨e, ξ, hξ, by rw [hOne.self_of_nhds]; exact one_ne_zero⟩

/-- At the actual cut of a tested upper history, the current normal coordinate
is a tangent direction on the selected chart once its simultaneous fields
preserve the literal selected member intersection. Its zero locus is the
current strict normal section restricted to that selected carrier. -/
theorem later_positive_member_normal_contact_on_chart {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y) (V : Opens Y) (u : Y → ℂ) :
    let P := properNormalMarked Q
    let B := geoTransformAlong (barMarked P) H
    let I := membersThrough B.E (origMembers P H) p
    let K := memberRestrict B I
    let J := positiveMemberOn P H p V
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    IsTangentDirectionAlong B.N B.ideal B.d V u →
    B.N ∩ {z | u z = 0} ∩ V = D ∩ V →
    (∀ x ∈ V, ∃ (e : ComplexChart (n + 1) Y) (ξ : Fin (n + 1) → Y → ℂ),
      IsTangentField K.N e ξ x ∧ fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1) →
    IsTangentDirectionAlong J.N J.ideal J.d univ (u ∘ (Subtype.val : V → Y)) ∧
      J.N ∩ {z : V | u z.val = 0} = J.N ∩ (Subtype.val : V → Y) ⁻¹' D := by
  intro P B I K J D hu hZero hField
  let X := CMfd.of (n := n + 1) (productOpen U)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hBar := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hTest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hB : IsInvDomain (k + 1) B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hBar H hTest
  have hTang := selected_tangent_of_current_contact B hB.isWellFormed hB.one_le_d I V u hu hField
  have hK : K.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hB.isWellFormed I
  refine ⟨isTangentDirectionAlong_pullback_val V
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK.isCoherent hg) hTang, ?_⟩
  have hKN : K.N ⊆ B.N := fun _ hz => hz.1
  ext z
  constructor
  · rintro ⟨hz, hu0⟩
    have h := Set.ext_iff.mp hZero z.val
    exact ⟨hz, (h.mp ⟨⟨hKN hz, hu0⟩, z.property⟩).1⟩
  · rintro ⟨hz, hD⟩
    have h := Set.ext_iff.mp hZero z.val
    exact ⟨hz, (h.mpr ⟨hD, z.property⟩).1.2⟩

end Hironaka.HironakaG1LaterSelectedNormalTangent
