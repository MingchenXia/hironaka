import Hironaka.Resolution.HironakaG8FlatFieldCalculus
import Hironaka.Resolution.HironakaG1LaterSelectedNormalTangent

/-! Normalized tangent fields in simultaneous coordinates of a selected carrier. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1NormalSimultaneousFields

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  DerivativeIdeal DerivativeIdealAlong DerivativeIdealAlongCoherent
  BlowupTowers MarkedIdeals BoundaryCount InvDomainMemberRestriction NormalCrossings BlowupFlatCoordinates HironakaG8FlatFieldCalculus

/-- A free direction in an actual straightening chart gives a normalized tangent
field whenever its derivative of the contact coordinate is nonzero at the point. -/
theorem exists_normalized_tangent_field_of_flatPartial {n : ℕ} {X : CMfd.{0} n}
    {x p : X} {K : Set X} {u : X → ℂ}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hp : p ∈ flatDomain Φ)
    (T : Finset (Fin n))
    (hK : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ K ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace T))
    (r : Fin n) (hr : r ∉ T) (hu : HolomorphicAt n u p)
    (hNormal : flatPartial Φ r u p ≠ 0) :
    ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField K e ξ p ∧ fieldDeriv e ξ u =ᶠ[𝓝 p] fun _ => 1 := by
  classical
  let a : Fin n → X → ℂ := fun j y => if j = r then (flatPartial Φ r u y)⁻¹ else 0
  have hPartial := holomorphicAt_flatPartial r hp hu
  have ha : ∀ j, HolomorphicAt n (a j) p := by
    intro j
    by_cases hj : j = r
    · simpa [a, hj] using BlowupFlatCoordinates.HolomorphicAt.inv hPartial hNormal
    · simpa [a, hj] using (holomorphicAt_const 0 : HolomorphicAt n (fun _ : X => 0) p)
  refine ⟨complexChartAt (n := n) x, combField Φ a,
    isTangentField_of_coordinate (e := complexChartAt (n := n) x) hSrc T hK hp hp.1
      (holomorphicAt_combField hp ha) ?_, ?_⟩
  · intro t ht
    have htr : t ≠ r := by rintro rfl; exact hr ht
    refine ⟨holomorphicAt_fieldDeriv hp.1 (holomorphicAt_combField hp ha)
      (holomorphicAt_flatCoord Φ t hp), ?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hp] with y hy _
    rw [fieldDeriv_combField_flatCoord hSrc a t hy]
    simp [a, htr]
  · have hn : ∀ᶠ y in 𝓝 p, flatPartial Φ r u y ≠ 0 :=
      hPartial.continuousAt.eventually (isOpen_ne.mem_nhds hNormal)
    filter_upwards [hn] with y hy
    rw [fieldDeriv_combField]
    simp [a, hy]

/-- On a simultaneous chart for the carrier and the selected members, their
coordinate index sets unite to give the literal carrier of member restriction. -/
theorem selected_members_normalized_tangent_fields {n : ℕ} {X : CMfd.{0} n}
    (B : MarkedIdeal n X) (I : Finset (Fin B.E.length)) {x : X} {u : X → ℂ}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (T : Finset (Fin n)) (S : Fin B.E.length → Finset (Fin n))
    (hN : ∀ y ∈ flatDomain Φ, y ∈ B.N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace T)
    (hE : ∀ i ∈ I, ∀ y ∈ flatDomain Φ, y ∈ B.E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace (S i))
    (r : Fin n) (hr : r ∉ T) (hrE : ∀ i ∈ I, r ∉ S i)
    (V : Set X) (hV : V ⊆ flatDomain Φ)
    (hu : ∀ p ∈ V, HolomorphicAt n u p) (hNormal : ∀ p ∈ V, flatPartial Φ r u p ≠ 0) :
    ∀ p ∈ V, ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField (memberRestrict B I).N e ξ p ∧ fieldDeriv e ξ u =ᶠ[𝓝 p] fun _ => 1 := by
  classical
  let R := T ∪ I.biUnion S
  have hrR : r ∉ R := by simpa [R, hr, Finset.mem_biUnion] using hrE
  intro p hp
  apply exists_normalized_tangent_field_of_flatPartial Φ hSrc (hV hp) R _ r hrR (hu p hp)
    (hNormal p hp)
  intro y hy hy'
  have hyF : y ∈ flatDomain Φ := ⟨hy, hy'⟩
  rw [memberRestrict_N]
  change (y ∈ B.N ∧ ∀ i ∈ I, y ∈ B.E.get i) ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace R
  rw [hN y hyF]
  constructor
  · rintro ⟨hT, hS⟩ t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact hT t ht
    · obtain ⟨i, hi, ht⟩ := Finset.mem_biUnion.mp ht
      exact (hE i hi y hyF).mp (hS i hi) t ht
  · intro h
    exact ⟨fun t ht => h t (Finset.mem_union_left _ ht),
      fun i hi => (hE i hi y hyF).mpr fun t ht =>
        h t (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, ht⟩))⟩

open RelativePrincipalizationSpan BlowupTowerTransforms MarkedIdeals.MarkedIdeal HomogenizedIdealAlong TangentDirectionAlong
  ResolutionInvariantSpec InvDomainTowerAlong StepOneValue StepOneValueMasked HironakaG8HomStable
  HironakaG1RecursiveMemberValueTransport HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1PositiveNormalPhase
  HironakaG1LaterSelectedNormalTangent HironakaActualRelativeNormalGeometry
  HironakaActualOpenZeroSectionDifferentials
open HomogenizedGlueingTower (strictAlong)

/-- A simultaneous chart with a free direction detecting the contact function
supplies the normalized fields for the actual later positive member cut. -/
theorem later_positive_member_normal_contact_of_simultaneous_chart {n k : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p x : Y) (V : Opens Y) (u : Y → ℂ)
    (Φ : LocalHolomorphicEquivAt (n := n + 1) (chartAt (ComplexModel (n + 1)) x x))
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel (n + 1)) x).target)
    (hV : (V : Set Y) ⊆ flatDomain Φ) :
    let P := properNormalMarked Q
    let B := geoTransformAlong (barMarked P) H
    let I := membersThrough B.E (origMembers P H) p
    let J := positiveMemberOn P H p V
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    ∀ (T : Finset (Fin (n + 1))) (S : Fin B.E.length → Finset (Fin (n + 1)))
      (r : Fin (n + 1)),
    (∀ y ∈ flatDomain Φ, y ∈ B.N ↔
      Φ.toFun (chartAt (ComplexModel (n + 1)) x y) ∈ coordSubspace T) →
    (∀ i ∈ I, ∀ y ∈ flatDomain Φ, y ∈ B.E.get i ↔
      Φ.toFun (chartAt (ComplexModel (n + 1)) x y) ∈ coordSubspace (S i)) →
    r ∉ T → (∀ i ∈ I, r ∉ S i) →
    (∀ y ∈ V, flatPartial Φ r u y ≠ 0) →
    IsTangentDirectionAlong B.N B.ideal B.d V u →
    B.N ∩ {z | u z = 0} ∩ V = D ∩ V →
    IsTangentDirectionAlong J.N J.ideal J.d univ (u ∘ (Subtype.val : V → Y)) ∧
      J.N ∩ {z : V | u z.val = 0} = J.N ∩ (Subtype.val : V → Y) ⁻¹' D := by
  intro P B I J D T S r hN hE hr hrE hNormal hu hZero
  refine later_positive_member_normal_contact_on_chart Q hQ H hH p V u hu hZero ?_
  refine selected_members_normalized_tangent_fields B I Φ hSrc T S hN hE r hr hrE V hV ?_ hNormal
  let X := CMfd.of (n := n + 1) (productOpen U)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hBar := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hTest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hB : IsInvDomain (k + 1) B := isInvDomain_geoTransformAlong hBar H hTest
  exact fun y hy => GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg)
    (B.d - 1) y u (hu.mem y hy)

end Hironaka.HironakaG1NormalSimultaneousFields
