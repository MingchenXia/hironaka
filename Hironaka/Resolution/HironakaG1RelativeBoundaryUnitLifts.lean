import Hironaka.Resolution.HironakaG1QuotientLabelledBoundaryFrame
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Relative whole labelled native boundary generators and ambient unit lifts

Equal principal ideals over a LOCAL ring have unit-related generators even
with zero divisors and zero images. Apply this to two genuine actual quotient
SNC readers, then lift the actual units through BOTH genuine ambient stalk
maps. No graph/common-ambient or quotient-regularity assertion is made.

Blueprint FIRST: `hironaka-g1-relative-boundary-unit-lifts.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1RelativeBoundaryUnitLifts

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings SimultaneousNormalCrossings BlowupFlatCoordinates HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualIntrinsicLabelledBoundaryIdeals HironakaG1QuotientLabelledBoundaryFrame

noncomputable section

/-- LOCALITY replaces domain cancellation. Both-zero generators are included. -/
theorem exists_unit_mul_of_span_eq {S : Type*} [CommRing S] [IsLocalRing S]
    (a b : S) (h : Ideal.span ({a} : Set S) = Ideal.span {b}) :
    ∃ u : Sˣ, b = (u : S) * a := by
  have hab : a ∣ b := Ideal.span_singleton_le_span_singleton.mp h.ge
  have hba : b ∣ a := Ideal.span_singleton_le_span_singleton.mp h.le
  obtain ⟨c, hc⟩ := hab
  obtain ⟨d, hd⟩ := hba
  by_cases hcu : IsUnit c
  · obtain ⟨u, rfl⟩ := hcu
    exact ⟨u, hc.trans (mul_comm _ _)⟩
  · have hcd : ¬IsUnit (c * d) := fun hunit => hcu (isUnit_of_mul_isUnit_left hunit)
    have hone : IsUnit (1 - c * d) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hcd
    have hmul : a = a * (c * d) := by
      calc
        a = b * d := hd
        _ = (a * c) * d := by rw [← hc]
        _ = a * (c * d) := mul_assoc _ _ _
    have hz : (1 - c * d) * a = 0 := by
      calc
        _ = a - a * (c * d) := by ring
        _ = 0 := sub_eq_zero.mpr hmul
    have ha : a = 0 := hone.mul_left_cancel (by simpa only [mul_zero] using hz)
    have hb : b = 0 := by rw [hc, ha, zero_mul]
    exact ⟨1, by simp only [Units.val_one, ha, hb, mul_zero]⟩

private abbrev NativeStalk {n : ℕ} {M : CMfd.{0} n} (C : Set M) (p : C) :=
  ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier

/-- Exact unit lift through the GENUINE whole actual inclusion stalk map. -/
theorem exists_actual_ambient_unit_lift {n : ℕ} {M : CMfd.{0} n}
    (C : Set M) (p : C) (u : (NativeStalk C p)ˣ) :
    ∃ v : (actualComplexStructureStalk (n := n) p.val)ˣ,
      Units.map ((actualSubspaceInclusion (n := n) C).stalkMap p).hom.toMonoidHom v = u := by
  exact IsLocalRing.surjective_units_map_of_local_ringHom
    ((actualSubspaceInclusion (n := n) C).stalkMap p).hom
    (actualSubspaceInclusionRingedHom_stalk_surjective (n := n) C p)
    ((actualSubspaceInclusion (n := n) C).prop p) u

/-- Genuine readers precede ALL paired original labels. Every ratio is a
native UNIT and lifts to units in BOTH actual ambient stalks, even for zero
Cartier images; active-label matching is DERIVED from the whole ideals. -/
theorem exists_relative_labelled_unit_lifts
    {n₁ n₂ : ℕ} {M₁ : CMfd.{0} n₁} {M₂ : CMfd.{0} n₂}
    (C₁ : Set M₁) (C₂ : Set M₂) (p₁ : C₁) (p₂ : C₂)
    {E₁ : List (Set M₁)} {E₂ : List (Set M₂)}
    (hE₁ : IsSNCDivisor n₁ E₁) (hE₂ : IsSNCDivisor n₂ E₂)
    (τ : Fin E₁.length ≃ Fin E₂.length)
    (e : NativeStalk C₂ p₂ ≃+* NativeStalk C₁ p₁)
    (hI : ∀ i : Fin E₁.length,
      Ideal.map e.toRingHom (actualLabelledBoundaryTraceIdeal C₂ E₂ (τ i) p₂) =
        actualLabelledBoundaryTraceIdeal C₁ E₁ i p₁) :
    ∃ (Φ₁ : LocalHolomorphicEquivAt (n := n₁) (chartAt (ComplexModel n₁) p₁.val p₁.val))
      (κ₁ : Fin E₁.length → Option (Fin n₁))
      (Φ₂ : LocalHolomorphicEquivAt (n := n₂) (chartAt (ComplexModel n₂) p₂.val p₂.val))
      (κ₂ : Fin E₂.length → Option (Fin n₂)),
      Φ₁.source ⊆ (chartAt (ComplexModel n₁) p₁.val).target ∧
      Φ₂.source ⊆ (chartAt (ComplexModel n₂) p₂.val).target ∧
      Φ₁.toFun (chartAt (ComplexModel n₁) p₁.val p₁.val) = 0 ∧
      Φ₂.toFun (chartAt (ComplexModel n₂) p₂.val p₂.val) = 0 ∧
      Set.InjOn κ₁ {i | p₁.val ∈ E₁.get i} ∧
      Set.InjOn κ₂ {i | p₂.val ∈ E₂.get i} ∧
      (∀ y ∈ flatDomain Φ₁, ∀ i : Fin E₁.length,
        y ∈ E₁.get i ↔ ∃ j, κ₁ i = some j ∧ flatCoord Φ₁ j y = 0) ∧
      (∀ y ∈ flatDomain Φ₂, ∀ i : Fin E₂.length,
        y ∈ E₂.get i ↔ ∃ j, κ₂ i = some j ∧ flatCoord Φ₂ j y = 0) ∧
      (∀ i : Fin E₁.length, p₁.val ∈ E₁.get i ↔ p₂.val ∈ E₂.get (τ i)) ∧
      ∀ i : Fin E₁.length,
        actualLabelledBoundaryTraceIdeal C₁ E₁ i p₁ =
            Ideal.span {quotientBoundaryGerm C₁ Φ₁ κ₁ p₁ (mem_flatDomain_self Φ₁) i} ∧
        actualLabelledBoundaryTraceIdeal C₂ E₂ (τ i) p₂ =
            Ideal.span {quotientBoundaryGerm C₂ Φ₂ κ₂ p₂ (mem_flatDomain_self Φ₂) (τ i)} ∧
        ∃ (u : (NativeStalk C₁ p₁)ˣ)
          (v₁ : (actualComplexStructureStalk (n := n₁) p₁.val)ˣ)
          (v₂ : (actualComplexStructureStalk (n := n₂) p₂.val)ˣ),
          e (quotientBoundaryGerm C₂ Φ₂ κ₂ p₂ (mem_flatDomain_self Φ₂) (τ i)) =
            (u : NativeStalk C₁ p₁) * quotientBoundaryGerm C₁ Φ₁ κ₁ p₁ (mem_flatDomain_self Φ₁) i ∧
          Units.map ((actualSubspaceInclusion (n := n₁) C₁).stalkMap p₁).hom.toMonoidHom v₁ = u ∧
          Units.map ((actualSubspaceInclusion (n := n₂) C₂).stalkMap p₂).hom.toMonoidHom v₂ =
            Units.map e.symm.toMonoidHom u := by
  let : IsLocalRing (NativeStalk C₁ p₁) := actualSubspaceStalk_isLocalRing (n := n₁) C₁ p₁
  obtain ⟨Φ₁, κ₁, hsrc₁, hzero₁, hinj₁, hmem₁, hall₁⟩ := exists_quotient_labelled_boundary_frame hE₁ p₁.val
  obtain ⟨Φ₂, κ₂, hsrc₂, hzero₂, hinj₂, hmem₂, hall₂⟩ := exists_quotient_labelled_boundary_frame hE₂ p₂.val
  let g₁ := fun i => quotientBoundaryGerm C₁ Φ₁ κ₁ p₁ (mem_flatDomain_self Φ₁) i
  let g₂ := fun i => quotientBoundaryGerm C₂ Φ₂ κ₂ p₂ (mem_flatDomain_self Φ₂) i
  have hspan : ∀ i, Ideal.span {g₁ i} = Ideal.span {e (g₂ (τ i))} := by
    intro i
    calc
      _ = actualLabelledBoundaryTraceIdeal C₁ E₁ i p₁ := (hall₁ C₁ p₁ (mem_flatDomain_self Φ₁) i).1.symm
      _ = Ideal.map e.toRingHom (actualLabelledBoundaryTraceIdeal C₂ E₂ (τ i) p₂) := (hI i).symm
      _ = _ := by
        rw [(hall₂ C₂ p₂ (mem_flatDomain_self Φ₂) (τ i)).1, Ideal.map_span, Set.image_singleton]
        rfl
  refine ⟨Φ₁, κ₁, Φ₂, κ₂, hsrc₁, hsrc₂, hzero₁, hzero₂, hinj₁, hinj₂, hmem₁, hmem₂, ?_, ?_⟩
  · intro i
    have hu : IsUnit (g₁ i) ↔ IsUnit (g₂ (τ i)) := by
      rw [← Ideal.span_singleton_eq_top, hspan i, Ideal.span_singleton_eq_top]
      exact MulEquiv.isUnit_map e
    have hoff := (hall₁ C₁ p₁ (mem_flatDomain_self Φ₁) i).2.1.symm.trans
      (hu.trans (hall₂ C₂ p₂ (mem_flatDomain_self Φ₂) (τ i)).2.1)
    simpa only [not_not] using not_congr hoff
  · intro i
    obtain ⟨u, hu⟩ := exists_unit_mul_of_span_eq (g₁ i) (e (g₂ (τ i))) (hspan i)
    obtain ⟨v₁, hv₁⟩ := exists_actual_ambient_unit_lift C₁ p₁ u
    obtain ⟨v₂, hv₂⟩ := exists_actual_ambient_unit_lift C₂ p₂ (Units.map e.symm.toMonoidHom u)
    exact ⟨(hall₁ C₁ p₁ (mem_flatDomain_self Φ₁) i).1,
      (hall₂ C₂ p₂ (mem_flatDomain_self Φ₂) (τ i)).1, u, v₁, v₂, hu, hv₁, hv₂⟩

end
end Hironaka.HironakaG1RelativeBoundaryUnitLifts
