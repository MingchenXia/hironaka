import Hironaka.Resolution.HironakaIntrinsicCarrierBoundaryCharts
import Hironaka.Resolution.HironakaG4OptionalDivisorMasks
import Hironaka.Resolution.HironakaG34CoordinateScaling

/-! Actual singleton divisor charts from prepared SNC and transversality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4PreparedDivisorChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates NormalCrossings
  HironakaIntrinsicCarrierBoundaryCharts HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks
  HironakaG34CoordinateScaling BlowupSNCTransform

variable {n : ℕ} {X : CMfd.{u} n}

/-- Prepared SNC and transversality supply an actual centered coordinate
chart with distinct optional singleton masks outside the carrier mask. -/
theorem exists_prepared_divisor_chart {N : Set X} {E : List (Set X)} {x : X}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) (hx : x ∈ N) :
    ∃ (S : Finset (Fin n)) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (m : Fin E.length → Option (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      DivisorMasksValid S m ∧
      (∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace S) ∧
      ∀ i y, y ∈ flatDomain Φ → (y ∈ E.get i ↔
        flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))) := by
  classical
  obtain ⟨a, ha, Φ, m, hsrc, hzero, hlt, hinj, hflat⟩ :=
    exists_actual_indexed_carrier_boundary_chart hE hT x hx
  let S : Finset (Fin n) := Finset.univ.filter fun j => a ≤ j.val
  have hsome_incident : ∀ i k, m i = some k → x ∈ E.get i := by
    intro i k hk
    apply ((hflat x (mem_flatDomain_self Φ)).2 i).mpr
    refine ⟨k, hk, ?_⟩
    change Φ.toFun (chartAt (ComplexModel n) x x) k = 0
    rw [hzero]
    rfl
  have hm : DivisorMasksValid S m := by
    constructor
    · intro i k hk hks
      have hklt := hlt i k hk
      have := (Finset.mem_filter.mp hks).2
      omega
    · intro i j k hi hj
      apply hinj (hsome_incident i k hi) (hsome_incident j k hj)
      exact hi.trans hj.symm
  refine ⟨S, Φ, m, hsrc, hzero, hm, ?_, ?_⟩
  · intro y hy
    rw [coordSubspace_eq_complexCoordinatePlane]
    exact (hflat y hy).1
  · intro i y hy
    cases hmi : m i with
    | none =>
      simp only [Option.map_none, optionalCoordLocus, mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨k, hk, _⟩ := ((hflat y hy).2 i).mp h
      simp [hmi] at hk
    | some k =>
      simp only [Option.map_some, optionalCoordLocus]
      rw [mem_coordSubspace_singleton]
      constructor
      · intro h
        obtain ⟨j, hj, hz⟩ := ((hflat y hy).2 i).mp h
        have hjk : j = k := Option.some.inj (hj.symm.trans hmi)
        subst j
        exact hz
      · intro hz
        exact ((hflat y hy).2 i).mpr ⟨k, hmi, hz⟩

/-- If the auxiliary divisor passes through the carrier point, its assigned
coordinate is present and outside the carrier mask. -/
theorem exists_prepared_auxiliary_chart {N H : Set X} {F : List (Set X)} {x : X}
    (hE : IsSNCDivisor n (H :: F)) (hT : IsTransverse n N (H :: F))
    (hx : x ∈ N) (hxH : x ∈ H) :
    ∃ (S : Finset (Fin n)) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (m : Fin (H :: F).length → Option (Fin n)) (t : Fin n),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      DivisorMasksValid S m ∧ m ⟨0, by simp⟩ = some t ∧ t ∉ S ∧
      (∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace S) ∧
      ∀ i y, y ∈ flatDomain Φ → (y ∈ (H :: F).get i ↔
        flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))) := by
  obtain ⟨S, Φ, m, hsrc, hzero, hm, hN, hD⟩ := exists_prepared_divisor_chart hE hT hx
  have hpres : ∃ t, m ⟨0, by simp⟩ = some t := by
    cases ht : m ⟨0, by simp⟩ with
    | none =>
      have h := (hD ⟨0, by simp⟩ x (mem_flatDomain_self Φ)).mp hxH
      have ht' : m (0 : Fin (H :: F).length) = none := ht
      simp [ht', optionalCoordLocus] at h
    | some t => exact ⟨t, rfl⟩
  obtain ⟨t, ht⟩ := hpres
  exact ⟨S, Φ, m, t, hsrc, hzero, hm, ht, hm.1 _ _ ht, hN, hD⟩

end
end Hironaka.HironakaG4PreparedDivisorChart
