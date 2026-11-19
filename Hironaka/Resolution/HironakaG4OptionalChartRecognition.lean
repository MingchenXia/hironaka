import Hironaka.Resolution.HironakaG4ToricDivisorRecognition

/-! Direct recognition of SNC and transversality from optional coordinates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OptionalChartRecognition
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates NormalCrossings
  HironakaG34CoordinateScaling HironakaG4OptionalBoundaryTransform
  HironakaG4OptionalDivisorMasks HironakaSharpNormalCrossingsOpenLocus
  HironakaG4RebaseFlatChart HironakaG4ToricDivisorRecognition

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Optional coordinate equations yield a genuine SNC and transverse open neighborhood. -/
theorem exists_snc_transverse_of_optional_chart {N : Set X} {E : List (Set X)} {x : X}
    (hEclosed : ∀ H ∈ E, IsClosed H)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (S : Finset (Fin n)) (m : Fin E.length → Option (Fin n))
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace S)
    (hD : ∀ i y, y ∈ flatDomain Φ → (y ∈ E.get i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (hm : DivisorMasksValid S m) :
    ∃ U : Opens X, x ∈ U ∧
      IsSNCDivisor n (E.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' N) (E.map ((Subtype.val : U → X) ⁻¹' ·)) := by
  classical
  have hadapt : ∀ᶠ y in 𝓝 x, ∃ (S : Finset (Fin n)) (R : Fin E.length → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option (Fin E.length) => o.elim N (fun i => E.get i))
        (fun o => o.elim S R) y ∧
      (∀ i, y ∈ E.get i → (R i).card = 1 ∧ Disjoint (R i) S) ∧
      Set.InjOn R {i | y ∈ E.get i} := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
    obtain ⟨Ψ, hΨsrc, hcoords⟩ := exists_rebased_flat_chart Φ hy
    apply adapted_of_optional_chart Ψ S m ?_ ?_ hm
    · intro z hz
      rw [(hcoords z hz).2]
      exact hN z (hcoords z hz).1
    · intro i z hz
      rw [(hcoords z hz).2]
      exact hD i z (hcoords z hz).1
  obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.mp hadapt
  let U : Opens X := ⟨O, hOopen⟩
  have hget (i : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length) :
      (E.map ((Subtype.val : U → X) ⁻¹' ·)).get i =
        (Subtype.val : U → X) ⁻¹' (E.get ⟨i.val, by simpa using i.isLt⟩) := by
    simp [List.get_eq_getElem]
  refine ⟨U, hxO, ?_, ?_⟩
  · constructor
    · intro H hH
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      exact (hEclosed H₀ hH₀).preimage continuous_subtype_val
    · intro y
      obtain ⟨S, R, hcoord, hcard, hinj⟩ := hOsub y.property
      let R' : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length → Finset (Fin n) :=
        fun i => R ⟨i.val, by simpa using i.isLt⟩
      refine ⟨R', ?_, ?_, ?_⟩
      · simp_rw [hget]
        apply NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff.mpr
        obtain ⟨Ψ, hsrc, hzero, hflat⟩ := hcoord
        refine ⟨Ψ, hsrc, hzero, ?_⟩
        intro i hi z hz hzΨ
        exact hflat (some ⟨i.val, by simpa using i.isLt⟩) hi hz hzΨ
      · intro i hi
        rw [hget] at hi
        exact (hcard ⟨i.val, by simpa using i.isLt⟩ hi).1
      · intro i hi j hj hij
        change y ∈ (E.map ((Subtype.val : U → X) ⁻¹' ·)).get i at hi
        change y ∈ (E.map ((Subtype.val : U → X) ⁻¹' ·)).get j at hj
        rw [hget] at hi hj
        apply Fin.ext
        have h := hinj (show (y : X) ∈ E.get ⟨i.val, by simpa using i.isLt⟩ from hi)
          (show (y : X) ∈ E.get ⟨j.val, by simpa using j.isLt⟩ from hj) hij
        exact congrArg (fun q : Fin E.length => q.val) h
  · intro y hy
    obtain ⟨S, R, hcoord, hcard, hinj⟩ := hOsub y.property
    let R' : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length → Finset (Fin n) :=
      fun i => R ⟨i.val, by simpa using i.isLt⟩
    refine ⟨S, R', ?_, ?_⟩
    · have hA : (fun o : Option (Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length) =>
          o.elim ((Subtype.val : U → X) ⁻¹' N) (fun i => (E.map ((Subtype.val : U → X) ⁻¹' ·)).get i)) =
          (fun o => (Subtype.val : U → X) ⁻¹' (o.elim N (fun i => E.get ⟨i.val, by simpa using i.isLt⟩))) := by
        funext o
        cases o with
        | none => rfl
        | some i => exact hget i
      rw [hA]
      apply NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff.mpr
      obtain ⟨Ψ, hsrc, hzero, hflat⟩ := hcoord
      refine ⟨Ψ, hsrc, hzero, ?_⟩
      intro i hi z hz hzΨ
      cases i with
      | none => exact hflat none hi hz hzΨ
      | some i => exact hflat (some ⟨i.val, by simpa using i.isLt⟩) hi hz hzΨ
    · intro i hi
      rw [hget] at hi
      exact hcard ⟨i.val, by simpa using i.isLt⟩ hi


end
end Hironaka.HironakaG4OptionalChartRecognition
