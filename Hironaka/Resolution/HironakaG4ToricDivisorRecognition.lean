import Hironaka.Resolution.HironakaG4LocalToricDivisors
import Hironaka.Resolution.HironakaSharpNormalCrossingsOpenLocus
import Hironaka.Resolution.HironakaG4RebaseFlatChart

/-! The strong toric state gives pointwise adapted coordinates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricDivisorRecognition
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates NormalCrossings
  HironakaG34CoordinateScaling HironakaG4OptionalBoundaryTransform
  HironakaG4OptionalDivisorMasks HironakaG4LocalToricDivisors HironakaSharpNormalCrossingsOpenLocus
  HironakaG4RebaseFlatChart

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {A : Type*} {F : Filter A}

/-- Optional singleton equations give adapted coordinates at the chart point. -/
theorem adapted_of_optional_chart {ι : Type*} {N : Set X} {D : ι → Set X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (S : Finset (Fin n)) (m : ι → Option (Fin n))
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace S)
    (hD : ∀ i y, y ∈ flatDomain Φ → (y ∈ D i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (hm : DivisorMasksValid S m) :
    ∃ (S : Finset (Fin n)) (R : ι → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option ι => o.elim N D)
        (fun o => o.elim S R) x ∧
      (∀ i, x ∈ D i → (R i).card = 1 ∧ Disjoint (R i) S) ∧
      Set.InjOn R {i | x ∈ D i} := by
  classical
  let R : ι → Finset (Fin n) := fun i => ((m i).map fun k => ({k} : Finset (Fin n))).getD ∅
  have hSome : ∀ i, x ∈ D i → ∃ k, m i = some k := by
    intro i hi
    cases hmi : m i with
    | none =>
      have := (hD i x (mem_flatDomain_self Φ)).mp hi
      simp [hmi, optionalCoordLocus] at this
    | some k => exact ⟨k, rfl⟩
  have hR : ∀ i k, m i = some k → R i = {k} := by
    intro i k hk
    simp [R, hk]
  refine ⟨S, R, ?_, ?_, ?_⟩
  · apply coordinateFamilyAt_of_flattening Φ
    · intro o ho y hy hyΦ
      cases o with
      | none => exact hN y ⟨hy, hyΦ⟩
      | some i =>
        obtain ⟨k, hk⟩ := hSome i ho
        change y ∈ D i ↔ flatMap Φ y ∈ coordSubspace (R i)
        simpa [hR i k hk, hk, optionalCoordLocus] using hD i y ⟨hy, hyΦ⟩
    · exact mem_complexChartAt_source x
    · exact Φ.center_mem_source
    · intro i hi
      exact hi
  · intro i hi
    obtain ⟨k, hk⟩ := hSome i hi
    rw [hR i k hk]
    refine ⟨Finset.card_singleton k, ?_⟩
    exact Finset.disjoint_singleton_left.mpr (hm.1 i k hk)
  · intro i hi j hj hij
    obtain ⟨k, hk⟩ := hSome i hi
    obtain ⟨l, hl⟩ := hSome j hj
    have hkl : k = l := by simpa [hR i k hk, hR j l hl] using hij
    subst l
    exact hm.2 i j k hk hl


/-- Throughout the actual chart of a strong toric state, every point has
adapted carrier and boundary coordinates, including points off the carrier. -/
theorem eventually_adapted_of_localToricDivisorState {ι : Type*} {N : Set X} {D : ι → Set X}
    {x : X} {act : A → X → X}
    (hstate : LocalToricDivisorState (n := n) F N D x act) :
    ∀ᶠ y in 𝓝 x, ∃ (S : Finset (Fin n)) (R : ι → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option ι => o.elim N D)
        (fun o => o.elim S R) y ∧
      (∀ i, y ∈ D i → (R i).card = 1 ∧ Disjoint (R i) S) ∧
      Set.InjOn R {i | y ∈ D i} := by
  obtain ⟨S, μ, sec, Φ, m, hΦsrc, hN, hD, hm, hμ, hdiag, hsec, hrealize⟩ := hstate
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
  obtain ⟨Ψ, hΨsrc, hcoords⟩ := exists_rebased_flat_chart Φ hy
  apply adapted_of_optional_chart Ψ S m ?_ ?_ hm
  · intro z hz
    rw [(hcoords z hz).2]
    exact hN z (hcoords z hz).1
  · intro i z hz
    rw [(hcoords z hz).2]
    exact hD i z (hcoords z hz).1

/-- A strong state gives a genuine open neighborhood on which the tracked
closed list is SNC and transverse to the carrier. -/
theorem exists_snc_transverse_neighborhood {N : Set X} {E : List (Set X)}
    {x : X} {act : A → X → X} (hE : ∀ H ∈ E, IsClosed H)
    (hstate : LocalToricDivisorState (n := n) F N (fun i : Fin E.length => E.get i) x act) :
    ∃ U : Opens X, x ∈ U ∧
      IsSNCDivisor n (E.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' N) (E.map ((Subtype.val : U → X) ⁻¹' ·)) := by
  classical
  obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.mp
    (eventually_adapted_of_localToricDivisorState hstate)
  let U : Opens X := ⟨O, hOopen⟩
  have hget (i : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length) :
      (E.map ((Subtype.val : U → X) ⁻¹' ·)).get i =
        (Subtype.val : U → X) ⁻¹' (E.get ⟨i.val, by simpa using i.isLt⟩) := by
    simp [List.get_eq_getElem]
  refine ⟨U, hxO, ?_, ?_⟩
  · constructor
    · intro H hH
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      exact (hE H₀ hH₀).preimage continuous_subtype_val
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
end Hironaka.HironakaG4ToricDivisorRecognition
