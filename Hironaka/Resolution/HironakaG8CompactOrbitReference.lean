import Hironaka.Resolution.HironakaG8NativeHomogeneousRank

/-! Uniform compact orbit representatives for actual native charts. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CompactOrbitReference
open BlowupTowers HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8SpatialCofinalPrecedence
  HironakaG8PhysicalChartOccupiedLifts HironakaG8OccupiedSlotComparison

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*}

/-- Every event meeting a fixed compact transversal has a representative
in the same chart. The rank there preserves even full chart precedence. -/
theorem finite_serial_rank_of_compact_footprint_transversal
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCofinal : ∀ C : Set X, IsCompact C → ∃ i, C ⊆ (c i).U)
    (C : Set X) (hC : IsCompact C)
    (hMeet : ∀ a, (cofinalEventFootprint E a ∩ C).Nonempty) :
    Finite ι ∧ ∃ (i₀ : ℕ) (rank : ι → ℕ), Function.Injective rank ∧
      (∀ a, rank a < (c i₀).T.length) ∧
      (∀ ⦃a b⦄, E.Before a b → rank a < rank b) := by
  classical
  obtain ⟨i₀,hi₀⟩ := hCofinal C hC
  have hRep (a : ι) : ∃ p : {k // Occupied (c i₀).T k}, E.event i₀ p = a := by
    obtain ⟨x,hx,hxC⟩ := hMeet a
    obtain ⟨p,hp,_⟩ :=
      (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i₀ a (hi₀ hxC)).mp hx
    exact ⟨p,hp⟩
  obtain ⟨hFin,rank,hInj,hBound,hOrder⟩ :=
    HironakaG8CofinalFiniteRank.finite_serial_rank_of_reference_chart E i₀ hRep
  exact ⟨hFin,i₀,rank,hInj,hBound,fun {_ _} h => hOrder h⟩

/-- A local orbit representative in a common compact set suffices. Only
charts containing the compact set need the local symmetry and orbit data. -/
theorem finite_serial_rank_of_compact_orbit_representatives
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCofinal : ∀ C : Set X, IsCompact C → ∃ i, C ⊆ (c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (C : Set X) (hC : IsCompact C) (S : Set X)
    (hSub : ∀ i k, slotFootprint (c i).T k ⊆ (Subtype.val : (c i).U → X) ⁻¹' S)
    (hOrbit : ∀ i, C ⊆ (c i).U → ∀ x : (c i).U, x.val ∈ S →
      ∃ (y : (c i).U) (φ : (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).U),
        y.val ∈ C ∧ φ y = x ∧
          ∀ k, slotFootprint (c i).T k = φ ⁻¹' slotFootprint (c i).T k) :
    Finite ι ∧ ∃ (i₀ : ℕ) (rank : ι → ℕ), Function.Injective rank ∧
      (∀ a, rank a < (c i₀).T.length) ∧
      (∀ ⦃a b⦄, E.Before a b → rank a < rank b) := by
  apply finite_serial_rank_of_compact_footprint_transversal E cmp hMono hLift hCofinal C hC
  intro a
  obtain ⟨i,p,hp⟩ := hOccurs a
  obtain ⟨i₀,hi₀⟩ := hCofinal C hC
  let j := max i i₀
  let q := E.lift (le_max_left i i₀) p
  obtain ⟨x,hx⟩ := (slotFootprint_nonempty_iff (c j).T q.val).mpr q.property
  obtain ⟨y,φ,hy,hφ,hInvariant⟩ :=
    hOrbit j (hi₀.trans (hMono (le_max_right i i₀))) x (hSub j q.val hx)
  have hY : y ∈ slotFootprint (c j).T q.val := by
    rw [hInvariant q.val]
    change φ y ∈ slotFootprint (c j).T q.val
    rwa [hφ]
  exact ⟨y.val,⟨j,q,(E.lift_event (le_max_left i i₀) p).trans hp,⟨y,hY,rfl⟩⟩,hy⟩

end Hironaka.HironakaG8CompactOrbitReference
namespace Hironaka.HironakaG8CompactOrbitReference
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  HironakaG8LabelledNativeHistory HironakaG8NativeOccupiedFootprintSymmetry
  HironakaG8FirstFootprintOrder HironakaG8OccupiedSlotComparison HironakaEmbeddedAnalytic HironakaResolutionSpaceLocal
  HironakaG8IntrinsicSingularBlockSchedule HironakaAdmissibleSequence

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*} {W : Set X}

/-- A uniform compact set of representatives for the singular orbits
of the actual native chart actions forces finite serial rank. A finite
set of common representatives is a special case. -/
theorem finite_serial_rank_of_native_compact_orbits
    (hn : 0 < n) (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCofinal : ∀ C : Set X, IsCompact C → ∃ i, C ⊆ (c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (C : Set X) (hC : IsCompact C)
    (hNative : ∀ i, ∃ L, LabelledNativeTower n
      ((Subtype.val : (c i).U → X) ⁻¹' W) [] univ (c i).T L)
    (hOrbit : ∀ i, C ⊆ (c i).U → ∀ x : (c i).U,
      x.val ∈ singularSet (n := n) W →
      ∃ (y : (c i).U) (φ : (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).U),
        y.val ∈ C ∧ φ y = x ∧
          φ ⁻¹' ((Subtype.val : (c i).U → X) ⁻¹' W) =
            ((Subtype.val : (c i).U → X) ⁻¹' W)) :
    Finite ι ∧ ∃ (i₀ : ℕ) (rank : ι → ℕ), Function.Injective rank ∧
      (∀ a, rank a < (c i₀).T.length) ∧
      (∀ ⦃a b⦄, E.Before a b → rank a < rank b) := by
  refine finite_serial_rank_of_compact_orbit_representatives E cmp hMono hLift hCofinal hOccurs
    C hC (singularSet (n := n) W) ?_ ?_
  · intro i k
    obtain ⟨L,hT⟩ := hNative i
    have hSubset := HironakaG8NativeHomogeneousRank.native_footprint_subset_original_singular hT k
    simpa only [singularSet_preimage_val] using hSubset
  · intro i hi x hx
    obtain ⟨L,hT⟩ := hNative i
    obtain ⟨y,φ,hy,hφ,hW⟩ := hOrbit i hi x hx
    exact ⟨y,φ,hy,hφ,native_empty_boundary_footprint_symmetry hn hT φ hW⟩

end Hironaka.HironakaG8CompactOrbitReference
