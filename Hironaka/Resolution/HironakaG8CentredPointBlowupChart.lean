import Hironaka.Resolution.HironakaActualInheritedVerticalPointChart

set_option autoImplicit false
open Set
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CentredPointBlowupChart

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  NormalCrossings BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  HironakaActualInheritedVerticalPointChart PointSupportedIdealPrincipalization GiraudAlong

/-- A chosen centred atlas chart induces a chart of the actual point blowup
in any chosen pivot direction, with exact monomial projection. -/
theorem exists_centred_point_blowup_chart {n : ℕ} {X : CMfd.{0} (n+1)}
    (e : OpenPartialHomeomorph X (ComplexModel (n+1)))
    (he : e ∈ atlas (ComplexModel (n+1)) X) (x : X) (hx : x ∈ e.source)
    (h0 : e x = 0) (j : Fin (n+1)) :
    let C : Set X := {x}
    let _ : Fact (IsClosedSubmanifold (n+1) C) := ⟨(singleton_geometry_and_coherence x).1⟩
    let Y : CMfd.{0} (n+1) := CMfd.of (BlowupSpace (n+1) C)
    let π : Y → X := blowupProj (n+1) C
    ∃ (f : OpenPartialHomeomorph Y (ComplexModel (n+1))) (z : Y),
      f ∈ atlas (ComplexModel (n+1)) Y ∧ z ∈ f.source ∧ f z = 0 ∧ π z = x ∧
      IsBlowupAlong (n+1) C π ∧
      ∀ y ∈ f.source, π y ∈ e.source ∧ e (π y) = monomial 0 j (f y) := by
  dsimp only
  let C : Set X := {x}
  let _ : Fact (IsClosedSubmanifold (n+1) C) := ⟨(singleton_geometry_and_coherence x).1⟩
  let Y : CMfd.{0} (n+1) := CMfd.of (BlowupSpace (n+1) C)
  let π : Y → X := blowupProj (n+1) C
  obtain ⟨Θ,hΘs,hΘ0,hΘdom⟩ :=
    exists_inherited_coordinates e he x hx h0 e.source e.open_source hx subset_rfl
  have hFlat : ∀ {y : X}, y ∈ (chartAt (ComplexModel (n+1)) x).source →
      chartAt (ComplexModel (n+1)) x y ∈ Θ.source →
      (y ∈ C ↔ Θ.toFun (chartAt (ComplexModel (n+1)) x y) ∈ complexCoordinatePlane (n+1) 0) := by
    intro y hy hyΘ
    obtain ⟨hye,hEq⟩ := hΘdom y ⟨hy,hyΘ⟩
    change y ∈ C ↔ flatMap Θ y ∈ _
    rw [hEq]
    constructor
    · intro hyx i hi
      rw [mem_singleton_iff.mp hyx,h0]
      rfl
    · intro hz
      have hEz : e y = 0 := by
        ext i
        exact hz i (Nat.zero_le _)
      exact mem_singleton_iff.mpr (e.injOn hye hx (hEz.trans h0.symm))
  let c : FlatChart (n+1) C := {
    y₀ := x
    k := 0
    Φ := Θ
    hsrc := hΘs
    hflat := hFlat
    j := j
    hj := Nat.zero_le _ }
  have hCi : interior C = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro y hy
    have hyx : y = x := mem_singleton_iff.mp (interior_subset hy)
    subst y
    have hopen : IsOpen C := by
      apply isOpen_iff_mem_nhds.mpr
      intro y hyx
      rw [mem_singleton_iff.mp hyx]
      exact mem_interior_iff_mem_nhds.mp hy
    have him := e.isOpen_image_of_subset_source hopen (singleton_subset_iff.mpr hx)
    rw [show C = {x} from rfl,image_singleton] at him
    exact not_isOpen_singleton (e x) him
  have hc0 : (0 : ComplexModel (n+1)) ∈ c.target := by
    change monomial 0 j 0 ∈ Θ.target
    have hm : monomial 0 j (0 : ComplexModel (n+1)) = 0 := by
      ext i
      simp [monomial_apply]
    rw [hm,←hΘ0]
    exact Θ.mapsTo_toFun Θ.center_mem_source
  let z := c.invFun 0
  have hz : z ∈ c.source := c.map_target hc0
  refine ⟨atlasHomeo c.toPartialEquiv (Or.inl ⟨c,rfl⟩), z,
    atlasHomeo_mem_atlas _ _, hz, c.right_inv hc0, ?_,
    isBlowupAlong_blowupProj (n := n+1) (C := C) hCi, ?_⟩
  · change z.base = x
    rw [c.base_invFun hc0]
    exact mem_singleton_iff.mp ((c.pt_mem_iff hc0).mpr rfl)
  · intro y hy
    obtain ⟨hye,hEq⟩ := hΘdom (π y) hy.1
    exact ⟨hye,hEq.symm.trans (c.monomial_toFun hy).symm⟩

end Hironaka.HironakaG8CentredPointBlowupChart
