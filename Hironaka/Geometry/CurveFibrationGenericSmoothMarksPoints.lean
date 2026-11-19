import Hironaka.Geometry.ProjectiveSecantSmoothPoint
import Hironaka.Geometry.CurveBoundaryBasic
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Genuine distinct smooth finite separable points on the SAME original curve

ANY specified original nonempty smooth open is retained. The actual fibration
consumer may use the pullback of its ORIGINAL ambient smooth locus; no equality
with the intrinsic fibre smooth locus is assumed here.
-/
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
namespace Hironaka.Geometry.CurveFibrationGenericSmoothMarks
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- Positive ORIGINAL dimension forces the SAME original integral generic point to be nonclosed. -/
theorem genericPoint_not_closed [IsIntegral C] (hdim : 0 < topologicalKrullDim C) :
    ¬ IsClosed ({genericPoint C} : Set C) := by
  intro h
  have hall : (Set.univ : Set C) ⊆ {genericPoint C} := by
    rw [← (genericPoint_spec C).def, h.closure_eq]
  let : Subsingleton C := ⟨fun x y =>
    (Set.mem_singleton_iff.mp (hall (Set.mem_univ x))).trans
      (Set.mem_singleton_iff.mp (hall (Set.mem_univ y))).symm⟩
  let : T1Space C := inferInstance
  exact (not_le_of_gt hdim) (CurveBoundary.topologicalKrullDim_le_zero_of_t1 C)

/-- The actual ORIGINAL finite-extension point has a closed image, derived from original properness and whole coefficient identity. -/
theorem finite_point_isClosed (p : C ⟶ Spec (.of k)) [IsProper p]
    {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L]
    (q : Spec (.of L) ⟶ C)
    (hq : q ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    IsClosed ({q (⊥ : PrimeSpectrum L)} : Set C) := by
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : IsProper (q ≫ p) := by rw [hq]; infer_instance
  let : IsProper q := IsProper.of_comp q p
  have hrange : Set.range q = {q (⊥ : PrimeSpectrum L)} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg q (Subsingleton.elim y _))
    · rintro rfl
      exact ⟨_, rfl⟩
  exact hrange ▸ q.isClosedMap.isClosed_range

/-- Actual single-point DATA internally produced from the ORIGINAL nonempty smooth open. -/
structure Point (p : C ⟶ Spec (.of k)) (U : C.Opens) where
  extension : IntermediateField k (SeparableClosure k)
  finite : FiniteDimensional k extension
  separable : Algebra.IsSeparable k extension
  map : Spec (.of extension) ⟶ C
  over : map ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k extension))
  mem_open : map (⊥ : PrimeSpectrum extension) ∈ U

/-- The actual ORIGINAL underlying point of the actual finite separable point map. -/
def point {p : C ⟶ Spec (.of k)} {U : C.Opens} (z : Point p U) : C :=
  z.map (⊥ : PrimeSpectrum z.extension)

/-- Actual ORIGINAL point closedness uses only the internally retained finite field and coefficient triangle. -/
theorem point_isClosed {p : C ⟶ Spec (.of k)} [IsProper p] {U : C.Opens} (z : Point p U) :
    IsClosed ({point z} : Set C) := by
  let := z.finite
  exact finite_point_isClosed p z.map z.over

/-- The existing native smooth-point producer internally supplies actual finite separable point DATA in the SAME original open. -/
theorem exists_point (p : C ⟶ Spec (.of k)) (U : C.Opens) (hU : (U : Set C).Nonempty)
    [Smooth (U.ι ≫ p)] : Nonempty (Point p U) := by
  obtain ⟨L, hfin, hsep, q, hq, hm⟩ :=
    ProjectiveSecant.exists_finite_separable_point_in_smooth_open k p U hU
  exact ⟨⟨L, hfin, hsep, q, hq, hm⟩⟩

/-- Actual positive-dimensional original geometry chooses a new smooth finite separable point outside any actual closed subset missing its original generic point. -/
theorem exists_point_avoiding_closed [IsIntegral C]
    (p : C ⟶ Spec (.of k)) (U : C.Opens) (hU : (U : Set C).Nonempty)
    [Smooth (U.ι ≫ p)] (Z : Set C) (hZ : IsClosed Z) (hη : genericPoint C ∉ Z) :
    ∃ z : Point p U, point z ∉ Z := by
  let V : C.Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  have hηU : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hV : (V : Set C).Nonempty := ⟨genericPoint C, hηU, hη⟩
  let : Smooth (V.ι ≫ p) := by
    have heq : V.ι ≫ p = C.homOfLE (show V ≤ U from inf_le_left) ≫ (U.ι ≫ p) := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [heq]
    infer_instance
  obtain ⟨z⟩ := exists_point p V hV
  exact ⟨⟨z.extension, z.finite, z.separable, z.map, z.over, z.mem_open.1⟩, z.mem_open.2⟩

/-- ONLY original proper integral positive-dimensional geometry and the SAME specified nonempty smooth open construct THREE DISTINCT actual finite separable points. -/
theorem exists_three_distinct_points [IsIntegral C]
    (p : C ⟶ Spec (.of k)) [IsProper p] (hdim : 0 < topologicalKrullDim C)
    (U : C.Opens) (hU : (U : Set C).Nonempty) [Smooth (U.ι ≫ p)] :
    ∃ z : Fin 3 → Point p U, Function.Injective (fun i => point (z i)) := by
  have hη (z : Point p U) : genericPoint C ≠ point z := by
    intro h
    exact genericPoint_not_closed hdim (h.symm ▸ point_isClosed z)
  obtain ⟨a⟩ := exists_point p U hU
  obtain ⟨b, hb⟩ := exists_point_avoiding_closed p U hU {point a} (point_isClosed a) (hη a)
  obtain ⟨c, hc⟩ := exists_point_avoiding_closed p U hU ({point a} ∪ {point b})
    ((point_isClosed a).union (point_isClosed b)) (by
      rintro (ha | hb)
      · exact hη a ha
      · exact hη b hb)
  refine ⟨![a, b, c], ?_⟩
  have hba : point b ≠ point a := hb
  have hca : point c ≠ point a := fun h => hc (Or.inl h)
  have hcb : point c ≠ point b := fun h => hc (Or.inr h)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end Hironaka.Geometry.CurveFibrationGenericSmoothMarks
