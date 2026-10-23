import DeJongAlterations.Algebra.NodeBlowupChart
import DeJongAlterations.Geometry.AffineBlowupCover

/-!
# The two actual node charts cover the native blowup

The degree-one Rees elements of the two genuine ideal generators cover Proj.
The released smaller-node chart immersions therefore give an actual two-chart scheme open cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.NodeBlowupCover

open Algebra.NodeBlowupChart

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] (t q : A)

/-- The native basic open corresponding to the coordinate generator `u` of the center. -/
def coordinateChartOpen : (affineBlowup (centerIdeal t q)).Opens :=
  affineBlowupChartOpen (centerIdeal t q) (coordinate (t * q) 0)
    (Ideal.subset_span (Set.mem_insert _ _))

/-- The native basic open corresponding to the coefficient generator `t` of the center. -/
def parameterChartOpen : (affineBlowup (centerIdeal t q)).Opens :=
  affineBlowupChartOpen (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
    (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- A Rees ideal containing the two genuine degree-one generators contains every center element. -/
theorem reesDegreeOne_mem_of_generators (P : Ideal (reesAlgebra (centerIdeal t q)))
    (hu : reesDegreeOne (centerIdeal t q) (coordinate (t * q) 0)
      (Ideal.subset_span (Set.mem_insert _ _)) ∈ P)
    (ht : reesDegreeOne (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))) ∈ P)
    {a : Node A (t * q)} (ha : a ∈ centerIdeal t q) :
    reesDegreeOne (centerIdeal t q) a ha ∈ P := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hu
    · have heq : a = algebraMap A (Node A (t * q)) t := Set.mem_singleton_iff.mp ha
      subst a
      exact ht
  | zero =>
    have hz : reesDegreeOne (centerIdeal t q) 0 (Ideal.zero_mem _) = 0 := by
      apply Subtype.ext
      simp [reesDegreeOne]
    rw [hz]
    exact P.zero_mem
  | add a b ha hb hia hib =>
    have hadd : reesDegreeOne (centerIdeal t q) (a + b) (Ideal.add_mem _ ha hb) =
        reesDegreeOne (centerIdeal t q) a ha + reesDegreeOne (centerIdeal t q) b hb := by
      apply Subtype.ext
      exact (Polynomial.monomial 1).map_add a b
    rw [hadd]
    exact P.add_mem hia hib
  | smul r a ha hia =>
    have hmul : reesDegreeOne (centerIdeal t q) (r * a) (Ideal.mul_mem_left _ r ha) =
        algebraMap (Node A (t * q)) (reesAlgebra (centerIdeal t q)) r *
          reesDegreeOne (centerIdeal t q) a ha := by
      apply Subtype.ext
      exact (Polynomial.C_mul_monomial (a := r) (b := a) (n := 1)).symm
    change reesDegreeOne (centerIdeal t q) (r * a) (Ideal.mul_mem_left _ r ha) ∈ P
    rw [hmul]
    exact P.mul_mem_left _ hia

/-- The two explicit generators of the actual center ideal give a cover of its native Proj. -/
theorem coordinateChartOpen_sup_parameterChartOpen :
    coordinateChartOpen t q ⊔ parameterChartOpen t q = ⊤ := by
  apply top_le_iff.mp
  intro x hx
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp ((iSup_affineBlowupChartOpen (centerIdeal t q)).ge hx)
  by_contra hnot
  have hu : reesDegreeOne (centerIdeal t q) (coordinate (t * q) 0)
      (Ideal.subset_span (Set.mem_insert _ _)) ∈ x.asHomogeneousIdeal.toIdeal := by
    by_contra h
    exact hnot (Or.inl h)
  have ht : reesDegreeOne (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))) ∈
        x.asHomogeneousIdeal.toIdeal := by
    by_contra h
    exact hnot (Or.inr h)
  exact ha (reesDegreeOne_mem_of_generators t q x.asHomogeneousIdeal.toIdeal hu ht a.property)

variable [IsDomain A] [Fact (t ≠ 0)] [Fact (q ≠ 0)]

/-- The genuine smaller coordinate-node immersion has exactly its native degree-one basic-open image. -/
theorem uChartInclusion_opensRange :
    (uChartInclusion t q).opensRange = coordinateChartOpen t q := by
  dsimp only [uChartInclusion, coordinateChartOpen]
  rw [Scheme.Hom.opensRange_comp_of_isIso, affineBlowupFractionChartInclusion_opensRange]

/-- The genuine smaller parameter-node immersion has exactly its native degree-one basic-open image. -/
theorem tChartInclusion_opensRange :
    (tChartInclusion t q).opensRange = parameterChartOpen t q := by
  dsimp only [tChartInclusion, parameterChartOpen]
  rw [Scheme.Hom.opensRange_comp_of_isIso, affineBlowupFractionChartInclusion_opensRange]

/-- The two released genuine node-chart immersions jointly cover the whole native blowup. -/
theorem chartInclusions_sup_opensRange :
    (uChartInclusion t q).opensRange ⊔ (tChartInclusion t q).opensRange = ⊤ := by
  rw [uChartInclusion_opensRange, tChartInclusion_opensRange,
    coordinateChartOpen_sup_parameterChartOpen]

/-- The two source schemes are the literal smaller node spectra, in coordinate/parameter order. -/
def nodeChartSource : Bool → Scheme
  | false => Spec (CommRingCat.of (Node A t))
  | true => Spec (CommRingCat.of (Node A q))

/-- The exact previously constructed native node-chart morphisms. -/
def nodeChartMap : (b : Bool) → nodeChartSource t q b ⟶ affineBlowup (centerIdeal t q)
  | false => uChartInclusion t q
  | true => tChartInclusion t q

/-- Each of the two specified maps is the actual open immersion already proved for that chart. -/
instance nodeChartMap_isOpenImmersion (b : Bool) : IsOpenImmersion (nodeChartMap t q b) := by
  cases b <;> dsimp only [nodeChartMap] <;> infer_instance

/-- The two exact smaller-node chart immersions form a genuine scheme open cover of the blowup. -/
@[simps! I₀ X f]
def nodeBlowupOpenCover : (affineBlowup (centerIdeal t q)).OpenCover.{0} :=
  Scheme.Cover.mkOfCovers Bool (nodeChartSource t q) (nodeChartMap t q) (by
    intro x
    have hx : x ∈ (uChartInclusion t q).opensRange ⊔ (tChartInclusion t q).opensRange := by
      rw [chartInclusions_sup_opensRange]
      trivial
    rcases hx with hu | ht
    · exact ⟨false, hu⟩
    · exact ⟨true, ht⟩)

@[simp]
theorem nodeBlowupOpenCover_source_false :
    (nodeBlowupOpenCover t q).X false = Spec (CommRingCat.of (Node A t)) := rfl

@[simp]
theorem nodeBlowupOpenCover_source_true :
    (nodeBlowupOpenCover t q).X true = Spec (CommRingCat.of (Node A q)) := rfl

@[simp]
theorem nodeBlowupOpenCover_map_false :
    (nodeBlowupOpenCover t q).f false = uChartInclusion t q := rfl

@[simp]
theorem nodeBlowupOpenCover_map_true :
    (nodeBlowupOpenCover t q).f true = tChartInclusion t q := rfl

end DeJongAlterations.NodeBlowupCover
