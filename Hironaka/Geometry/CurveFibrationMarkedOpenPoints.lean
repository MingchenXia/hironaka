import Hironaka.Geometry.CurveFibrationBaseChangeSectionPreservation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Actual geometric marking points and the internally derived three-mark lower bound. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace Hironaka.Geometry.CurveFibrationMarkedOpen
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual rational marking point induced by an ORIGINAL section on an ORIGINAL field fibre. -/
def fieldSectionPoint {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    (pullback f a : Scheme.{u}) :=
  CurveFibrationBaseChange.originalSectionBaseChange f a σ hσ (IsLocalRing.closedPoint K)

/-- Original section-image support coverage covers every actual geometric inverse-support point. -/
theorem fieldFiber_support_covered_by_section_points {X S : Scheme.{u}}
    (f : X ⟶ S) (D : X.IdealSheafData) {ι : Type u} (σ : ι → (S ⟶ X))
    (hσ : ∀ i, σ i ≫ f = 𝟙 S)
    (hcover : ⋃ i, Set.range (σ i) = (D.support : Set X))
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (z : (pullback f a : Scheme.{u})) (hz : pullback.fst f a z ∈ D.support) :
    ∃ i, fieldSectionPoint f (σ i) (hσ i) a = z := by
  have hx : pullback.fst f a z ∈ ⋃ i, Set.range (σ i) := by rw [hcover]; exact hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hzi : z ∈ Set.range (CurveFibrationBaseChange.originalSectionBaseChange f a (σ i) (hσ i)) := by
    rw [CurveFibrationBaseChange.originalSectionBaseChange_range]
    exact hi
  obtain ⟨t, ht⟩ := hzi
  refine ⟨i, ?_⟩
  change CurveFibrationBaseChange.originalSectionBaseChange f a (σ i) (hσ i)
    (IsLocalRing.closedPoint K) = z
  exact (congrArg _ (Subsingleton.elim (IsLocalRing.closedPoint K) t)).trans ht

/-- Three ORIGINAL distinct smooth boundary points construct three distinct ORIGINAL marking indices. -/
theorem three_section_indices_of_geometric_three_points {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (D : X.IdealSheafData)
    {ι : Type u} (σ : ι → (S ⟶ X)) (hσ : ∀ i, σ i ≫ f = 𝟙 S)
    (hcover : ⋃ i, Set.range (σ i) = (D.support : Set X))
    (hthree : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) →
      ∃ v : Fin 3 → (pullback f a : Scheme.{u}), Function.Injective v ∧ ∀ i,
        v i ∈ C ∧ pullback.fst f a (v i) ∈ f.smoothLocus ∧
          pullback.fst f a (v i) ∈ D.support)
    {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    (C : Set (pullback f a : Scheme.{u}))
    (hC : C ∈ irreducibleComponents (pullback f a : Scheme.{u})) :
    ∃ j : Fin 3 → ι, Function.Injective j ∧ ∀ i,
      fieldSectionPoint f (σ (j i)) (hσ (j i)) a ∈ C ∧
        pullback.fst f a (fieldSectionPoint f (σ (j i)) (hσ (j i)) a) ∈ f.smoothLocus := by
  obtain ⟨v, hvinj, hv⟩ := hthree K a C hC
  have H : ∀ i : Fin 3, ∃ j, fieldSectionPoint f (σ j) (hσ j) a = v i :=
    fun i => fieldFiber_support_covered_by_section_points f D σ hσ hcover a (v i) (hv i).2.2
  choose j hj using H
  refine ⟨j, ?_, ?_⟩
  · intro i l hil
    apply hvinj
    calc
      v i = fieldSectionPoint f (σ (j i)) (hσ (j i)) a := (hj i).symm
      _ = fieldSectionPoint f (σ (j l)) (hσ (j l)) a := by rw [hil]
      _ = v l := hj l
  · intro i
    rw [hj i]
    exact ⟨(hv i).1, (hv i).2.1⟩

/-- ORIGINAL geometric connectedness and the three-point condition force the ACTUAL finite index cardinality. -/
theorem three_le_card_sections_of_geometric_three_points {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [GeometricallyConnected f]
    (D : X.IdealSheafData) {ι : Type u} [Finite ι] (σ : ι → (S ⟶ X))
    (hσ : ∀ i, σ i ≫ f = 𝟙 S)
    (hcover : ⋃ i, Set.range (σ i) = (D.support : Set X))
    (hthree : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) →
      ∃ v : Fin 3 → (pullback f a : Scheme.{u}), Function.Injective v ∧ ∀ i,
        v i ∈ C ∧ pullback.fst f a (v i) ∈ f.smoothLocus ∧
          pullback.fst f a (v i) ∈ D.support) : 3 ≤ Nat.card ι := by
  let F : Type u := S.residueField (genericPoint S)
  let K := AlgebraicClosure F
  let a : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫ S.fromSpecResidueField (genericPoint S)
  let : ConnectedSpace (pullback f a : Scheme.{u}) :=
    GeometricallyConnected.geometrically_connectedSpace a (pullback.fst f a) (pullback.snd f a)
      (IsPullback.of_hasPullback f a)
  let z : (pullback f a : Scheme.{u}) := Classical.choice inferInstance
  obtain ⟨j, hj, _⟩ := three_section_indices_of_geometric_three_points f D σ hσ hcover hthree
    a (irreducibleComponent z) (irreducibleComponent_mem_irreducibleComponents z)
  simpa using Nat.card_le_card_of_injective j hj

end Hironaka.Geometry.CurveFibrationMarkedOpen
