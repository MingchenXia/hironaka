import DeJongAlterations.Geometry.NodeFamilyQuadraticProjection
import DeJongAlterations.Geometry.FiberDimensionGenericFinite
import DeJongAlterations.Geometry.FiberDimensionCurveComponents
import DeJongAlterations.Geometry.NodeFamilyDimension
import DeJongAlterations.Geometry.FiberDimensionGenericGlobalIsolation

/-!
# No isolated points on the actual field nodes

The actual flat quadratic projection is open over every field. The affine line
has no open singleton by its actual positive generic fibre dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Polynomial

namespace DeJongAlterations.Geometry.NodeFamilyGeometricPurity

open Algebra.NodeBlowupChart NodeFamilyQuadraticProjection
open FiberDimension FiberDimensionCurveComponents FiberDimensionGenericFinite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An open singleton in a source gives an actual quasi-finite point for every locally finite-type map. -/
theorem quasiFiniteAt_of_isOpen_singleton {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (h : IsOpen ({x} : Set X)) : f.QuasiFiniteAt x := by
  apply Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
  have heq : (f.fiberι (f x)) ⁻¹' ({x} : Set X) = {f.asFiber x} := by
    ext z
    constructor
    · intro hz
      apply Set.mem_singleton_iff.mpr
      apply (f.fiberι (f x)).isEmbedding.injective
      exact (Set.mem_singleton_iff.mp hz).trans (f.fiberι_asFiber x).symm
    · rintro hz
      rw [Set.mem_singleton_iff.mp hz]
      change f.fiberι (f x) (f.asFiber x) = x
      exact f.fiberι_asFiber x
  rw [← heq]
  exact h.preimage (f.fiberι (f x)).continuous

variable (K : Type u) [Field K]

/-- The actual affine line over every field has no open singleton. -/
theorem affineLine_not_isOpen_singleton (x : Spec (CommRingCat.of (MvPolynomial (Fin 1) K))) :
    ¬ IsOpen ({x} : Set (Spec (CommRingCat.of (MvPolynomial (Fin 1) K)))) := by
  let p := affineSpaceStructure K 1
  let : LocallyOfFiniteType p :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : Surjective p := ⟨fun s =>
    (fiberDimension_nonneg_iff_mem_range p s).mp (by
      rw [show fiberDimension p s = 1 from affineSpace_fiber_dimension K 1 s]
      exact zero_le_one)⟩
  have hpos : (1 : WithBot ℕ∞) ≤ fiberDimension p (genericPoint (Spec (CommRingCat.of K))) :=
    (affineSpace_fiber_dimension K 1 _).ge
  intro h
  exact not_quasiFiniteAt_of_one_le_genericFiberDimension p hpos x
    (quasiFiniteAt_of_isOpen_singleton p x h)

/-- The actual one-variable polynomial spectrum has no open singleton over any field. -/
theorem polynomial_not_isOpen_singleton (x : Spec (CommRingCat.of K[X])) :
    ¬ IsOpen ({x} : Set (Spec (CommRingCat.of K[X]))) := by
  let e : Spec (CommRingCat.of K[X]) ≅ Spec (CommRingCat.of (MvPolynomial (Fin 1) K)) :=
    Scheme.Spec.mapIso (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toCommRingCatIso.op
  intro h
  have ho := e.hom.homeomorph.isOpenMap ({x} : Set (Spec (CommRingCat.of K[X]))) h
  rw [Set.image_singleton] at ho
  exact affineLine_not_isOpen_singleton K (e.hom x) ho

/-- Actual nodes have no open singleton, including the reducible zero-parameter node. -/
theorem node_not_isOpen_singleton (t : K) (x : Spec (CommRingCat.of (Node K t))) :
    ¬ IsOpen ({x} : Set (Spec (CommRingCat.of (Node K t)))) := by
  intro h
  have ho := quadraticProjection_isOpenMap t ({x} : Set (Spec (CommRingCat.of (Node K t)))) h
  rw [Set.image_singleton] at ho
  exact polynomial_not_isOpen_singleton K (quadraticProjection t x) ho

/-- Absence of open points and the actual Noetherian component-isolation theorem give positive component dimension. -/
theorem one_le_component_dimension_of_no_open_singletons (T : Type u)
    [TopologicalSpace T] [T0Space T] [NoetherianSpace T]
    (hno : ∀ x : T, ¬ IsOpen ({x} : Set T)) (Z : Set T)
    (hZ : Z ∈ irreducibleComponents T) : (1 : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  by_contra hnot
  have hdim : topologicalKrullDim Z ≤ 0 := by
    have hthreshold : (1 : WithBot ℕ∞) ≤ topologicalKrullDim Z ↔
        ¬ topologicalKrullDim Z ≤ 0 := by
      simpa only [Nat.cast_zero, zero_add, lt_iff_not_ge] using
        (ENat.WithBot.add_one_le_iff (n := 0) (m := topologicalKrullDim Z))
    exact Classical.not_not.mp (fun h => hnot (hthreshold.mpr h))
  obtain ⟨x, _, hx⟩ :=
    FiberComponentIsolation.exists_isOpen_singleton_of_component_dimension_le_zero T Z hZ hdim
  exact hno x hx

/-- Every actual irreducible component of every field node has dimension one. -/
theorem node_component_dimension (t : K) (Z : Set (Spec (CommRingCat.of (Node K t))))
    (hZ : Z ∈ irreducibleComponents (Spec (CommRingCat.of (Node K t)))) :
    topologicalKrullDim Z = 1 := by
  apply le_antisymm
  · have hdim : topologicalKrullDim (Spec (CommRingCat.of (Node K t))) = 1 := by
      change topologicalKrullDim (PrimeSpectrum (Node K t)) = 1
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      exact Algebra.NodeFamilyDimension.node_ringKrullDim K t
    exact (topologicalKrullDim_subspace_le _ Z).trans hdim.le
  · exact one_le_component_dimension_of_no_open_singletons _ (node_not_isOpen_singleton K t) Z hZ

variable {A : Type u} [CommRing A]

/-- The actual scheme-theoretic field base change of the literal node family. -/
abbrev nodeFieldBaseChange [Algebra A K] (t : A) : Scheme.{u} :=
  pullback (NodeFamilyFlat.nodeMorphism t) (Spec.map (CommRingCat.ofHom (algebraMap A K)))

/-- The actual field base change is the genuine literal node after coefficient extension. -/
def nodeFieldBaseChangeIso [Algebra A K] (t : A) :
    nodeFieldBaseChange K t ≅ Spec (CommRingCat.of (Node K (algebraMap A K t))) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A K (Node A t) ≪≫
    Scheme.Spec.mapIso (Algebra.NodeFamilyBaseChange.nodeBaseChangeEquiv K t).toRingEquiv.toCommRingCatIso.symm.op

/-- Actual field base changes of nodes have no open singleton. -/
theorem nodeFieldBaseChange_not_isOpen_singleton [Algebra A K] (t : A)
    (x : nodeFieldBaseChange K t) : ¬ IsOpen ({x} : Set (nodeFieldBaseChange K t)) := by
  intro hx
  have ho := (nodeFieldBaseChangeIso K t).hom.homeomorph.isOpenMap _ hx
  rw [Set.image_singleton] at ho
  exact node_not_isOpen_singleton K _ _ ho

/-- Every actual field base change of the literal node has whole-space dimension one. -/
theorem nodeFieldBaseChange_dimension [Algebra A K] (t : A) :
    topologicalKrullDim (nodeFieldBaseChange K t) = 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ (nodeFieldBaseChangeIso K t).hom.homeomorph.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum (Node K (algebraMap A K t))) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact Algebra.NodeFamilyDimension.node_ringKrullDim K _

/-- Every actual component of every actual field base change of the node has dimension one. -/
theorem nodeFieldBaseChange_component_dimension [Algebra A K] (t : A)
    (Z : Set (nodeFieldBaseChange K t))
    (hZ : Z ∈ irreducibleComponents (nodeFieldBaseChange K t)) : topologicalKrullDim Z = 1 := by
  let : NoetherianSpace (nodeFieldBaseChange K t) :=
    (noetherianSpace_iff_of_homeomorph (nodeFieldBaseChangeIso K t).hom.homeomorph).mpr inferInstance
  exact le_antisymm ((topologicalKrullDim_subspace_le _ Z).trans
    (nodeFieldBaseChange_dimension K t).le)
    (one_le_component_dimension_of_no_open_singletons _
      (nodeFieldBaseChange_not_isOpen_singleton K t) Z hZ)

end DeJongAlterations.Geometry.NodeFamilyGeometricPurity
