import Hironaka.Resolution.HironakaG10JointNativeScalar
import Hironaka.Analytic.HolomorphicGermNoetherian
import Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport

/-!
# H3.4 (`local₀`, `noetherian`): the joint chart ring of the fibre product is noetherian and `ψ` is local

Lane G10H3, run 0081 (fields `noetherian` and `local₀` of `HironakaG10NfGeoFibreModel.GeoFibreModel`; also the
`local_`/`noetherian` fields of G10GL's pulled presentations).  On a real-open blowup chart with the joint ideal
`raw ⊔ target` (TN `HironakaG10JointStrictTorsion`):

* `jointQuotient_isNoetherianRing` — the joint quotient `𝒪_{ℂ^{d+t},y} ⧸ joint` is noetherian;
* `targetStalkToJoint_mem_jacobson` — the joint target scalar map sends nonunits of the target strict stalk into the
  Jacobson radical;
* `map_targetStalkToJoint_comp_le_jacobson` — hence so does `targetStalkToJoint ∘ φ` on the maximal ideal, for every
  local homomorphism `φ` from a local ring (e.g. the stalk map of the target chart).

No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NfJointLocal

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport

noncomputable section

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (U : Opens (ComplexModel (d+t))) (W : Set U)
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  (f : realOpenChartDomain d t j b U → Y) (V : Set Y)
  (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
  (hV : IsComplexAnalyticSubset (n := n) V)

/-- The ambient stalk of a complex manifold is noetherian. -/
theorem ambientStalk_isNoetherianRing {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel m) M]
    [IsComplexManifold m M] (p : M) : IsNoetherianRing (actualComplexStructureStalk (n := m) p) :=
  let : IsNoetherianRing (HolGerm (ComplexModel m)) := isNoetherianRing_holGerm_euclidean m
  isNoetherianRing_of_ringEquiv _ (actualStalkChartEquiv (n := m) p).symm

/-- **The joint quotient is noetherian.** -/
instance jointQuotient_isNoetherianRing (y : realOpenChartDomain d t j b U) :
    IsNoetherianRing (JointQuotient (n := n) d t j b U W f V y) :=
  let : IsNoetherianRing (AmbientStalk d t j b U y) := ambientStalk_isNoetherianRing y
  inferInstance

/-- **The joint target scalar map sends nonunits into the Jacobson radical.** -/
theorem targetStalkToJoint_mem_jacobson (y : realOpenChartDomain d t j b U) (hyV : f y ∈ V)
    (z : TargetStalk (n := n) d t j b U f V y hyV) (hz : ¬ IsUnit z) :
    targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV z ∈ Ideal.jacobson ⊥ := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (actualSubspaceStalkWholeEquiv (n := n) V ⟨f y, hyV⟩ z)
  have hna : ¬ IsUnit a := fun hu => hz (by
    have h1 := hu.map (Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y)))
    rw [ha] at h1
    have h2 := h1.map (actualSubspaceStalkWholeEquiv (n := n) V ⟨f y, hyV⟩).symm
    rwa [RingEquiv.symm_apply_apply] at h2)
  have hz' : targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV z =
      Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)
        (((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y).hom a) := by
    change targetQuotientToJoint (n := n) d t j b U W f V hf hV y
      (actualSubspaceStalkWholeEquiv (n := n) V ⟨f y, hyV⟩ z) = _
    rw [← ha]
    rfl
  rw [hz']
  have hmem : (((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y).hom a : AmbientStalk d t j b U y) ∈
      IsLocalRing.maximalIdeal (AmbientStalk d t j b U y) :=
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu => hna
      ((AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap (ChartedSpace.locallyRingedSpaceMap f hf) y).map_nonunit
        a hu)
  exact map_mk_maximalIdeal_le_jacobson _ (Ideal.mem_map_of_mem _ hmem)

/-- **`targetStalkToJoint ∘ φ` sends the maximal ideal into the Jacobson radical**, for every local homomorphism
`φ` from a local ring. -/
theorem map_targetStalkToJoint_comp_le_jacobson {A : Type*} [CommRing A] [IsLocalRing A]
    (y : realOpenChartDomain d t j b U) (hyV : f y ∈ V)
    (φ : A →+* TargetStalk (n := n) d t j b U f V y hyV) [IsLocalHom φ] :
    Ideal.map ((targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV).comp φ)
      (IsLocalRing.maximalIdeal A) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap]
  refine targetStalkToJoint_mem_jacobson d t j b U W f V hf hV y hyV (φ a) fun hu => ?_
  exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_map_unit φ a hu)

end

end Hironaka.Analytic.Unibranch.HironakaG10NfJointLocal
