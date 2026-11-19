import Hironaka.Resolution.HironakaG10JointNativeIdealMap

/-! # The native target scalar map of the open-chart joint quotient

The whole target quotient stalk maps to the joint source quotient with the
same actual ambient stalk map. With geometric landing, its composite to
the strict-source stalk is the actual restricted subspace morphism.
The canonical-family identification of the joint quotient is separate.
-/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG10JointNativeScalar
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeIdealMap
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
  (U : Opens (ComplexModel (d+t))) (W : Set U)
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
variable (f : realOpenChartDomain d t j b U → Y) (V : Set Y)
  (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
  (hV : IsComplexAnalyticSubset (n := n) V)

/-- The whole target quotient uses its actual full vanishing stalk ideal. -/
abbrev TargetQuotient (y : realOpenChartDomain d t j b U) :=
  actualComplexStructureStalk (n := n) (f y) ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y)

/-- The target quotient acts via the actual native ambient stalk map. -/
def targetQuotientToJoint
    (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hV : IsComplexAnalyticSubset (n := n) V) (y : realOpenChartDomain d t j b U) :
    TargetQuotient (n := n) d t j b U f V y →+* JointQuotient (n := n) d t j b U W f V y := by
  apply Ideal.quotientMap (I := actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y))
    (jointIdeal (n := n) d t j b U W f V y)
    ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y).hom
  apply Ideal.map_le_iff_le_comap.mp
  calc
    _ = targetIdeal (n := n) d t j b U f V y :=
      (targetIdeal_eq_native_map (n := n) d t j b U f V hf hV y).symm
    _ ≤ _ := le_sup_right

theorem targetQuotientToJoint_mk (y : realOpenChartDomain d t j b U)
    (r : actualComplexStructureStalk (n := n) (f y)) :
    targetQuotientToJoint (n := n) d t j b U W f V hf hV y
      (Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) V) (f y)) r) =
    Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)
      ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y r) := rfl

/-- The genuine target subspace stalk, at an actual included target point. -/
abbrev TargetStalk (y : realOpenChartDomain d t j b U) (hyV : f y ∈ V) :=
  ((actualSubspaceLocallyRingedSpace (n := n) V).presheaf.stalk ⟨f y,hyV⟩).carrier

def targetStalkToJoint
    (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hV : IsComplexAnalyticSubset (n := n) V) (y : realOpenChartDomain d t j b U) (hyV : f y ∈ V) :
    TargetStalk (n := n) d t j b U f V y hyV →+* JointQuotient (n := n) d t j b U W f V y :=
  (targetQuotientToJoint (n := n) d t j b U W f V hf hV y).comp
    (actualSubspaceStalkWholeEquiv (n := n) V ⟨f y,hyV⟩).toRingHom

/-- This is the actual scalar map on EVERY original target ambient germ. -/
theorem targetStalkToJoint_inclusion (y : realOpenChartDomain d t j b U) (hyV : f y ∈ V)
    (r : actualComplexStructureStalk (n := n) (f y)) :
    targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV
      ((actualSubspaceInclusion (n := n) V).stalkMap ⟨f y,hyV⟩ r) =
    Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)
      ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y r) := by
  change targetQuotientToJoint (n := n) d t j b U W f V hf hV y
    (actualSubspaceStalkWholeEquiv (n := n) V ⟨f y,hyV⟩
      ((actualSubspaceInclusion (n := n) V).stalkMap ⟨f y,hyV⟩ r)) = _
  rw [actualSubspaceInclusion_stalk,targetQuotientToJoint_mk]

variable (h0 : (0 : ComplexModel (d+t)) ∈ U) (hW : IsComplexAnalyticSubset (n := d+t) W)
  (hland : realOpenStrictTransform d t j b U W ⊆ f ⁻¹' V)

/-- The joint target scalar map and strict-source quotient recover the
actual restricted morphism, on every target strict-space stalk element. -/
theorem targetStalkToJoint_strict_square (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (hyS : y ∈ realOpenStrictTransform d t j b U W)
    (r : TargetStalk (n := n) d t j b U f V y (hland hyS)) :
    jointStrictStalkMap (n := n) d t j b U W f V h0 hW hf.continuous hland y hy hyS
      (targetStalkToJoint (n := n) d t j b U W f V hf hV y (hland hyS) r) =
    (actualSubspaceMap hf (fun _ hx => hland hx)).stalkMap ⟨y,hyS⟩ r := by
  obtain ⟨a,rfl⟩ := actualSubspaceInclusionRingedHom_stalk_surjective (n := n) V ⟨f y,hland hyS⟩ r
  change jointStrictStalkMap (n := n) d t j b U W f V h0 hW hf.continuous hland y hy hyS
    (targetStalkToJoint (n := n) d t j b U W f V hf hV y (hland hyS)
      ((actualSubspaceInclusion (n := n) V).stalkMap ⟨f y,hland hyS⟩ a)) =
    (actualSubspaceMap hf (fun _ hx => hland hx)).stalkMap ⟨y,hyS⟩
      ((actualSubspaceInclusion (n := n) V).stalkMap ⟨f y,hland hyS⟩ a)
  rw [targetStalkToJoint_inclusion,jointStrictStalkMap_mk]
  apply (actualSubspaceStalkWholeEquiv (n := d+t) (realOpenStrictTransform d t j b U W) ⟨y,hyS⟩).injective
  rw [actualSubspaceInclusion_stalk]
  exact (actualSubspaceMap_stalk hf (fun _ hx => hland hx) ⟨y,hyS⟩ a).symm
/-- The whole torsion-quotient identification preserves the action of every
actual target strict-stalk scalar, not just coordinate generators. -/
theorem torsionQuotientEquiv_target_mul (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (hyS : y ∈ realOpenStrictTransform d t j b U W)
    (r : TargetStalk (n := n) d t j b U f V y (hland hyS))
    (s : JointQuotient (n := n) d t j b U W f V y) :
    jointTorsionQuotientEquiv (n := n) d t j b U W f V h0 hW hf.continuous hland y hy hyS
      (Ideal.Quotient.mk (pivotTorsion (n := n) d t j b U W f V y)
        (targetStalkToJoint (n := n) d t j b U W f V hf hV y (hland hyS) r * s)) =
    (actualSubspaceMap hf (fun _ hx => hland hx)).stalkMap ⟨y,hyS⟩ r *
      jointTorsionQuotientEquiv (n := n) d t j b U W f V h0 hW hf.continuous hland y hy hyS
        (Ideal.Quotient.mk (pivotTorsion (n := n) d t j b U W f V y) s) := by
  rw [jointTorsionQuotientEquiv_mk,map_mul,targetStalkToJoint_strict_square,
    jointTorsionQuotientEquiv_mk]

end
end Hironaka.HironakaG10JointNativeScalar
