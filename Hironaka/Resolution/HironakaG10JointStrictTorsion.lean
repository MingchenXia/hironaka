import Hironaka.Resolution.HironakaG10RealOpenStrictTorsionKernel

/-! # Strict torsion after imposing an actual target vanishing ideal

On a genuine open source chart, adjoin the whole pullback of an actual
analytic target subset whose inverse image contains the geometric strict
source. The resulting whole joint ideal has the same pivot saturation and
its quotient maps to the actual strict-space stalk with precisely powers
torsion kernel. The geometric landing condition is explicit: the later
canonical-chart consumer must derive it from its actual morphism square.
No nonreduced target or arbitrary fibre-product universality is asserted.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG10JointStrictTorsion
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaActualAnalyticSubspace HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualCentreRingSheafStalk

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
  (U : Opens (ComplexModel (d+t))) (W : Set U)
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
variable (f : realOpenChartDomain d t j b U → Y) (V : Set Y)

/-- The whole actual ambient-stalk pullback of the target vanishing ideal. -/
def targetIdeal (y : realOpenChartDomain d t j b U) : Ideal (AmbientStalk d t j b U y) :=
  actualWholeSheafStalkIdeal (GermIdeal.pullback (m := d+t) f (vanishingIdeal (n := n) V)) y

/-- The entire joint source-plus-target ideal, retaining all source multiplicities. -/
def jointIdeal (y : realOpenChartDomain d t j b U) : Ideal (AmbientStalk d t j b U y) :=
  rawAnalyticIdeal d t j b U W y ⊔ targetIdeal (n := n) d t j b U f V y

/-- Actual holomorphic functions vanishing on the target pull back to functions
vanishing on any source subset which lands in that target. -/
theorem targetIdeal_le_strict (hf : Continuous f)
    (hland : realOpenStrictTransform d t j b U W ⊆ f ⁻¹' V)
    (y : realOpenChartDomain d t j b U) :
    targetIdeal (n := n) d t j b U f V y ≤ geometricStrictIdeal d t j b U W y := by
  have hle : (GermIdeal.pullback (m := d+t) f (vanishingIdeal (n := n) V)).Le
      (vanishingIdeal (n := d+t) (realOpenStrictTransform d t j b U W)) := by
    intro y g hg
    obtain ⟨hgh,K,s,a,hs,_,hsum⟩ := hg
    refine ⟨hgh,?_⟩
    have hzero : ∀ i, ∀ᶠ y' in 𝓝 y, f y' ∈ V → s i y' = 0 := by
      intro i
      obtain ⟨c,hc,hsc⟩ := hs i
      filter_upwards [hf.continuousAt.eventually hc.2] with y' hy' hV
      rw [hsc]
      exact hy' hV
    filter_upwards [hsum,eventually_all.mpr hzero] with y' hsum' hzero' hy'
    rw [hsum']
    exact Finset.sum_eq_zero fun i _ => by rw [hzero' i (hland hy'),mul_zero]
  apply Ideal.span_le.mpr
  rintro _ ⟨g,hg,hmem,rfl⟩
  exact Ideal.subset_span ⟨g,hg,hle y g hmem,rfl⟩

variable (h0 : (0 : ComplexModel (d+t)) ∈ U)
  (hW : IsComplexAnalyticSubset (n := d+t) W)
  (hf : Continuous f) (hland : realOpenStrictTransform d t j b U W ⊆ f ⁻¹' V)

include hf hland in
theorem joint_le_strict (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) :
    jointIdeal (n := n) d t j b U W f V y ≤ geometricStrictIdeal d t j b U W y :=
  sup_le (rawAnalyticIdeal_le_geometricStrictIdeal d t j b U W h0 hW y hy)
    (targetIdeal_le_strict (n := n) d t j b U W f V hf hland y)

include hf hland in
/-- The literal joint ideal has the SAME whole pivot saturation as the strict
ideal. It follows from the original source saturation and actual landing. -/
theorem strict_mem_iff_joint_pivot_power (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (g : AmbientStalk d t j b U y) :
    g ∈ geometricStrictIdeal d t j b U W y ↔
      ∃m : ℕ, (exceptionalGerm d t j b U y)^m*g ∈ jointIdeal (n := n) d t j b U W f V y := by
  constructor
  · intro hg
    obtain ⟨m,hm⟩ := (local_whole_saturation d t j b U W h0 hW y hy g).mp hg
    exact ⟨m,Submodule.mem_sup_left hm⟩
  · rintro ⟨m,hm⟩
    have hp := joint_le_strict (n := n) d t j b U W f V h0 hW hf hland y hy hm
    obtain ⟨k,hk⟩ := (local_whole_saturation d t j b U W h0 hW y hy _).mp hp
    apply (local_whole_saturation d t j b U W h0 hW y hy g).mpr
    refine ⟨k+m,?_⟩
    simpa only [pow_add,mul_assoc] using hk

abbrev JointQuotient (y : realOpenChartDomain d t j b U) :=
  AmbientStalk d t j b U y ⧸ jointIdeal (n := n) d t j b U W f V y

def pivotClass (y : realOpenChartDomain d t j b U) : JointQuotient (n := n) d t j b U W f V y :=
  Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) (exceptionalGerm d t j b U y)

abbrev pivotTorsion (y : realOpenChartDomain d t j b U) : Ideal (JointQuotient (n := n) d t j b U W f V y) :=
  Submodule.torsion' (JointQuotient (n := n) d t j b U W f V y) (JointQuotient (n := n) d t j b U W f V y)
    (Submonoid.powers (pivotClass (n := n) d t j b U W f V y))

include hf hland in
def jointStrictQuotientMap (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) :
    JointQuotient (n := n) d t j b U W f V y →+* GeometricStrictQuotient d t j b U W y :=
  Ideal.quotientMap (geometricStrictIdeal d t j b U W y) (RingHom.id (AmbientStalk d t j b U y))
    (joint_le_strict (n := n) d t j b U W f V h0 hW hf hland y hy)

theorem jointStrictQuotientMap_mk (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (g : AmbientStalk d t j b U y) :
    jointStrictQuotientMap (n := n) d t j b U W f V h0 hW hf hland y hy
      (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g) =
        Ideal.Quotient.mk (geometricStrictIdeal d t j b U W y) g := rfl

theorem jointStrictQuotientMap_surjective (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) :
    Function.Surjective (jointStrictQuotientMap (n := n) d t j b U W f V h0 hW hf hland y hy) :=
  Ideal.quotientMap_surjective Function.surjective_id

theorem jointStrictQuotientMap_ker (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) :
    RingHom.ker (jointStrictQuotientMap (n := n) d t j b U W f V h0 hW hf hland y hy) =
      pivotTorsion (n := n) d t j b U W f V y := by
  ext s
  refine Submodule.Quotient.induction_on (jointIdeal (n := n) d t j b U W f V y) s ?_
  intro g
  change jointStrictQuotientMap (n := n) d t j b U W f V h0 hW hf hland y hy
    (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g) = 0 ↔ _
  rw [jointStrictQuotientMap_mk,Ideal.Quotient.eq_zero_iff_mem,
    strict_mem_iff_joint_pivot_power (n := n) d t j b U W f V h0 hW hf hland y hy g]
  constructor
  · rintro ⟨m,hm⟩
    refine ⟨⟨(pivotClass (n := n) d t j b U W f V y)^m,⟨m,rfl⟩⟩,?_⟩
    change (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)
      (exceptionalGerm d t j b U y))^m * Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g = 0
    rw [←map_pow,←map_mul,Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  · rintro ⟨⟨s,hs⟩,hsg⟩
    obtain ⟨m,rfl⟩ := hs
    refine ⟨m,?_⟩
    change (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)
      (exceptionalGerm d t j b U y))^m * Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g = 0 at hsg
    rw [←map_pow,←map_mul,Ideal.Quotient.eq_zero_iff_mem] at hsg
    exact hsg

include hf hland in
def jointStrictStalkMap (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (hyS : y ∈ realOpenStrictTransform d t j b U W) :
    JointQuotient (n := n) d t j b U W f V y →+* StrictStalk d t j b U W y hyS :=
  (strictStalkEquiv d t j b U W y hyS).symm.toRingHom.comp
    (jointStrictQuotientMap (n := n) d t j b U W f V h0 hW hf hland y hy)

theorem jointStrictStalkMap_surjective (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (hyS : y ∈ realOpenStrictTransform d t j b U W) :
    Function.Surjective (jointStrictStalkMap (n := n) d t j b U W f V h0 hW hf hland y hy hyS) :=
  (strictStalkEquiv d t j b U W y hyS).symm.surjective.comp
    (jointStrictQuotientMap_surjective (n := n) d t j b U W f V h0 hW hf hland y hy)

theorem jointStrictStalkMap_ker (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (hyS : y ∈ realOpenStrictTransform d t j b U W) :
    RingHom.ker (jointStrictStalkMap (n := n) d t j b U W f V h0 hW hf hland y hy hyS) =
      pivotTorsion (n := n) d t j b U W f V y := by
  rw [←jointStrictQuotientMap_ker (n := n) d t j b U W f V h0 hW hf hland y hy]
  ext s
  change (strictStalkEquiv d t j b U W y hyS).symm
    (jointStrictQuotientMap (n := n) d t j b U W f V h0 hW hf hland y hy s) = 0 ↔ _
  exact (strictStalkEquiv d t j b U W y hyS).symm.map_eq_zero_iff

theorem jointStrictStalkMap_mk (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (hyS : y ∈ realOpenStrictTransform d t j b U W)
    (g : AmbientStalk d t j b U y) :
    jointStrictStalkMap (n := n) d t j b U W f V h0 hW hf hland y hy hyS
      (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g) =
        (actualSubspaceInclusion (n := d+t) (realOpenStrictTransform d t j b U W)).stalkMap ⟨y,hyS⟩ g := by
  apply (strictStalkEquiv d t j b U W y hyS).injective
  change (strictStalkEquiv d t j b U W y hyS)
    ((strictStalkEquiv d t j b U W y hyS).symm
      (jointStrictQuotientMap (n := n) d t j b U W f V h0 hW hf hland y hy
        (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g))) = _
  rw [RingEquiv.apply_symm_apply,jointStrictQuotientMap_mk]
  exact (actualSubspaceInclusion_stalk (n := d+t) (realOpenStrictTransform d t j b U W) ⟨y,hyS⟩ g).symm
include hf hland in
/-- The actual strict stalk is the full exceptional-torsion quotient of the joint family model. -/
def jointTorsionQuotientEquiv (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (hyS : y ∈ realOpenStrictTransform d t j b U W) :
    JointQuotient (n := n) d t j b U W f V y ⧸ pivotTorsion (n := n) d t j b U W f V y ≃+*
      StrictStalk d t j b U W y hyS :=
  (Ideal.quotEquivOfEq (jointStrictStalkMap_ker (n := n) d t j b U W f V h0 hW hf hland y hy hyS).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (jointStrictStalkMap_surjective (n := n) d t j b U W f V h0 hW hf hland y hy hyS))

theorem jointTorsionQuotientEquiv_mk (y : realOpenChartDomain d t j b U)
    (hy : y ∈ localDomain d t j b U W h0 hW) (hyS : y ∈ realOpenStrictTransform d t j b U W)
    (s : JointQuotient (n := n) d t j b U W f V y) :
    jointTorsionQuotientEquiv (n := n) d t j b U W f V h0 hW hf hland y hy hyS
      (Ideal.Quotient.mk (pivotTorsion (n := n) d t j b U W f V y) s) =
        jointStrictStalkMap (n := n) d t j b U W f V h0 hW hf hland y hy hyS s := rfl

end
end Hironaka.HironakaG10JointStrictTorsion
