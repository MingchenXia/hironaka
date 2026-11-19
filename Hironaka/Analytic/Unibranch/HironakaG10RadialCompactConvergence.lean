import Hironaka.Resolution.HironakaG10FlatPrivilegedEuclidean
import Hironaka.Resolution.HironakaG10FlatPolydiscAlgebra
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.CompactOpen

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10RadialCompactConvergence
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E} [CompactSpace K]

def radialPoint (c : E) (r : ℝ) (z : E) : E := c + r • (z - c)

omit [CompactSpace K] in
/-- Contraction fixes K, and enters its interior before the endpoint. -/
theorem radialPoint_mem (hK : Convex ℝ K) {c : E} (hc : c ∈ interior K)
    (r : Set.Icc (0 : ℝ) 1) (z : K) : radialPoint c r z ∈ K := by
  exact hK.add_smul_sub_mem (interior_subset hc) z.property r.property

omit [CompactSpace K] in
theorem radialPoint_mem_interior (hK : Convex ℝ K) {c : E} (hc : c ∈ interior K)
    (r : Set.Icc (0 : ℝ) 1) (hr : (r : ℝ) < 1) (z : K) :
    radialPoint c r z ∈ interior K := by
  have h := hK.combo_interior_self_mem_interior hc z.property (sub_pos.mpr hr) r.property.1
    (sub_add_cancel (1 : ℝ) r)
  convert h using 1; simp only [radialPoint, sub_smul, one_smul, smul_sub]; abel

/-- The radial restriction of one fixed continuous function. -/
def radialRestriction (hK : Convex ℝ K) {c : E} (hc : c ∈ interior K)
    (g : C(K, ℂ)) (r : Set.Icc (0 : ℝ) 1) : C(K, ℂ) :=
  ⟨fun z => g ⟨radialPoint c r z, radialPoint_mem hK hc r z⟩,
    g.continuous.comp ((continuous_const.add (continuous_const.smul
      (continuous_subtype_val.sub continuous_const))).subtype_mk _)⟩

omit [CompactSpace K] in
/-- For each fixed continuous function the radial restrictions converge in
sup norm to that function as r tends to 1 from the closed unit interval. -/
theorem continuous_radialRestriction (hK : Convex ℝ K) {c : E} (hc : c ∈ interior K)
    (g : C(K, ℂ)) : Continuous (radialRestriction hK hc g) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h : Continuous (fun p : Set.Icc (0 : ℝ) 1 × K => radialPoint c p.1 p.2) := by
    unfold radialPoint
    exact continuous_const.add ((continuous_subtype_val.comp continuous_fst).smul
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const))
  exact g.continuous.comp (h.subtype_mk _)

omit [CompactSpace K] in
@[simp] theorem radialRestriction_one (hK : Convex ℝ K) {c : E} (hc : c ∈ interior K)
    (g : C(K, ℂ)) : radialRestriction hK hc g ⟨1, by simp⟩ = g := by
  ext z
  simp [radialRestriction, radialPoint]

/-- Every literal closed polydisc is real convex. -/
theorem closedPolydisc_convex (n : ℕ) (c : EuclideanSpace ℂ (Fin n)) (ρ : Fin n → ℝ) :
    Convex ℝ {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Metric.closedBall (c i) (ρ i)} := by
  have heq : {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Metric.closedBall (c i) (ρ i)} =
      ⋂ i, ((EuclideanSpace.proj (𝕜 := ℂ) i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
        : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ).restrictScalars ℝ ⁻¹' Metric.closedBall (c i) (ρ i) := by
    ext z
    simp
  rw [heq]
  exact convex_iInter fun i => (convex_closedBall _ _).linear_preimage _

/-- Positive radii put the centre in the interior, including dimension zero. -/
theorem closedPolydisc_centre_interior (n : ℕ) (c : EuclideanSpace ℂ (Fin n))
    (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) :
    c ∈ interior {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Metric.closedBall (c i) (ρ i)} := by
  let U : Set (EuclideanSpace ℂ (Fin n)) := ⋂ i,
    (fun z : EuclideanSpace ℂ (Fin n) => z i) ⁻¹' Metric.ball (c i) (ρ i)
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact Metric.isOpen_ball.preimage (EuclideanSpace.proj (𝕜 := ℂ) i).continuous
  have hcU : c ∈ U := by
    simp only [U, mem_iInter, mem_preimage]
    exact fun i => Metric.mem_ball_self (hρ i)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hU.mem_nhds hcU)
  intro z hz i
  exact Metric.ball_subset_closedBall (mem_iInter.mp hz i)

/-- The real radial map is complex-affine and holomorphic. -/
theorem radialPoint_differentiable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : E) (r : ℝ) :
    Differentiable ℂ (radialPoint c r) := by
  change Differentiable ℂ (fun z : E => c + r • (z - c))
  simp_rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (differentiable_const c).add ((differentiable_id.sub (differentiable_const c)).const_smul (r : ℂ))

/-- For every strict radial contraction, a literal B(K) entry becomes
holomorphic on an open neighborhood of the whole compact K. -/
theorem radial_holomorphic_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : Set E} [CompactSpace K] (hK : Convex ℝ K)
    {c : E} (hc : c ∈ interior K) (g : Hironaka.HironakaG10FlatPolydiscAlgebra.holSubalgebra K)
    (r : Set.Icc (0 : ℝ) 1) (hr : (r : ℝ) < 1) :
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧
      DifferentiableOn ℂ (fun z =>
        Hironaka.HironakaG10FlatPolydiscAlgebra.extendZero K g (radialPoint c r z)) U ∧
      ∀ z : K, Hironaka.HironakaG10FlatPolydiscAlgebra.extendZero K g
        (radialPoint c r z) = radialRestriction hK hc (g : C(K, ℂ)) r z := by
  let U : Set E := (radialPoint c r) ⁻¹' interior K
  have hd : Differentiable ℂ (radialPoint c r) := radialPoint_differentiable c r
  have hU : IsOpen U := isOpen_interior.preimage hd.continuous
  have hKU : K ⊆ U := fun z hz => radialPoint_mem_interior hK hc r hr ⟨z,hz⟩
  refine ⟨U,hU,hKU,?_,?_⟩
  · exact g.property.comp hd.differentiableOn (fun _ hx => hx)
  · intro z
    change Hironaka.HironakaG10FlatPolydiscAlgebra.extendZero K g
      (radialPoint c r z) = (g : C(K,ℂ)) ⟨radialPoint c r z, radialPoint_mem hK hc r z⟩
    exact Hironaka.HironakaG10FlatPolydiscAlgebra.extendZero_of_mem K g
      (radialPoint_mem hK hc r z)

/-- Radial restriction as an element of the actual Banach algebra B(K). -/
def radialHolomorphic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : Set E} [CompactSpace K] (hK : Convex ℝ K)
    {c : E} (hc : c ∈ interior K)
    (g : Hironaka.HironakaG10FlatPolydiscAlgebra.holSubalgebra K)
    (r : Set.Icc (0 : ℝ) 1) : Hironaka.HironakaG10FlatPolydiscAlgebra.holSubalgebra K := by
  by_cases hr : (r : ℝ) < 1
  · let h := radial_holomorphic_neighborhood hK hc g r hr
    let U := Classical.choose h
    have hU := Classical.choose_spec h
    exact Hironaka.HironakaG10FlatPolydiscAlgebra.restrict K hU.2.1
      (fun z => Hironaka.HironakaG10FlatPolydiscAlgebra.extendZero K g (radialPoint c r z)) hU.2.2.1
  · exact g

/-- The entire continuous-map value of the B(K) contraction is literal radial composition. -/
theorem radialHolomorphic_coe
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : Set E} [CompactSpace K] (hK : Convex ℝ K)
    {c : E} (hc : c ∈ interior K)
    (g : Hironaka.HironakaG10FlatPolydiscAlgebra.holSubalgebra K)
    (r : Set.Icc (0 : ℝ) 1) :
    (radialHolomorphic hK hc g r : C(K,ℂ)) = radialRestriction hK hc (g : C(K,ℂ)) r := by
  by_cases hr : (r : ℝ) < 1
  · ext z
    simp only [radialHolomorphic, hr, ↓reduceDIte]
    change Hironaka.HironakaG10FlatPolydiscAlgebra.extendZero K g
      (radialPoint c r z) = (g : C(K,ℂ)) ⟨radialPoint c r z, radialPoint_mem hK hc r z⟩
    exact Hironaka.HironakaG10FlatPolydiscAlgebra.extendZero_of_mem K g
      (radialPoint_mem hK hc r z)
  · have hr1 : r = ⟨1, by simp⟩ := Subtype.ext (le_antisymm r.property.2 (le_of_not_gt hr))
    subst r
    rw [radialRestriction_one]
    simp [radialHolomorphic]

/-- Fixed B(K) elements vary continuously in the actual B(K) norm. -/
theorem continuous_radialHolomorphic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : Set E} [CompactSpace K] (hK : Convex ℝ K)
    {c : E} (hc : c ∈ interior K)
    (g : Hironaka.HironakaG10FlatPolydiscAlgebra.holSubalgebra K) :
    Continuous (radialHolomorphic hK hc g) := by
  apply continuous_induced_rng.mpr
  have heq : (Subtype.val ∘ radialHolomorphic hK hc g) = radialRestriction hK hc (g : C(K,ℂ)) :=
    funext fun r => radialHolomorphic_coe hK hc g r
  rw [heq]
  exact continuous_radialRestriction hK hc (g : C(K,ℂ))

/-- The literal finite matrix multiplication operators of fixed B(K) entries
converge in operator norm along radial contraction. -/
theorem continuous_radialMatrixOperator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : Set E} [CompactSpace K] (hK : Convex ℝ K)
    {c : E} (hc : c ∈ interior K) {a b : ℕ}
    (G : Fin a → Fin b → Hironaka.HironakaG10FlatPolydiscAlgebra.holSubalgebra K) :
    Continuous (fun r => Hironaka.HironakaG10FlatPolydiscAlgebra.matrixOperator
      (fun i j => radialHolomorphic hK hc (G i j) r)) := by
  apply Hironaka.HironakaG10FlatPolydiscAlgebra.matrixOperatorCLM.continuous.comp
  exact continuous_pi fun i => continuous_pi fun j => continuous_radialHolomorphic hK hc (G i j)
end
end Hironaka.Analytic.Unibranch.HironakaG10RadialCompactConvergence
