import Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
import Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorTranslation
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
noncomputable section

def shiftJoint (d t : ℕ) (p : ComplexModel d) : ComplexModel d × ComplexModel t → ComplexModel d × ComplexModel t :=
  fun x => (p+x.1,x.2)

theorem continuous_shiftJoint (d t : ℕ) (p : ComplexModel d) : Continuous (shiftJoint d t p) :=
  (continuous_const.add continuous_fst).prodMk continuous_snd

theorem differentiable_shiftJoint (d t : ℕ) (p : ComplexModel d) : Differentiable ℂ (shiftJoint d t p) :=
  (differentiable_const p |>.add differentiable_fst).prodMk differentiable_snd

/-- Translating the same original matrix gives the translated source operator
on one actual neighbourhood of zero, without any new family assumption. -/
theorem sourceOperator_shift_eventually
    (d t : ℕ) {a b : ℕ} {K : Set (ComplexModel t)} [CompactSpace K]
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (p : ComplexModel d) (hp : ∀ z ∈ K, (p,z) ∈ O) :
    let O' := (shiftJoint d t p) ⁻¹' O
    let F' := fun i j x => F i j (shiftJoint d t p x)
    let hF' : ∀ i j, DifferentiableOn ℂ (F' i j) O' := fun i j =>
      (hF i j).comp (differentiable_shiftJoint d t p).differentiableOn (fun _ h => h)
    ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      sourceOperator d t (K₁ := K) hF' s = sourceOperator d t (K₁ := K) hF (p+s) := by
  let O' := (shiftJoint d t p) ⁻¹' O
  let F' := fun i j x => F i j (shiftJoint d t p x)
  let hF' : ∀ i j, DifferentiableOn ℂ (F' i j) O' := fun i j =>
    (hF i j).comp (differentiable_shiftJoint d t p).differentiableOn (fun _ h => h)
  have hnear : ∀ᶠ s in 𝓝 (0 : ComplexModel d), ∀ z ∈ K, (p+s,z) ∈ O := by
    have hbase := eventually_forall_mem_of_isOpen (isCompact_iff_compactSpace.mpr inferInstance) hO hp
    have hc : ContinuousAt (fun s : ComplexModel d => p+s) (0 : ComplexModel d) :=
      (show Continuous (fun s : ComplexModel d => p+s) from
        continuous_const.add continuous_id).continuousAt
    have ht : Tendsto (fun s : ComplexModel d => p+s) (𝓝 (0 : ComplexModel d)) (𝓝 p) := by
      simpa only [add_zero] using hc.tendsto
    exact ht.eventually hbase
  filter_upwards [hnear] with s hs
  have hs' : ∀ z ∈ K, (s,z) ∈ O' := hs
  change matrixOperator (fun i j => restrictParam K (hF' i j) s) =
    matrixOperator (fun i j => restrictParam K (hF i j) (p+s))
  apply congrArg matrixOperator
  funext i j
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  rw [restrictParam_apply K (hF' i j) hs' z, restrictParam_apply K (hF i j) hs z]
  rfl
end
end Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorTranslation
