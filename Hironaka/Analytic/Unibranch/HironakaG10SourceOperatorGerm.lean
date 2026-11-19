import Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur
import Hironaka.Analytic.Unibranch.HironakaG10SourceCoefficientOperator
import Hironaka.Resolution.HironakaG10FlatPolydiscParametric

/-! The actual original Banach matrix operator near its zero fibre. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
open Filter Set Metric
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  HironakaG10FlatResolutionStart
  Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur

/-- The original jointly holomorphic source matrix as a Banach-operator family. -/
noncomputable def sourceOperator (d t : ℕ) {a b : ℕ}
    {K₁ : Set (ComplexModel t)} [CompactSpace K₁]
    {O : Set (ComplexModel d × ComplexModel t)}
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O) :
    ComplexModel d → ((Fin b → holSubalgebra K₁) →L[ℂ] (Fin a → holSubalgebra K₁)) :=
  fun s => matrixOperator (fun i j => restrictParam K₁ (hF i j) s)

/-- The original source operator family is holomorphic near the zero parameter. -/
theorem sourceOperator_holomorphic (d t : ℕ) {a b : ℕ}
    {K₁ : Set (ComplexModel t)} [CompactSpace K₁]
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₁ : ∀ z ∈ K₁, (0,z) ∈ O) :
    ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (sourceOperator d t (K₁ := K₁) hF) s := by
  have hzero : DifferentiableOn ℂ (fun _ : ComplexModel d × ComplexModel t => (0 : ℂ)) O :=
    differentiableOn_const 0
  obtain ⟨δ,hδ,L,hL,hballs,hbound⟩ := exists_tube_bound K₁ hO hzero hK₁
  have hnear : ∀ᶠ s in 𝓝 (0 : ComplexModel d), ∀ z ∈ K₁, (s,z) ∈ O := by
    filter_upwards [ball_mem_nhds (0 : ComplexModel d) hδ] with s hs z hz
    apply hballs z hz
    simpa only [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hs
  filter_upwards [hnear] with s hs
  exact differentiableAt_matrixOperator_restrictParam K₁ hO hF hs

/-- Its value at zero is the literal original zero-fibre operator. -/
theorem sourceOperator_zero (d t : ℕ) {a b : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₁]
    (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O) :
    sourceOperator d t (K₁ := K₁) hF 0 =
      matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
        (zeroFibre_holomorphic d t hO hF hK₀)) := by
  change matrixOperator (fun i j => restrictParam K₁ (hF i j) 0) = _
  apply congrArg matrixOperator
  funext i j
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  rw [restrictParam_apply K₁ (hF i j) (fun z hz => hK₀ z (interior_subset (hK₁₀ hz))) z]
  rfl
end Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
