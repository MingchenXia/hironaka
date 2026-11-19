import Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorTranslation
import Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10NativeFibreRestriction
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  HironakaG10FlatResolutionStart Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
noncomputable section

theorem fibre_holomorphic (d t : ℕ) {a b : ℕ}
    {K₀ : Set (ComplexModel t)} {O : Set (ComplexModel d × ComplexModel t)}
    (hO : IsOpen O) {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O) (p : ComplexModel d)
    (hp : ∀ z ∈ K₀, (p,z) ∈ O) :
    ∀ i j, DifferentiableOn ℂ (fun x => F i j (p,x)) (interior K₀) := by
  intro i j x hx
  have hxO := hp x (interior_subset hx)
  exact ((hF i j (p,x) hxO).differentiableAt (hO.mem_nhds hxO)).comp x
    ((differentiableAt_const p).prodMk differentiableAt_id) |>.differentiableWithinAt

theorem restrictParam_eq_fibreRestriction (d t : ℕ) {a b : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₁] (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O) (p : ComplexModel d)
    (hp : ∀ z ∈ K₀, (p,z) ∈ O) :
    (fun i j => restrictParam K₁ (hF i j) p) =
      restrictMatrix K₁ hK₁₀ (fun i j z => F i j (p,z)) (fibre_holomorphic d t hO hF p hp) := by
  funext i j
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  rw [restrictParam_apply K₁ (hF i j) (fun z hz => hp z (interior_subset (hK₁₀ hz))) z]
  rfl
end
end Hironaka.Analytic.Unibranch.HironakaG10NativeFibreRestriction
