import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections
import Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm

/-! The scalar Schur sections of the original jointly holomorphic matrix. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus HironakaG10LocSectionNoether
  HironakaSmoothCentreRealDomainActualSheafStalk
  Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur
  Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorGerm
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections
namespace Hironaka.Analytic.Unibranch.HironakaG10NativeSourceSchurScalarSections
noncomputable section

/-- The original jointly holomorphic matrix and its original directly exact
zero-fibre start internally yield fixed inverses and ONE family of actual
scalar Schur sections, locally finitely generated near every parameter point.
No flatness assumption is made on the source family. -/
theorem original_source_schur_scalar_sections
    (d t : ℕ) {a b c : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₁]
    (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (G₀ : Fin b → Fin c → ComplexModel t → ℂ)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) (interior K₀))
    (hex : DirectExact (restrictMatrix K₁ hK₁₀ G₀ hG₀)
      (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x)) (zeroFibre_holomorphic d t hO hF hK₀))) :
    let f₀ := matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
      (zeroFibre_holomorphic d t hO hF hK₀))
    let g₀ := matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀)
    let f := sourceOperator d t (K₁ := K₁) hF
    ∃ (R₀ : (Fin b → holSubalgebra K₁) →L[ℂ] (Fin c → holSubalgebra K₁))
      (S₀ : (Fin a → holSubalgebra K₁) →L[ℂ] (Fin b → holSubalgebra K₁)),
      (∀ e, g₀ (R₀ (g₀ e)) = g₀ e) ∧
      (∀ e, f₀ (S₀ (f₀ e)) = f₀ e) ∧
      ∃ (U : Opens (ComplexModel d)) (_h0 : (0 : ComplexModel d) ∈ U)
        (hSU : DifferentiableOn ℂ (fun z => schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ (f z)) U),
        let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) U
        let s : (Fin b → holSubalgebra K₁) × ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
          fun q => operatorScalarSection d U (fun z => schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ (f z)) hSU q.1 q.2
        ∀ p : U, ∃ T : Finset ((Fin b → holSubalgebra K₁) × ((Fin a → holSubalgebra K₁) →L[ℂ] ℂ)),
          ∀ᶠ y in 𝓝 p, spanFamily s univ y = spanFamily s (T : Set _) y := by
  let f₀ := matrixOperator (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x))
    (zeroFibre_holomorphic d t hO hF hK₀))
  let g₀ := matrixOperator (restrictMatrix K₁ hK₁₀ G₀ hG₀)
  let f := sourceOperator d t (K₁ := K₁) hF
  obtain ⟨S₀,hS⟩ := hex.exists_generalizedInverse_f
  obtain ⟨R₀,hR⟩ := hex.exists_generalizedInverse_g
  have hK₁O : ∀ z ∈ K₁, (0,z) ∈ O := fun z hz => hK₀ z (interior_subset (hK₁₀ hz))
  have hf : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f s :=
    sourceOperator_holomorphic d t hO hF hK₁O
  have hf0 : f 0 = f₀ := sourceOperator_zero d t hK₁₀ hO hF hK₀
  have hcomp : ∀ e, f₀ (g₀ e) = 0 := matrixOperator_comp_apply _ _ hex.comp
  have hC0 : opC (g₀.comp R₀) (f₀.comp S₀) S₀ (f 0) = ContinuousLinearMap.id ℂ _ := by
    rw [hf0]
    exact opC_self hcomp
  exact ⟨R₀,S₀,hR,hS,exists_schurScalarSections_near d (g₀.comp R₀) (f₀.comp S₀) S₀ f hf hC0⟩
end
end Hironaka.Analytic.Unibranch.HironakaG10NativeSourceSchurScalarSections
