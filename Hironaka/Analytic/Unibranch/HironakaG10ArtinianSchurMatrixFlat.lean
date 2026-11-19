import Hironaka.Analytic.Unibranch.HironakaG10ArtinianSchurHolomorphicRelation
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrixFlat

/-! Zero finite-coefficient Schur obstruction forces actual matrix-germ
flatness on the interior wherever the original reference germ is exact. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ArtinianSchurMatrixFlat
open Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianSchurHolomorphicRelation
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrixFlat
noncomputable section
local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] :
    Algebra ℂ (HolGerm X) := (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

/-- The exactness assumptions are for the literal original scalar germ
complex at each point; the conclusion is the actual Artinian matrix cokernel. -/
theorem matrixGermMap_flat_of_artinian_schur_zero
    {Q X ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
    {K U : Set X} [CompactSpace K] (hU : IsOpen U) (hKU : K ⊆ U) {a r c : ℕ}
    (F₀ : Fin a → Fin r → X → ℂ) (G₀ : Fin r → Fin c → X → ℂ)
    (hF₀ : ∀ i j, DifferentiableOn ℂ (F₀ i j) U)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) U)
    (hex : DirectExact (restrictMatrix K hKU G₀ hG₀) (restrictMatrix K hKU F₀ hF₀))
    (R₀ : (Fin r → holSubalgebra K) →L[ℂ] (Fin c → holSubalgebra K))
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin r → holSubalgebra K))
    (hR : ∀ x, matrixOperator (restrictMatrix K hKU G₀ hG₀)
      (R₀ (matrixOperator (restrictMatrix K hKU G₀ hG₀) x)) =
      matrixOperator (restrictMatrix K hKU G₀ hG₀) x)
    (hS : ∀ x, matrixOperator (restrictMatrix K hKU F₀ hF₀)
      (S₀ (matrixOperator (restrictMatrix K hKU F₀ hF₀) x)) =
      matrixOperator (restrictMatrix K hKU F₀ hF₀) x)
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ n : ℕ, (RingHom.ker ε.toRingHom) ^ n = ⊥)
    (F : Fin a → Fin r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hres : ∀ x ∈ U, ∀ i j, ε (F i j x) = F₀ i j x)
    (hSchur : schurOp ((coefficientCLM (matrixOperator (restrictMatrix K hKU G₀ hG₀))).comp
      (coefficientCLM R₀)) ((coefficientCLM (matrixOperator (restrictMatrix K hKU F₀ hF₀))).comp
      (coefficientCLM S₀)) (coefficientCLM S₀) (banachMatrixCLM b hKU F hF) = 0)
    (hcomp : ∀ z ∈ interior K, ∀ w,
      (Matrix.mulVecLin (fun i j => germAt z (F₀ i j)))
        ((Matrix.mulVecLin (fun j l => germAt z (G₀ j l))) w) = 0)
    (hExact : ∀ z ∈ interior K, ∀ u,
      (Matrix.mulVecLin (fun i j => germAt z (F₀ i j))) u = 0 →
        ∃ w, (Matrix.mulVecLin (fun j l => germAt z (G₀ j l))) w = u) :
    ∀ z ∈ interior K, Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm X) ⧸
      LinearMap.range (matrixGermMap b z F)) := by
  have hresK : ∀ (z : K) i j, ε (F i j z) =
      ((restrictMatrix K hKU F₀ hF₀ i j : holSubalgebra K) : C(K,ℂ)) z := by
    intro z i j
    simpa [restrictMatrix] using hres z (hKU z.2) i j
  obtain ⟨G,hG,hFG,hresG⟩ := exists_holomorphic_relation_of_artinian_schur_zero
    (Q := Q) (X := X) (ι := ι)
    hKU (restrictMatrix K hKU F₀ hF₀) (restrictMatrix K hKU G₀ hG₀) hex R₀ S₀ hR hS
    b ε hnil F hF hresK hSchur
  intro z hz
  have hzU : z ∈ U := hKU (interior_subset hz)
  have hFz (i j) : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (F i j) x := by
    filter_upwards [hU.mem_nhds hzU] with x hx
    exact (hF i j x hx).differentiableAt (hU.mem_nhds hx)
  have hGz (j l) : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (G j l) x := by
    filter_upwards [isOpen_interior.mem_nhds hz] with x hx
    exact (hG j l x hx).differentiableAt (isOpen_interior.mem_nhds hx)
  have hF₀z (i j) : HolAt (F₀ i j) z := by
    filter_upwards [hU.mem_nhds hzU] with x hx
    exact (hF₀ i j x hx).differentiableAt (hU.mem_nhds hx)
  have hG₀z (j l) : HolAt (G₀ j l) z := by
    filter_upwards [hU.mem_nhds hzU] with x hx
    exact (hG₀ j l x hx).differentiableAt (hU.mem_nhds hx)
  have hrF (i j) : ∀ᶠ x in 𝓝 z, ε (F i j x) = F₀ i j x := by
    filter_upwards [hU.mem_nhds hzU] with x hx
    exact hres x hx i j
  have hrG (j l) : ∀ᶠ x in 𝓝 z, ε (G j l x) = G₀ j l x := by
    filter_upwards [isOpen_interior.mem_nhds hz] with x hx
    simpa [restrictMatrix] using hresG x hx j l
  have hFGz : ∀ᶠ x in 𝓝 z, ∀ i l, ∑ j, F i j x * G j l x = 0 := by
    filter_upwards [isOpen_interior.mem_nhds hz] with x hx
    exact hFG x hx
  exact matrixGermMap_flat_of_holomorphic_relation_lift (Q := Q) (X := X) (ι := ι) b ε hnil F G F₀ G₀
    hFz hGz hF₀z hG₀z hrF hrG hFGz (hcomp z hz) (hExact z hz)
end
end Hironaka.Analytic.Unibranch.HironakaG10ArtinianSchurMatrixFlat
