import Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurRelation
import Hironaka.Analytic.Unibranch.HironakaG10BKReferenceGerm
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrixFlat
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurMatrixFlat
open Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10LocFrischLocus
  HironakaG10LocDirectPersistence
  HironakaG10LocSheafExact HironakaG10FlatPrivilegedEuclidean
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrixFlat
  Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurRelation
  Hironaka.Analytic.Unibranch.HironakaG10BKReferenceGerm
noncomputable section
local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] :
    Algebra ℂ (HolGerm X) := (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

theorem matrixGermMap_flat_of_varying_schur_zero
    {Q ι : Type} {n : ℕ} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι]
    {K U : Set (EuclideanSpace ℂ (Fin n))} [CompactSpace K]
    (hK : K ∈ closedPolydiscs n) (hU : IsOpen U) (hKU : K ⊆ U) {a r c : ℕ}
    (F₀ : Fin a → Fin r → holSubalgebra K) (G₀ : Fin r → Fin c → holSubalgebra K)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin r → holSubalgebra K) →L[ℂ] (Fin c → holSubalgebra K))
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin r → holSubalgebra K))
    (hR : ∀ x, matrixOperator G₀ (R₀ (matrixOperator G₀ x)) = matrixOperator G₀ x)
    (hS : ∀ x, matrixOperator F₀ (S₀ (matrixOperator F₀ x)) = matrixOperator F₀ x)
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ n : ℕ, (RingHom.ker ε.toRingHom) ^ n = ⊥)
    (F : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (Fr : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → ℂ)
    (hFr : ∀ i j, DifferentiableOn ℂ (Fr i j) U)
    (hres : ∀ x ∈ U, ∀ i j, ε (F i j x) = Fr i j x)
    (hC : (opC ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
      (matrixOperator (restrictMatrix K hKU Fr hFr))).IsInvertible)
    (hCQ : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM b hKU F hF)).IsInvertible)
    (hSchur : schurOp ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM b hKU F hF) = 0)
    (hDirect : DirectExact
      (fun j l => kerSec ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
        (matrixOperator (restrictMatrix K hKU Fr hFr)) (fun j' => G₀ j' l) j)
      (restrictMatrix K hKU Fr hFr)) :
    ∀ z ∈ interior K, Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
      LinearMap.range (matrixGermMap b z F)) := by
  let Gr : Fin r → Fin c → holSubalgebra K := fun j l =>
    kerSec ((matrixOperator G₀).comp R₀) ((matrixOperator F₀).comp S₀) S₀
      (matrixOperator (restrictMatrix K hKU Fr hFr)) (fun j' => G₀ j' l) j
  have hresK : ∀ (z : K) i j, ε (F i j z) =
      ((restrictMatrix K hKU Fr hFr i j : holSubalgebra K) : C(K,ℂ)) z := by
    intro z i j
    simpa [restrictMatrix] using hres z (hKU z.2) i j
  obtain ⟨G,hG,hFG,hresG⟩ := exists_varying_schur_holomorphic_relation
    (Q := Q) (X := EuclideanSpace ℂ (Fin n)) (ι := ι)
    hKU F₀ G₀ hex R₀ S₀ hR hS b ε F hF (restrictMatrix K hKU Fr hFr) hresK hC hCQ hSchur
  intro z hz
  have hzU : z ∈ U := hKU (interior_subset hz)
  have hFz (i j) : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (F i j) x := by
    filter_upwards [hU.mem_nhds hzU] with x hx
    exact (hF i j x hx).differentiableAt (hU.mem_nhds hx)
  have hGz (j l) : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (G j l) x := by
    filter_upwards [isOpen_interior.mem_nhds hz] with x hx
    exact (hG j l x hx).differentiableAt (isOpen_interior.mem_nhds hx)
  have hFrz (i j) : HolAt (Fr i j) z := by
    filter_upwards [hU.mem_nhds hzU] with x hx
    exact (hFr i j x hx).differentiableAt (hU.mem_nhds hx)
  have hGrz (j l) : HolAt (bkFun K Gr j l) z := holAt_bkFun K Gr j l hz
  have hrF (i j) : ∀ᶠ x in 𝓝 z, ε (F i j x) = Fr i j x := by
    filter_upwards [hU.mem_nhds hzU] with x hx
    exact hres x hx i j
  have hrG (j l) : ∀ᶠ x in 𝓝 z, ε (G j l x) = bkFun K Gr j l x := by
    filter_upwards [isOpen_interior.mem_nhds hz] with x hx
    simpa [bkFun, extendZero_of_mem K _ (interior_subset hx)] using hresG x hx j l
  have hFGz : ∀ᶠ x in 𝓝 z, ∀ i l, ∑ j, F i j x * G j l x = 0 := by
    filter_upwards [isOpen_interior.mem_nhds hz] with x hx
    exact hFG x hx
  exact matrixGermMap_flat_of_holomorphic_relation_lift b ε hnil F G Fr (bkFun K Gr)
    hFz hGz hFrz hGrz hrF hrG hFGz
    (fun w => directExact_bk_germ_comp hU hKU Fr Gr hFr hDirect hz w)
    (fun u hu => directExact_bk_germ_exact hK hU hKU Fr Gr hFr hDirect hz u hu)
end
end Hironaka.Analytic.Unibranch.HironakaG10VaryingSchurMatrixFlat
