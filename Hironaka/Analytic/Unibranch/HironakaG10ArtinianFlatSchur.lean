import Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
import Hironaka.Analytic.Unibranch.HironakaG10NilpotentKernelSchur
import Hironaka.Resolution.HironakaG10FlatResolutionStart
set_option autoImplicit false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ArtinianFlatSchur
open Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedEuclidean HironakaG10LocDirectPersistence
  HironakaG10LocFrischLocus
open Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10NilpotentKernelSchur
noncomputable section

local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] : Algebra ℂ (HolGerm X) :=
  (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

/-- The comparison inverses depend only on the initial exact fibre and work
for every flat nilpotent finite-parameter deformation of the same matrix. -/
theorem exists_fixed_flat_artinian_schur (n : ℕ) {a k c : Type}
    [Fintype a] [Fintype k] [Fintype c] [DecidableEq a] [DecidableEq k] [DecidableEq c]
    {K U : Set (EuclideanSpace ℂ (Fin n))} [CompactSpace K]
    (hK : K ∈ closedPolydiscs n) (hU : IsOpen U) (hKU : K ⊆ U)
    (F₀ : a → k → EuclideanSpace ℂ (Fin n) → ℂ)
    (G₀ : k → c → EuclideanSpace ℂ (Fin n) → ℂ)
    (hF₀ : ∀ i j, DifferentiableOn ℂ (F₀ i j) U)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) U)
    (hFG₀ : ∀ x ∈ U, ∀ i l, ∑ j, F₀ i j x * G₀ j l x = 0)
    (hex : DirectExact (restrictMatrix K hKU G₀ hG₀) (restrictMatrix K hKU F₀ hF₀)) :
    ∃ (R₀ : (k → holSubalgebra K) →L[ℂ] (c → holSubalgebra K))
      (S₀ : (a → holSubalgebra K) →L[ℂ] (k → holSubalgebra K)),
      (∀ e, matrixOperator (restrictMatrix K hKU G₀ hG₀)
        (R₀ (matrixOperator (restrictMatrix K hKU G₀ hG₀) e)) =
        matrixOperator (restrictMatrix K hKU G₀ hG₀) e) ∧
      (∀ e, matrixOperator (restrictMatrix K hKU F₀ hF₀)
        (S₀ (matrixOperator (restrictMatrix K hKU F₀ hF₀) e)) =
        matrixOperator (restrictMatrix K hKU F₀ hF₀) e) ∧
      ∀ (Q : Type) [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
        (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
        (ε : Q →ₐ[ℂ] ℂ) (_hnil : ∃ m : ℕ, (RingHom.ker ε.toRingHom) ^ m = ⊥)
        (F : a → k → EuclideanSpace ℂ (Fin n) → Q)
        (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
        (_hres : ∀ x ∈ U, ∀ i j, ε (F i j x) = F₀ i j x)
        (_hflat : ∀ z ∈ K, Module.Flat Q
          ((a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
            LinearMap.range (matrixGermMap b z F))),
        ∃ V, ∃ (_hV : IsOpen V), ∃ (hKV : K ⊆ V), ∃ (hVU : V ⊆ U),
          ∃ (G : k → c → EuclideanSpace ℂ (Fin n) → Q)
            (_hG : ∀ j l, DifferentiableOn ℂ (G j l) V),
            (∀ x ∈ V, ∀ i l, ∑ j, F i j x * G j l x = 0) ∧
            (∀ x ∈ V, ∀ j l, ε (G j l x) = G₀ j l x) ∧
            schurOp ((coefficientCLM (matrixOperator (restrictMatrix K hKU G₀ hG₀))).comp
                (coefficientCLM R₀))
              ((coefficientCLM (matrixOperator (restrictMatrix K hKU F₀ hF₀))).comp
                (coefficientCLM S₀)) (coefficientCLM S₀)
              (banachMatrixCLM b hKV F
                (fun i j => (hF i j).mono hVU)) = 0 := by
  obtain ⟨R₀,hR₀⟩ := hex.exists_generalizedInverse_g
  obtain ⟨S₀,hS₀⟩ := hex.exists_generalizedInverse_f
  refine ⟨R₀,S₀,hR₀,hS₀,?_⟩
  intro Q _ _ _ ι _ _ b ε hnil F hF hres hflat
  have hrel : ∀ z ∈ K, ∀ i l, ∀ᶠ x in 𝓝 z, ∑ j, ε (F i j x) * G₀ j l x = 0 := by
    intro z hz i l
    filter_upwards [hU.mem_nhds (hKU hz)] with x hx
    simpa only [hres x hx] using hFG₀ x hx i l
  obtain ⟨V,hV,hKV,hVU,G,hG,hFG,hGres⟩ :=
    exists_compact_relation_lift b ε hK hU hKU F G₀ hF hG₀ hrel hflat
  refine ⟨V,hV,hKV,hVU,G,hG,hFG,hGres,?_⟩
  have hfref : ∀ (z : K) i j,
      ε (F i j z) = ((restrictMatrix K hKU F₀ hF₀ i j : holSubalgebra K) : C(K,ℂ)) z := by
    intro z i j
    simpa [restrictMatrix] using hres z (hKU z.2) i j
  have hgref : ∀ (z : K) j l,
      ε (G j l z) = ((restrictMatrix K hKU G₀ hG₀ j l : holSubalgebra K) : C(K,ℂ)) z := by
    intro z j l
    simpa [restrictMatrix] using hGres z (hKV z.2) j l
  have hcomp : ∀ e, matrixOperator (restrictMatrix K hKU F₀ hF₀)
      (matrixOperator (restrictMatrix K hKU G₀ hG₀) e) = 0 :=
    matrixOperator_comp_apply _ _ hex.comp
  have hzero := banachMatrix_comp_eq_zero b hKV F G
    (fun i j => (hF i j).mono hVU) hG (fun z i l => hFG z (hKV z.2) i l)
  apply schurOp_eq_zero_of_nilpotent_kernel_extension b
    (matrixOperator (restrictMatrix K hKU G₀ hG₀))
    (matrixOperator (restrictMatrix K hKU F₀ hF₀)) R₀ S₀ hR₀ hS₀ hcomp hex.exact
    (RingHom.ker ε.toRingHom) hnil
    (banachMatrixCLM b hKV F (fun i j => (hF i j).mono hVU))
    (banachMatrixLinear b hKV F (fun i j => (hF i j).mono hVU))
    (banachMatrixCLM b hKV G hG) (banachMatrixLinear b hKV G hG)
  · intro x; rfl
  · intro x; rfl
  · exact banachMatrix_reduction_error b ε hKV F (fun i j => (hF i j).mono hVU)
      (restrictMatrix K hKU F₀ hF₀) hfref
  · exact banachMatrix_reduction_error b ε hKV G hG (restrictMatrix K hKU G₀ hG₀) hgref
  · intro x
    exact congrFun (congrArg DFunLike.coe hzero) x
end
end Hironaka.Analytic.Unibranch.HironakaG10ArtinianFlatSchur
