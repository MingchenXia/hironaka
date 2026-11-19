import Hironaka.Analytic.Unibranch.HironakaG10RadialFiniteQAction
import Hironaka.Analytic.Unibranch.HironakaG10RadialCompactRelationLift
import Hironaka.Analytic.Unibranch.HironakaG10RadialSequence
import Hironaka.Analytic.Unibranch.HironakaG10SchurOperatorLimit
import Hironaka.Analytic.Unibranch.HironakaG10VaryingArtinianRelationSchurZero
import Hironaka.Analytic.Unibranch.HironakaG10BanachMatrixRestrictionIndependence

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10RadialSchurLimit
open Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPrivilegedEuclidean
  HironakaG10FlatResolutionStart HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10RadialCompactConvergence
  Hironaka.Analytic.Unibranch.HironakaG10RadialCompactRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10RadialFiniteQAction
  Hironaka.Analytic.Unibranch.HironakaG10SchurOperatorLimit
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10VaryingArtinianRelationSchurZero
  Hironaka.Analytic.Unibranch.HironakaG10BanachMatrixRestrictionIndependence
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
noncomputable section

/-- The actual contracted relation gives zero for the literal old coefficient
Schur operator, provided both comparison operators at that radius are invertible. -/
theorem radially_contracted_flat_forces_schur_zero
    {Q ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (basis : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ n, (RingHom.ker ε.toRingHom) ^ n = ⊥)
    (n : ℕ) {a k m : ℕ} {K U₀ : Set (EuclideanSpace ℂ (Fin n))}
    [CompactSpace K] (hK : K ∈ closedPolydiscs n) (hconv : Convex ℝ K)
    {c : EuclideanSpace ℂ (Fin n)} (hc : c ∈ interior K)
    (hU₀ : IsOpen U₀) (hKU₀ : K ⊆ U₀)
    (F₀ : Fin a → Fin k → holSubalgebra K) (G₀ : Fin k → Fin m → holSubalgebra K)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin k → holSubalgebra K) →L[ℂ] (Fin m → holSubalgebra K))
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin k → holSubalgebra K))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (Gr : Fin k → Fin m → holSubalgebra K)
    (F : Fin a → Fin k → EuclideanSpace ℂ (Fin n) → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U₀)
    (hrel : ∀ z ∈ K, ∀ i l, ∑ j, ε (F i j z) * extendZero K (Gr j l) z = 0)
    (hflat : ∀ z ∈ K, Module.Flat Q
      ((Fin a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
        LinearMap.range (matrixGermMap basis z F)))
    (r : Set.Icc (0 : ℝ) 1) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1)
    (hRef : (opA ((matrixOperator G₀).comp R₀) R₀
      (matrixOperator (fun j l => radialHolomorphic hconv hc (Gr j l) r))).IsInvertible)
    (hC : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (radialFiniteQAction basis hKU₀ hconv hc F hF r)).IsInvertible) :
    schurOp ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (radialFiniteQAction basis hKU₀ hconv hc F hF r) = 0 := by
  obtain ⟨V,hVo,hKV,G,hG,hFG,hred⟩ :=
    exists_radially_contracted_compact_relation_lift basis ε n hK hconv hc hU₀ hKU₀
      r hr0 hr1 F Gr hF hrel hflat
  let U := V ∩ (radialPoint c r) ⁻¹' U₀
  have hKU : K ⊆ U := fun z hz => ⟨hKV hz, hKU₀ (radialPoint_mem hconv hc r ⟨z,hz⟩)⟩
  let Fr := fun i j x => F i j (radialPoint c r x)
  have hFr : ∀ i j, DifferentiableOn ℂ (Fr i j) U := fun i j =>
    (hF i j).comp (radialPoint_differentiable c r).differentiableOn (fun x hx => hx.2)
  have hGu : ∀ i j, DifferentiableOn ℂ (G i j) U := fun i j => (hG i j).mono inter_subset_left
  have haction : radialFiniteQAction basis hKU₀ hconv hc F hF r =
      banachMatrixCLM basis hKU Fr hFr := by
    rw [radialFiniteQAction_eq_matrix basis hU₀ hKU₀ hconv hc F hF r]
    exact banachMatrixCLM_eq_of_windows basis _ _ Fr _ _
  have hC' : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU Fr hFr)).IsInvertible := by rw [← haction]; exact hC
  have hred' : ∀ (z : K) j l, ε (G j l z) =
      ((radialHolomorphic hconv hc (Gr j l) r : holSubalgebra K) : C(K,ℂ)) z := by
    intro z j l
    rw [hred z (hKV z.property) j l, radialHolomorphic_coe]
    change extendZero K (Gr j l) (radialPoint c r z) = _
    exact extendZero_of_mem K (Gr j l) (radialPoint_mem hconv hc r z)
  have hzero := artinian_relation_with_invertible_current_reference_forces_old_schur_zero
    hKU basis ε hnil F₀ G₀ hex R₀ S₀ hR hS _ hRef Fr G hFr hGu
    (fun z i l => hFG z (hKV z.property) i l) hred' hC'
  rw [← haction] at hzero
  exact hzero
theorem continuousAt_opC
    {E₁ E₀ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S : E₀ →L[ℂ] E₁)
    (f : E₁ →L[ℂ] E₀) : ContinuousAt (fun g => opC P Q S g) f := by
  unfold opC
  exact (continuousAt_id.clm_comp continuousAt_const).add continuousAt_const

/-- Norm convergence to an invertible operator implies eventual invertibility. -/
theorem eventually_invertible_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {α : Type*} (l : Filter α) (T : α → E →L[ℂ] E) (T₀ : E →L[ℂ] E)
    (hT : Tendsto T l (𝓝 T₀)) (hT₀ : T₀.IsInvertible) :
    ∀ᶠ x in l, (T x).IsInvertible := by
  change T ⁻¹' {S : E →L[ℂ] E | S.IsInvertible} ∈ l
  apply hT
  obtain ⟨e, he⟩ := hT₀
  have hn : Set.range ((↑) : (E ≃L[ℂ] E) → E →L[ℂ] E) ∈ 𝓝 T₀ := by
    rw [← he]
    exact ContinuousLinearEquiv.nhds e
  filter_upwards [hn] with T ⟨e', he'⟩
  exact ⟨e', he'⟩

theorem flat_forces_old_schur_zero_of_radial_limit
    {Q ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (basis : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ n, (RingHom.ker ε.toRingHom) ^ n = ⊥)
    (n : ℕ) {a k m : ℕ} {K U₀ : Set (EuclideanSpace ℂ (Fin n))}
    [CompactSpace K] (hK : K ∈ closedPolydiscs n) (hconv : Convex ℝ K)
    {c : EuclideanSpace ℂ (Fin n)} (hc : c ∈ interior K)
    (hU₀ : IsOpen U₀) (hKU₀ : K ⊆ U₀)
    (F₀ : Fin a → Fin k → holSubalgebra K) (G₀ : Fin k → Fin m → holSubalgebra K)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin k → holSubalgebra K) →L[ℂ] (Fin m → holSubalgebra K))
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin k → holSubalgebra K))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (Gr : Fin k → Fin m → holSubalgebra K)
    (F : Fin a → Fin k → EuclideanSpace ℂ (Fin n) → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U₀)
    (hrel : ∀ z ∈ K, ∀ i l, ∑ j, ε (F i j z) * extendZero K (Gr j l) z = 0)
    (hflat : ∀ z ∈ K, Module.Flat Q
      ((Fin a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
        LinearMap.range (matrixGermMap basis z F)))
    (hRef : (opA ((matrixOperator G₀).comp R₀) R₀ (matrixOperator Gr)).IsInvertible)
    (hC : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU₀ F hF)).IsInvertible)
    {α : Type} (l : Filter α) [NeBot l] (t : α → Set.Icc (0 : ℝ) 1)
    (ht : Tendsto t l (𝓝 ⟨1,by simp⟩))
    (hstrict : ∀ᶠ x in l, 0 < (t x : ℝ) ∧ (t x : ℝ) < 1) :
    schurOp ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU₀ F hF) = 0 := by
  have hone : (fun j l => radialHolomorphic hconv hc (Gr j l) ⟨1,by simp⟩) = Gr := by
    funext j l
    apply Subtype.ext
    rw [radialHolomorphic_coe, radialRestriction_one]
  have hFt : Tendsto (fun x => radialFiniteQAction basis hKU₀ hconv hc F hF (t x)) l
      (𝓝 (banachMatrixCLM basis hKU₀ F hF)) := by
    have H := (continuous_radialFiniteQAction basis hKU₀ hconv hc F hF).continuousAt.tendsto.comp ht
    simpa only [radialFiniteQAction_one, Function.comp_def] using H
  have hGt : Tendsto (fun x => matrixOperator (fun j l => radialHolomorphic hconv hc (Gr j l) (t x))) l
      (𝓝 (matrixOperator Gr)) := by
    have H := (continuous_radialMatrixOperator hconv hc Gr).continuousAt.tendsto.comp ht
    simpa only [hone, Function.comp_def] using H
  have hAt : Tendsto (fun x => opA ((matrixOperator G₀).comp R₀) R₀
      (matrixOperator (fun j l => radialHolomorphic hconv hc (Gr j l) (t x)))) l
      (𝓝 (opA ((matrixOperator G₀).comp R₀) R₀ (matrixOperator Gr))) := by
    have hcont : Continuous (fun g => opA ((matrixOperator G₀).comp R₀) R₀ g) := by
      unfold opA
      exact (continuous_const.clm_comp (continuous_id.clm_comp continuous_const)).add continuous_const
    simpa only [Function.comp_def] using hcont.continuousAt.tendsto.comp hGt
  have hCt : Tendsto (fun x => opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (radialFiniteQAction basis hKU₀ hconv hc F hF (t x))) l
      (𝓝 (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU₀ F hF))) := by
    simpa only [Function.comp_def] using
      (continuousAt_opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
        ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
        (banachMatrixCLM basis hKU₀ F hF)).tendsto.comp hFt
  have hAi := eventually_invertible_of_tendsto l _ _ hAt hRef
  have hCi := eventually_invertible_of_tendsto l _ _ hCt hC
  apply schurOp_eq_zero_of_tendsto l _ _ _ _ hC _ hFt
  filter_upwards [hstrict, hAi, hCi] with x hx hax hcx
  exact radially_contracted_flat_forces_schur_zero basis ε hnil n hK hconv hc hU₀ hKU₀
    F₀ G₀ hex R₀ S₀ hR hS Gr F hF hrel hflat (t x) hx.1 hx.2 hax hcx
theorem flat_forces_old_schur_zero
    {Q ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (basis : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ n, (RingHom.ker ε.toRingHom) ^ n = ⊥)
    (n : ℕ) {a k m : ℕ} {K U₀ : Set (EuclideanSpace ℂ (Fin n))}
    [CompactSpace K] (hK : K ∈ closedPolydiscs n) (hconv : Convex ℝ K)
    {c : EuclideanSpace ℂ (Fin n)} (hc : c ∈ interior K)
    (hU₀ : IsOpen U₀) (hKU₀ : K ⊆ U₀)
    (F₀ : Fin a → Fin k → holSubalgebra K) (G₀ : Fin k → Fin m → holSubalgebra K)
    (hex : DirectExact G₀ F₀)
    (R₀ : (Fin k → holSubalgebra K) →L[ℂ] (Fin m → holSubalgebra K))
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin k → holSubalgebra K))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (Gr : Fin k → Fin m → holSubalgebra K)
    (F : Fin a → Fin k → EuclideanSpace ℂ (Fin n) → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U₀)
    (hrel : ∀ z ∈ K, ∀ i l, ∑ j, ε (F i j z) * extendZero K (Gr j l) z = 0)
    (hflat : ∀ z ∈ K, Module.Flat Q
      ((Fin a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
        LinearMap.range (matrixGermMap basis z F)))
    (hRef : (opA ((matrixOperator G₀).comp R₀) R₀ (matrixOperator Gr)).IsInvertible)
    (hC : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU₀ F hF)).IsInvertible)
 :
    schurOp ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKU₀ F hF) = 0 := by
  apply flat_forces_old_schur_zero_of_radial_limit basis ε hnil n hK hconv hc hU₀ hKU₀
    F₀ G₀ hex R₀ S₀ hR hS Gr F hF hrel hflat hRef hC atTop
    Hironaka.Analytic.Unibranch.HironakaG10RadialSequence.radii Hironaka.Analytic.Unibranch.HironakaG10RadialSequence.radii_tendsto
  exact Filter.Eventually.of_forall Hironaka.Analytic.Unibranch.HironakaG10RadialSequence.radii_strict
end
end Hironaka.Analytic.Unibranch.HironakaG10RadialSchurLimit
