import Hironaka.Analytic.Unibranch.HironakaG10CompactWindowRestriction
import Hironaka.Analytic.Unibranch.HironakaG10InnerPolydiscCorrectedRelationLift
import Hironaka.Analytic.Unibranch.HironakaG10VaryingArtinianRelationSchurZero
import Hironaka.Analytic.Unibranch.HironakaG10BanachMatrixRestrictionIndependence

set_option autoImplicit false
open Set Filter
open scoped Topology BigOperators TensorProduct
set_option maxHeartbeats 2000000
namespace Hironaka.Analytic.Unibranch.HironakaG10InnerFlatSmallSchur
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus HironakaG10LocSheafExact
  OkaRelationSheaf HironakaG10FlatPrivilegedEuclidean
  Hironaka.Analytic.Unibranch.HironakaG10CompactWindowRestriction
  Hironaka.Analytic.Unibranch.HironakaG10InnerPolydiscCorrectedRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10VaryingArtinianRelationSchurZero
  Hironaka.Analytic.Unibranch.HironakaG10BanachMatrixRestrictionIndependence
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (EuclideanSpace ℂ (Fin n))) :=
  (HolGerm.constHom : ℂ →+* HolGerm (EuclideanSpace ℂ (Fin n))).toAlgebra

/-- Actual flatness on the smaller closed polydisc forces the old small-window
coefficient Schur obstruction to vanish, provided the large corrected relation
is direct exact and its literal restriction has invertible comparison. -/
theorem inner_flat_forces_small_window_schur_zero
    {Q : Type*} {ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] {n a r c : ℕ}
    {L K U : Set (EuclideanSpace ℂ (Fin n))} [CompactSpace L] [CompactSpace K]
    (hK : K ∈ closedPolydiscs n) (hKL : K ⊆ interior L)
    (hU : IsOpen U) (hLU : L ⊆ U)
    (basis : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ m, (RingHom.ker ε.toRingHom)^m = ⊥)
    (F : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → Q)
    (Fr : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → ℂ)
    (Gr : Fin r → Fin c → holSubalgebra L)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hFr : ∀ i j, DifferentiableOn ℂ (Fr i j) U)
    (hres : ∀ z ∈ U, ∀ i j, ε (F i j z) = Fr i j z)
    (hexL : DirectExact Gr (restrictMatrix L hLU Fr hFr))
    (hflat : ∀ z ∈ K, Module.Flat Q
      ((Fin a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
        LinearMap.range (matrixGermMap basis z F)))
    (F₀ : Fin a → Fin r → holSubalgebra K) (G₀ : Fin r → Fin c → holSubalgebra K)
    (hexK : DirectExact G₀ F₀)
    (R₀ : (Fin r → holSubalgebra K) →L[ℂ] (Fin c → holSubalgebra K))
    (S₀ : (Fin a → holSubalgebra K) →L[ℂ] (Fin r → holSubalgebra K))
    (hR : ∀ e, matrixOperator G₀ (R₀ (matrixOperator G₀ e)) = matrixOperator G₀ e)
    (hS : ∀ e, matrixOperator F₀ (S₀ (matrixOperator F₀ e)) = matrixOperator F₀ e)
    (hRef : (opA ((matrixOperator G₀).comp R₀) R₀
      (matrixOperator (fun i j => windowRestriction (hKL.trans interior_subset) (Gr i j)))).IsInvertible)
    (hC : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis ((hKL.trans interior_subset).trans hLU) F hF)).IsInvertible) :
    schurOp ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis ((hKL.trans interior_subset).trans hLU) F hF) = 0 := by
  obtain ⟨V,hV,hKV,hVL,G,hG,hFG,hred⟩ :=
    exists_inner_polydisc_corrected_relation_lift hK hKL hU hLU basis ε F Fr Gr hF hFr hres hexL hflat
  have hVU : V ⊆ U := hVL.trans (interior_subset.trans hLU)
  let hFV : ∀ i j, DifferentiableOn ℂ (F i j) V := fun i j => (hF i j).mono hVU
  have hmatrix : banachMatrixCLM basis hKV F hFV =
      banachMatrixCLM basis ((hKL.trans interior_subset).trans hLU) F hF :=
    banachMatrixCLM_eq_of_windows basis hKV ((hKL.trans interior_subset).trans hLU) F hFV hF
  have hC' : (opC ((coefficientCLM (matrixOperator G₀)).comp (coefficientCLM R₀))
      ((coefficientCLM (matrixOperator F₀)).comp (coefficientCLM S₀)) (coefficientCLM S₀)
      (banachMatrixCLM basis hKV F hFV)).IsInvertible := by rw [hmatrix]; exact hC
  have hred' : ∀ (z : K) i j, ε (G i j z) =
      ((windowRestriction (hKL.trans interior_subset) (Gr i j) : holSubalgebra K) : C(K,ℂ)) z := by
    intro z i j
    rw [hred z (hKV z.property) i j]
    exact bkFun_windowRestriction (hKL.trans interior_subset) Gr z i j
  have hSchur := artinian_relation_with_invertible_current_reference_forces_old_schur_zero
    hKV basis ε hnil F₀ G₀ hexK R₀ S₀ hR hS
    (fun i j => windowRestriction (hKL.trans interior_subset) (Gr i j)) hRef F G hFV hG
    (fun z i j => hFG z (hKV z.property) i j) hred' hC'
  rw [hmatrix] at hSchur
  exact hSchur

end
end Hironaka.Analytic.Unibranch.HironakaG10InnerFlatSmallSchur
