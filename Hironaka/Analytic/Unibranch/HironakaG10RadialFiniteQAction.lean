import Hironaka.Analytic.Unibranch.HironakaG10RadialCompactConvergence
import Hironaka.Analytic.Unibranch.HironakaG10ContinuousBlockAction
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10RadialFiniteQAction
open Hironaka.HironakaG10FlatPolydiscAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10RadialCompactConvergence
  Hironaka.Analytic.Unibranch.HironakaG10ContinuousBlockAction
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
noncomputable section

variable {Q X ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
  {K U₀ : Set X} [CompactSpace K] {a k : ℕ}

/-- Literal finite-Q coefficient action built from radial restrictions of
its original actual block entries. -/
def radialFiniteQAction (basis : Module.Basis ι ℂ Q) (hKU₀ : K ⊆ U₀)
    (hconv : Convex ℝ K) {c : X} (hc : c ∈ interior K)
    (F : Fin a → Fin k → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U₀)
    (r : Set.Icc (0 : ℝ) 1) :
    (ι → Fin k → holSubalgebra K) →L[ℂ] (ι → Fin a → holSubalgebra K) :=
  blockAction (fun p q => radialHolomorphic hconv hc (banachBlockMatrix basis hKU₀ F hF p q) r)

omit [DecidableEq ι] in
/-- The actual finite-Q coefficient action varies in operator norm. -/
theorem continuous_radialFiniteQAction (basis : Module.Basis ι ℂ Q) (hKU₀ : K ⊆ U₀)
    (hconv : Convex ℝ K) {c : X} (hc : c ∈ interior K)
    (F : Fin a → Fin k → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U₀) :
    Continuous (radialFiniteQAction basis hKU₀ hconv hc F hF) := by
  apply continuous_blockAction.comp
  exact continuous_pi fun p => continuous_pi fun q =>
    continuous_radialHolomorphic hconv hc (banachBlockMatrix basis hKU₀ F hF p q)

omit [DecidableEq ι] in
/-- At the endpoint this IS the original literal coefficient action. -/
theorem radialFiniteQAction_one (basis : Module.Basis ι ℂ Q) (hKU₀ : K ⊆ U₀)
    (hconv : Convex ℝ K) {c : X} (hc : c ∈ interior K)
    (F : Fin a → Fin k → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U₀) :
    radialFiniteQAction basis hKU₀ hconv hc F hF ⟨1,by simp⟩ =
      banachMatrixCLM basis hKU₀ F hF := by
  have hB : (fun p q => radialHolomorphic hconv hc (banachBlockMatrix basis hKU₀ F hF p q) ⟨1,by simp⟩) =
      banachBlockMatrix basis hKU₀ F hF := by
    funext p q
    apply Subtype.ext
    rw [radialHolomorphic_coe, radialRestriction_one]
  change blockAction _ = banachMatrixCLM basis hKU₀ F hF
  rw [hB]
  rfl

omit [DecidableEq ι] in
/-- At every radial parameter the coefficient action is the literal action of
the radially pulled Q-valued matrix. -/
theorem radialFiniteQAction_eq_matrix (basis : Module.Basis ι ℂ Q) (hU₀ : IsOpen U₀) (hKU₀ : K ⊆ U₀)
    (hconv : Convex ℝ K) {c : X} (hc : c ∈ interior K)
    (F : Fin a → Fin k → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U₀)
    (r : Set.Icc (0 : ℝ) 1) :
    let U := (radialPoint c r) ⁻¹' U₀
    let Fr := fun i j x => F i j (radialPoint c r x)
    let hKU : K ⊆ U := fun z hz => hKU₀ (radialPoint_mem hconv hc r ⟨z,hz⟩)
    let hFr : ∀ i j, DifferentiableOn ℂ (Fr i j) U := fun i j =>
      (hF i j).comp (radialPoint_differentiable c r).differentiableOn (fun _ hx => hx)
    radialFiniteQAction basis hKU₀ hconv hc F hF r = banachMatrixCLM basis hKU Fr hFr := by
  dsimp only
  have hB : (fun p q => radialHolomorphic hconv hc (banachBlockMatrix basis hKU₀ F hF p q) r) =
      banachBlockMatrix (U := (radialPoint c r) ⁻¹' U₀) basis (fun z (hz : z ∈ K) => hKU₀ (radialPoint_mem hconv hc r ⟨z,hz⟩))
        (fun i j x => F i j (radialPoint c r x))
        (fun i j x (hx : x ∈ (radialPoint c r) ⁻¹' U₀) =>
          (((hF i j).differentiableAt (hU₀.mem_nhds hx)).comp x
            (radialPoint_differentiable c r).differentiableAt).differentiableWithinAt) := by
    funext p q
    apply Subtype.ext
    rw [radialHolomorphic_coe]
    ext z
    rfl
  change blockAction _ = _
  rw [hB]
  rfl
end
end Hironaka.Analytic.Unibranch.HironakaG10RadialFiniteQAction
