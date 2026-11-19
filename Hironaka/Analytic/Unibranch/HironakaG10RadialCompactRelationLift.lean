import Hironaka.Analytic.Unibranch.HironakaG10RadialCompactConvergence
import Hironaka.Analytic.Unibranch.HironakaG10AffineTensorGermFlat

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10RadialCompactRelationLift
open Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10FlatPrivilegedEuclidean HironakaG10FlatPolydiscAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10RadialCompactConvergence
  Hironaka.Analytic.Unibranch.HironakaG10AffineTensorGermFlat
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (EuclideanSpace ℂ (Fin n))) :=
  (HolGerm.constHom : ℂ →+* HolGerm (EuclideanSpace ℂ (Fin n))).toAlgebra

/-- Flatness at the literal contracted points lifts any continuous K-reference
relation after contraction to one Q-valued holomorphic relation near all K. -/
theorem exists_radially_contracted_compact_relation_lift
    {Q ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (basis : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (n : ℕ) {a k m : ℕ} {K U₀ : Set (EuclideanSpace ℂ (Fin n))}
    [CompactSpace K] (hK : K ∈ closedPolydiscs n) (hconv : Convex ℝ K)
    {c : EuclideanSpace ℂ (Fin n)} (hc : c ∈ interior K)
    (hU₀ : IsOpen U₀) (hKU₀ : K ⊆ U₀)
    (r : Set.Icc (0 : ℝ) 1) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1)
    (F : Fin a → Fin k → EuclideanSpace ℂ (Fin n) → Q)
    (G₀ : Fin k → Fin m → holSubalgebra K)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U₀)
    (hrel : ∀ z ∈ K, ∀ i l, ∑ j, ε (F i j z) * extendZero K (G₀ j l) z = 0)
    (hflat : ∀ z ∈ K, Module.Flat Q
      ((Fin a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
        LinearMap.range (matrixGermMap basis z F))) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧
      ∃ G : Fin k → Fin m → EuclideanSpace ℂ (Fin n) → Q,
        (∀ j l, DifferentiableOn ℂ (G j l) V) ∧
        (∀ z ∈ V, ∀ i l, ∑ j, F i j (radialPoint c r z) * G j l z = 0) ∧
        ∀ z ∈ V, ∀ j l, ε (G j l z) = extendZero K (G₀ j l) (radialPoint c r z) := by
  let δ := radialPoint c (r : ℝ)
  let U : Set (EuclideanSpace ℂ (Fin n)) := δ ⁻¹' interior K
  have hd : Differentiable ℂ δ := radialPoint_differentiable c r
  have hU : IsOpen U := isOpen_interior.preimage hd.continuous
  have hKU : K ⊆ U := fun z hz => radialPoint_mem_interior hconv hc r hr1 ⟨z,hz⟩
  let Fr := fun i j z => F i j (δ z)
  let Gr := fun j l z => extendZero K (G₀ j l) (δ z)
  have hFr : ∀ i j, DifferentiableOn ℂ (Fr i j) U := by
    intro i j
    exact (hF i j).comp hd.differentiableOn (fun _ hx => hKU₀ (interior_subset hx))
  have hGr : ∀ j l, DifferentiableOn ℂ (Gr j l) U := by
    intro j l
    exact (G₀ j l).property.comp hd.differentiableOn (fun _ hx => hx)
  have hrel' : ∀ z ∈ K, ∀ i l, ∀ᶠ x in 𝓝 z, ∑ j, ε (Fr i j x) * Gr j l x = 0 := by
    intro z hz i l
    filter_upwards [hU.mem_nhds (hKU hz)] with x hx
    exact hrel (δ x) (interior_subset hx) i l
  have hflat' : ∀ z ∈ K, Module.Flat Q
      ((Fin a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
        LinearMap.range (matrixGermMap basis z Fr)) := by
    intro z hz
    have hδK : δ z ∈ K := interior_subset (hKU hz)
    have hδU₀ : δ z ∈ U₀ := hKU₀ hδK
    have hfz : ∀ i j, ∀ᶠ x in 𝓝 (δ z), DifferentiableAt ℂ (F i j) x := by
      intro i j
      filter_upwards [hU₀.mem_nhds hδU₀] with x hx
      exact (hF i j x hx).differentiableAt (hU₀.mem_nhds hx)
    exact (matrixGermMap_flat_iff_radial basis c r hr0 z F hfz).mp (hflat (δ z) hδK)
  obtain ⟨V,hVo,hKV,_,G,hG,hFG,hres⟩ :=
    exists_compact_relation_lift basis ε hK hU hKU Fr Gr hFr hGr hrel' hflat'
  exact ⟨V,hVo,hKV,G,hG,hFG,hres⟩
end
end Hironaka.Analytic.Unibranch.HironakaG10RadialCompactRelationLift
