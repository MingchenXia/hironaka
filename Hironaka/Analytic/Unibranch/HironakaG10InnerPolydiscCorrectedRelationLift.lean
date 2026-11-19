import Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
import Hironaka.Analytic.Unibranch.HironakaG10BKReferenceGerm
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10InnerPolydiscCorrectedRelationLift
open Hironaka Hironaka
  OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedEuclidean HironakaG10LocSheafExact
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (EuclideanSpace ℂ (Fin n))) :=
  (HolGerm.constHom : ℂ →+* HolGerm (EuclideanSpace ℂ (Fin n))).toAlgebra

theorem exists_inner_polydisc_corrected_relation_lift
    {Q : Type*} {ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] {n a r c : ℕ}
    {K₁ K₂ U : Set (EuclideanSpace ℂ (Fin n))} [CompactSpace K₁]
    (hK₂ : K₂ ∈ closedPolydiscs n) (hK₂₁ : K₂ ⊆ interior K₁)
    (hU : IsOpen U) (hK₁U : K₁ ⊆ U)
    (basis : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (F : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → Q)
    (Fr : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → ℂ)
    (Gr : Fin r → Fin c → holSubalgebra K₁)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hFr : ∀ i j, DifferentiableOn ℂ (Fr i j) U)
    (hres : ∀ x ∈ U, ∀ i j, ε (F i j x) = Fr i j x)
    (hex : DirectExact Gr (restrictMatrix K₁ hK₁U Fr hFr))
    (hflat : ∀ z ∈ K₂, Module.Flat Q
      ((Fin a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
        LinearMap.range (matrixGermMap basis z F))) :
    ∃ V, IsOpen V ∧ K₂ ⊆ V ∧ V ⊆ interior K₁ ∧
      ∃ G : Fin r → Fin c → EuclideanSpace ℂ (Fin n) → Q,
        (∀ j l, DifferentiableOn ℂ (G j l) V) ∧
        (∀ x ∈ V, ∀ i l, ∑ j, F i j x * G j l x = 0) ∧
        ∀ x ∈ V, ∀ j l, ε (G j l x) = bkFun K₁ Gr j l x := by
  have hF' : ∀ i j, DifferentiableOn ℂ (F i j) (interior K₁) :=
    fun i j => (hF i j).mono (interior_subset.trans hK₁U)
  have hG : ∀ j l, DifferentiableOn ℂ (bkFun K₁ Gr j l) (interior K₁) :=
    fun j l => (Gr j l).2
  have hrel : ∀ z ∈ K₂, ∀ i l, ∀ᶠ x in 𝓝 z,
      ∑ j, ε (F i j x) * bkFun K₁ Gr j l x = 0 := by
    intro z hz i l
    filter_upwards [isOpen_interior.mem_nhds (hK₂₁ hz), hU.mem_nhds (hK₁U (interior_subset (hK₂₁ hz)))] with x hx hxU
    have hc := congrArg (fun q : holSubalgebra K₁ => (q : C(K₁,ℂ)) ⟨x, interior_subset hx⟩) (hex.comp i l)
    simpa [restrictMatrix, bkFun, extendZero_of_mem K₁ _ (interior_subset hx),
      hres x hxU] using hc
  exact exists_compact_relation_lift basis ε hK₂ isOpen_interior hK₂₁
    F (bkFun K₁ Gr) hF' hG hrel hflat
end
end Hironaka.Analytic.Unibranch.HironakaG10InnerPolydiscCorrectedRelationLift
