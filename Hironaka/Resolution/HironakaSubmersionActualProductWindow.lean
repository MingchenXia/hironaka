import Hironaka.Resolution.HironakaSmoothSubmersionComposition
import Hironaka.Resolution.HironakaActualFlatCoordinateIntrinsicHS
import Hironaka.Analytic.ProductComplexManifold

/-! Genuine actual open product normal forms of complex submersions.
No native smoothness, reduced-ideal or algorithmic packet is assumed.
Blueprint first: `hironaka-submersion-actual-product-window.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSubmersionActualProductWindow
noncomputable section
open ProductComplexManifold HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionComposition HironakaActualFlatCoordinateIntrinsicHS BlowupFlatCoordinates
open scoped ProductComplexManifold

theorem join_holomorphic (n r : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞
      (prodModelEquiv n r : ComplexModel n × ComplexModel r → ComplexModel (n+r)) := by
  intro z
  have h := (contMDiffOn_chart (I := 𝓘(ℂ,ComplexModel (n+r))) (n := ∞)
    (x := ((0,0) : ComplexModel n × ComplexModel r))).contMDiffAt (x := z)
      (by simp [chartAt_prod,prodChart_source,chartAt_self_eq])
  have heq : (chartAt (ComplexModel (n+r)) ((0,0) : ComplexModel n × ComplexModel r) :
      ComplexModel n × ComplexModel r → ComplexModel (n+r)) = prodModelEquiv n r := by
    funext q
    simp only [chartAt_prod,prodChart_apply,chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq]
  exact heq ▸ h

def productWindow {n r : ℕ} (A : Opens (ComplexModel (n+r))) (B : Opens (ComplexModel n)) :
    Opens (B × ComplexModel r) :=
  ⟨(fun p : B × ComplexModel r => prodModelEquiv n r (p.1.val,p.2)) ⁻¹' (A : Set (ComplexModel (n+r))),
    A.isOpen.preimage ((prodModelEquiv n r).continuous.comp (continuous_subtype_val.prodMap continuous_id))⟩

def splitWindowDiffeomorph {n r : ℕ} (A : Opens (ComplexModel (n+r))) (B : Opens (ComplexModel n))
    (hAB : ∀ z ∈ A, ((prodModelEquiv n r).symm z).1 ∈ B) :
    A ≃ₘ⟮𝓘(ℂ,ComplexModel (n+r)),𝓘(ℂ,ComplexModel (n+r))⟯ productWindow A B where
  toFun z := ⟨(⟨((prodModelEquiv n r).symm z.val).1,hAB z.val z.property⟩,
      ((prodModelEquiv n r).symm z.val).2),by
        change prodModelEquiv n r ((prodModelEquiv n r).symm z.val) ∈ A
        exact Eq.mpr (congrArg (fun u => u ∈ A) ((prodModelEquiv n r).apply_symm_apply z.val)) z.property⟩
  invFun p := ⟨prodModelEquiv n r (p.val.1.val,p.val.2),p.property⟩
  left_inv z := Subtype.ext ((prodModelEquiv n r).apply_symm_apply z.val)
  right_inv p := by
    apply Subtype.ext
    dsimp only
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (productWindow A B) _).mp
    apply ProductComplexManifold.contMDiff_prodMk
    · apply (ContMDiff.subtypeVal_comp_iff B _).mp
      exact (((ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel r)).contDiff.contMDiff).comp
        (prodModelEquiv n r).symm.contDiff.contMDiff).comp contMDiff_subtype_val
    · exact (((ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel r)).contDiff.contMDiff).comp
        (prodModelEquiv n r).symm.contDiff.contMDiff).comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff A _).mp
    exact (join_holomorphic n r).comp
      ((ProductComplexManifold.contMDiff_prodMk
        (contMDiff_subtype_val.comp ProductComplexManifold.contMDiff_fst)
        ProductComplexManifold.contMDiff_snd).comp contMDiff_subtype_val)

private theorem split_first_coordinate {n r : ℕ} (z : ComplexModel (n+r)) (j : Fin n) :
    ((prodModelEquiv n r).symm z).1 j = z (Fin.castAdd r j) :=
  (first_block_coordinate ((prodModelEquiv n r).symm z).1 ((prodModelEquiv n r).symm z).2 j).symm.trans
    (congrArg (fun u : ComplexModel (n+r) => u (Fin.castAdd r j)) ((prodModelEquiv n r).apply_symm_apply z))

universe u

/-- Actual complete ambient product charts, derived from ordinary submersion data alone. -/
theorem exists_actual_product_window {n r : ℕ} {M N : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (n+r)) M] [IsComplexManifold (n+r) M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    {f : M → N} {y : M}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f y) :
    ∃ (P : Opens N) (Q : Opens M) (B : Opens (ComplexModel n)) (W : Opens (B × ComplexModel r))
      (φ : P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B)
      (ψ : Q ≃ₘ⟮𝓘(ℂ,ComplexModel (n+r)),𝓘(ℂ,ComplexModel (n+r))⟯ W),
      f y ∈ P ∧ y ∈ Q ∧ ∀ p : W, f (ψ.symm p).val = (φ.symm p.val.1).val := by
  let Φ := centeredCoordinates (n := n) (f y)
  let Ξ := liftedCoordinatesAdd hf Φ (centeredCoordinates_zero (n := n) (f y))
  have hd := liftedCoordinatesAdd_dictionary hf Φ (centeredCoordinates_zero (n := n) (f y))
  let P : Opens N := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let Q : Opens M := ⟨flatDomain Ξ,isOpen_flatDomain Ξ⟩
  let B : Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  let A : Opens (ComplexModel (n+r)) := ⟨Ξ.target,Ξ.isOpen_target⟩
  let φ : P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B :=
    actualFlatCoordinateDiffeomorph Φ (centeredCoordinates_source (n := n) (f y))
  let θ : Q ≃ₘ⟮𝓘(ℂ,ComplexModel (n+r)),𝓘(ℂ,ComplexModel (n+r))⟯ A :=
    actualFlatCoordinateDiffeomorph Ξ hd.1
  have hblock (q : Q) : ((prodModelEquiv n r).symm (θ q).val).1 =
      (φ ⟨f q.val,(hd.2.2 q.val q.property).1⟩).val := by
    ext j
    exact (split_first_coordinate (θ q).val j).trans ((hd.2.2 q.val q.property).2 j)
  have hAB : ∀ z ∈ A, ((prodModelEquiv n r).symm z).1 ∈ B := by
    intro z hz
    let q : Q := θ.symm ⟨z,hz⟩
    have hθ : (θ q).val = z := congrArg Subtype.val (θ.apply_symm_apply ⟨z,hz⟩)
    have heq : ((prodModelEquiv n r).symm z).1 =
        (φ ⟨f q.val,(hd.2.2 q.val q.property).1⟩).val :=
      (congrArg (fun t => ((prodModelEquiv n r).symm t).1) hθ).symm.trans (hblock q)
    exact Eq.mpr (congrArg (fun t => t ∈ B) heq) (φ ⟨f q.val,(hd.2.2 q.val q.property).1⟩).property
  let W := productWindow A B
  let ψ : Q ≃ₘ⟮𝓘(ℂ,ComplexModel (n+r)),𝓘(ℂ,ComplexModel (n+r))⟯ W :=
    θ.trans (splitWindowDiffeomorph A B hAB)
  refine ⟨P,Q,B,W,φ,ψ,mem_flatDomain_self Φ,mem_flatDomain_self Ξ,?_⟩
  intro p
  let q : Q := ψ.symm p
  let v : P := ⟨f q.val,(hd.2.2 q.val q.property).1⟩
  have hfirst : (ψ q).val.1 = φ v := Subtype.ext (hblock q)
  have hψ : (ψ q).val.1 = p.val.1 := congrArg (fun t : W => t.val.1) (ψ.apply_symm_apply p)
  have heq : p.val.1 = φ v := hψ.symm.trans hfirst
  exact ((congrArg (fun t : B => (φ.symm t).val) heq).trans
    (congrArg Subtype.val (φ.symm_apply_apply v))).symm

end
end Hironaka.HironakaSubmersionActualProductWindow
