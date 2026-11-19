import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalLocalFactorization
import Hironaka.Resolution.HironakaIntrinsicMorphismGluingAnalytic

/-!
# Global actual singular-source factorization from standard invertible stalk ideals

The source is the ORIGINAL arbitrary reduced complex analytic space. Standard
Module.Invertible is imposed on the SAME canonical actual ideal at each stalk.
All source opens, ambient representatives, ratios, literal strict-transform
containment, overlap equalities and full over-ℂ morphism gluing are derived.
This is the standard stalk-module version; the ideal-sheaf/stalk bridge remains
explicitly separate, as do general coherent-ideal Projan and flattening.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-global.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalGlobal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  HironakaSingularSubspaceBlowupCartierUniversalLocalFactorization
  HironakaIntrinsicMorphismGluing HironakaIntrinsicMorphismGluingAnalytic

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

/-- Actual projection equality determines the original base maps when the
centre complement is dense; full sheaf-map equality is a separate step. -/
theorem base_eq_of_dense_projection_eq (hπ : IsBlowupAlong n C π) (hW : IsClosed W)
    {T : LocallyRingedSpace}
    (F : T ⟶ actualSubspaceLocallyRingedSpace (n := n) W)
    (hdense : Dense {x : T | (F.base x).val ∉ C})
    (L₁ L₂ : T ⟶ actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W))
    (hL₁ : L₁ ≫ strictTransformProjection hπ hW = F)
    (hL₂ : L₂ ≫ strictTransformProjection hπ hW = F) : L₁.base = L₂.base := by
  let : T2Space (actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W)).toPresheafedSpace :=
    inferInstanceAs (T2Space (strictTransform n π W))
  have hsub : {x : T | (F.base x).val ∉ C} ⊆ {x : T | L₁.base x = L₂.base x} := by
    intro x hx
    have h₁ : π (L₁.base x).val = (F.base x).val :=
      congrArg (fun H : T ⟶ actualSubspaceLocallyRingedSpace (n := n) W => (H.base x).val) hL₁
    have h₂ : π (L₂.base x).val = (F.base x).val :=
      congrArg (fun H : T ⟶ actualSubspaceLocallyRingedSpace (n := n) W => (H.base x).val) hL₂
    apply Subtype.ext
    apply (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.2.1
    · change π (L₁.base x).val ∉ C
      rwa [h₁]
    · change π (L₂.base x).val ∉ C
      rwa [h₂]
    · exact h₁.trans h₂.symm
  have hclosed : IsClosed {x : T | L₁.base x = L₂.base x} :=
    isClosed_eq L₁.base.hom.continuous L₂.base.hom.continuous
  have hall : Set.univ ⊆ {x : T | L₁.base x = L₂.base x} := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hclosed
  ext x
  exact hall (mem_univ x)

/-- ORIGINAL arbitrary reduced complex-space sources have a unique WHOLE
actual over-ℂ lift to the LITERAL singular strict transform. The sole ideal
input is standard Module.Invertible of the SAME canonical ideal at each
original source stalk; no source smoothness or incoming local lifts. -/
theorem exists_unique_intrinsic_factorization_of_module_invertible
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W)
    (A : ReducedComplexAnalyticSpace)
    (F : A.obj.left ⟶ actualSubspaceLocallyRingedSpace (n := n) W)
    (hF : F ≫ subspacePointMap (n := n) W = A.obj.hom)
    (hInv : ∀ x : A.obj.left,
      Module.Invertible (A.obj.left.presheaf.stalk x).carrier
        (Ideal.map (F.stalkMap x).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.base x)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F.base x).val)))) :
    ∃! L : A.obj ⟶ Over.mk (subspacePointMap (n := n) (strictTransform n π W)),
      L.left ≫ strictTransformProjection hπ hW = F := by
  classical
  have hlocal : ∀ x : A.obj.left,
      ∃ (P : LocallyRingedSpace) (j : P ⟶ A.obj.left)
        (K : P ⟶ actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W)),
        LocallyRingedSpace.IsOpenImmersion j ∧ x ∈ Set.range j.base ∧
        K ≫ subspacePointMap (n := n) (strictTransform n π W) = j ≫ A.obj.hom ∧
        K ≫ strictTransformProjection hπ hW = j ≫ F ∧
        Dense {u : P | (F.base (j.base u)).val ∉ C} := by
    intro x
    obtain ⟨d, U, S, _hS, i, hi, hip, c, hcx⟩ := A.property.2.2 x
    let i₀ : actualSubspaceLocallyRingedSpace (n := d) S ⟶ A.obj.left := i
    let : LocallyRingedSpace.IsOpenImmersion i₀ := hi
    let F₀ : actualSubspaceLocallyRingedSpace (n := d) S ⟶
        actualSubspaceLocallyRingedSpace (n := n) W := i₀ ≫ F
    have hF₀ : F₀ ≫ subspacePointMap (n := n) W = subspacePointMap (n := d) S := by
      change (i₀ ≫ F) ≫ _ = _
      rw [Category.assoc, hF]
      exact hip
    have hCart₀ : ∀ z : S,
        ∃ alpha : ((actualSubspaceSheaf (n := d) S).presheaf.stalk z).carrier,
          IsRegular alpha ∧
          Ideal.map (F₀.stalkMap z).hom
            (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F₀.base z)).hom
              (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F₀.base z).val)) =
            Ideal.span {alpha} := by
      intro z
      exact exists_regular_generator_on_open_chart i₀ F z
        (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.base (i₀.base z))).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F.base (i₀.base z)).val))
        (hInv (i₀.base z))
    obtain ⟨P, j₀, K, hj₀, hcj, hpK, hKπ, hd⟩ :=
      exists_local_factorization_of_actual_cartier hπ hW F₀ hF₀ hCart₀ c
    let : LocallyRingedSpace.IsOpenImmersion j₀ := hj₀
    refine ⟨P, j₀ ≫ i₀, K, inferInstance, ?_, ?_, ?_, hd⟩
    · obtain ⟨u, hu⟩ := hcj
      refine ⟨u, ?_⟩
      change i₀.base (j₀.base u) = x
      rw [hu]
      exact hcx
    · calc
        _ = j₀ ≫ subspacePointMap (n := d) S := hpK
        _ = j₀ ≫ (i₀ ≫ A.obj.hom) := congrArg (fun H => j₀ ≫ H) hip.symm
        _ = _ := (Category.assoc _ _ _).symm
    · exact hKπ.trans (Category.assoc _ _ _).symm
  choose P j K hj hxj hpoint hfac hdenseLocal using hlocal
  let : ∀ x, LocallyRingedSpace.IsOpenImmersion (j x) := hj
  have hcover : ∀ x : A.obj.left, ∃ (a : A.obj.left) (u : P a), (j a).base u = x := by
    intro x
    obtain ⟨u, hu⟩ := hxj x
    exact ⟨x, u, hu⟩
  have hdense : Dense {x : A.obj.left | (F.base x).val ∉ C} := by
    rw [dense_iff_inter_open]
    intro V hV hVne
    obtain ⟨x, hx⟩ := hVne
    obtain ⟨u, hu⟩ := hxj x
    have hpre : IsOpen ((j x).base ⁻¹' V) := hV.preimage (j x).base.hom.continuous
    obtain ⟨v, hvD, hvV⟩ := (hdenseLocal x).exists_mem_open hpre
      ⟨u, by change (j x).base u ∈ V; rwa [hu]⟩
    exact ⟨(j x).base v, hvV, hvD⟩
  have hcompat : ∀ a b, pullback.fst (j a) (j b) ≫ K a = pullback.snd (j a) (j b) ≫ K b := by
    intro a b
    let H := pullback (j a) (j b)
    let q₁ : H ⟶ P a := pullback.fst (j a) (j b)
    let q₂ : H ⟶ P b := pullback.snd (j a) (j b)
    let t : H ⟶ A.obj.left := q₁ ≫ j a
    let σH := t ≫ A.obj.hom
    let : LocallyRingedSpace.IsOpenImmersion t := by
      dsimp only [t, q₁, H]
      infer_instance
    have ht : q₂ ≫ j b = t := (pullback.condition (f := j a) (g := j b)).symm
    have hAH : hasAnalyticCharts (Over.mk σH) :=
      hasAnalyticCharts_of_openImmersion σH A.obj.hom A.property t rfl
    have hdH : Dense {x : H | ((t ≫ F).base x).val ∉ C} :=
      hdense.preimage (inferInstance : LocallyRingedSpace.IsOpenImmersion t).base_open.isOpenMap
    have h₁ : (q₁ ≫ K a) ≫ strictTransformProjection hπ hW = t ≫ F := by
      rw [Category.assoc, hfac a]
      exact (Category.assoc _ _ _).symm
    have h₂ : (q₂ ≫ K b) ≫ strictTransformProjection hπ hW = t ≫ F := by
      rw [Category.assoc, hfac b, ← Category.assoc, ht]
    apply morphism_eq_of_base_eq σH hAH
    · rw [Category.assoc, hpoint a]
      exact (Category.assoc _ _ _).symm
    · rw [Category.assoc, hpoint b, ← Category.assoc, ht]
    · exact base_eq_of_dense_projection_eq hπ hW (t ≫ F) hdH _ _ h₁ h₂
  obtain ⟨L, hL, _⟩ := exists_unique_over P j hcover A.obj.hom
    (subspacePointMap (n := n) (strictTransform n π W)) K hcompat hpoint
  have hLp : L.left ≫ strictTransformProjection hπ hW = F := by
    apply HironakaIntrinsicMorphismGluing.hom_ext P j hcover
    intro a
    rw [← Category.assoc, hL a, hfac a]
  refine ⟨L, hLp, ?_⟩
  intro L' hL'p
  apply Over.OverMorphism.ext
  exact morphism_eq_of_base_eq A.obj.hom A.property L'.left L.left (Over.w L') (Over.w L)
    (base_eq_of_dense_projection_eq hπ hW F hdense _ _ hL'p hLp)

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalGlobal
