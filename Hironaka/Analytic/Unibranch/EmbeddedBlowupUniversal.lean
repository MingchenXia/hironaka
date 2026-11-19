import Hironaka.Analytic.Unibranch.EmbeddedBlowup
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalGlobal

/-!
# Universal lifting in the ORIGINAL Hausdorff/paracompact source category

Original source spaces carry precisely Hironaka's book local-model property, with
NO global second-countability or compactness assumption. Native analytic charts
are derived only on the actual locally constructed source opens P and their
pullback overlaps. Generic full LRS gluing stays on the SAME original source.

The ideal input is standard Module.Invertible of the SAME actual pulled ideal
at each original source stalk. No local lift or chart certificate is supplied.
The full original category square uses the literal EmbeddedBlowup projection.
Blueprint: `embedded-blowup-universal.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupUniversal

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  HironakaSingularSubspaceBlowupCartierUniversalLocalFactorization
  HironakaSingularSubspaceBlowupCartierUniversalGlobal
  HironakaIntrinsicMorphismGluing HironakaIntrinsicMorphismGluingAnalytic
  SourceReducedComplexSpace EmbeddedBlowup

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

/-- The original source's local models produce genuine local lifts on actual
source opens P. Native analytic charts are derived on P from its MODEL source,
without asserting native charts or second countability on the original A. -/
theorem exists_local_source_factorization_of_module_invertible
    (hπ : IsBlowupAlong n C π) (hWa : IsComplexAnalyticSubset (n := n) W)
    (A : SourceReducedComplexSpace) (F : A ⟶ ofClosedAnalytic W hWa)
    (hInv : ∀ x : A.obj.left,
      Module.Invertible (A.obj.left.presheaf.stalk x).carrier
        (Ideal.map (F.hom.left.stalkMap x).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.hom.left.base x)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C)
              (F.hom.left.base x).val)))) (x : A.obj.left) :
    ∃ (P : LocallyRingedSpace) (j : P ⟶ A.obj.left)
      (K : P ⟶ actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W)),
      LocallyRingedSpace.IsOpenImmersion j ∧ x ∈ range j.base ∧
      hasAnalyticCharts (Over.mk (j ≫ A.obj.hom)) ∧
      K ≫ subspacePointMap (n := n) (strictTransform n π W) = j ≫ A.obj.hom ∧
      K ≫ strictTransformProjection hπ hWa.isClosed = j ≫ F.hom.left ∧
      Dense {u : P | (F.hom.left.base (j.base u)).val ∉ C} := by
  obtain ⟨d, U, S, hS, i, hi, hip, c, hcx⟩ := A.property.2.2 x
  let i₀ : actualSubspaceLocallyRingedSpace (n := d) S ⟶ A.obj.left := i
  let : LocallyRingedSpace.IsOpenImmersion i₀ := hi
  have hip₀ : i₀ ≫ A.obj.hom = subspacePointMap (n := d) S := hip
  let F₀ : actualSubspaceLocallyRingedSpace (n := d) S ⟶
      actualSubspaceLocallyRingedSpace (n := n) W := i₀ ≫ F.hom.left
  have hFpoint : F.hom.left ≫ subspacePointMap (n := n) W = A.obj.hom := Over.w F.hom
  have hF₀ : F₀ ≫ subspacePointMap (n := n) W = subspacePointMap (n := d) S := by
    change (i₀ ≫ F.hom.left) ≫ _ = _
    rw [Category.assoc, hFpoint]
    exact hip₀
  have hCart₀ : ∀ z : S,
      ∃ alpha : ((actualSubspaceSheaf (n := d) S).presheaf.stalk z).carrier,
        IsRegular alpha ∧
        Ideal.map (F₀.stalkMap z).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F₀.base z)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F₀.base z).val)) =
          Ideal.span {alpha} := by
    intro z
    exact exists_regular_generator_on_open_chart i₀ F.hom.left z
      (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap
          (F.hom.left.base (i₀.base z))).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C)
          (F.hom.left.base (i₀.base z)).val)) (hInv (i₀.base z))
  obtain ⟨P, j₀, K, hj₀, hcj, hpK, hKπ, hd⟩ :=
    exists_local_factorization_of_actual_cartier hπ hWa.isClosed F₀ hF₀ hCart₀ c
  let : LocallyRingedSpace.IsOpenImmersion j₀ := hj₀
  have hP : hasAnalyticCharts (Over.mk (j₀ ≫ subspacePointMap (n := d) S)) :=
    hasAnalyticCharts_of_openImmersion _ _ (hasAnalyticCharts_model U S hS) j₀ rfl
  refine ⟨P, j₀ ≫ i₀, K, inferInstance, ?_, ?_, ?_, ?_, hd⟩
  · obtain ⟨u, hu⟩ := hcj
    refine ⟨u, ?_⟩
    change i₀.base (j₀.base u) = x
    rw [hu]
    exact hcx
  · rw [Category.assoc, hip₀]
    exact hP
  · calc
      _ = j₀ ≫ subspacePointMap (n := d) S := hpK
      _ = j₀ ≫ (i₀ ≫ A.obj.hom) := congrArg (fun H => j₀ ≫ H) hip₀.symm
      _ = _ := (Category.assoc _ _ _).symm
  · exact hKπ.trans (Category.assoc _ _ _).symm

/-- The original book source category has universal lifting through the SAME
singular strict transform, from standard invertibility of SAME actual ideal
stalks. No global source second countability or compactness is assumed. -/
theorem exists_unique_source_factorization_of_module_invertible
    (hπ : IsBlowupAlong n C π) (hWa : IsComplexAnalyticSubset (n := n) W)
    (A : SourceReducedComplexSpace) (F : A ⟶ ofClosedAnalytic W hWa)
    (hInv : ∀ x : A.obj.left,
      Module.Invertible (A.obj.left.presheaf.stalk x).carrier
        (Ideal.map (F.hom.left.stalkMap x).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.hom.left.base x)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C)
              (F.hom.left.base x).val)))) :
    ∃! L : A ⟶ ofClosedAnalytic (strictTransform n π W)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ hWa),
      L ≫ strictTransformMorphism hπ hWa = F := by
  classical
  have hlocal := exists_local_source_factorization_of_module_invertible hπ hWa A F hInv
  choose P j K hj hxj hP hpoint hfac hdenseLocal using hlocal
  let : ∀ x, LocallyRingedSpace.IsOpenImmersion (j x) := hj
  have hcover : ∀ x : A.obj.left, ∃ (a : A.obj.left) (u : P a), (j a).base u = x := by
    intro x
    obtain ⟨u, hu⟩ := hxj x
    exact ⟨x, u, hu⟩
  have hcompat : ∀ a b, pullback.fst (j a) (j b) ≫ K a =
      pullback.snd (j a) (j b) ≫ K b := by
    intro a b
    let H := pullback (j a) (j b)
    let q₁ : H ⟶ P a := pullback.fst (j a) (j b)
    let q₂ : H ⟶ P b := pullback.snd (j a) (j b)
    let t : H ⟶ A.obj.left := q₁ ≫ j a
    let σH := t ≫ A.obj.hom
    let : LocallyRingedSpace.IsOpenImmersion q₁ := by
      dsimp only [q₁, H]
      infer_instance
    have ht : q₂ ≫ j b = t := (pullback.condition (f := j a) (g := j b)).symm
    have hAH : hasAnalyticCharts (Over.mk σH) :=
      hasAnalyticCharts_of_openImmersion σH (j a ≫ A.obj.hom) (hP a) q₁
        (Category.assoc _ _ _).symm
    have hdH : Dense {x : H | ((t ≫ F.hom.left).base x).val ∉ C} :=
      (hdenseLocal a).preimage
        (inferInstance : LocallyRingedSpace.IsOpenImmersion q₁).base_open.isOpenMap
    have h₁ : (q₁ ≫ K a) ≫ strictTransformProjection hπ hWa.isClosed = t ≫ F.hom.left := by
      rw [Category.assoc, hfac a]
      exact (Category.assoc _ _ _).symm
    have h₂ : (q₂ ≫ K b) ≫ strictTransformProjection hπ hWa.isClosed = t ≫ F.hom.left := by
      rw [Category.assoc, hfac b, ← Category.assoc, ht]
    apply morphism_eq_of_base_eq σH hAH
    · rw [Category.assoc, hpoint a]
      exact (Category.assoc _ _ _).symm
    · rw [Category.assoc, hpoint b, ← Category.assoc, ht]
    · exact base_eq_of_dense_projection_eq hπ hWa.isClosed (t ≫ F.hom.left) hdH _ _ h₁ h₂
  obtain ⟨L, hL, _⟩ := exists_unique_over P j hcover A.obj.hom
    (subspacePointMap (n := n) (strictTransform n π W)) K hcompat hpoint
  have hLpoint : L.left ≫ subspacePointMap (n := n) (strictTransform n π W) =
      A.obj.hom := Over.w L
  have hLp : L.left ≫ strictTransformProjection hπ hWa.isClosed = F.hom.left := by
    apply HironakaIntrinsicMorphismGluing.hom_ext P j hcover
    intro a
    rw [← Category.assoc, hL a, hfac a]
  refine ⟨ObjectProperty.homMk L, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hLp
  · intro L' hL'p
    have hL'pr : L'.hom.left ≫ strictTransformProjection hπ hWa.isClosed = F.hom.left :=
      congrArg (fun H : A ⟶ ofClosedAnalytic W hWa => H.hom.left) hL'p
    have hL'point : L'.hom.left ≫ subspacePointMap (n := n) (strictTransform n π W) =
        A.obj.hom := Over.w L'.hom
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply HironakaIntrinsicMorphismGluing.hom_ext P j hcover
    intro a
    change j a ≫ L'.hom.left = j a ≫ L.left
    have h₁ : (j a ≫ L'.hom.left) ≫ strictTransformProjection hπ hWa.isClosed =
        j a ≫ F.hom.left := by rw [Category.assoc, hL'pr]
    have h₂ : (j a ≫ L.left) ≫ strictTransformProjection hπ hWa.isClosed =
        j a ≫ F.hom.left := by rw [Category.assoc, hLp]
    apply morphism_eq_of_base_eq (j a ≫ A.obj.hom) (hP a)
    · rw [Category.assoc, hL'point]
    · rw [Category.assoc, hLpoint]
    · exact base_eq_of_dense_projection_eq hπ hWa.isClosed (j a ≫ F.hom.left)
        (hdenseLocal a) _ _ h₁ h₂

end

end Hironaka.Analytic.Unibranch.EmbeddedBlowupUniversal
