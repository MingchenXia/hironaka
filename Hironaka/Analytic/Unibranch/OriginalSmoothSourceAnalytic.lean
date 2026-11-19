import Hironaka.Analytic.Unibranch.EmbeddedCommonResolutionGeneralAnalyticSubsets
import Hironaka.Resolution.HironakaEmbeddedNativeMorphism
import Hironaka.Analytic.AnalyticFibreProductCarrier

/-!
# Actual native analytic sets over an arbitrary ORIGINAL target

The full original maps internally give their local target-chart holomorphic
representatives. Native analytic pullbacks and the SAME product equality locus
are derived, without global target embedding/countability/diagonal data.
Blueprint: `original-smooth-source-analytic.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
  Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.OriginalSmoothSourceAnalytic

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaReducedComplexAnalyticMorphismCharts HironakaEmbeddedNativeMorphism
  SourceReducedComplexSpace

noncomputable section

variable {X : SourceReducedComplexSpace}

section OneSource

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal ORIGINAL target-valued point map, with no ambient target. -/
def pointMap (F : ofClosedAnalytic (n := n) (univ : Set M)
    (isComplexAnalyticSubset_univ (n := n)) ⟶ X) : M → X.obj.left :=
  fun y => F.hom.left.base ⟨y, mem_univ y⟩

theorem continuous_pointMap (F : ofClosedAnalytic (n := n) (univ : Set M)
    (isComplexAnalyticSubset_univ (n := n)) ⟶ X) : Continuous (pointMap F) :=
  F.hom.left.base.hom.continuous.comp (continuous_id.subtype_mk (fun y => mem_univ y))

/-- The ORIGINAL full map internally acquires a genuine local holomorphic
representative in any actual target chart at its image, with the WHOLE square. -/
theorem exists_local_chart_lift
    (F : ofClosedAnalytic (n := n) (univ : Set M)
      (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    (e : LocalEmbedding X) (x : M) (hx : pointMap F x ∈ range e.toPoint) :
    ∃ (U : Opens M) (_hxU : x ∈ U) (g : U → e.ambient)
      (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel e.dim) ∞ g)
      (hw : ∀ u, g u ∈ e.carrier),
      (∀ u, e.toPoint ⟨g u, hw u⟩ = pointMap F u.val) ∧
      actualSubspaceMap hg (fun u (_ : u ∈ (univ : Set U)) => hw u) ≫ e.map =
        actualOpenSubspaceMap (n := n) (univ : Set M) U ≫ F.hom.left := by
  have hF : F.hom.left ≫ X.obj.hom = subspacePointMap (n := n) (univ : Set M) := Over.w F.hom
  obtain ⟨U, hxU, H, hHp, hfac⟩ := exists_actual_model_chart_factor X.obj F.hom.left hF
    e.map (hj := e.isOpenImmersion) e.overPoint (⟨x, mem_univ x⟩ : (univ : Set M)) hx
  let g : U → e.ambient := fun u => (H.base ⟨u, mem_univ u.val⟩).val
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel e.dim) ∞ g :=
    contMDiff_original_pointMap H hHp
  have hw (u : U) : g u ∈ e.carrier := (H.base ⟨u, mem_univ u.val⟩).property
  have hwhole : actualSubspaceMap hg (fun u (_ : u ∈ (univ : Set U)) => hw u) = H :=
    original_morphism_eq_actualSubspaceMap H hHp
  have hmap : actualSubspaceMap hg (fun u (_ : u ∈ (univ : Set U)) => hw u) ≫ e.map =
      actualOpenSubspaceMap (n := n) (univ : Set M) U ≫ F.hom.left := by
    rw [hwhole]
    exact hfac
  refine ⟨U, hxU, g, hg, hw, ?_, hmap⟩
  intro u
  exact congrArg (fun K => K.base (⟨u, mem_univ u⟩ : (univ : Set U))) hmap

/-- The inverse image of an ORIGINAL intrinsic analytic subset is analytic
in the SAME actual native source, with no properness/compactness premise. -/
theorem isComplexAnalyticSubset_preimage
    (F : ofClosedAnalytic (n := n) (univ : Set M)
      (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    {A : Set X.obj.left} (hA : X.IsAnalyticSubset A) :
    IsComplexAnalyticSubset (n := n) (pointMap F ⁻¹' A) := by
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro x
  let e := LocalEmbedding.ofPoint X (pointMap F x)
  obtain ⟨U, hxU, g, hg, hw, hpoint, _hwhole⟩ :=
    exists_local_chart_lift F e x (LocalEmbedding.mem_range_ofPoint X (pointMap F x))
  let B : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' A)
  have hBa : IsComplexAnalyticSubset (n := e.dim) B := hA.analytic_image_localEmbedding e
  have heq : (Subtype.val : U → M) ⁻¹' (pointMap F ⁻¹' A) = g ⁻¹' B := by
    ext u
    constructor
    · intro hu
      refine ⟨⟨g u, hw u⟩, ?_, rfl⟩
      change e.toPoint ⟨g u, hw u⟩ ∈ A
      rw [hpoint u]
      exact hu
    · rintro ⟨v, hv, hvg⟩
      have hvu : v = (⟨g u, hw u⟩ : e.carrier) := Subtype.ext hvg
      change pointMap F u.val ∈ A
      rw [← hpoint u, ← hvu]
      exact hv
  refine ⟨U, hxU, ?_⟩
  rw [heq]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg hBa

end OneSource

section TwoSources

variable {n₀ n₁ : ℕ} {M₀ M₁ : Type}
  [TopologicalSpace M₀] [ChartedSpace (ComplexModel n₀) M₀] [IsComplexManifold n₀ M₀]
  [TopologicalSpace M₁] [ChartedSpace (ComplexModel n₁) M₁] [IsComplexManifold n₁ M₁]

theorem isClosed_equalityLocus
    (F₀ : ofClosedAnalytic (n := n₀) (univ : Set M₀) (isComplexAnalyticSubset_univ (n := n₀)) ⟶ X)
    (F₁ : ofClosedAnalytic (n := n₁) (univ : Set M₁) (isComplexAnalyticSubset_univ (n := n₁)) ⟶ X) :
    IsClosed {p : M₀ × M₁ | pointMap F₀ p.1 = pointMap F₁ p.2} := by
  let := X.property.1
  exact isClosed_eq ((continuous_pointMap F₀).comp continuous_fst)
    ((continuous_pointMap F₁).comp continuous_snd)

/-- The literal product equality locus over an arbitrary ORIGINAL target is
analytic; only actual local target ambients supply diagonal equations. -/
theorem isComplexAnalyticSubset_equalityLocus
    (F₀ : ofClosedAnalytic (n := n₀) (univ : Set M₀) (isComplexAnalyticSubset_univ (n := n₀)) ⟶ X)
    (F₁ : ofClosedAnalytic (n := n₁) (univ : Set M₁) (isComplexAnalyticSubset_univ (n := n₁)) ⟶ X) :
    IsComplexAnalyticSubset (n := n₀ + n₁)
      {p : M₀ × M₁ | pointMap F₀ p.1 = pointMap F₁ p.2} := by
  let K : Set (M₀ × M₁) := {p | pointMap F₀ p.1 = pointMap F₁ p.2}
  have hKc : IsClosed K := isClosed_equalityLocus F₀ F₁
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro p
  by_cases hp : p ∈ K
  · let e := LocalEmbedding.ofPoint X (pointMap F₀ p.1)
    have hx₀ : pointMap F₀ p.1 ∈ range e.toPoint :=
      LocalEmbedding.mem_range_ofPoint X (pointMap F₀ p.1)
    have hx₁ : pointMap F₁ p.2 ∈ range e.toPoint := by rw [← hp]; exact hx₀
    obtain ⟨U₀, hxU₀, g₀, hg₀, hw₀, hpoint₀, _hwhole₀⟩ := exists_local_chart_lift F₀ e p.1 hx₀
    obtain ⟨U₁, hxU₁, g₁, hg₁, hw₁, hpoint₁, _hwhole₁⟩ := exists_local_chart_lift F₁ e p.2 hx₁
    let O : Opens (M₀ × M₁) := ⟨Prod.fst ⁻¹' (U₀ : Set M₀) ∩ Prod.snd ⁻¹' (U₁ : Set M₁),
      (U₀.isOpen.preimage continuous_fst).inter (U₁.isOpen.preimage continuous_snd)⟩
    let a₀ : O → U₀ := fun q => ⟨q.val.1, q.property.1⟩
    let a₁ : O → U₁ := fun q => ⟨q.val.2, q.property.2⟩
    have ha₀ : ContMDiff 𝓘(ℂ, ComplexModel (n₀ + n₁)) 𝓘(ℂ, ComplexModel n₀) ∞ a₀ :=
      BlowupRestrictOpen.contMDiff_opens_mk
        (ProductComplexManifold.contMDiff_fst.comp contMDiff_subtype_val) (fun q : O => q.property.1)
    have ha₁ : ContMDiff 𝓘(ℂ, ComplexModel (n₀ + n₁)) 𝓘(ℂ, ComplexModel n₁) ∞ a₁ :=
      BlowupRestrictOpen.contMDiff_opens_mk
        (ProductComplexManifold.contMDiff_snd.comp contMDiff_subtype_val) (fun q : O => q.property.2)
    have heq : (Subtype.val : O → M₀ × M₁) ⁻¹' K =
        (fun q : O => (g₀ (a₀ q), g₁ (a₁ q))) ⁻¹' diagonal e.ambient := by
      ext q
      change pointMap F₀ q.val.1 = pointMap F₁ q.val.2 ↔ g₀ (a₀ q) = g₁ (a₁ q)
      rw [← hpoint₀ (a₀ q), ← hpoint₁ (a₁ q)]
      exact ⟨fun h => congrArg Subtype.val (e.toPoint_injective h),
        fun h => congrArg e.toPoint (Subtype.ext h)⟩
    refine ⟨O, ⟨hxU₀, hxU₁⟩, ?_⟩
    rw [heq]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (ProductComplexManifold.contMDiff_prodMk (hg₀.comp ha₀) (hg₁.comp ha₁))
      AnalyticFibreProductCarrier.isComplexAnalyticSubset_diagonal
  · let O : Opens (M₀ × M₁) := ⟨Kᶜ, hKc.isOpen_compl⟩
    refine ⟨O, hp, ?_⟩
    have heq : (Subtype.val : O → M₀ × M₁) ⁻¹' K = ∅ := by
      ext q
      exact ⟨fun h => (q.property h).elim, False.elim⟩
    rw [heq]
    exact isComplexAnalyticSubset_empty

end TwoSources

end

end Hironaka.Analytic.Unibranch.OriginalSmoothSourceAnalytic
