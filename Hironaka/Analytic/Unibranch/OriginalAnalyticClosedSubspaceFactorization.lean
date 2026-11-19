import Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspace
import Hironaka.Resolution.HironakaIntrinsicMorphismGluing

/-!
# Full original factorization into the actual analytic closed subspace

Ordinary point landing produces the unique whole morphism into the SAME
original global analytic-subspace factory. Actual source model restrictions,
native open lifts and closed-model factorization derive the local maps;
native monicity gives full overlap compatibility on the original source.
Blueprint FIRST: `original-analytic-closed-subspace-factorization.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceFactorization

open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaIntrinsicMorphismGluing
  SourceReducedComplexSpace EmbeddedBlowupOpenRestriction
  OriginalAnalyticClosedSubspace OriginalAnalyticClosedSubspaceOverlap

noncomputable section

variable (X : SourceReducedComplexSpace) (S : Set X.obj.left) (hS : X.IsAnalyticSubset S)

/-- Native monicity is derived from actual base injectivity and stalk surjectivity. -/
instance inclusion_left_mono : Mono (inclusion X S hS).hom.left := by
  apply LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact (inclusion_isClosedEmbedding X S hS).injective
  · intro z
    exact ConcreteCategory.epi_of_surjective _ (inclusion_stalk_surjective X S hS z)

/-- The SAME actual factory chart with its derived original complex scalar triangle. -/
def factoryChartMorphism (a : X.obj.left) :
    localObject X S hS a ⟶ sourceObject X S hS := by
  apply ObjectProperty.homMk
  refine Over.homMk (chartInclusion X S hS a) ?_
  change chartInclusion X S hS a ≫ (projection X S hS ≫ X.obj.hom) = _
  rw [← Category.assoc, chartInclusion_projection, Over.w (localProjection X S hS a).hom]

instance factoryChartMorphism_isOpenImmersion (a : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (factoryChartMorphism X S hS a).hom.left :=
  chartInclusion_isOpenImmersion X S hS a

theorem factoryChartMorphism_inclusion (a : X.obj.left) :
    factoryChartMorphism X S hS a ≫ inclusion X S hS = localProjection X S hS a := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact chartInclusion_projection X S hS a

private theorem exists_local_factorization (A : SourceReducedComplexSpace) (F : A ⟶ X)
    (hland : ∀ a : A.obj.left, F.hom.left.base a ∈ S) (a : A.obj.left) :
    ∃ (P : SourceReducedComplexSpace) (j : P ⟶ A) (K : P ⟶ sourceObject X S hS),
      LocallyRingedSpace.IsOpenImmersion j.hom.left ∧
      a ∈ range j.hom.left.base ∧ K ≫ inclusion X S hS = j ≫ F := by
  classical
  let eA := LocalEmbedding.ofPoint A a
  obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint A a
  let b := F.hom.left.base a
  let eT := localEmbedding X S hS b
  let Q : Opens eA.carrier :=
    ⟨(fun w => F.hom.left.base (eA.toPoint w)) ⁻¹' range eT.toPoint,
      eT.isOpen_range_toPoint.preimage
        (F.hom.left.base.hom.continuous.comp eA.map.base.hom.continuous)⟩
  have hcQ : c ∈ Q := by
    change F.hom.left.base (eA.toPoint c) ∈ range eT.toPoint
    rw [hc]
    exact mem_chartOpen_self X S hS b
  let P := restrictedClosedAnalytic eA.analytic Q
  let j : P ⟶ A := restrictionInclusion eA.analytic Q ≫ EmbeddedBlowupOverlap.chartMorphism eA
  have hj : LocallyRingedSpace.IsOpenImmersion j.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion
      ((restrictionInclusion eA.analytic Q).hom.left ≫
        (EmbeddedBlowupOverlap.chartMorphism eA).hom.left)
    infer_instance
  have ha : a ∈ range j.hom.left.base := ⟨⟨c, hcQ⟩, hc⟩
  let k := EmbeddedBlowupOverlap.chartMorphism eT
  let : LocallyRingedSpace.IsOpenImmersion k.hom.left := eT.isOpenImmersion
  have hRange : range (j ≫ F).hom.left.base ⊆ range k.hom.left.base := by
    rintro _ ⟨u, rfl⟩
    exact u.property
  let l := LocallyRingedSpace.IsOpenImmersion.lift k.hom.left (j ≫ F).hom.left hRange
  have hl : l ≫ k.hom.left = (j ≫ F).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac k.hom.left (j ≫ F).hom.left hRange
  have hp : l ≫ (ofClosedAnalytic eT.carrier eT.analytic).obj.hom = P.obj.hom := by
    rw [← Over.w k.hom, ← Category.assoc, hl, Over.w (j ≫ F).hom]
  let L : P ⟶ ofClosedAnalytic eT.carrier eT.analytic :=
    ObjectProperty.homMk (Over.homMk l hp)
  have hL : L ≫ k = j ≫ F := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hl
  have hD (u : P.obj.left) : (L.hom.left.base u).val ∈ localCentre X S hS b := by
    refine ⟨(L.hom.left.base u).property, ?_⟩
    apply (Set.ext_iff.mp (ambientTrace_eq X S hS b) (L.hom.left.base u)).mp
    have he : eT.toPoint (L.hom.left.base u) = F.hom.left.base (j.hom.left.base u) :=
      congrArg (fun H => H.hom.left.base u) hL
    change eT.toPoint (L.hom.left.base u) ∈ S
    rw [he]
    exact hland (j.hom.left.base u)
  obtain ⟨H, hH, _⟩ := OriginalClosedSubspaceFactorization.exists_unique_factorization
    (localCentre_analytic X S hS b) eT.analytic (localCentre_subset X S hS b) P L hD
  have hHF : H ≫ localProjection X S hS b = j ≫ F := by
    change H ≫ (OriginalClosedSubspaceFactorization.inclusion (localCentre_analytic X S hS b)
      eT.analytic (localCentre_subset X S hS b) ≫ k) = j ≫ F
    rw [← Category.assoc, hH, hL]
  refine ⟨P, j, H ≫ factoryChartMorphism X S hS b, hj, ha, ?_⟩
  rw [Category.assoc, factoryChartMorphism_inclusion]
  exact hHF

/-- Ordinary point landing derives the UNIQUE FULL map into the SAME actual factory. -/
theorem exists_unique_factorization (A : SourceReducedComplexSpace) (F : A ⟶ X)
    (hland : ∀ a : A.obj.left, F.hom.left.base a ∈ S) :
    ∃! G : A ⟶ sourceObject X S hS, G ≫ inclusion X S hS = F := by
  classical
  choose P j K hj hx hfac using exists_local_factorization X S hS A F hland
  let U (a : A.obj.left) := (P a).obj.left
  let J (a : A.obj.left) : U a ⟶ A.obj.left := (j a).hom.left
  let : ∀ a, LocallyRingedSpace.IsOpenImmersion (J a) := hj
  have hcover : ∀ a : A.obj.left, ∃ (b : A.obj.left) (u : U b), (J b).base u = a := by
    intro a
    obtain ⟨u, hu⟩ := hx a
    exact ⟨a, u, hu⟩
  have hcompat : ∀ a b, pullback.fst (J a) (J b) ≫ (K a).hom.left =
      pullback.snd (J a) (J b) ≫ (K b).hom.left := by
    intro a b
    apply (cancel_mono (inclusion X S hS).hom.left).mp
    have ha : (K a).hom.left ≫ (inclusion X S hS).hom.left = (J a) ≫ F.hom.left :=
      congrArg (fun H => H.hom.left) (hfac a)
    have hb : (K b).hom.left ≫ (inclusion X S hS).hom.left = (J b) ≫ F.hom.left :=
      congrArg (fun H => H.hom.left) (hfac b)
    simpa only [Category.assoc, ha, hb] using
      congrArg (fun H => H ≫ F.hom.left) (pullback.condition (f := J a) (g := J b))
  have hpoint (a : A.obj.left) :
      (K a).hom.left ≫ (sourceObject X S hS).obj.hom = (J a) ≫ A.obj.hom := by
    rw [Over.w (K a).hom, Over.w (j a).hom]
  obtain ⟨G, hG, _⟩ := exists_unique_over U J hcover A.obj.hom
    (sourceObject X S hS).obj.hom (fun a => (K a).hom.left) hcompat hpoint
  have hGi : G.left ≫ (inclusion X S hS).hom.left = F.hom.left := by
    apply HironakaIntrinsicMorphismGluing.hom_ext U J hcover
    intro a
    rw [← Category.assoc, hG a]
    exact congrArg (fun H => H.hom.left) (hfac a)
  refine ⟨ObjectProperty.homMk G, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hGi
  · intro G' hG'
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (inclusion X S hS).hom.left).mp
    exact (congrArg (fun H => H.hom.left) hG').trans hGi.symm

end

end Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceFactorization
