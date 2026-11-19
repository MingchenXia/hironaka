import Hironaka.Analytic.Unibranch.ReducedComplexSpaces
import Hironaka.Resolution.HironakaIntrinsicMorphismGluingAnalytic

/-!
# Full original morphisms determined by original point maps

Both original reduced complex spaces can fail global second countability.
Only actual restrictions of actual local models use native analytic charts.
The conclusion retains the entire original locally ringed/over-space maps.
Blueprint: `source-morphism-ext.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open Hironaka
open Hironaka
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaIntrinsicMorphismGluingAnalytic

namespace Hironaka.Analytic.Unibranch.SourceReducedComplexSpace

noncomputable section

private theorem exists_local_morphism_eq {A B : SourceReducedComplexSpace}
    (F G : A ⟶ B) (hbase : F.hom.left.base = G.hom.left.base) (x : A.obj.left) :
    ∃ (P : LocallyRingedSpace) (j : P ⟶ A.obj.left),
      LocallyRingedSpace.IsOpenImmersion j ∧ x ∈ range j.base ∧
      j ≫ F.hom.left = j ≫ G.hom.left := by
  obtain ⟨d, U, C, hC, i, hi, hip, c, hcx⟩ := A.property.2.2 x
  obtain ⟨e, V, D, _hD, k, hk, hkp, hFx⟩ := B.property.2.2 (F.hom.left.base x)
  let S := (modelOver U C).left
  let i₀ : S ⟶ A.obj.left := i
  let k₀ : (modelOver V D).left ⟶ B.obj.left := k
  let : LocallyRingedSpace.IsOpenImmersion i₀ := hi
  let : LocallyRingedSpace.IsOpenImmersion k₀ := hk
  have hip₀ : i₀ ≫ A.obj.hom = subspacePointMap (n := d) C := hip
  have hkp₀ : k₀ ≫ B.obj.hom = subspacePointMap (n := e) D := hkp
  let Q : Opens S.toTopCat :=
    ⟨(i₀ ≫ F.hom.left).base ⁻¹' range k₀.base,
      hk.base_open.isOpen_range.preimage (i₀ ≫ F.hom.left).base.hom.continuous⟩
  let P := S.restrict Q.isOpenEmbedding
  let p : P ⟶ S := S.ofRestrict Q.isOpenEmbedding
  let hp : LocallyRingedSpace.IsOpenImmersion p := by
    dsimp only [p, P]
    infer_instance
  let j : P ⟶ A.obj.left := p ≫ i₀
  have hcQ : c ∈ Q := by
    change F.hom.left.base (i₀.base c) ∈ range k₀.base
    rw [hcx]
    exact hFx
  have hF : range (j ≫ F.hom.left).base ⊆ range k₀.base := by
    rintro _ ⟨u, rfl⟩
    exact u.property
  have hG : range (j ≫ G.hom.left).base ⊆ range k₀.base := by
    rintro _ ⟨u, rfl⟩
    change G.hom.left.base (i₀.base u.val) ∈ range k₀.base
    rw [← hbase]
    exact u.property
  let L := LocallyRingedSpace.IsOpenImmersion.lift k₀ (j ≫ F.hom.left) hF
  let R := LocallyRingedSpace.IsOpenImmersion.lift k₀ (j ≫ G.hom.left) hG
  have hL : L ≫ k₀ = j ≫ F.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac k₀ _ hF
  have hR : R ≫ k₀ = j ≫ G.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac k₀ _ hG
  have hP : hasAnalyticCharts (Over.mk (j ≫ A.obj.hom)) := by
    have hP₀ := @hasAnalyticCharts_of_openImmersion P S
      (p ≫ subspacePointMap (n := d) C) (subspacePointMap (n := d) C)
      (hasAnalyticCharts_model U C hC) p hp rfl
    change hasAnalyticCharts (Over.mk ((p ≫ i₀) ≫ A.obj.hom))
    rw [Category.assoc, hip₀]
    exact hP₀
  have hLp : L ≫ subspacePointMap (n := e) D = j ≫ A.obj.hom := by
    rw [← hkp₀, ← Category.assoc, hL, Category.assoc, Over.w F.hom]
  have hRp : R ≫ subspacePointMap (n := e) D = j ≫ A.obj.hom := by
    rw [← hkp₀, ← Category.assoc, hR, Category.assoc, Over.w G.hom]
  have hLRbase : L.base = R.base := by
    ext u
    apply hk.base_open.injective
    calc
      k₀.base (L.base u) = (j ≫ F.hom.left).base u :=
        congrArg (fun f => f.base u) hL
      _ = (j ≫ G.hom.left).base u := by
        simp only [LocallyRingedSpace.comp_base, hbase]
      _ = k₀.base (R.base u) := (congrArg (fun f => f.base u) hR).symm
  have hLR : L = R :=
    HironakaIntrinsicMorphismGluingAnalytic.morphism_eq_of_base_eq
      (j ≫ A.obj.hom) hP L R hLp hRp hLRbase
  refine ⟨P, j, inferInstance, ?_, ?_⟩
  · exact ⟨⟨c, hcQ⟩, hcx⟩
  · exact hL.symm.trans ((congrArg (fun f => f ≫ k₀) hLR).trans hR)

/-- FULL morphism equality on the original Hausdorff/paracompact source and
target from equality of original point maps, without global countability. -/
theorem morphism_eq_of_base_eq {A B : SourceReducedComplexSpace}
    (F G : A ⟶ B) (hbase : F.hom.left.base = G.hom.left.base) : F = G := by
  classical
  choose P j hj hx heq using exists_local_morphism_eq F G hbase
  let : ∀ x, LocallyRingedSpace.IsOpenImmersion (j x) := hj
  have hcover : ∀ x : A.obj.left, ∃ (a : A.obj.left) (u : P a), (j a).base u = x := by
    intro x
    obtain ⟨u, hu⟩ := hx x
    exact ⟨x, u, hu⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact HironakaIntrinsicMorphismGluing.hom_ext P j hcover F.hom.left G.hom.left heq

/-- The pointwise form retains the entire original structure-sheaf map. -/
theorem morphism_eq_of_pointwise_eq {A B : SourceReducedComplexSpace}
    (F G : A ⟶ B) (h : ∀ x, F.hom.left.base x = G.hom.left.base x) : F = G := by
  apply morphism_eq_of_base_eq F G
  ext x
  exact h x

end

end Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
