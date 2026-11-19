import Hironaka.Analytic.Unibranch.HironakaG10GenDisjointModification
import Hironaka.Analytic.Unibranch.HironakaG1NativeDisjointCoproduct
import Hironaka.Analytic.Unibranch.HironakaG1NativeIsoOverDisjointCover
import Hironaka.Analytic.Unibranch.HironakaG1NativeModificationIsoTransport

/-! # Finite clopen modification locality on the SAME given native source

Actual local finite modifications/full source-target squares internally derive
the global source comparison. No global comparison or endpoint/properness
certificate is supplied. Blueprint first; the existing G10 engine is reused.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG1FiniteClopenModification

open SourceReducedComplexSpace SmoothCentreModification
  HironakaG1NativeModificationIsoTransport

noncomputable section

private theorem isIso_of_isIsoOver_univ {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsIsoOver f univ) : IsIso f := by
  obtain ⟨V, j, hj, hjr, hcomp, hcompr⟩ := hf
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  have hjs : Function.Surjective j.base := range_eq_univ.mp (by simpa only [preimage_univ] using hjr)
  let : Epi j.base := (TopCat.epi_iff_surjective _).mpr hjs
  let : IsIso j := LocallyRingedSpace.IsOpenImmersion.to_iso j
  let : LocallyRingedSpace.IsOpenImmersion (j ≫ f.hom.left) := hcomp
  have hcs : Function.Surjective (j ≫ f.hom.left).base := range_eq_univ.mp hcompr
  let : Epi (j ≫ f.hom.left).base := (TopCat.epi_iff_surjective _).mpr hcs
  let : IsIso (j ≫ f.hom.left) := LocallyRingedSpace.IsOpenImmersion.to_iso (j ≫ f.hom.left)
  have : IsIso f.hom.left := IsIso.of_isIso_comp_left j f.hom.left
  have : IsIso ((Over.forget _).map f.hom) := this
  have : IsIso f.hom := isIso_of_reflects_iso f.hom (Over.forget _)
  have : IsIso ((ObjectProperty.ι _).map f) := this
  exact isIso_of_reflects_iso f (ObjectProperty.ι _)

private def coproductCoverIso {ι : Type} (A : ι → SourceReducedComplexSpace)
    {Y : SourceReducedComplexSpace} (j : ∀ i, A i ⟶ Y)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (hcover : ∀ y : Y.obj.left, ∃ (i : ι) (a : (A i).obj.left), (j i).hom.left.base a = y) :
    HironakaG1NativeDisjointCoproduct.coproduct A ≅ Y := by
  let f := HironakaG1NativeDisjointCoproduct.desc A j
  have hs (i : ι) : HironakaG1NativeDisjointCoproduct.inclusion A i ≫ f = 𝟙 (A i) ≫ j i := by
    simpa only [Category.id_comp] using HironakaG1NativeDisjointCoproduct.inclusion_desc A j i
  have hq (i : ι) : IsIsoOver (𝟙 (A i)) ((j i).hom.left.base ⁻¹' (univ : Set Y.obj.left)) := by
    simpa only [preimage_univ] using IsIsoOver.id_of_isOpen (A i) isOpen_univ
  have hgood := HironakaG1NativeIsoOverDisjointCover.isIsoOver_of_disjoint_cover
    f j (HironakaG1NativeDisjointCoproduct.inclusion A) (fun i => 𝟙 (A i)) hj
    (HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion A) hcover
    (HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective A) hdisj hs univ isOpen_univ hq
  let : IsIso f := isIso_of_isIsoOver_univ f hgood
  exact asIso f

private theorem sourcePieces_disjoint {ι : Type} {X Y : SourceReducedComplexSpace}
    {A B : ι → SourceReducedComplexSpace} (f : Y ⟶ X)
    (j : ∀ i, B i ⟶ X) (L : ∀ i, A i ⟶ Y) (q : ∀ i, A i ⟶ B i)
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (hsq : ∀ i, L i ≫ f = q i ≫ j i) :
    Pairwise (fun i k => Disjoint (range (L i).hom.left.base) (range (L k).hom.left.base)) := by
  intro i k hik
  apply disjoint_left.mpr
  rintro y ⟨a, ha⟩ ⟨b, hb⟩
  have hp (s : ι) (c : (A s).obj.left) :
      f.hom.left.base ((L s).hom.left.base c) = (j s).hom.left.base ((q s).hom.left.base c) :=
    congrArg (fun F : A s ⟶ X => F.hom.left.base c) (hsq s)
  exact disjoint_left.mp (hdisj hik)
    ⟨(q i).hom.left.base a, (hp i a).symm.trans (congrArg f.hom.left.base ha)⟩
    ⟨(q k).hom.left.base b, (hp k b).symm.trans (congrArg f.hom.left.base hb)⟩

/-- REAL local modifications and full finite clopen geometry derive IsModification
of the SAME original f, without a caller global-source comparison. -/
theorem isModification_of_finite_clopen_cover {N : ℕ} {X Y : SourceReducedComplexSpace}
    {A B : Fin N → SourceReducedComplexSpace} (f : Y ⟶ X)
    (j : ∀ i, B i ⟶ X) (L : ∀ i, A i ⟶ Y) (q : ∀ i, A i ⟶ B i)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hjc : ∀ i, IsClosed (range (j i).hom.left.base))
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (hjcover : ∀ x : X.obj.left, ∃ (i : Fin N) (b : (B i).obj.left), (j i).hom.left.base b = x)
    (hL : ∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left)
    (hLcover : ∀ y : Y.obj.left, ∃ (i : Fin N) (a : (A i).obj.left), (L i).hom.left.base a = y)
    (hq : ∀ i, IsModification (q i)) (hsq : ∀ i, L i ≫ f = q i ≫ j i) :
    IsModification f := by
  obtain ⟨W, p, J, hp, hJ, hJsq, hJcover⟩ :=
    HironakaG10GenDisjointModification.exists_isModification_of_cover j hj hjc hdisj
      (fun x => by obtain ⟨i, b, hb⟩ := hjcover x; exact ⟨i, b, hb⟩) q hq
  let a := coproductCoverIso A J hJ (sourcePieces_disjoint p j J q hdisj hJsq)
    (fun w => by obtain ⟨i, y, hy⟩ := hJcover w; exact ⟨i, y, hy⟩)
  let b := coproductCoverIso A L hL (sourcePieces_disjoint f j L q hdisj hsq) hLcover
  have hcomp : a.hom ≫ p = b.hom ≫ f := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext A
    intro i
    change HironakaG1NativeDisjointCoproduct.inclusion A i ≫
      (HironakaG1NativeDisjointCoproduct.desc A J ≫ p) =
        HironakaG1NativeDisjointCoproduct.inclusion A i ≫
          (HironakaG1NativeDisjointCoproduct.desc A L ≫ f)
    rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc,
      ← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, hJsq, hsq]
  let E : W ≅ Y := a.symm.trans b
  have hE : E.hom ≫ f = p := by
    change (a.inv ≫ b.hom) ≫ f = p
    rw [Category.assoc, ← hcomp, Iso.inv_hom_id_assoc]
  have heq : E.inv ≫ p = f := by
    rw [← hE, Iso.inv_hom_id_assoc]
  have hfinite := isModification_precomp_iso hp E.symm
  change IsModification (E.inv ≫ p) at hfinite
  rwa [heq] at hfinite

end
end Hironaka.Analytic.Unibranch.HironakaG1FiniteClopenModification
