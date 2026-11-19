import Hironaka.Analytic.Unibranch.HironakaG10ChowGeometricBlowupIsoOver

/-! Full prescribed isomorphism loci descend on actual saturated native covers.
Blueprint first: `original-native-iso-over-saturated-cover.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeIsoOverSaturatedCover
noncomputable section
open SourceReducedComplexSpace

/-- Arbitrarily overlapping target OIs and exact source saturation descend full IsIsoOver. -/
theorem isIsoOver_of_saturated_cover {ι : Type} {X Z : SourceReducedComplexSpace}
    (f : Z ⟶ X) {B A : ι → SourceReducedComplexSpace}
    (J : ∀ i, B i ⟶ X) (L : ∀ i, A i ⟶ Z) (q : ∀ i, A i ⟶ B i)
    (hJ : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left)
    (hL : ∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left)
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (b : (B i).obj.left), (J i).hom.left.base b = x)
    (hsq : ∀ i, L i ≫ f = q i ≫ J i)
    (hsat : ∀ i, range (L i).hom.left.base = f.hom.left.base ⁻¹' range (J i).hom.left.base)
    (G : Set X.obj.left) (hG : IsOpen G)
    (hq : ∀ i, IsIsoOver (q i) ((J i).hom.left.base ⁻¹' G)) : IsIsoOver f G := by
  classical
  choose V u hu hur hqu hqur using hq
  let v (i : ι) := u i ≫ (L i).hom.left
  have hv (i : ι) : LocallyRingedSpace.IsOpenImmersion (v i) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (u i) (hu i) _ (hL i)
  have hsq' (i : ι) : v i ≫ f.hom.left =
      (u i ≫ (q i).hom.left) ≫ (J i).hom.left := by
    have h := congrArg (fun F : A i ⟶ X => F.hom.left) (hsq i)
    change (L i).hom.left ≫ f.hom.left = (q i).hom.left ≫ (J i).hom.left at h
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => u i ≫ a) h).trans (Category.assoc _ _ _).symm)
  have hvf (i : ι) : LocallyRingedSpace.IsOpenImmersion (v i ≫ f.hom.left) := by
    rw [hsq']
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ (hqu i) _ (hJ i)
  have hvG (i : ι) (a : V i) : f.hom.left.base ((v i).base a) ∈ G := by
    have hqa : (q i).hom.left.base ((u i).base a) ∈ (J i).hom.left.base ⁻¹' G := by
      rw [← hqur i]
      exact ⟨a,rfl⟩
    have hpt := congrArg (fun F : V i ⟶ X.obj.left => F.base a) (hsq' i)
    exact hpt.symm ▸ hqa
  have same_chart_lift (i : ι) (z : Z.obj.left) (hz : f.hom.left.base z ∈ G)
      (hzi : f.hom.left.base z ∈ range (J i).hom.left.base) :
      ∃ a : V i, (v i).base a = z := by
    have hzL : z ∈ range (L i).hom.left.base := (Set.ext_iff.mp (hsat i) z).mpr hzi
    obtain ⟨a,ha⟩ := hzL
    have hqa : a ∈ (q i).hom.left.base ⁻¹' ((J i).hom.left.base ⁻¹' G) := by
      have hpt := congrArg (fun F : A i ⟶ X => F.hom.left.base a) (hsq i)
      change f.hom.left.base ((L i).hom.left.base a) = (J i).hom.left.base ((q i).hom.left.base a) at hpt
      change (J i).hom.left.base ((q i).hom.left.base a) ∈ G
      rw [← hpt,ha]
      exact hz
    rw [← hur i] at hqa
    obtain ⟨b,hb⟩ := hqa
    exact ⟨b,(congrArg (L i).hom.left.base hb).trans ha⟩
  have hvcover (z : Z.obj.left) (hz : f.hom.left.base z ∈ G) :
      ∃ (i : ι) (a : V i), (v i).base a = z := by
    obtain ⟨i,b,hb⟩ := hcover (f.hom.left.base z)
    obtain ⟨a,ha⟩ := same_chart_lift i z hz ⟨b,hb⟩
    exact ⟨i,a,ha⟩
  let O : Opens Z.obj.left := ⟨f.hom.left.base ⁻¹' G,hG.preimage f.hom.left.base.hom.continuous⟩
  let W := Z.obj.left.restrict O.isOpenEmbedding
  let I : W ⟶ Z.obj.left := Z.obj.left.ofRestrict O.isOpenEmbedding
  have hI : LocallyRingedSpace.IsOpenImmersion I := by
    dsimp only [I]
    infer_instance
  let : LocallyRingedSpace.IsOpenImmersion I := hI
  have hvI (i : ι) : range (v i).base ⊆ range I.base := by
    rintro _ ⟨a,rfl⟩
    exact ⟨⟨(v i).base a,hvG i a⟩,rfl⟩
  let l (i : ι) : V i ⟶ W := LocallyRingedSpace.IsOpenImmersion.lift I (v i) (hvI i)
  have hlI (i : ι) : l i ≫ I = v i := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (hvI i)
  have hl (i : ι) : LocallyRingedSpace.IsOpenImmersion (l i) := by
    let : LocallyRingedSpace.IsOpenImmersion (v i) := hv i
    let : IsIso (pullback.snd I (v i)) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset I (v i) (hvI i)
    dsimp only [l,LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  let K := I ≫ f.hom.left
  have hlK (i : ι) : l i ≫ K = v i ≫ f.hom.left :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ f.hom.left) (hlI i))
  have hcomp (i : ι) : LocallyRingedSpace.IsOpenImmersion (l i ≫ K) := (hlK i).symm ▸ hvf i
  have hlcover (w : W) : ∃ (i : ι) (a : V i), (l i).base a = w := by
    obtain ⟨i,a,ha⟩ := hvcover w.val w.property
    exact ⟨i,a,hI.base_open.injective ((congrArg (fun H => H.base a) (hlI i)).trans ha)⟩
  have hKinj : Function.Injective K.base := by
    intro z w hzw
    obtain ⟨i,b,hb⟩ := hcover (K.base z)
    obtain ⟨a,ha⟩ := same_chart_lift i z.val z.property ⟨b,hb⟩
    obtain ⟨c,hc⟩ := same_chart_lift i w.val w.property ⟨b,hb.trans hzw⟩
    have hla : (l i).base a = z := hI.base_open.injective
      ((congrArg (fun H => H.base a) (hlI i)).trans ha)
    have hlc : (l i).base c = w := hI.base_open.injective
      ((congrArg (fun H => H.base c) (hlI i)).trans hc)
    have heq : (l i ≫ K).base a = (l i ≫ K).base c :=
      (congrArg K.base hla).trans (hzw.trans (congrArg K.base hlc).symm)
    exact hla.symm.trans ((congrArg (l i).base ((hcomp i).base_open.injective heq)).trans hlc)
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (l i) := hl
  let : ∀ i, LocallyRingedSpace.IsOpenImmersion (l i ≫ K) := hcomp
  have hKO : LocallyRingedSpace.IsOpenImmersion K :=
    HironakaG10ChowGeometricBlowupIsoOver.isOpenImmersion_of_cover V l hlcover K hKinj
  refine ⟨W,I,hI,Subtype.range_coe,hKO,?_⟩
  apply subset_antisymm
  · rintro _ ⟨w,rfl⟩
    exact w.property
  · intro x hx
    obtain ⟨i,b,hb⟩ := hcover x
    have hbG : b ∈ range (u i ≫ (q i).hom.left).base := by
      rw [hqur i]
      change (J i).hom.left.base b ∈ G
      rw [hb]
      exact hx
    obtain ⟨a,ha⟩ := hbG
    refine ⟨⟨(v i).base a,hvG i a⟩,?_⟩
    exact (congrArg (fun H : V i ⟶ X.obj.left => H.base a) (hsq' i)).trans
      ((congrArg (J i).hom.left.base ha).trans hb)

end
end Hironaka.Analytic.Unibranch.OriginalNativeIsoOverSaturatedCover
