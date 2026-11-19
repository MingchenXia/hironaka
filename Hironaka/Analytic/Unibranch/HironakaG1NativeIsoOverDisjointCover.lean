import Hironaka.Analytic.Unibranch.HironakaG11ModificationCalculus

/-! # Prescribed original isomorphism loci under disjoint native covers

The given actual local squares and original isomorphism-over witnesses derive
the global original witness on the SAME prescribed set.  No global inverse,
stalk-isomorphism packet, finiteness, compactness, or uniform dimension is input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeIsoOverDisjointCover

open SourceReducedComplexSpace

noncomputable section

/-- Actual disjoint target covers and covering source squares descend the SAME
prescribed full original isomorphism locus. -/
theorem isIsoOver_of_disjoint_cover {ι : Type} {Y Z : SourceReducedComplexSpace}
    (f : Z ⟶ Y) {M A : ι → SourceReducedComplexSpace}
    (j : ∀ i, M i ⟶ Y) (L : ∀ i, A i ⟶ Z) (q : ∀ i, A i ⟶ M i)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hL : ∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left)
    (hjcover : ∀ y : Y.obj.left, ∃ (i : ι) (m : (M i).obj.left), (j i).hom.left.base m = y)
    (hLcover : ∀ z : Z.obj.left, ∃ (i : ι) (a : (A i).obj.left), (L i).hom.left.base a = z)
    (hdisj : Pairwise (fun i k =>
      Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (hsq : ∀ i, L i ≫ f = q i ≫ j i)
    (U : Set Y.obj.left) (hU : IsOpen U)
    (hq : ∀ i, IsIsoOver (q i) ((j i).hom.left.base ⁻¹' U)) : IsIsoOver f U := by
  choose V u hu hur hqu hqur using hq
  let v (i : ι) := u i ≫ (L i).hom.left
  have hv (i : ι) : LocallyRingedSpace.IsOpenImmersion (v i) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (u i) (hu i) _ (hL i)
  have hsq' (i : ι) : v i ≫ f.hom.left =
      (u i ≫ (q i).hom.left) ≫ (j i).hom.left := by
    have h := congrArg (fun F : A i ⟶ Y => F.hom.left) (hsq i)
    change (L i).hom.left ≫ f.hom.left = (q i).hom.left ≫ (j i).hom.left at h
    change (u i ≫ (L i).hom.left) ≫ f.hom.left = _
    rw [Category.assoc, h, ← Category.assoc]
  have hvf (i : ι) : LocallyRingedSpace.IsOpenImmersion (v i ≫ f.hom.left) := by
    rw [hsq']
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ (hqu i) _ (hj i)
  have hvU (i : ι) (a : V i) : f.hom.left.base ((v i).base a) ∈ U := by
    have hqa : (q i).hom.left.base ((u i).base a) ∈ (j i).hom.left.base ⁻¹' U := by
      rw [← hqur i]
      exact ⟨a, rfl⟩
    have hpt := congrArg (fun F : V i ⟶ Y.obj.left => F.base a) (hsq' i)
    exact hpt.symm ▸ hqa
  have hvcover (z : Z.obj.left) (hz : f.hom.left.base z ∈ U) :
      ∃ (i : ι) (a : V i), (v i).base a = z := by
    obtain ⟨i, a, rfl⟩ := hLcover z
    have hqa : a ∈ (q i).hom.left.base ⁻¹' ((j i).hom.left.base ⁻¹' U) := by
      have hpt := congrArg (fun F : A i ⟶ Y => F.hom.left.base a) (hsq i)
      change f.hom.left.base ((L i).hom.left.base a) =
        (j i).hom.left.base ((q i).hom.left.base a) at hpt
      change (j i).hom.left.base ((q i).hom.left.base a) ∈ U
      rw [← hpt]
      exact hz
    rw [← hur i] at hqa
    obtain ⟨b, rfl⟩ := hqa
    exact ⟨i, b, rfl⟩
  let O : Opens Z.obj.left.toTopCat := ⟨f.hom.left.base ⁻¹' U,
    hU.preimage f.hom.left.base.hom.continuous⟩
  let W := Z.obj.left.restrict O.isOpenEmbedding
  let J : W ⟶ Z.obj.left := Z.obj.left.ofRestrict O.isOpenEmbedding
  have hJ : LocallyRingedSpace.IsOpenImmersion J := by
    dsimp only [J]
    infer_instance
  let : LocallyRingedSpace.IsOpenImmersion J := hJ
  have hvJ (i : ι) : range (v i).base ⊆ range J.base := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨(v i).base a, hvU i a⟩, rfl⟩
  let l (i : ι) : V i ⟶ W := LocallyRingedSpace.IsOpenImmersion.lift J (v i) (hvJ i)
  have hlJ (i : ι) : l i ≫ J = v i :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac J (v i) (hvJ i)
  have hl (i : ι) : LocallyRingedSpace.IsOpenImmersion (l i) := by
    let : LocallyRingedSpace.IsOpenImmersion (v i) := hv i
    let : IsIso (pullback.snd J (v i)) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset J (v i) (hvJ i)
    dsimp only [l, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  let K := J ≫ f.hom.left
  have hlK (i : ι) : l i ≫ K = v i ≫ f.hom.left := by
    rw [← Category.assoc, hlJ]
  have hcomp (i : ι) : LocallyRingedSpace.IsOpenImmersion (l i ≫ K) :=
    (hlK i).symm ▸ hvf i
  have hlcover (w : W) : ∃ (i : ι) (a : V i), (l i).base a = w := by
    obtain ⟨i, a, ha⟩ := hvcover w.val w.property
    refine ⟨i, a, hJ.base_open.injective ?_⟩
    change (l i ≫ J).base a = J.base w
    rw [hlJ i]
    exact ha
  have hKinj : Function.Injective K.base := by
    intro z w hzw
    obtain ⟨i, a, rfl⟩ := hlcover z
    obtain ⟨k, b, rfl⟩ := hlcover w
    have hpoint (s : ι) (c : V s) : K.base ((l s).base c) =
        (j s).hom.left.base ((q s).hom.left.base ((u s).base c)) := by
      exact congrArg (fun F : V s ⟶ Y.obj.left => F.base c) ((hlK s).trans (hsq' s))
    by_cases hik : i = k
    · subst k
      exact congrArg (l i).base ((hcomp i).base_open.injective hzw)
    · exact (disjoint_left.mp (hdisj hik)
        ⟨_, (hpoint i a).symm⟩ ⟨_, (hpoint k b).symm.trans hzw.symm⟩).elim
  have hKO : LocallyRingedSpace.IsOpenImmersion K := by
    let s : (Σ i, V i) → W := fun a => (l a.1).base a.2
    have hs : Continuous s := continuous_sigma fun i => (l i).base.hom.continuous
    have hsurj : Function.Surjective s := by
      intro w
      obtain ⟨i, a, ha⟩ := hlcover w
      exact ⟨⟨i, a⟩, ha⟩
    have hopen : IsOpenMap (K.base ∘ s) :=
      isOpenMap_sigma.mpr fun i => (hcomp i).base_open.isOpenMap
    have hemb : IsOpenEmbedding K.base :=
      IsOpenEmbedding.of_continuous_injective_isOpenMap K.base.hom.continuous hKinj
        (IsOpenMap.of_comp hs hsurj hopen)
    have : ∀ w : W, IsIso (K.stalkMap w) := by
      intro w
      obtain ⟨i, a, rfl⟩ := hlcover w
      let : LocallyRingedSpace.IsOpenImmersion (l i) := hl i
      let : LocallyRingedSpace.IsOpenImmersion (l i ≫ K) := hcomp i
      have hc : IsIso ((l i ≫ K).stalkMap a) := by infer_instance
      rw [LocallyRingedSpace.stalkMap_comp] at hc
      have : IsIso (K.stalkMap ((l i).base a) ≫ (l i).stalkMap a) := hc
      exact IsIso.of_isIso_comp_right _ ((l i).stalkMap a)
    exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso K hemb
  refine ⟨W, J, hJ, Subtype.range_coe, hKO, ?_⟩
  apply subset_antisymm
  · rintro y ⟨w, rfl⟩
    exact w.property
  · intro y hy
    obtain ⟨i, m, rfl⟩ := hjcover y
    have hm : m ∈ range (u i ≫ (q i).hom.left).base := by
      rw [hqur i]
      exact hy
    obtain ⟨a, ha⟩ := hm
    refine ⟨⟨(v i).base a, hvU i a⟩, ?_⟩
    have hp := congrArg (fun F : V i ⟶ Y.obj.left => F.base a) (hsq' i)
    change (v i ≫ f.hom.left).base a = (j i).hom.left.base m
    exact hp.trans (congrArg (j i).hom.left.base ha)

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeIsoOverDisjointCover
