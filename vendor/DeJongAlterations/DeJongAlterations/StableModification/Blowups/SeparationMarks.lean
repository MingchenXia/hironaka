import DeJongAlterations.StableModification.Blowups.Separation

/-!
# Separation of the boundary with marks

The marked form of `exists_separation` (M. Temkin, *Stable modification of relative curves*,
Lemma 4.3.2, T:3019–3046; blueprint `sm-boundary-separation.tex`,
`lem:sm-boundary-separation-marks`): if `(C, ∅)` is strictly semi-stable over `Spec A` and the
sections `σₖ` of `C` have pairwise disjoint images whose closed points have smooth charts, then
`(C, D)` is strictly semi-stable for the marks `D = ⋂ₖ ker σₖ`, the reduced union of the
sections (`isStrictlySemistable_marks`). At a point of `σₖ` the smooth chart is shifted so that
`σₖ` becomes `T = 0`, and shrunk so that `{T = 0}` is exactly `σₖ` (Temkin's equivalent
formulation of strict semi-stability, `rem:sm-strictly-semistable-marks`).

## Main results

* `comap_iInf_of_isOpenImmersion`, `ker_comap_of_comp`, `ker_comap_eq_top_of_disjoint`,
  `smoothModelMarks_comap_eq_ker`: pullbacks of the marks to charts.
* `isStrictlySemistable_smoothModel_marks`: the marked smooth model is strictly semi-stable.
* `isStrictlySemistable_marks`, and **`exists_separation_marks`**: Lemma 4.3.2 for sections, with
  `(C', ⋂ₖ ker σ'ₖ)` strictly semi-stable, hence a semi-stable pair.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

open Curves

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section IdealSheaves

variable {X Y S : Scheme.{u}}

/-- Pullback of ideal sheaves along an open immersion commutes with finite infima. -/
theorem comap_iInf_of_isOpenImmersion {ι : Type*} [Finite ι] (I : ι → Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] : (⨅ i, I i).comap f = ⨅ i, (I i).comap f := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_iInf,
    Scheme.IdealSheafData.ideal_iInf, iInf_apply, iInf_apply, Ideal.comap_iInf]
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

/-- The pullback of the ideal of a closed immersion `σ = s ≫ ι` along the open immersion `ι` is
the ideal of `s`. -/
theorem ker_comap_of_comp (σ : S ⟶ X) [IsClosedImmersion σ] (ι : Y ⟶ X) [IsOpenImmersion ι]
    (s : S ⟶ Y) (hs : s ≫ ι = σ) : σ.ker.comap ι = s.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  let l : S ⟶ pullback ι σ := pullback.lift s (𝟙 S) (by rw [hs, Category.id_comp])
  have hl : l ≫ pullback.snd ι σ = 𝟙 S := pullback.lift_snd _ _ _
  have hl' : pullback.snd ι σ ≫ l = 𝟙 _ := by
    rw [← cancel_mono (pullback.snd ι σ), Category.assoc, hl, Category.comp_id, Category.id_comp]
  have : IsIso l := ⟨⟨pullback.snd ι σ, hl, hl'⟩⟩
  have hfst : pullback.fst ι σ = inv l ≫ s := by
    rw [IsIso.eq_inv_comp, pullback.lift_fst]
  rw [hfst, Scheme.Hom.ker_comp_of_isIso]

/-- The pullback of the ideal of a closed immersion along an open immersion with disjoint image
is the unit ideal. -/
theorem ker_comap_eq_top_of_disjoint (σ : S ⟶ X) [IsClosedImmersion σ] (ι : Y ⟶ X)
    (h : ∀ y, ι y ∉ Set.range σ) : σ.ker.comap ι = ⊤ := by
  apply comap_eq_top_of_forall_notMem_support
  intro y hy
  rw [Scheme.Hom.support_ker, σ.isClosedEmbedding.isClosed_range.closure_eq] at hy
  exact h y hy

/-- The marks of the smooth model pulled back along an étale `e`, when `{e = 0}` is exactly the
image of a section `s` (the section `(s, id)` of `e⁻¹{T = 0} ⟶ Spec A` is surjective), are the
ideal of `s`. -/
theorem smoothModelMarks_comap_eq_ker {A : Type u} [CommRing A] (e : Y ⟶ Spec (.of A[X]))
    [Etale e] (s : Spec (.of A) ⟶ Y) (hs : s ≫ e = smoothModelZeroSection A)
    (hsurj : Function.Surjective (pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp]) :
      Spec (.of A) ⟶ pullback e (smoothModelZeroSection A))) :
    (smoothModelMarks A).comap e = s.ker := by
  rw [smoothModelMarks, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  set l : Spec (.of A) ⟶ pullback e (smoothModelZeroSection A) :=
    pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp])
  have hl : l ≫ pullback.snd e (smoothModelZeroSection A) = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsOpenImmersion l :=
    DeJong.isOpenImmersion_of_comp_eq_id (pullback.snd e (smoothModelZeroSection A)) l hl
  have : Epi l.base := (TopCat.epi_iff_surjective _).mpr hsurj
  have : IsIso l := IsOpenImmersion.isIso l
  have hfst : pullback.fst e (smoothModelZeroSection A) = inv l ≫ s := by
    rw [IsIso.eq_inv_comp, pullback.lift_fst]
  rw [hfst, Scheme.Hom.ker_comp_of_isIso]

end IdealSheaves

section MarkedModel

variable {A : Type u} [CommRing A]

/-- **The marked smooth model is strictly semi-stable.** -/
theorem isStrictlySemistable_smoothModel_marks :
    IsStrictlySemistable (smoothModel A) (smoothModelMarks A) := by
  intro x
  have : IsIso (⊤ : (Spec (.of A[X])).Opens).ι := inferInstanceAs (IsIso (Scheme.topIso _).hom)
  exact ⟨⊤, trivial, A, inferInstance, 𝟙 _, inferInstance,
    (⊤ : (Spec (.of A[X])).Opens).ι ≫ smoothModel A, Category.comp_id _,
    Or.inl ⟨(⊤ : (Spec (.of A[X])).Opens).ι, inferInstance, rfl, rfl⟩⟩

/-- An étale chart to the smooth model along which the marks pull back to the marks of the
model gives a strictly semi-stable open. -/
theorem isStrictlySemistable_of_chart {C Y : Scheme.{u}} {g : C ⟶ Spec (.of A)}
    {D : C.IdealSheafData} (ι : Y ⟶ C) [IsOpenImmersion ι] (e : Y ⟶ Spec (.of A[X])) [Etale e]
    (he : e ≫ smoothModel A = ι ≫ g) (hD : D.comap ι = (smoothModelMarks A).comap e) :
    IsStrictlySemistable (ι.opensRange.ι ≫ g) (D.comap ι.opensRange.ι) := by
  have h1 := (isStrictlySemistable_smoothModel_marks (A := A)).etale_comp e
  rw [he, ← hD] at h1
  have h2 := h1.etale_comp ι.isoOpensRange.inv
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, ← Scheme.IdealSheafData.comap_comp,
    Scheme.Hom.isoOpensRange_inv_comp] at h2
  exact h2

end MarkedModel

section Marks

variable {A : Type u} [CommRing A] [IsLocalRing A] {C : Scheme.{u}} {n : ℕ}

omit [IsLocalRing A] in
/-- The image of a section of a separated morphism is closed. -/
theorem isClosed_range_section {g : C ⟶ Spec (.of A)} [IsSeparated g]
    (σ : Spec (.of A) ⟶ C) (hσ : σ ≫ g = 𝟙 _) : IsClosed (Set.range σ) := by
  have := DeJong.isClosedImmersion_of_comp_eq_id g σ hσ
  exact σ.isClosedEmbedding.isClosed_range

/-- **A marked chart at a point of a section.** -/
theorem exists_marked_chart (g : C ⟶ Spec (.of A)) [IsSeparated g]
    (σ : Fin n → (Spec (.of A) ⟶ C)) (hσ : ∀ k, σ k ≫ g = 𝟙 _)
    (hdisj : ∀ k l, k ≠ l → Disjoint (Set.range (σ k)) (Set.range (σ l))) (k : Fin n)
    (hch : HasSmoothChart g (σ k (closedPoint A))) (t : Spec (.of A)) :
    ∃ (Y : Scheme.{u}) (ι : Y ⟶ C) (_ : IsOpenImmersion ι) (e : Y ⟶ Spec (.of A[X]))
      (_ : Etale e), σ k t ∈ Set.range ι ∧ e ≫ smoothModel A = ι ≫ g ∧
      (⨅ l, (σ l).ker).comap ι = (smoothModelMarks A).comap e := by
  have hcl : ∀ l, IsClosedImmersion (σ l) := fun l ↦ DeJong.isClosedImmersion_of_comp_eq_id g _ (hσ l)
  obtain ⟨Y, ι, _, e₀, _, hιk, he₀⟩ := hch
  -- the section factors through the chart
  have hrange : Set.range (σ k) ⊆ Set.range ι := by
    rintro _ ⟨t', rfl⟩
    exact ((specializes_closedPoint t').map (σ k).continuous).mem_open
      ι.isOpenEmbedding.isOpen_range hιk
  let s₀ : Spec (.of A) ⟶ Y := IsOpenImmersion.lift ι (σ k) hrange
  have hs₀ : s₀ ≫ ι = σ k := IsOpenImmersion.lift_fac _ _ _
  -- shift the coordinate so that the section becomes `T = 0`
  obtain ⟨c, hc⟩ := exists_eq_specMap_evalRingHom (s₀ ≫ e₀) (by
    rw [Category.assoc, he₀, ← Category.assoc, hs₀, hσ])
  let ψ : A[X] ≃ₐ[A] A[X] := Polynomial.taylorEquiv (-c)
  let Ψ : Spec (.of A[X]) ⟶ Spec (.of A[X]) := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have : IsIso Ψ := inferInstanceAs (IsIso (Spec.map ψ.toRingEquiv.toCommRingCatIso.hom))
  let e₁ : Y ⟶ Spec (.of A[X]) := e₀ ≫ Ψ
  have hΨ : Ψ ≫ smoothModel A = smoothModel A := by
    dsimp only [Ψ, smoothModel]
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun r ↦ ψ.commutes r)
  have he₁ : e₁ ≫ smoothModel A = ι ≫ g := by
    simp only [e₁, Category.assoc, hΨ, he₀]
  have hs₁ : s₀ ≫ e₁ = smoothModelZeroSection A := by
    simp only [e₁, ← Category.assoc, hc, Ψ, smoothModelZeroSection, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (Polynomial.ringHom_ext (fun r ↦ ?_) ?_)
    · change Polynomial.eval c (Polynomial.taylor (-c) (Polynomial.C r)) =
        Polynomial.eval 0 (Polynomial.C r)
      simp
    · change Polynomial.eval c (Polynomial.taylor (-c) X) = Polynomial.eval 0 X
      simp
  -- the zero locus of the shifted coordinate and its section
  set Z := pullback e₁ (smoothModelZeroSection A)
  let sZ : Spec (.of A) ⟶ Z := pullback.lift s₀ (𝟙 _) (by rw [hs₁, Category.id_comp])
  have hsZ : sZ ≫ pullback.snd e₁ (smoothModelZeroSection A) = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsSeparated (pullback.snd e₁ (smoothModelZeroSection A)) := by
    have : IsSeparated e₁ := by
      have : IsSeparated (e₁ ≫ smoothModel A) := by rw [he₁]; infer_instance
      exact IsSeparated.of_comp e₁ (smoothModel A)
    infer_instance
  have hclopen : IsClopen (Set.range sZ) := DeJong.isClopen_range_of_comp_eq_id _ sZ hsZ
  let jZ := pullback.fst e₁ (smoothModelZeroSection A)
  have hjZ : Function.Injective jZ := jZ.isClosedEmbedding.injective
  -- the bad set: other components of the zero locus and the other sections
  let Bad : Set Y := jZ '' (Set.range sZ)ᶜ ∪ ι ⁻¹' (⋃ l ∈ ({k}ᶜ : Set (Fin n)), Set.range (σ l))
  have hBad : IsClosed Bad := by
    refine (jZ.isClosedEmbedding.isClosedMap _ hclopen.isOpen.isClosed_compl).union ?_
    refine IsClosed.preimage ι.continuous ?_
    exact (Set.toFinite _).isClosed_biUnion fun l _ ↦ isClosed_range_section (σ l) (hσ l)
  let Y' : Y.Opens := ⟨Badᶜ, hBad.isOpen_compl⟩
  have hsY' : ∀ t', s₀ t' ∈ Y' := by
    intro t' hbad
    rcases hbad with ⟨z, hz, hzt⟩ | hbad
    · apply hz
      refine ⟨t', hjZ ?_⟩
      rw [hzt, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    · simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_compl_iff,
        Set.mem_singleton_iff] at hbad
      obtain ⟨l, hlk, t'', ht''⟩ := hbad
      rw [← Scheme.Hom.comp_apply, hs₀] at ht''
      exact Set.disjoint_left.mp (hdisj l k hlk) ⟨t'', rfl⟩ ⟨t', ht''.symm⟩
  let s : Spec (.of A) ⟶ Y'.toScheme := IsOpenImmersion.lift Y'.ι s₀ (by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨t', rfl⟩; exact hsY' t')
  have hs : s ≫ Y'.ι = s₀ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Y'.toScheme, Y'.ι ≫ ι, inferInstance, Y'.ι ≫ e₁, inferInstance, ⟨s t, ?_⟩, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Category.assoc, hs, hs₀]
  · rw [Category.assoc, he₁, Category.assoc]
  · -- the marks
    rw [comap_iInf_of_isOpenImmersion]
    have hother : ∀ l, l ≠ k → (σ l).ker.comap (Y'.ι ≫ ι) = ⊤ := by
      intro l hlk
      apply ker_comap_eq_top_of_disjoint
      intro y hy
      apply y.2
      right
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨l, hlk, hy⟩
    have hk : (σ k).ker.comap (Y'.ι ≫ ι) = s.ker :=
      ker_comap_of_comp (σ k) (Y'.ι ≫ ι) s (by rw [← Category.assoc, hs, hs₀])
    have hinf : (⨅ l, (σ l).ker.comap (Y'.ι ≫ ι)) = s.ker := by
      apply le_antisymm
      · exact (iInf_le _ k).trans hk.le
      · refine le_iInf fun l ↦ ?_
        by_cases hlk : l = k
        · subst hlk; exact hk.ge
        · rw [hother l hlk]; exact le_top
    rw [hinf]
    symm
    refine smoothModelMarks_comap_eq_ker _ s (by rw [← Category.assoc, hs, hs₁]) ?_
    -- the zero locus of the shifted coordinate on `Y'` is the section
    intro w
    let w₁ := pullback.fst (Y'.ι ≫ e₁) (smoothModelZeroSection A) w
    let a := pullback.snd (Y'.ι ≫ e₁) (smoothModelZeroSection A) w
    have hwa : e₁ (Y'.ι w₁) = smoothModelZeroSection A a := by
      change (pullback.fst (Y'.ι ≫ e₁) (smoothModelZeroSection A) ≫ (Y'.ι ≫ e₁)) w =
        (pullback.snd (Y'.ι ≫ e₁) (smoothModelZeroSection A) ≫ smoothModelZeroSection A) w
      rw [pullback.condition]
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := e₁)
      (g := smoothModelZeroSection A) (Y'.ι w₁) a hwa
    -- `z` lies on the section, since `w₁ ∈ Y'`
    obtain ⟨t', ht'⟩ : z ∈ Set.range sZ := by
      by_contra hz
      exact w₁.2 (Or.inl ⟨z, hz, hz1⟩)
    have ht'a : t' = a := by
      rw [← hz2, ← ht', ← Scheme.Hom.comp_apply, hsZ]
      rfl
    subst ht'a
    refine ⟨a, ?_⟩
    -- points of the zero locus are determined by their images in `Y'`
    apply (pullback.fst (Y'.ι ≫ e₁) (smoothModelZeroSection A)).isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    apply Y'.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hs]
    change s₀ a = Y'.ι w₁
    rw [← hz1, ← ht']
    change s₀ a = (sZ ≫ pullback.fst e₁ (smoothModelZeroSection A)) a
    rw [pullback.lift_fst]

omit [IsLocalRing A] in
/-- Away from the sections, the marks are the unit ideal. -/
theorem comap_iInf_ker_eq_top {g : C ⟶ Spec (.of A)} [IsSeparated g]
    (σ : Fin n → (Spec (.of A) ⟶ C)) (hσ : ∀ k, σ k ≫ g = 𝟙 _) (V : C.Opens)
    (hV : ∀ k, Disjoint (V : Set C) (Set.range (σ k))) :
    (⨅ k, (σ k).ker).comap V.ι = ⊤ := by
  have hcl : ∀ l, IsClosedImmersion (σ l) := fun l ↦
    DeJong.isClosedImmersion_of_comp_eq_id g _ (hσ l)
  rw [comap_iInf_of_isOpenImmersion]
  refine eq_top_iff.mpr (le_iInf fun k ↦ ?_)
  rw [ker_comap_eq_top_of_disjoint (σ k) V.ι fun y hy ↦ Set.disjoint_left.mp (hV k) y.2 hy]

omit [IsLocalRing A] in
/-- **The marks are the union of the sections**: the support of `⋂ₖ ker σₖ` is `⋃ₖ σₖ(S)`. -/
theorem support_iInf_ker {g : C ⟶ Spec (.of A)} [IsSeparated g]
    (σ : Fin n → (Spec (.of A) ⟶ C)) (hσ : ∀ k, σ k ≫ g = 𝟙 _) :
    ((⨅ k, (σ k).ker).support : Set C) = ⋃ k, Set.range (σ k) := by
  have hcl : ∀ l, IsClosedImmersion (σ l) := fun l ↦
    DeJong.isClosedImmersion_of_comp_eq_id g _ (hσ l)
  have hZ : IsClosed (⋃ k, Set.range (σ k)) :=
    isClosed_iUnion_of_finite fun k ↦ isClosed_range_section (σ k) (hσ k)
  apply le_antisymm
  · intro x hx
    by_contra hxZ
    let V : C.Opens := ⟨_, hZ.isOpen_compl⟩
    have hD := comap_iInf_ker_eq_top σ hσ V fun k ↦ Set.disjoint_left.mpr fun y hy hy' ↦
      hy (Set.mem_iUnion.mpr ⟨k, hy'⟩)
    have : (⟨x, hxZ⟩ : V.toScheme) ∈ (((⨅ k, (σ k).ker).comap V.ι).support : Set V.toScheme) := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hx
    rw [hD, Scheme.IdealSheafData.support_top] at this
    exact this
  · refine Set.iUnion_subset fun k ↦ ?_
    have h1 : ((σ k).ker.support : Set C) ⊆ ((⨅ k, (σ k).ker).support : Set C) :=
      Scheme.IdealSheafData.support_antitone (iInf_le _ k)
    rw [Scheme.Hom.support_ker, (σ k).isClosedEmbedding.isClosed_range.closure_eq] at h1
    exact h1

/-- **Strict semi-stability with the sections as marks.** If `(C, ∅)` is strictly semi-stable
and separated over the local `Spec A`, and `σₖ` are sections with pairwise disjoint images whose
closed points have smooth charts, then `(C, ⋂ₖ ker σₖ)` is strictly semi-stable. -/
theorem isStrictlySemistable_marks (g : C ⟶ Spec (.of A)) [IsSeparated g]
    (hC : IsStrictlySemistable g ⊤) (σ : Fin n → (Spec (.of A) ⟶ C)) (hσ : ∀ k, σ k ≫ g = 𝟙 _)
    (hdisj : ∀ k l, k ≠ l → Disjoint (Set.range (σ k)) (Set.range (σ l)))
    (hch : ∀ k, HasSmoothChart g (σ k (closedPoint A))) :
    IsStrictlySemistable g (⨅ k, (σ k).ker) := by
  refine IsStrictlySemistable.of_openCover fun x ↦ ?_
  by_cases hx : ∃ k t, σ k t = x
  · obtain ⟨k, t, rfl⟩ := hx
    obtain ⟨Y, ι, _, e, _, hmem, he, hD⟩ := exists_marked_chart g σ hσ hdisj k (hch k) t
    exact ⟨ι.opensRange, hmem, isStrictlySemistable_of_chart ι e he hD⟩
  · push Not at hx
    have hZ : IsClosed (⋃ k, Set.range (σ k)) :=
      isClosed_iUnion_of_finite fun k ↦ isClosed_range_section (σ k) (hσ k)
    let V : C.Opens := ⟨_, hZ.isOpen_compl⟩
    have hxV : x ∈ V := by
      change x ∉ ⋃ k, Set.range (σ k)
      simp only [Set.mem_iUnion, Set.mem_range, not_exists]
      exact fun k t h ↦ hx k t h
    refine ⟨V, hxV, ?_⟩
    rw [comap_iInf_ker_eq_top σ hσ V fun k ↦ Set.disjoint_left.mpr fun y hy hy' ↦
      hy (Set.mem_iUnion.mpr ⟨k, hy'⟩)]
    have := hC.etale_comp V.ι
    rwa [Scheme.IdealSheafData.comap_top] at this

end Marks

section Main

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [IsIntegrallyClosed A]
  [HenselianLocalRing A] [IsSepClosed (ResidueField A)] {n : ℕ}

/-- **Separation of the boundary, with marks** (M. Temkin, *Stable modification of relative
curves*, Lemma 4.3.2, T:3019–3046, for marks which are sections;
`lem:sm-boundary-separation-marks`). In the situation of `exists_separation`, the modification
`β : C' ⟶ C` can be chosen so that `(C', D')` is strictly semi-stable over `A`, hence a
semi-stable pair, where `D' = ⋂ₖ ker σ'ₖ` is the reduced union of the lifted sections. -/
theorem exists_separation_marks {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g]
    [IsIntegral C] (hC : IsStrictlySemistable g ⊤) (σ : Fin n → (Spec (.of A) ⟶ C))
    (hσ : ∀ k, σ k ≫ g = 𝟙 _) (hinj : Function.Injective σ) :
    ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (σ' : Fin n → (Spec (.of A) ⟶ C')),
      IsModification β ∧ IsSeparated (β ≫ g) ∧ (∀ k, σ' k ≫ β = σ k) ∧
      (∀ k l, k ≠ l → Disjoint (Set.range (σ' k)) (Set.range (σ' l))) ∧
      ((⨅ k, (σ' k).ker).support : Set C') = ⋃ k, Set.range (σ' k) ∧
      IsStrictlySemistable (β ≫ g) (⨅ k, (σ' k).ker) ∧
      DeJong.IsSemistablePair (β ≫ g) (⨅ k, (σ' k).ker) := by
  obtain ⟨C', β, σ', hβ, hgood', hσ', hch', hdisj'⟩ :=
    exists_separation_of_good (g := g) ⟨inferInstance, inferInstance, hC, hσ, hinj⟩
  have := hgood'.separated
  have hdisj : ∀ k l, k ≠ l → Disjoint (Set.range (σ' k)) (Set.range (σ' l)) := fun k l hkl ↦
    disjoint_range_of_apply_closedPoint_ne (β ≫ g) (σ' k) (σ' l) (hgood'.isSection k)
      (hgood'.isSection l) (hdisj' k l hkl)
  have hss := isStrictlySemistable_marks (β ≫ g) hgood'.semistable σ' hgood'.isSection hdisj hch'
  exact ⟨C', β, σ', hβ, hgood'.separated, hσ', hdisj, support_iInf_ker σ' hgood'.isSection, hss,
    hss.isSemistablePair⟩

end Main

end DeJongAlterations.StableModification.Blowups
