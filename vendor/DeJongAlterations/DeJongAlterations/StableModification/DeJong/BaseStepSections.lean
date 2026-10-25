import DeJongAlterations.StableModification.DeJong.Interface
import DeJongAlterations.Geometry.FiniteBirationalNormalReducedSectionCoverExistence
import DeJongAlterations.Geometry.CurveFibrationBaseChangeSmooth
import DeJongAlterations.Geometry.ProjectiveReduction

/-!
# Splitting the marks into disjoint sections

In de Jong's base step 4.22 (`dejong96-alterations:page-0025`, `page-0026`) the horizontal
boundary is a union of disjoint sections `τ_i : Y → sm(X/Y)` (situation 4.23). With
Temkin's stable modification the marks `D' ⊆ C'` are finite étale over the base `S'`
(Temkin §1.2, `semi-stable.tex` l.1683–1687); they become a disjoint union of sections after
a finite base change splitting their generic fibre (the role of de Jong 4.16,
`page-0022`). This file proves this (`lem:sm-dj-split-marks`):

* `isOpenImmersion_of_comp_eq_id`, `isClosedImmersion_of_comp_eq_id`: a section of an
  unramified (resp. separated) morphism is an open (resp. closed) immersion (it is a base
  change of the diagonal, EGA IV 17.4.1.2);
* `eq_of_sections_of_range_inter_nonempty`: two sections of an unramified separated morphism
  over a connected base are equal as soon as their images meet;
* `range_eq_preimage_of_isPullback_section`: base change of sections;
* `exists_split_marks`: over a proper variety `S`, finite étale marks `D ⊆ C` become, after
  a projective alteration `ν : S'' → S`, a finite disjoint union of sections of
  `C ×_S S'' → S''` covering the preimage of `D`. The proof uses Chow's lemma
  (`Geometry.ProjectiveReduction.exists_projective_modification_of_isProper`) and Codex's
  Galois normalization
  `Geometry.FiniteBirationalNormal.exists_galois_normalization_reduced_section_cover`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Sections

variable {D S T : Scheme.{u}}

/-- A section of a morphism is the base change of its diagonal. -/
theorem isPullback_section (q : D ⟶ S) (s : S ⟶ D) (hs : s ≫ q = 𝟙 S) :
    IsPullback s (pullback.lift (𝟙 S) s (by simp [hs])) (pullback.diagonal q)
      (pullback.map (s ≫ q) q q q s (𝟙 D) (𝟙 S) (by simp) (by simp)) :=
  pullback_lift_diagonal_isPullback s q

/-- A section of a formally unramified morphism locally of finite type is an open
immersion. -/
theorem isOpenImmersion_of_comp_eq_id (q : D ⟶ S) [FormallyUnramified q] [LocallyOfFiniteType q]
    (s : S ⟶ D) (hs : s ≫ q = 𝟙 S) : IsOpenImmersion s := by
  have h1 : IsOpenImmersion (pullback.lift (𝟙 S) s (by simp [hs]) : S ⟶ pullback (s ≫ q) q) :=
    MorphismProperty.of_isPullback (isPullback_section q s hs) inferInstance
  have : IsIso (s ≫ q) := by rw [hs]; infer_instance
  have h2 : s = pullback.lift (𝟙 S) s (by simp [hs]) ≫ pullback.snd (s ≫ q) q := by simp
  rw [h2]
  infer_instance

/-- A section of a separated morphism is a closed immersion. -/
theorem isClosedImmersion_of_comp_eq_id (q : D ⟶ S) [IsSeparated q]
    (s : S ⟶ D) (hs : s ≫ q = 𝟙 S) : IsClosedImmersion s := by
  have h1 : IsClosedImmersion (pullback.lift (𝟙 S) s (by simp [hs]) : S ⟶ pullback (s ≫ q) q) :=
    MorphismProperty.of_isPullback (isPullback_section q s hs) inferInstance
  have : IsIso (s ≫ q) := by rw [hs]; infer_instance
  have h2 : s = pullback.lift (𝟙 S) s (by simp [hs]) ≫ pullback.snd (s ≫ q) q := by simp
  rw [h2]
  infer_instance

/-- The image of a section of an unramified separated morphism is open and closed. -/
theorem isClopen_range_of_comp_eq_id (q : D ⟶ S) [FormallyUnramified q] [LocallyOfFiniteType q]
    [IsSeparated q] (s : S ⟶ D) (hs : s ≫ q = 𝟙 S) : IsClopen (Set.range s) := by
  have := isOpenImmersion_of_comp_eq_id q s hs
  have := isClosedImmersion_of_comp_eq_id q s hs
  exact ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩

/-- **Sections of an unramified separated morphism over a connected base** are equal as soon
as their images meet. -/
theorem eq_of_sections_of_range_inter_nonempty [PreconnectedSpace S] (q : D ⟶ S)
    [FormallyUnramified q] [LocallyOfFiniteType q] [IsSeparated q] (s t : S ⟶ D)
    (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S) (hst : (Set.range s ∩ Set.range t).Nonempty) :
    s = t := by
  have hsub : ∀ (a b : S ⟶ D), a ≫ q = 𝟙 S → b ≫ q = 𝟙 S →
      (Set.range a ∩ Set.range b).Nonempty → Set.range a ⊆ Set.range b := by
    intro a b ha hb hab
    have hb' := isClopen_range_of_comp_eq_id q b hb
    have hpre : IsClopen (a ⁻¹' Set.range b) := hb'.preimage a.continuous
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hab
    have huniv : a ⁻¹' Set.range b = Set.univ :=
      (isClopen_iff.mp hpre).resolve_left fun h ↦ by
        have : y ∈ a ⁻¹' Set.range b := hy
        rw [h] at this
        exact this
    rintro _ ⟨z, rfl⟩
    have : z ∈ a ⁻¹' Set.range b := huniv ▸ Set.mem_univ z
    exact this
  have hrange : Set.range s = Set.range t :=
    (hsub s t hs ht hst).antisymm (hsub t s ht hs (Set.inter_comm _ _ ▸ hst))
  have := isOpenImmersion_of_comp_eq_id q s hs
  have := isOpenImmersion_of_comp_eq_id q t ht
  have he : (IsOpenImmersion.isoOfRangeEq s t hrange).hom = 𝟙 S := by
    have h1 : (IsOpenImmersion.isoOfRangeEq s t hrange).hom ≫ t ≫ q = s ≫ q := by
      rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
    rw [ht, hs, Category.comp_id] at h1
    exact h1
  have h2 := IsOpenImmersion.isoOfRangeEq_hom_fac s t hrange
  rw [he, Category.id_comp] at h2
  exact h2.symm

/-- The image of a section of an unramified separated morphism over an irreducible base is
an irreducible component. -/
theorem range_mem_irreducibleComponents_of_comp_eq_id [IrreducibleSpace S] (q : D ⟶ S)
    [FormallyUnramified q] [LocallyOfFiniteType q] [IsSeparated q] (s : S ⟶ D)
    (hs : s ≫ q = 𝟙 S) : Set.range s ∈ irreducibleComponents D := by
  have hirr : IsIrreducible (Set.range s) := by
    rw [← Set.image_univ]
    exact ((irreducibleSpace_def S).mp inferInstance).image s s.continuous.continuousOn
  refine ⟨hirr, fun K hK hsK ↦ ?_⟩
  exact (IsPreirreducible.isPreconnected hK.2).subset_isClopen (isClopen_range_of_comp_eq_id q s hs)
    (by obtain ⟨x, hx⟩ := hirr.nonempty; exact ⟨x, hsK hx, hx⟩)

/-- Range of a cartesian projection. -/
theorem range_fst_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst f g, ← H.isoPullback_hom_fst, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr H.isoPullback.hom.surjective,
    Set.image_univ]

/-- **Base change of sections.** In a cartesian square `C' = C ×_S T`, the base change
`τ : T → C'` of a section `ε` of `C → S` has image the preimage of the image of `ε`. -/
theorem range_eq_preimage_of_isPullback_section {C C' : Scheme.{u}} {r : C' ⟶ C} {g' : C' ⟶ T}
    {q : C ⟶ S} {a : T ⟶ S} (H : IsPullback r g' q a) (ε : S ⟶ C) (hε : ε ≫ q = 𝟙 S)
    (τ : T ⟶ C') (hτr : τ ≫ r = a ≫ ε) (hτg : τ ≫ g' = 𝟙 T) :
    Set.range τ = r ⁻¹' Set.range ε := by
  have Hout : IsPullback (τ ≫ g') a a (ε ≫ q) := by
    rw [hτg, hε]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact range_fst_of_isPullback (IsPullback.of_right Hout hτr H.flip)

end Sections

section Split

variable {k : Type u} [Field k] {S C : Scheme.{u}}

/-- **Splitting finite étale marks into disjoint sections** (`lem:sm-dj-split-marks`). Let
`S` be a proper variety over `k`, `g : C → S` a morphism and `D ⊆ C` a closed subscheme
finite étale over `S`. Then there are a projective alteration `ν : S'' → S` from a projective
variety and finitely many sections `τ_i` of `C ×_S S'' → S''` with pairwise disjoint images,
contained in the preimage of `D`, whose images cover the preimage of `D`. -/
theorem exists_split_marks (pS : S ⟶ Spec (.of k)) [IsVariety pS] [IsProper pS] (g : C ⟶ S)
    (D : C.IdealSheafData) [Etale (D.subschemeι ≫ g)] [IsFinite (D.subschemeι ≫ g)] :
    ∃ (S'' : Scheme.{u}) (ν : S'' ⟶ S) (n : ℕ) (τ : Fin n → (S'' ⟶ pullback g ν)),
      IsAlteration ν ∧ IsVariety (ν ≫ pS) ∧ IsProjectiveOver (ν ≫ pS) ∧
      (∀ i, τ i ≫ pullback.snd g ν = 𝟙 S'') ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (τ i)) (Set.range (τ j))) ∧
      (∀ i y, pullback.fst g ν (τ i y) ∈ (D.support : Set C)) ∧
      (∀ x : (pullback g ν : Scheme.{u}), pullback.fst g ν x ∈ (D.support : Set C) →
        ∃ i, x ∈ Set.range (τ i)) := by
  -- Chow's lemma
  obtain ⟨Sp, χ, hχ, hvarp, hprojp⟩ :=
    Geometry.ProjectiveReduction.exists_projective_modification_of_isProper pS
  let := hχ
  let := hvarp
  let : IsIntegral Sp := hχ.sourceIntegral
  -- the marks over the projective model
  let Z := pullback (D.subschemeι ≫ g) χ
  let f : Z ⟶ Sp := pullback.snd (D.subschemeι ≫ g) χ
  have : Etale f := by dsimp [f, Z]; infer_instance
  have : IsFinite f := by dsimp [f, Z]; infer_instance
  have : Flat f := by dsimp [f, Z]; infer_instance
  have : IsReduced Z := Geometry.CurveFibrationBaseChange.isReduced_of_smooth_integral_base f
  obtain ⟨L, hfinite, -, hvar, -, hfin, halt, -, hproj, hsec, hcov⟩ :=
    Geometry.FiniteBirationalNormal.exists_galois_normalization_reduced_section_cover
      (χ ≫ pS) hprojp f (isGenericallyEtale_of_etale f)
  let := hfinite
  let S'' := Geometry.NormalizationInExtension.normalization Sp L
  let ν₀ : S'' ⟶ Sp := Geometry.NormalizationInExtension.normalizationStructure Sp L
  let := halt
  let := hvar
  let ν : S'' ⟶ S := ν₀ ≫ χ
  have : IsIntegral S'' := halt.sourceIntegral
  -- the comparison map from the split marks to the base change of the curve
  let m : pullback f ν₀ ⟶ pullback g ν :=
    pullback.lift (pullback.fst f ν₀ ≫ pullback.fst (D.subschemeι ≫ g) χ ≫ D.subschemeι)
      (pullback.snd f ν₀) (by
        have h1 : pullback.fst (D.subschemeι ≫ g) χ ≫ D.subschemeι ≫ g = f ≫ χ :=
          pullback.condition
        have h2 : pullback.fst f ν₀ ≫ f = pullback.snd f ν₀ ≫ ν₀ := pullback.condition
        simp only [Category.assoc, ν]
        rw [h1, ← Category.assoc, h2, Category.assoc])
  have hmsnd : m ≫ pullback.snd g ν = pullback.snd f ν₀ := pullback.lift_snd _ _ _
  have hmfst : m ≫ pullback.fst g ν =
      (pullback.fst f ν₀ ≫ pullback.fst (D.subschemeι ≫ g) χ) ≫ D.subschemeι := by
    simp [m]
  have Hm : IsPullback m (pullback.fst f ν₀ ≫ pullback.fst (D.subschemeι ≫ g) χ)
      (pullback.fst g ν) D.subschemeι := by
    refine IsPullback.of_right ?_ hmfst (IsPullback.of_hasPullback g ν).flip
    rw [hmsnd]
    exact (IsPullback.of_hasPullback f ν₀).flip.paste_vert
      (IsPullback.of_hasPullback (D.subschemeι ≫ g) χ).flip
  have : IsClosedImmersion m := MorphismProperty.of_isPullback Hm.flip inferInstance
  -- the sections of the split marks
  let q : pullback f ν₀ ⟶ S'' := pullback.snd f ν₀
  have : PreconnectedSpace S'' := inferInstance
  have hqsec : ∀ σ ∈ Set.range (fun a : Σ C : irreducibleComponents Z,
      Geometry.FiniteBirationalNormal.reducedComponentEmbeddings f L C ↦
        Geometry.FiniteBirationalNormal.reducedComponentSection f L a.1 a.2), σ ≫ q = 𝟙 S'' := by
    rintro _ ⟨a, rfl⟩
    exact (hsec a.1 a.2).1
  let R : Set (S'' ⟶ pullback f ν₀) := Set.range (fun a : Σ C : irreducibleComponents Z,
      Geometry.FiniteBirationalNormal.reducedComponentEmbeddings f L C ↦
        Geometry.FiniteBirationalNormal.reducedComponentSection f L a.1 a.2)
  have : IsNoetherian (pullback f ν₀ : Scheme.{u}) := by
    have : LocallyOfFiniteType (q ≫ ν₀ ≫ χ ≫ pS) := by
      dsimp [q]; infer_instance
    have : QuasiCompact (q ≫ ν₀ ≫ χ ≫ pS) := by dsimp [q]; infer_instance
    have : IsLocallyNoetherian (pullback f ν₀ : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian (q ≫ ν₀ ≫ χ ≫ pS)
    have : CompactSpace (pullback f ν₀ : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (q ≫ ν₀ ≫ χ ≫ pS)
    exact ⟨⟩
  have hRfin : R.Finite := by
    have hinj : Set.InjOn (fun σ : S'' ⟶ pullback f ν₀ ↦ Set.range σ) R := by
      intro σ hσ σ' hσ' h
      apply eq_of_sections_of_range_inter_nonempty q σ σ' (hqsec σ hσ) (hqsec σ' hσ')
      have h' : Set.range σ = Set.range σ' := h
      obtain ⟨y⟩ := (inferInstance : Nonempty S'')
      exact ⟨σ y, ⟨y, rfl⟩, h' ▸ ⟨y, rfl⟩⟩
    refine Set.Finite.of_finite_image ?_ hinj
    refine Set.Finite.subset NoetherianSpace.finite_irreducibleComponents ?_
    rintro _ ⟨σ, hσ, rfl⟩
    exact range_mem_irreducibleComponents_of_comp_eq_id q σ (hqsec σ hσ)
  have : Finite R := hRfin.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin R
  let τ : Fin n → (S'' ⟶ pullback g ν) := fun i ↦ (e.symm i).1 ≫ m
  refine ⟨S'', ν, n, τ, IsAlteration.comp ν₀ χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ν] using hvar
  · simpa [ν] using hproj
  · intro i
    simp only [τ, Category.assoc, hmsnd]
    exact hqsec _ (e.symm i).2
  · intro i j hij
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨y, rfl⟩, ⟨y', hy'⟩⟩
    apply hij
    have hinj : Function.Injective m := m.isClosedEmbedding.injective
    have h1 : (e.symm j).1 y' = (e.symm i).1 y := hinj hy'
    have h2 : (e.symm i).1 = (e.symm j).1 :=
      eq_of_sections_of_range_inter_nonempty q _ _ (hqsec _ (e.symm i).2)
        (hqsec _ (e.symm j).2) ⟨(e.symm i).1 y, ⟨y, rfl⟩, ⟨y', h1⟩⟩
    exact e.symm.injective (Subtype.ext h2)
  · intro i y
    simp only [τ, Scheme.Hom.comp_apply]
    rw [← Scheme.Hom.comp_apply, hmfst, Scheme.Hom.comp_apply,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩
  · intro x hx
    have hxm : x ∈ Set.range m := by
      rw [range_fst_of_isPullback Hm, Scheme.IdealSheafData.range_subschemeι]
      exact hx
    obtain ⟨z, rfl⟩ := hxm
    have hz : z ∈ ⋃ C : irreducibleComponents Z,
        ⋃ σ : Geometry.FiniteBirationalNormal.reducedComponentEmbeddings f L C,
          Set.range (Geometry.FiniteBirationalNormal.reducedComponentSection f L C σ) := by
      rw [hcov]; trivial
    simp only [Set.mem_iUnion] at hz
    obtain ⟨C, σ, y, rfl⟩ := hz
    let r : R := ⟨_, ⟨⟨C, σ⟩, rfl⟩⟩
    refine ⟨e r, y, ?_⟩
    simp only [τ, Equiv.symm_apply_apply, Scheme.Hom.comp_apply]
    rfl

end Split

end DeJongAlterations.StableModification.DeJong
