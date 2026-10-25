import DeJongAlterations.StableModification.Global.SetupModel
import DeJongAlterations.Algebra.NodeFittingIdealSheafGluing

/-!
# Gluing stable models over an open cover of the base

Node G7 of `PLAN-T5.md` (§2.1 step 5; Temkin, *Stable modification of relative curves*,
`semi-stable.tex`, proof of Theorem 1.5, T:3394–3397): stable models `X_i ⟶ P` over the members
`U_i` of an open cover of an integral base `T`, which are locally isomorphic over `P` on the
overlaps, glue to a scheme `X ⟶ P` which is

* proper over `P`, with glued marks making `(X, D_X)` a semi-stable pair over `T`,
* numerically stable (`IsNumericallyStable`),
* with marks satisfying the generic marks condition (hence the transported marks,
  `GenericMarksCondition.eq_genericMarksClosure`),
* projective over each `g⁻¹(U_i)` (obligation E3 of PLAN-OM3 §6: local projectivity over the
  cover `g⁻¹(U_i)` of the target), and an isomorphism over a nonempty open of `T`.

Only *morphisms* over `P` near each point of the overlaps are needed: by rigidity
(`eq_of_comp_eq_of_isIso_morphismRestrict`, Temkin T:3395 "the isomorphisms are unique") they
glue to morphisms `X_i|_{U_j} ⟶ X_j` which are inverse to each other, hence open immersions, and
satisfy the cocycle condition; `Global.exists_glue` then glues the schemes, and Codex's ideal
sheaf gluing (`Algebra.NodeFittingIdealSheaf.glue`) the marks, which agree on the overlaps because
flat marks satisfying the generic marks condition are the transported marks.

* `IsStableModelOn pT g D U β D'`: a stable model of `(P, D)` over the open `U ⊆ T`, as a scheme
  over `P` lying over `U`.
* `exists_glue_isStableModelOn`: the gluing theorem.

Blueprint: `sm-global.tex`, `thm:sm-global-glue-models`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective IsSmoothAt)
open Curves (pullbackCompMap)

section Helpers

/-- An open immersion restricts to an isomorphism over an open contained in its image. -/
theorem isIso_morphismRestrict_of_isOpenImmersion {A B : Scheme.{u}} (j : A ⟶ B)
    [IsOpenImmersion j] (V : B.Opens) (hV : (V : Set B) ⊆ Set.range j) : IsIso (j ∣_ V) := by
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr fun v ↦ ?_⟩
  obtain ⟨a, ha⟩ := hV v.2
  have haV : a ∈ ((j ⁻¹ᵁ V : A.Opens) : Set A) := by
    change j a ∈ V
    rw [ha]
    exact v.2
  obtain ⟨w, hw⟩ : a ∈ Set.range (j ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    exact haV
  refine ⟨w, V.ι.isOpenEmbedding.injective ?_⟩
  change (((j ∣_ V) ≫ V.ι) w) = V.ι v
  rw [morphismRestrict_ι, Scheme.Hom.comp_apply, hw, ha]
  rfl

/-- If `β` restricted along an open immersion `j` whose image contains `β⁻¹(W)` is an isomorphism
over `W`, so is `β`. -/
theorem isIso_morphismRestrict_of_comp {A X P : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (β : X ⟶ P) (W : P.Opens) (hW : ((β ⁻¹ᵁ W : X.Opens) : Set X) ⊆ Set.range j)
    [IsIso ((j ≫ β) ∣_ W)] : IsIso (β ∣_ W) := by
  have h0 := isIso_morphismRestrict_of_isOpenImmersion j (β ⁻¹ᵁ W) hW
  have h1 : IsIso ((j ≫ β) ∣_ W) := inferInstance
  rw [morphismRestrict_comp] at h1
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h0 h1

/-- Relative projectivity can be checked after precomposing with an isomorphism. -/
theorem IsRelativelyProjective.of_iso_comp {k : Type u} [CommRing k] {T' X' X'' : Scheme.{u}}
    {pT' : T' ⟶ Spec (.of k)} {f : X' ⟶ T'} (e : X'' ⟶ X') [IsIso e]
    (h : IsRelativelyProjective pT' (e ≫ f)) : IsRelativelyProjective pT' f := by
  have h' := IsRelativelyProjective.iso_comp h (inv e)
  rwa [IsIso.inv_hom_id_assoc] at h'

/-- Relative projectivity over an open transfers from the restriction along an open immersion
whose image contains the preimage. -/
theorem isRelativelyProjective_morphismRestrict_of_comp {k : Type u} [CommRing k]
    {A X P : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j] (β : X ⟶ P) (W : P.Opens)
    (pW : W.toScheme ⟶ Spec (.of k))
    (hW : ((β ⁻¹ᵁ W : X.Opens) : Set X) ⊆ Set.range j)
    (h : IsRelativelyProjective pW ((j ≫ β) ∣_ W)) : IsRelativelyProjective pW (β ∣_ W) := by
  have h0 := isIso_morphismRestrict_of_isOpenImmersion j (β ⁻¹ᵁ W) hW
  rw [morphismRestrict_comp] at h
  exact @IsRelativelyProjective.of_iso_comp _ _ _ _ _ _ _ (j ∣_ β ⁻¹ᵁ W) h0 h

/-- **Rigidity with an isomorphism over an open of the base**: over an integral `T`, morphisms
`f₁, f₂ : X₁ ⟶ X₂` over `P` agree if `X₁` is flat over `T`, `β₂` is separated and an
isomorphism over `g⁻¹(U)` for a nonempty open `U ⊆ T`. -/
theorem eq_of_comp_eq_of_isIso_morphismRestrict {T P X₁ X₂ : Scheme.{u}} [IsIntegral T]
    (g : P ⟶ T) (β₁ : X₁ ⟶ P) (β₂ : X₂ ⟶ P) [IsSeparated β₂] [Flat (β₁ ≫ g)] (U : T.Opens)
    (hU : (U : Set T).Nonempty) [IsIso (β₂ ∣_ (g ⁻¹ᵁ U))] {f₁ f₂ : X₁ ⟶ X₂}
    (h₁ : f₁ ≫ β₂ = β₁) (h₂ : f₂ ≫ β₂ = β₁) : f₁ = f₂ := by
  have hη : genericPoint T ∈ U :=
    ((genericPoint_spec T).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have : IsIso (Curves.fiberMap β₂ g (genericPoint T)) :=
    Limits.SpreadModification.isIso_pullbackCompMap_of_isIso_morphismRestrict β₂ g U _ (by
      refine eq_top_iff.mpr fun x _ ↦ ?_
      change T.fromSpecResidueField (genericPoint T) x ∈ U
      rw [Scheme.fromSpecResidueField_apply]
      exact hη)
  exact eq_of_comp_eq_of_isIso_fiberMap g β₁ β₂ h₁ h₂

/-- **Gluing of morphisms along open immersions with rigidity** (variant of `exists_glueHom` for
covers by open immersions). -/
theorem exists_glueHom' {A Y P : Scheme.{u}} (βA : A ⟶ P) (βY : Y ⟶ P) {κ : Type u}
    (Z : κ → Scheme.{u}) (e : ∀ k, Z k ⟶ A) [∀ k, IsOpenImmersion (e k)]
    (hcov : ∀ a : A, ∃ k z, e k z = a) (m : ∀ k, Z k ⟶ Y)
    (hm : ∀ k, m k ≫ βY = e k ≫ βA)
    (rigid : ∀ (W : Scheme.{u}) (e : W ⟶ A) [IsOpenImmersion e] (a b : W ⟶ Y),
      a ≫ βY = e ≫ βA → b ≫ βY = e ≫ βA → a = b) :
    ∃ f : A ⟶ Y, f ≫ βY = βA ∧ ∀ k, e k ≫ f = m k := by
  let 𝒱 : A.OpenCover.{u} :=
    { I₀ := κ
      X := Z
      f := e
      mem₀ := (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) κ Z e hcov).mem₀ }
  have hcompat : ∀ x y, pullback.fst (𝒱.f x) (𝒱.f y) ≫ m x = pullback.snd _ _ ≫ m y := by
    intro x y
    refine rigid _ (pullback.fst (𝒱.f x) (𝒱.f y) ≫ e x) _ _ ?_ ?_
    · change pullback.fst (e x) (e y) ≫ m x ≫ βY = (pullback.fst (e x) (e y) ≫ e x) ≫ βA
      rw [hm, Category.assoc]
    · change pullback.snd (e x) (e y) ≫ m y ≫ βY = (pullback.fst (e x) (e y) ≫ e x) ≫ βA
      rw [hm, Category.assoc, pullback.condition_assoc]
  refine ⟨𝒱.glueMorphisms m hcompat, ?_, fun k ↦ 𝒱.ι_glueMorphisms m hcompat k⟩
  refine 𝒱.hom_ext _ _ fun k ↦ ?_
  rw [Scheme.Cover.ι_glueMorphisms_assoc]
  exact hm k

end Helpers

section Model

variable {k : Type u} [CommRing k] {T P X : Scheme.{u}}

/-- **A stable model over an open of the base** (`PLAN-T5.md` §2.1 step 5): over the integral
`T` with `g : P ⟶ T`, the morphism `β : X ⟶ P` lies over the open `U ⊆ T`; `(X, D')` is a
semi-stable pair over `T` satisfying the generic marks condition and numerically stable; `β` is
projective over `g⁻¹(U)` relative to `g⁻¹(U) ⟶ P ⟶ T ⟶ Spec k`, and an isomorphism over a
nonempty open `U° ⊆ U` with quasi-compact inclusion. -/
structure IsStableModelOn [IsIntegral T] (pT : T ⟶ Spec (.of k)) (g : P ⟶ T)
    (D : P.IdealSheafData) (U : T.Opens) (β : X ⟶ P) (D' : X.IdealSheafData) : Prop where
  preimage_eq_top : (β ≫ g) ⁻¹ᵁ U = ⊤
  isSemistablePair : IsSemistablePair (β ≫ g) D'
  genericMarks : GenericMarksCondition g D β D'
  isNumericallyStable : IsNumericallyStable β g D'
  isRelativelyProjective : IsRelativelyProjective ((g ⁻¹ᵁ U).ι ≫ g ≫ pT) (β ∣_ (g ⁻¹ᵁ U))
  isoLocus : ∃ U₀ : T.Opens, U₀ ≤ U ∧ (U₀ : Set T).Nonempty ∧ QuasiCompact U₀.ι ∧
    IsIso (β ∣_ (g ⁻¹ᵁ U₀))

variable [IsIntegral T] {pT : T ⟶ Spec (.of k)} {g : P ⟶ T} {D : P.IdealSheafData}
  {U : T.Opens} {β : X ⟶ P} {D' : X.IdealSheafData}

/-- The morphism of a stable model over an open is separated. -/
theorem IsStableModelOn.isSeparated (h : IsStableModelOn pT g D U β D') : IsSeparated β := by
  have := h.isRelativelyProjective.isProper
  have hβ : (β ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ≫ β = (β ∣_ (g ⁻¹ᵁ U)) ≫ (g ⁻¹ᵁ U).ι :=
    (morphismRestrict_ι _ _).symm
  have htop : β ⁻¹ᵁ (g ⁻¹ᵁ U) = ⊤ := by rw [← Scheme.Hom.comp_preimage, h.preimage_eq_top]
  have : IsIso (β ⁻¹ᵁ (g ⁻¹ᵁ U)).ι := by
    rw [htop]
    exact inferInstanceAs (IsIso X.topIso.hom)
  have : IsSeparated ((β ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ≫ β) := by
    rw [hβ]
    infer_instance
  have e : β = inv (β ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ≫ (β ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ≫ β := by
    rw [IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- **Rigidity for stable models over opens**: morphisms from an open of `X_i` to `X_j` over the
inclusion into `X_i` are unique. -/
theorem IsStableModelOn.rigid {ι : Type*} {U : ι → T.Opens} {X : ι → Scheme.{u}}
    {β : ∀ i, X i ⟶ P} {D' : ∀ i, (X i).IdealSheafData}
    (hX : ∀ i, IsStableModelOn pT g D (U i) (β i) (D' i)) (i j : ι) (W : Scheme.{u})
    (e : W ⟶ X i) [IsOpenImmersion e] (a b : W ⟶ X j) (ha : a ≫ β j = e ≫ β i)
    (hb : b ≫ β j = e ≫ β i) : a = b := by
  obtain ⟨U₀, -, hU₀, -, hiso⟩ := (hX j).isoLocus
  have := (hX j).isSeparated
  have := (hX i).isSemistablePair.nodal
  have : Flat ((e ≫ β i) ≫ g) := by
    rw [Category.assoc]
    infer_instance
  exact eq_of_comp_eq_of_isIso_morphismRestrict g (e ≫ β i) (β j) U₀ hU₀ ha hb

omit [IsIntegral T] in
/-- An open immersion `j : X' ⟶ X` whose image contains the geometric fibre of `X` over `a`
identifies the geometric fibres; numerical stability transfers. -/
theorem NumericallyStableFibre.of_isOpenImmersion {X' X : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (β : X ⟶ P) (D₀ : X.IdealSheafData) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ T)
    (hj : ∀ y : (pullback (C := Scheme.{u}) (β ≫ g) a : Scheme.{u}),
      pullback.fst (β ≫ g) a y ∈ Set.range j)
    (h : NumericallyStableFibre (j ≫ β) g (D₀.comap j) a) : NumericallyStableFibre β g D₀ a := by
  let c : pullback ((j ≫ β) ≫ g) a ≅ pullback (j ≫ β ≫ g) a :=
    pullback.congrHom (Category.assoc _ _ _) rfl
  let ψ := pullbackCompMap j (β ≫ g) a
  have hψ : IsIso ψ := by
    rw [isIso_iff_isOpenImmersion_and_epi_base]
    refine ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr fun y ↦ ?_⟩
    have : y ∈ Set.range ψ := by
      rw [Curves.range_pullbackCompMap]
      exact hj y
    exact this
  let φ : pullback ((j ≫ β) ≫ g) a ≅ pullback (β ≫ g) a := c ≪≫ asIso ψ
  have hφfst : φ.hom ≫ pullback.fst (β ≫ g) a = pullback.fst ((j ≫ β) ≫ g) a ≫ j := by
    simp only [φ, c, ψ, Iso.trans_hom, asIso_hom, Category.assoc, Curves.pullbackCompMap_fst,
      pullback.congrHom_hom, pullback.lift_fst_assoc, Category.comp_id]
  have hsnd : φ.hom ≫ pullback.snd (β ≫ g) a = pullback.snd ((j ≫ β) ≫ g) a := by
    simp only [φ, c, ψ, Iso.trans_hom, asIso_hom, Category.assoc, Curves.pullbackCompMap_snd,
      pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  have hmap : φ.hom ≫ pullbackCompMap β g a = pullbackCompMap (j ≫ β) g a := by
    apply pullback.hom_ext
    · rw [Category.assoc φ.hom, Curves.pullbackCompMap_fst, ← Category.assoc φ.hom, hφfst,
        Curves.pullbackCompMap_fst]
      exact Category.assoc _ _ _
    · rw [Category.assoc φ.hom, Curves.pullbackCompMap_snd, Curves.pullbackCompMap_snd, hsnd]
  refine NumericallyStableFibre.of_iso φ.symm (𝟙 _) ?_ ?_ ?_ h
  · rw [Iso.symm_hom, Iso.inv_comp_eq, hsnd]
  · rw [Iso.symm_hom, Iso.inv_comp_eq, Category.comp_id, hmap]
  · intro y
    have hy : φ.hom (φ.inv y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    have := congrArg (fun m ↦ m (φ.inv y)) hφfst
    simp only [Scheme.Hom.comp_apply, hy] at this
    rw [Iso.symm_hom, Scheme.IdealSheafData.support_comap]
    change j (pullback.fst ((j ≫ β) ≫ g) a (φ.inv y)) ∈ (D₀.support : Set X) ↔ _
    rw [← this]

end Model

section Etale

/-- **Étaleness of a closed subscheme over a base is local on an open cover of the ambient
scheme.** -/
theorem etale_subschemeι_of_cover {X Y : Scheme.{u}} {ι : Type u} (Z : ι → Scheme.{u})
    (j : ∀ i, Z i ⟶ X) [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i z, j i z = x)
    (q : X ⟶ Y) (D₀ : X.IdealSheafData)
    (h : ∀ i, Etale ((D₀.comap (j i)).subschemeι ≫ j i ≫ q)) : Etale (D₀.subschemeι ≫ q) := by
  let e : ∀ i, (D₀.comap (j i)).subscheme ⟶ D₀.subscheme := fun i ↦
    (D₀.comapIso (j i)).hom ≫ pullback.snd (j i) D₀.subschemeι
  have he : ∀ i, e i ≫ D₀.subschemeι = (D₀.comap (j i)).subschemeι ≫ j i := fun i ↦ by
    simp only [e, Category.assoc, ← pullback.condition,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  have : ∀ i, IsOpenImmersion (e i) := fun i ↦ by
    simp only [e]
    infer_instance
  let 𝒟 : D₀.subscheme.OpenCover.{u} :=
    Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι _ e (fun d ↦ by
      obtain ⟨i, z, hz⟩ := hcov (D₀.subschemeι d)
      obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback z d hz
      refine ⟨i, (D₀.comapIso (j i)).inv w, ?_⟩
      change ((D₀.comapIso (j i)).inv ≫ (D₀.comapIso (j i)).hom ≫
        pullback.snd (j i) D₀.subschemeι) w = d
      rw [Iso.inv_hom_id_assoc, hw₂])
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
  have key : ∀ i : ι, Etale (e i ≫ D₀.subschemeι ≫ q) := fun i ↦ by
    rw [← Category.assoc, he, Category.assoc]
    exact h i
  exact IsZariskiLocalAtSource.of_openCover (P := @Etale) 𝒟 key

end Etale


section Glued

variable {k : Type u} [CommRing k] {T P : Scheme.{u}} [IsIntegral T] {pT : T ⟶ Spec (.of k)}
  {g : P ⟶ T} {D : P.IdealSheafData} {ι : Type u} {U : ι → T.Opens} {X : ι → Scheme.{u}}
  {β : ∀ i, X i ⟶ P} {D' : ∀ i, (X i).IdealSheafData}

/-- The transition morphisms `X_i|_{U_j} ⟶ X_j` over `P`, glued from local ones by rigidity. -/
theorem exists_transition (hX : ∀ i, IsStableModelOn pT g D (U i) (β i) (D' i))
    (hloc : ∀ i j (x : X i), (β i ≫ g) x ∈ U j → ∃ (V : (X i).Opens), x ∈ V ∧
      V ≤ (β i ≫ g) ⁻¹ᵁ U j ∧ ∃ m : V.toScheme ⟶ X j, m ≫ β j = V.ι ≫ β i) (i j : ι) :
    ∃ φ : ((β i ≫ g) ⁻¹ᵁ U j).toScheme ⟶ X j, φ ≫ β j = ((β i ≫ g) ⁻¹ᵁ U j).ι ≫ β i := by
  set A := (β i ≫ g) ⁻¹ᵁ U j
  choose V hxV hVA m hm using fun a : A.toScheme ↦ hloc i j (A.ι a) (by
    have : A.ι a ∈ A := opens_ι_mem a
    exact this)
  have e : ∀ a, (X i).homOfLE (hVA a) ≫ A.ι = (V a).ι := fun a ↦ Scheme.homOfLE_ι _ _
  obtain ⟨φ, hφ, -⟩ := exists_glueHom' (A.ι ≫ β i) (β j) (fun a ↦ (V a).toScheme)
    (fun a ↦ (X i).homOfLE (hVA a)) (fun a ↦ by
      obtain ⟨z, hz⟩ : A.ι a ∈ Set.range (V a).ι := by
        rw [Scheme.Opens.range_ι]
        exact hxV a
      refine ⟨a, z, A.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, e, hz]) m (fun a ↦ by rw [hm, ← e, Category.assoc])
    (fun W e' _ a b ha hb ↦ by
      have := IsStableModelOn.rigid hX i j W (e' ≫ A.ι) a b (by rw [ha, Category.assoc])
        (by rw [hb, Category.assoc])
      exact this)
  exact ⟨φ, hφ⟩

/-- The transition morphisms are open immersions onto `X_j|_{U_i}` (their inverses are the
transitions in the other direction, by rigidity). -/
theorem exists_transition_isOpenImmersion (hX : ∀ i, IsStableModelOn pT g D (U i) (β i) (D' i))
    (hloc : ∀ i j (x : X i), (β i ≫ g) x ∈ U j → ∃ (V : (X i).Opens), x ∈ V ∧
      V ≤ (β i ≫ g) ⁻¹ᵁ U j ∧ ∃ m : V.toScheme ⟶ X j, m ≫ β j = V.ι ≫ β i) (i j : ι) :
    ∃ φ : ((β i ≫ g) ⁻¹ᵁ U j).toScheme ⟶ X j, φ ≫ β j = ((β i ≫ g) ⁻¹ᵁ U j).ι ≫ β i ∧
      IsOpenImmersion φ ∧ Set.range φ = ((β j ≫ g) ⁻¹ᵁ U i : Set (X j)) := by
  obtain ⟨φ₁, hφ₁⟩ := exists_transition hX hloc i j
  obtain ⟨φ₂, hφ₂⟩ := exists_transition hX hloc j i
  have hover : ∀ l (x : X l), (β l ≫ g) x ∈ U l := fun l x ↦ by
    have : x ∈ (β l ≫ g) ⁻¹ᵁ U l := by rw [(hX l).preimage_eq_top]; trivial
    exact this
  have hr₁ : Set.range φ₁ ⊆ Set.range ((β j ≫ g) ⁻¹ᵁ U i).ι := by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (β j ≫ g) (φ₁ a) ∈ U i
    rw [← Scheme.Hom.comp_apply, reassoc_of% hφ₁, Scheme.Hom.comp_apply]
    exact hover i _
  have hr₂ : Set.range φ₂ ⊆ Set.range ((β i ≫ g) ⁻¹ᵁ U j).ι := by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (β i ≫ g) (φ₂ a) ∈ U j
    rw [← Scheme.Hom.comp_apply, reassoc_of% hφ₂, Scheme.Hom.comp_apply]
    exact hover j _
  let φ₁' := IsOpenImmersion.lift ((β j ≫ g) ⁻¹ᵁ U i).ι φ₁ hr₁
  let φ₂' := IsOpenImmersion.lift ((β i ≫ g) ⁻¹ᵁ U j).ι φ₂ hr₂
  have h₁ : φ₁' ≫ ((β j ≫ g) ⁻¹ᵁ U i).ι = φ₁ := IsOpenImmersion.lift_fac _ _ _
  have h₂ : φ₂' ≫ ((β i ≫ g) ⁻¹ᵁ U j).ι = φ₂ := IsOpenImmersion.lift_fac _ _ _
  have e₁ : φ₁' ≫ φ₂' = 𝟙 _ := by
    rw [← cancel_mono ((β i ≫ g) ⁻¹ᵁ U j).ι, Category.assoc, h₂, Category.id_comp]
    refine IsStableModelOn.rigid hX i i _ ((β i ≫ g) ⁻¹ᵁ U j).ι _ _ ?_ rfl
    rw [Category.assoc, hφ₂, ← Category.assoc, h₁, hφ₁]
  have e₂ : φ₂' ≫ φ₁' = 𝟙 _ := by
    rw [← cancel_mono ((β j ≫ g) ⁻¹ᵁ U i).ι, Category.assoc, h₁, Category.id_comp]
    refine IsStableModelOn.rigid hX j j _ ((β j ≫ g) ⁻¹ᵁ U i).ι _ _ ?_ rfl
    rw [Category.assoc, hφ₁, ← Category.assoc, h₂, hφ₂]
  have : IsIso φ₁' := ⟨⟨φ₂', e₁, e₂⟩⟩
  refine ⟨φ₁, hφ₁, ?_, ?_⟩
  · rw [← h₁]
    infer_instance
  · rw [← h₁, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Opens.opensRange_ι]

omit [IsIntegral T] in
/-- Points of the glued scheme lie over the members of the cover. -/
theorem exists_mem_of_iSup_eq_top (hU : ⨆ i, U i = ⊤) (t : T) : ∃ i, t ∈ U i := by
  have ht : t ∈ ⨆ i, U i := by rw [hU]; trivial
  exact Opens.mem_iSup.mp ht

/-- **Gluing stable models over an open cover of the base** (node G7; Temkin T:3394–3397). Stable
models `β i : X i ⟶ P` over the members `U i` of an open cover of the integral base `T`, with
morphisms over `P` near every point of the overlaps, glue to `β : X ⟶ P`, proper, with marks
`D_X` such that `(X, D_X)` is a semi-stable pair over `T` satisfying the generic marks condition,
numerically stable, projective over each `g⁻¹(U i)` (relative to `Spec k`), and an isomorphism
over a nonempty open of `T` with quasi-compact inclusion. -/
theorem exists_glue_isStableModelOn (hU : ⨆ i, U i = ⊤)
    (hX : ∀ i, IsStableModelOn pT g D (U i) (β i) (D' i))
    (hloc : ∀ i j (x : X i), (β i ≫ g) x ∈ U j → ∃ (V : (X i).Opens), x ∈ V ∧
      V ≤ (β i ≫ g) ⁻¹ᵁ U j ∧ ∃ m : V.toScheme ⟶ X j, m ≫ β j = V.ι ≫ β i) :
    ∃ (Xg : Scheme.{u}) (βg : Xg ⟶ P) (Dg : Xg.IdealSheafData),
      IsProper βg ∧ IsSemistablePair (βg ≫ g) Dg ∧ GenericMarksCondition g D βg Dg ∧
      IsNumericallyStable βg g Dg ∧
      (∀ i, IsRelativelyProjective ((g ⁻¹ᵁ U i).ι ≫ g ≫ pT) (βg ∣_ (g ⁻¹ᵁ U i))) ∧
      ∃ U₀ : T.Opens, (U₀ : Set T).Nonempty ∧ QuasiCompact U₀.ι ∧ IsIso (βg ∣_ (g ⁻¹ᵁ U₀)) := by
  choose φ hφ hφo hφr using exists_transition_isOpenImmersion hX hloc
  have hrigid : ∀ i j (O : (X i).Opens) (a b : O.toScheme ⟶ X j), a ≫ β j = O.ι ≫ β i →
      b ≫ β j = O.ι ≫ β i → a = b := fun i j O a b ha hb ↦
    IsStableModelOn.rigid hX i j O.toScheme O.ι a b ha hb
  have : ∀ i j, IsOpenImmersion (φ i j) := hφo
  obtain ⟨Xg, βg, j, hjo, hjβ, hjr⟩ := exists_glue g φ hφ hrigid hU hφr
    (fun i ↦ (hX i).preimage_eq_top)
  have hover : ∀ l (x : X l), (β l ≫ g) x ∈ U l := fun l x ↦ by
    have : x ∈ (β l ≫ g) ⁻¹ᵁ U l := by rw [(hX l).preimage_eq_top]; trivial
    exact this
  have hcov : ∀ x : Xg, ∃ i z, j i z = x := fun x ↦ by
    obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top hU ((βg ≫ g) x)
    have : x ∈ Set.range (j i) := by rw [hjr i]; exact hi
    obtain ⟨z, hz⟩ := this
    exact ⟨i, z, hz⟩
  -- the glued marks
  let 𝒳 : Xg.OpenCover.{u} :=
    { I₀ := ι
      X := X
      f := j
      mem₀ := (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι X j hcov).mem₀ }
  have hjj : ∀ i₁ i₂, pullback.fst (j i₁) (j i₂) ≫ β i₁ = pullback.snd (j i₁) (j i₂) ≫ β i₂ :=
    fun i₁ i₂ ↦ by rw [← hjβ, ← hjβ, pullback.condition_assoc]
  have hcompat : Algebra.NodeFittingIdealSheaf.GlueCompat 𝒳 D' := by
    intro i₁ i₂
    change (D' i₁).comap (pullback.fst (j i₁) (j i₂)) = (D' i₂).comap (pullback.snd (j i₁) (j i₂))
    have e₁ := Curves.IsSemistablePair.etale_comp (hX i₁).isSemistablePair
      (pullback.fst (j i₁) (j i₂))
    have e₂ := Curves.IsSemistablePair.etale_comp (hX i₂).isSemistablePair
      (pullback.snd (j i₁) (j i₂))
    have := e₁.etale
    have := e₂.etale
    have hf₁ : Flat (((D' i₁).comap (pullback.fst (j i₁) (j i₂))).subschemeι ≫
        (pullback.fst (j i₁) (j i₂) ≫ β i₁) ≫ g) := by
      rw [Category.assoc]
      infer_instance
    have hf₂ : Flat (((D' i₂).comap (pullback.snd (j i₁) (j i₂))).subschemeι ≫
        (pullback.fst (j i₁) (j i₂) ≫ β i₁) ≫ g) := by
      rw [hjj, Category.assoc]
      infer_instance
    have g₁ := ((hX i₁).genericMarks.comp (pullback.fst (j i₁) (j i₂))).eq_genericMarksClosure
    have g₂ := ((hX i₂).genericMarks.comp (pullback.snd (j i₁) (j i₂)))
    rw [← hjj] at g₂
    rw [g₁, g₂.eq_genericMarksClosure]
  obtain ⟨Dg, hDg⟩ : ∃ Dg : Xg.IdealSheafData, ∀ i, Dg.comap (j i) = D' i :=
    ⟨@Algebra.NodeFittingIdealSheaf.glue _ 𝒳 D' hcompat,
      @Algebra.NodeFittingIdealSheaf.glue_comap _ 𝒳 D' hcompat⟩
  obtain ⟨i₀, hi₀⟩ := exists_mem_of_iSup_eq_top hU (genericPoint T)
  -- projectivity over the members and properness
  have hproj : ∀ i, IsRelativelyProjective ((g ⁻¹ᵁ U i).ι ≫ g ≫ pT) (βg ∣_ (g ⁻¹ᵁ U i)) := by
    intro i
    refine isRelativelyProjective_morphismRestrict_of_comp (j i) βg (g ⁻¹ᵁ U i) _ ?_ ?_
    · rw [hjr i]
      intro x hx
      exact hx
    · rw [hjβ]
      exact (hX i).isRelativelyProjective
  have hsup : ⨆ i, g ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  have hproper : IsProper βg :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (fun i ↦ g ⁻¹ᵁ U i) hsup
      fun i ↦ (hproj i).isProper
  refine ⟨Xg, βg, Dg, hproper, ?_, ?_, ?_, hproj, ?_⟩
  · -- semi-stable pair
    have hnod : DeJong.IsNodalCurve (βg ≫ g) := by
      refine Curves.IsNodalCurve.of_openCover _ fun x ↦ ?_
      obtain ⟨i, z, rfl⟩ := hcov x
      refine ⟨(j i).opensRange, ⟨z, rfl⟩, ?_⟩
      have := (hX i).isSemistablePair.nodal
      have h := Curves.IsNodalCurve.etale_comp (j i).isoOpensRange.inv (β i ≫ g)
      rwa [← hjβ, ← Category.assoc, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp,
        Category.assoc] at h
    refine ⟨hnod, ?_, ?_⟩
    · refine etale_subschemeι_of_cover X j hcov (βg ≫ g) Dg fun i ↦ ?_
      rw [hDg, ← Category.assoc (j i) βg g, hjβ]
      exact (hX i).isSemistablePair.etale
    · intro x hx
      obtain ⟨i, z, rfl⟩ := hcov x
      have hz : z ∈ ((D' i).support : Set (X i)) := by
        rw [← hDg, Scheme.IdealSheafData.support_comap]
        exact hx
      have h := (hX i).isSemistablePair.smoothAlong z hz
      rw [← hjβ, Category.assoc] at h
      exact Curves.isSmoothAt_of_isOpenImmersion_comp (j i) h
  · -- generic marks
    intro Y m n hmn
    have hr : Set.range m ⊆ Set.range (j i₀) := by
      rintro _ ⟨y, rfl⟩
      rw [hjr i₀]
      change (βg ≫ g) (m y) ∈ U i₀
      rw [← Scheme.Hom.comp_apply, hmn, Scheme.Hom.comp_apply,
        Scheme.fromSpecResidueField_apply]
      exact hi₀
    have hm := IsOpenImmersion.lift_fac (j i₀) m hr
    rw [← hm, Scheme.IdealSheafData.comap_comp, hDg, (hX i₀).genericMarks Y _ n (by
      rw [← hjβ, Category.assoc, reassoc_of% hm, hmn]), ← Scheme.IdealSheafData.comap_comp, ← hjβ,
      Scheme.IdealSheafData.comap_comp D, Scheme.IdealSheafData.comap_comp]
    rw [← Scheme.IdealSheafData.comap_comp]
  · -- numerical stability
    intro K _ _ a
    obtain ⟨z⟩ : Nonempty (Spec (.of K)) := inferInstance
    obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top hU (a z)
    have h := (hX i).isNumericallyStable K a
    rw [← hjβ, ← hDg] at h
    refine NumericallyStableFibre.of_isOpenImmersion (j i) βg Dg a (fun y ↦ ?_) h
    rw [hjr i]
    change (βg ≫ g) (pullback.fst (βg ≫ g) a y) ∈ U i
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      Subsingleton.elim (pullback.snd (βg ≫ g) a y) z]
    exact hi
  · -- isomorphism locus
    obtain ⟨U₀, hU₀i, hU₀, hqc, hiso⟩ := (hX i₀).isoLocus
    refine ⟨U₀, hU₀, hqc, ?_⟩
    have : IsIso ((j i₀ ≫ βg) ∣_ (g ⁻¹ᵁ U₀)) := by rw [hjβ]; exact hiso
    refine isIso_morphismRestrict_of_comp (j i₀) βg (g ⁻¹ᵁ U₀) ?_
    rw [hjr i₀]
    intro x hx
    exact hU₀i hx

end Glued

end DeJongAlterations.StableModification.Global
