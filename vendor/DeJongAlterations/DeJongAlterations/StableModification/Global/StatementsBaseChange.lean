import DeJongAlterations.StableModification.Global.Statements

/-!
# Numerical stability is fibrewise: transport and base change

Numerical stability (`Global.NumericallyStableFibre`, `PLAN-T5.md` §1.3) is a condition on each
geometric fibre separately (Temkin, T:1686–1690: stability is a condition on geometric fibres),
so it transports along isomorphisms of geometric fibres compatible with the structure maps, the
fibre maps and the marks (`NumericallyStableFibre.of_iso`, the analogue of
`Curves.IsExceptionalComponent.of_iso`), is stable under base change
(`IsNumericallyStable.pullback`, `IsNumericallyStableAt.pullback`, analogues of
`Curves.not_isExceptionalComponent_pullback`) and descends along open immersions of the base
(`isNumericallyStableAt_of_pullback_isOpenImmersion`), hence is local on the base.

Blueprint: `sm-global.tex`, `lem:sm-global-numerically-stable-base-change`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSmoothAt)
open Curves (pullbackCompMap)
open Cohomology (structureCoeff)
open CurvesField.Genus (arithmeticGenus eulerChar)

/-- **Numerical stability transports along isomorphisms of geometric fibres** compatible with
the structure maps to `Spec K`, the maps of geometric fibres and the marks. -/
theorem NumericallyStableFibre.of_iso {C₁ C₁' S₁ C₂ C₂' S₂ : Scheme.{u}} {β₁ : C₁' ⟶ C₁}
    {g₁ : C₁ ⟶ S₁} {D₁ : C₁'.IdealSheafData} {β₂ : C₂' ⟶ C₂} {g₂ : C₂ ⟶ S₂}
    {D₂ : C₂'.IdealSheafData} {K : Type u} [Field K] {a₁ : Spec (.of K) ⟶ S₁}
    {a₂ : Spec (.of K) ⟶ S₂}
    (φ : pullback (β₁ ≫ g₁) a₁ ≅ pullback (β₂ ≫ g₂) a₂) (χ : pullback g₁ a₁ ⟶ pullback g₂ a₂)
    (hsnd : φ.hom ≫ pullback.snd (β₂ ≫ g₂) a₂ = pullback.snd (β₁ ≫ g₁) a₁)
    (hmap : φ.hom ≫ pullbackCompMap β₂ g₂ a₂ = pullbackCompMap β₁ g₁ a₁ ≫ χ)
    (hmarks : ∀ y, pullback.fst (β₂ ≫ g₂) a₂ (φ.hom y) ∈ (D₂.support : Set C₂') ↔
      pullback.fst (β₁ ≫ g₁) a₁ y ∈ (D₁.support : Set C₁'))
    (h : NumericallyStableFibre β₂ g₂ D₂ a₂) : NumericallyStableFibre β₁ g₁ D₁ a₁ := by
  intro Z hZ hcon _ _ hpa
  have hZc := isClosed_of_mem_irreducibleComponents Z hZ
  have hZ₂ : φ.hom '' Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β₂ ≫ g₂) a₂) := by
    refine image_mem_irreducibleComponents_of_isPreirreducible_fiber φ.hom φ.hom.continuous
      φ.hom.homeomorph.isOpenMap (fun x ↦ ?_) φ.hom.homeomorph.surjective hZ
    exact (Set.subsingleton_singleton.preimage φ.hom.homeomorph.injective).isPreirreducible
  have hZ₂c := isClosed_of_mem_irreducibleComponents _ hZ₂
  have hcon₂ : (pullbackCompMap β₂ g₂ a₂ '' (φ.hom '' Z)).Subsingleton := by
    rw [Set.image_image]
    have : (fun y ↦ pullbackCompMap β₂ g₂ a₂ (φ.hom y)) =
        fun y ↦ χ (pullbackCompMap β₁ g₁ a₁ y) :=
      funext fun y ↦ by
        rw [← Scheme.Hom.comp_apply, hmap, Scheme.Hom.comp_apply]
    rw [this, ← Set.image_image]
    exact hcon.image _
  let e := isoReducedSubschemeOfIso φ Z hZc (φ.hom '' Z) hZ₂c rfl
  have : CompactSpace (reducedSubscheme (φ.hom '' Z) hZ₂c) := e.hom.homeomorph.compactSpace
  have : IsSeparated (terminal.from (reducedSubscheme (φ.hom '' Z) hZ₂c)) := by
    rw [← terminal.comp_from e.inv]
    infer_instance
  have hpa₂ : arithmeticGenus (reducedSubscheme (φ.hom '' Z) hZ₂c)
      (structureCoeff (reducedSubschemeι (φ.hom '' Z) hZ₂c ≫ pullback.snd (β₂ ≫ g₂) a₂)) = 0 := by
    have hχ := BlowDown.eulerChar_eq_of_iso
      (reducedSubschemeι Z hZc ≫ pullback.snd (β₁ ≫ g₁) a₁)
      (reducedSubschemeι (φ.hom '' Z) hZ₂c ≫ pullback.snd (β₂ ≫ g₂) a₂) e (by
        rw [isoReducedSubschemeOfIso_hom_ι_assoc, hsnd])
    rw [arithmeticGenus] at hpa ⊢
    rw [← hχ]
    exact hpa
  have h3 := h (φ.hom '' Z) hZ₂ hcon₂ hpa₂
  have hsm : ∀ y, IsSmoothAt (pullback.snd (β₂ ≫ g₂) a₂) (φ.hom y) ↔
      IsSmoothAt (pullback.snd (β₁ ≫ g₁) a₁) y := by
    intro y
    rw [← hsnd]
    exact ⟨fun h' ↦ Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth φ.hom y) h',
      fun h' ↦ Curves.isSmoothAt_of_isOpenImmersion_comp φ.hom h'⟩
  have hA : φ.hom '' Z ∩ specialPoints β₂ g₂ D₂ a₂ = φ.hom '' (Z ∩ specialPoints β₁ g₁ D₁ a₁) := by
    ext w
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hw⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      rcases hw with hw | hw
      · exact Or.inl ((hmarks y).mp hw)
      · exact Or.inr fun hs ↦ hw ((hsm y).mpr hs)
    · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      rcases hy' with hy' | hy'
      · exact Or.inl ((hmarks y).mpr hy')
      · exact Or.inr fun hs ↦ hy' ((hsm y).mp hs)
  have hinj : Function.Injective φ.hom := φ.hom.homeomorph.injective
  rw [hA, Set.InjOn.encard_image hinj.injOn] at h3
  exact h3

variable {C C' S S' : Scheme.{u}}

/-- The isomorphism of geometric fibres `(C' ×_S S')_a ≅ C'_{a ≫ ψ}` used for base change, with
its compatibilities. -/
theorem exists_iso_pullback_fibre (β : C' ⟶ C) (g : C ⟶ S) (ψ : S' ⟶ S) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ S') :
    ∃ (φ : pullback (pullbackCompMap β g ψ ≫ pullback.snd g ψ) a ≅ pullback (β ≫ g) (a ≫ ψ))
      (χ : pullback (pullback.snd g ψ) a ≅ pullback g (a ≫ ψ)),
      φ.hom ≫ pullback.snd (β ≫ g) (a ≫ ψ) =
        pullback.snd (pullbackCompMap β g ψ ≫ pullback.snd g ψ) a ∧
      φ.hom ≫ pullbackCompMap β g (a ≫ ψ) =
        pullbackCompMap (pullbackCompMap β g ψ) (pullback.snd g ψ) a ≫ χ.hom ∧
      φ.hom ≫ pullback.fst (β ≫ g) (a ≫ ψ) =
        pullback.fst _ a ≫ pullback.fst (β ≫ g) ψ := by
  let φ : pullback (pullbackCompMap β g ψ ≫ pullback.snd g ψ) a ≅ pullback (β ≫ g) (a ≫ ψ) :=
    pullback.congrHom (Curves.pullbackCompMap_snd β g ψ) rfl ≪≫
      pullbackLeftPullbackSndIso (β ≫ g) ψ a
  let χ : pullback (pullback.snd g ψ) a ≅ pullback g (a ≫ ψ) := pullbackLeftPullbackSndIso g ψ a
  have hfst : φ.hom ≫ pullback.fst (β ≫ g) (a ≫ ψ) =
      pullback.fst _ a ≫ pullback.fst (β ≫ g) ψ := by
    simp only [φ, Iso.trans_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullback.congrHom_hom]
    rw [pullback.lift_fst_assoc, Category.comp_id]
  have hsnd : φ.hom ≫ pullback.snd (β ≫ g) (a ≫ ψ) = pullback.snd _ a := by
    simp only [φ, Iso.trans_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      pullback.congrHom_hom]
    rw [pullback.lift_snd, Category.comp_id]
  refine ⟨φ, χ, hsnd, ?_, hfst⟩
  apply pullback.hom_ext
  · simp only [χ, Category.assoc, Curves.pullbackCompMap_fst, pullbackLeftPullbackSndIso_hom_fst,
      Curves.pullbackCompMap_fst_assoc]
    rw [← Category.assoc, hfst, Category.assoc]
  · simp only [χ, Category.assoc, Curves.pullbackCompMap_snd, pullbackLeftPullbackSndIso_hom_snd]
    exact hsnd

/-- **Base change of a numerically stable geometric fibre**: the fibre of the base change of
`(β, g, D')` along `ψ : S' ⟶ S` over `a` is the fibre of `(β, g, D')` over `a ≫ ψ`. -/
theorem numericallyStableFibre_pullback_iff (β : C' ⟶ C) (g : C ⟶ S) (D' : C'.IdealSheafData)
    (ψ : S' ⟶ S) {K : Type u} [Field K] (a : Spec (.of K) ⟶ S') :
    NumericallyStableFibre (pullbackCompMap β g ψ) (pullback.snd g ψ)
        (D'.comap (pullback.fst (β ≫ g) ψ)) a ↔
      NumericallyStableFibre β g D' (a ≫ ψ) := by
  obtain ⟨φ, χ, hsnd, hmap, hfst⟩ := exists_iso_pullback_fibre β g ψ a
  have hmarks : ∀ y, pullback.fst (β ≫ g) (a ≫ ψ) (φ.hom y) ∈ (D'.support : Set C') ↔
      pullback.fst (pullbackCompMap β g ψ ≫ pullback.snd g ψ) a y ∈
        ((D'.comap (pullback.fst (β ≫ g) ψ)).support : Set _) := by
    intro y
    have := congrArg (fun m ↦ m y) hfst
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, Scheme.IdealSheafData.support_comap]
    rfl
  constructor
  · intro h
    refine NumericallyStableFibre.of_iso φ.symm χ.inv ?_ ?_ ?_ h
    · rw [Iso.symm_hom, Iso.inv_comp_eq, hsnd]
    · rw [Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hmap, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · intro y
      have hy : φ.hom (φ.inv y) = y := by
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
      rw [Iso.symm_hom, ← hmarks (φ.inv y), hy]
  · exact NumericallyStableFibre.of_iso φ χ.hom hsnd hmap hmarks

/-- **Numerical stability is stable under base change** (Temkin T:1686–1690; analogue of
`Curves.not_isExceptionalComponent_pullback`). -/
theorem IsNumericallyStable.pullback {β : C' ⟶ C} {g : C ⟶ S} {D' : C'.IdealSheafData}
    (h : IsNumericallyStable β g D') (ψ : S' ⟶ S) :
    IsNumericallyStable (pullbackCompMap β g ψ) (pullback.snd g ψ)
      (D'.comap (pullback.fst (β ≫ g) ψ)) :=
  fun K _ _ a ↦ (numericallyStableFibre_pullback_iff β g D' ψ a).mpr (h K (a ≫ ψ))

/-- **Numerical stability over a point is stable under base change**: if the geometric fibres
over `ψ(s')` are numerically stable, so are those of the base change over `s'`. -/
theorem IsNumericallyStableAt.pullback {β : C' ⟶ C} {g : C ⟶ S} {D' : C'.IdealSheafData}
    (ψ : S' ⟶ S) {s' : S'} (h : IsNumericallyStableAt β g D' (ψ s')) :
    IsNumericallyStableAt (pullbackCompMap β g ψ) (pullback.snd g ψ)
      (D'.comap (pullback.fst (β ≫ g) ψ)) s' :=
  fun K _ _ a ha ↦ (numericallyStableFibre_pullback_iff β g D' ψ a).mpr
    (h K (a ≫ ψ) fun z ↦ by rw [Scheme.Hom.comp_apply, ha])

/-- **Numerical stability descends along open immersions of the base**: if `ψ : S' ⟶ S` is an
open immersion and the geometric fibres of the base change over `s'` are numerically stable, so
are those of `(β, g, D')` over `ψ(s')` (every geometric point over `ψ(s')` factors through `ψ`). -/
theorem isNumericallyStableAt_of_pullback_isOpenImmersion {β : C' ⟶ C} {g : C ⟶ S}
    {D' : C'.IdealSheafData} (ψ : S' ⟶ S) [IsOpenImmersion ψ] {s' : S'}
    (h : IsNumericallyStableAt (pullbackCompMap β g ψ) (pullback.snd g ψ)
      (D'.comap (pullback.fst (β ≫ g) ψ)) s') :
    IsNumericallyStableAt β g D' (ψ s') := by
  intro K _ _ a ha
  have hr : Set.range a ⊆ Set.range ψ := by
    rintro _ ⟨z, rfl⟩
    exact ⟨s', (ha z).symm⟩
  let a' := IsOpenImmersion.lift ψ a hr
  have ha' : a' ≫ ψ = a := IsOpenImmersion.lift_fac ψ a hr
  rw [← ha']
  refine (numericallyStableFibre_pullback_iff β g D' ψ a').mp (h K a' fun z ↦ ?_)
  apply ψ.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ha', ha]

/-- **Numerical stability is local on the base**: if the base changes along the members of an
open cover are numerically stable, so is `(β, g, D')`. -/
theorem isNumericallyStable_of_openCover {β : C' ⟶ C} {g : C ⟶ S} {D' : C'.IdealSheafData}
    (𝒰 : S.OpenCover)
    (h : ∀ i, IsNumericallyStable (pullbackCompMap β g (𝒰.f i)) (pullback.snd g (𝒰.f i))
      (D'.comap (pullback.fst (β ≫ g) (𝒰.f i)))) :
    IsNumericallyStable β g D' := by
  rw [isNumericallyStable_iff]
  intro s
  obtain ⟨i, s', rfl⟩ := 𝒰.exists_eq s
  exact isNumericallyStableAt_of_pullback_isOpenImmersion (𝒰.f i)
    ((isNumericallyStable_iff _ _ _).mp (h i) s')

end DeJongAlterations.StableModification.Global
