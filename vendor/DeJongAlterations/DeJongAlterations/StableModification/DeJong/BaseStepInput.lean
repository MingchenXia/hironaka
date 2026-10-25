import DeJongAlterations.StableModification.DeJong.BaseStepOutput
import DeJongAlterations.StableModification.DeJong.StrictTransform
import DeJongAlterations.Geometry.CurveFibrationBaseChangeSmooth
import DeJongAlterations.Geometry.FiberDimension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Preparing the input of Temkin's theorem

Steps S1–S2 of PLAN-DJ-MAIN §3.4. Let `f : X' → Y` be a Temkin-ready fibration
(`TemkinReadyFibration k`, the generic part of de Jong 4.11–4.12,
`dejong96-alterations:page-0018`–`page-0020`) with horizontal boundary `Dᴴ ⊆ X'`, and let
`ψ₁ : S₁ → Y` be the generically étale alteration of `FlatteningAfterGEAlteration k` making the
strict transforms `C` of `X'` and `M` of `Dᴴ` flat over `S₁` (a weak form of de Jong 2.19 and
of 4.18 h), `page-0011`, `page-0023`). Then `(C, D_C)`, with `D_C ⊆ C` the image of `M`,
satisfies the hypotheses of Temkin's stable modification theorem (Temkin Thm 1.5,
`semi-stable.tex` l.1771–1775):

* the generic fibres of `C` and `M` are the base changes of the generic fibres of `X'` and
  `Dᴴ` along `κ(Y) → κ(S₁)` (`strictTransformFiberIso`), so `C_η` is smooth, geometrically
  integral and nodal, and `(D_C)_η` is étale;
* `C` and `D_C` are flat over `S₁` (`FlatteningAfterGEAlteration k`); their generic fibres have
  pure dimension one (`C_η` is integral and `dim C = dim S₁ + 1`, by transcendence degrees)
  and zero (`(D_C)_η` is étale). That they have pure relative dimension one and zero is the
  dimension theory of flat families, `FlatFamilyPureFiberDimension` (EGA IV 6.1.2: for a flat
  morphism of finite type over a variety, every irreducible component of every fibre has the
  dimension of the generic fibre). In this file it is a named proposition taken as a
  hypothesis; it is proved in `BaseStepFlatDimension`.

Moreover `C → X' → X` is an alteration (`C` is flat over `S₁` with integral generic fibre,
`lem:sm-dj-strict-transform-integral`) and, outside a proper closed subset of `S₁`, the
preimage of the boundary lies in `D_C` (`exists_closed_forall_mem_strictTransform_support`,
`lem:sm-dj-boundary-bookkeeping`). The result is `temkinInput_of_fibration`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- **Pure fibre dimension of flat families** (EGA IV 6.1.2 with the dimension formula for
varieties). Let `S` be a variety over a field with generic point `η` and `g : C → S` flat and
of finite type. If every irreducible component of the generic fibre `C_η` has dimension `n`,
then every irreducible component of every fibre of `g` has dimension `n`.

The statement is proved in `BaseStepFlatDimension` (`FlatDimension.flatFamilyPureFiberDimension`):
for `z` the generic point of a component of `C_s`, going down gives
`dim 𝒪_{C,z} = dim 𝒪_{S,s}` (Mathlib `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`),
and the dimension formula for finite type domains over a field (Codex
`Algebra.AffinePrimeDimension.height_add_quotient_dimension`) applied to a component of `C`
through `z` (which dominates `S` by flatness) gives `trdeg κ(z)/κ(s) = n`. -/
def FlatFamilyPureFiberDimension : Prop :=
  ∀ (k : Type u) [Field k] (S C : Scheme.{u}) (pS : S ⟶ Spec (.of k)) [IsVariety pS]
    (g : C ⟶ S) [Flat g] [LocallyOfFiniteType g] [QuasiCompact g] (n : ℕ),
    (∀ Z ∈ irreducibleComponents (g.fiber (genericPoint S)), topologicalKrullDim Z = n) →
    HasPureFiberDimension g n

section Helpers

/-- A formally unramified morphism locally of finite type is locally quasi-finite. -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff]
  intro U hU V hV e
  have h1 := HasRingHomProperty.appLE @FormallyUnramified f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e
  have h2 := HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e
  algebraize [(f.appLE U V e).hom]
  have : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) := h1
  have : Algebra.FiniteType Γ(Y, U) Γ(X, V) := h2
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

/-- The irreducible components of a scheme locally quasi-finite over a field are points. -/
theorem dim_irreducibleComponents_of_locallyQuasiFinite {K : Type u} [Field K] {T : Scheme.{u}}
    (q : T ⟶ Spec (.of K)) [LocallyQuasiFinite q] :
    ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = 0 := by
  intro Z hZ
  have hdisc : DiscreteTopology T := by
    obtain ⟨pt⟩ : Nonempty (Spec (.of K)) := inferInstance
    have h := q.isDiscrete_preimage_singleton pt
    have : q ⁻¹' {pt} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [this] at h
    exact isDiscrete_univ_iff.mp h
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le T Z).trans
      (topologicalKrullDim_zero_of_discreteTopology T)
  · have : Nonempty Z := hZ.1.1.to_subtype
    exact (Geometry.FiberDimension.topologicalKrullDim_nonneg_iff Z).mpr this

/-- The only irreducible component of an irreducible space is the whole space. -/
theorem topologicalKrullDim_eq_of_mem_irreducibleComponents {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {Z : Set T} (hZ : Z ∈ irreducibleComponents T) :
    topologicalKrullDim Z = topologicalKrullDim T := by
  have hZu : Z = Set.univ :=
    Set.eq_univ_of_univ_subset (hZ.2 ((irreducibleSpace_def T).mp inferInstance)
      (Set.subset_univ Z))
  subst hZu
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ T).isHomeomorph

end Helpers

variable {k : Type u} [Field k]

/-- **Steps S1–S2 of the base step.** A Temkin-ready fibration over `X`, flattened by
`FlatteningAfterGEAlteration k`, gives the input of Temkin's theorem. The pure relative
dimension of the flat strict transforms is the named hypothesis
`FlatFamilyPureFiberDimension`. -/
theorem temkinInput_of_fibration [IsAlgClosed k] (hFD : FlatFamilyPureFiberDimension.{u})
    (hFLAT : FlatteningAfterGEAlteration k) {X : Scheme.{u}} {p : X ⟶ Spec (.of k)}
    [IsVariety p] {d : ℕ} (hd : 2 ≤ d) (hXdim : topologicalKrullDim X = d) (D : X.IdealSheafData)
    {X' Y : Scheme.{u}} (φ : X' ⟶ X) (pY : Y ⟶ Spec (.of k)) [IsVariety pY] (f : X' ⟶ Y)
    (Dh : X'.IdealSheafData) (T : Closeds Y) (hφ : IsAlteration φ)
    (hX'proj : IsProjectiveOver (φ ≫ p)) (hYn : IsNormalScheme Y) (hYproj : IsProjectiveOver pY)
    (hYdim : topologicalKrullDim Y = ((d - 1 : ℕ) : WithBot ℕ∞)) (hfY : f ≫ pY = φ ≫ p)
    (hfdom : IsDominant f) (hsm : Smooth (f.fiberToSpecResidueField (genericPoint Y)))
    (hgi : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y)))
    (hss : IsSemistablePair (f.fiberToSpecResidueField (genericPoint Y))
      (fiberMarks f Dh (genericPoint Y)))
    (hT : T ≠ ⊤)
    (hcov : φ ⁻¹' (D.support : Set X) ⊆ (Dh.support : Set X') ∪ f ⁻¹' (T : Set Y)) :
    Nonempty (TemkinInput p (D.support : Set X) d) := by
  let := hφ
  have : IsIntegral X' := hφ.sourceIntegral
  have : IsProper (φ ≫ p) := hX'proj.isProper
  have : IsProper pY := hYproj.isProper
  have : IsProper f := by
    have : IsProper (f ≫ pY) := by rw [hfY]; infer_instance
    exact IsProper.of_comp f pY
  -- flattening `X'` and `Dᴴ`
  let W : Fin 2 → Scheme.{u} := Fin.cons X' (fun _ : Fin 1 ↦ Dh.subscheme)
  let w : (i : Fin 2) → W i ⟶ Y :=
    Fin.cases (motive := fun i ↦ W i ⟶ Y) f (fun _ ↦ Dh.subschemeι ≫ f)
  have hw0 : ∀ i, LocallyOfFiniteType (w i) := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change LocallyOfFiniteType f; infer_instance
    · change LocallyOfFiniteType (Dh.subschemeι ≫ f); infer_instance
  have hw1 : ∀ i, QuasiCompact (w i) := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change QuasiCompact f; infer_instance
    · change QuasiCompact (Dh.subschemeι ≫ f); infer_instance
  obtain ⟨S₁, hS₁int, ψ₁, hψ₁, -, hS₁n, hS₁proj, hflat⟩ :=
    hFLAT Y pY inferInstance hYn hYproj 2 W w hw0 hw1
  let := hψ₁
  have : IsVariety (ψ₁ ≫ pY) := {}
  have : IsProper (ψ₁ ≫ pY) := hS₁proj.isProper
  have : QuasiSeparatedSpace S₁ := quasiSeparatedSpace_of_quasiSeparated (ψ₁ ≫ pY)
  have : IsLocallyNoetherian S₁ := LocallyOfFiniteType.isLocallyNoetherian (ψ₁ ≫ pY)
  have hψη : ψ₁ (genericPoint S₁) = genericPoint Y := genericPoint_map_of_isDominant ψ₁
  -- the strict transform `C` of `X'`
  have hflat0 : Flat (strictTransformHom f ψ₁) := hflat 0
  have hflat1 : Flat (strictTransformHom (Dh.subschemeι ≫ f) ψ₁) := hflat 1
  let C := (strictTransform f ψ₁).subscheme
  let ιC := strictTransformι f ψ₁
  let g := strictTransformHom f ψ₁
  have hlftg : LocallyOfFiniteType g := by dsimp [g, strictTransformHom]; infer_instance
  have hlfpg : LocallyOfFinitePresentation g :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr hlftg
  have hqcg : QuasiCompact g := by dsimp [g, strictTransformHom]; infer_instance
  have : IsProper g := by dsimp [g, strictTransformHom]; infer_instance
  -- generic fibre of `X' ×_Y S₁`
  have hsmP : Smooth ((pullback.snd f ψ₁).fiberToSpecResidueField (genericPoint S₁)) :=
    Geometry.CurveFibrationBaseChange.genericFiber_smooth f ψ₁
  have hgiP : GeometricallyIntegral
      ((pullback.snd f ψ₁).fiberToSpecResidueField (genericPoint S₁)) := by
    have hg : GeometricallyIntegral (f.fiberToSpecResidueField (ψ₁ (genericPoint S₁))) := by
      rw [hψη]; exact hgi
    exact MorphismProperty.of_isPullback (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f ψ₁) (genericPoint S₁)) hg
  have hnodP : IsNodalCurve ((pullback.snd f ψ₁).fiberToSpecResidueField (genericPoint S₁)) := by
    have : IsNodalCurve (f.fiberToSpecResidueField (ψ₁ (genericPoint S₁))) := by
      rw [hψη]; exact hss.nodal
    exact IsNodalCurve.of_isPullback (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f ψ₁) (genericPoint S₁))
  -- generic fibre of `C`
  let EC := strictTransformFiberIso f ψ₁
  have hEC : EC.hom ≫ (pullback.snd f ψ₁).fiberToSpecResidueField (genericPoint S₁) =
      g.fiberToSpecResidueField (genericPoint S₁) :=
    strictTransformFiberIso_hom_fiberToSpecResidueField f ψ₁
  have hsmC : Smooth (g.fiberToSpecResidueField (genericPoint S₁)) := by
    rw [← hEC]; infer_instance
  have hgiC : GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S₁)) := by
    rw [← hEC]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral EC.hom _).mpr hgiP
  have hnodC : IsNodalCurve (g.fiberToSpecResidueField (genericPoint S₁)) := by
    rw [← hEC]; exact IsNodalCurve.of_iso EC _
  have hintC : IsIntegral C := isIntegral_of_flat_of_isIntegral_genericFiber g
    (GeometricallyIntegral.isIntegral_of_subsingleton (g.fiberToSpecResidueField _))
  -- the strict transform `M` of `Dᴴ` and the marks `D_C ⊆ C`
  let Q := pullback (Dh.subschemeι ≫ f) ψ₁
  let ιM := strictTransformι (Dh.subschemeι ≫ f) ψ₁
  let gM := strictTransformHom (Dh.subschemeι ≫ f) ψ₁
  let iQP : Q ⟶ pullback f ψ₁ :=
    pullback.map (Dh.subschemeι ≫ f) ψ₁ f ψ₁ Dh.subschemeι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hiQPsnd : iQP ≫ pullback.snd f ψ₁ = pullback.snd (Dh.subschemeι ≫ f) ψ₁ := by
    simp [iQP]
  have : IsClosedImmersion iQP := by
    dsimp [iQP]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance
      (by simp) (by simp)
  let m := ιM ≫ iQP
  have hker : ιC.ker ≤ m.ker := by
    let fm := pullback.map (pullback.snd (Dh.subschemeι ≫ f) ψ₁)
      (S₁.fromSpecResidueField (genericPoint S₁)) (pullback.snd f ψ₁)
      (S₁.fromSpecResidueField (genericPoint S₁)) iQP (𝟙 _) (𝟙 _) (by rw [hiQPsnd]; simp)
      (by simp)
    have hfm : fm ≫ (pullback.snd f ψ₁).fiberι (genericPoint S₁) =
        (pullback.snd (Dh.subschemeι ≫ f) ψ₁).fiberι (genericPoint S₁) ≫ iQP := by
      simp [fm, Scheme.Hom.fiberι]
    have h1 : ιC.ker = Scheme.Hom.ker ((pullback.snd f ψ₁).fiberι (genericPoint S₁)) :=
      Scheme.IdealSheafData.ker_subschemeι _
    have h2 : m.ker =
        ((pullback.snd (Dh.subschemeι ≫ f) ψ₁).fiberι (genericPoint S₁) ≫ iQP).ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
      rfl
    rw [h1, h2, ← hfm]
    exact Scheme.Hom.le_ker_comp _ _
  let l : (strictTransform (Dh.subschemeι ≫ f) ψ₁).subscheme ⟶ C :=
    IsClosedImmersion.lift ιC m hker
  have hl : l ≫ ιC = m := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion l := by
    have : IsClosedImmersion (l ≫ ιC) := by rw [hl]; dsimp [m]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion l ιC
  let DC : C.IdealSheafData := l.ker
  have : IsIso l.toImage :=
    IsClosedImmersion.isIso_of_ker_eq l l.imageι l.toImage l.toImage_imageι
      (Scheme.IdealSheafData.ker_subschemeι _).symm
  let eM : DC.subscheme ≅ (strictTransform (Dh.subschemeι ≫ f) ψ₁).subscheme :=
    (asIso l.toImage).symm
  have heM : eM.hom ≫ l = DC.subschemeι := by
    simp [eM, DC]
  have heMg : eM.hom ≫ gM = DC.subschemeι ≫ g := by
    rw [← heM, Category.assoc]
    dsimp [gM, g, strictTransformHom]
    rw [← Category.assoc l, hl, Category.assoc, hiQPsnd]
  have hDCflat : Flat (DC.subschemeι ≫ g) := by rw [← heMg]; infer_instance
  have hDClft : LocallyOfFiniteType (DC.subschemeι ≫ g) := inferInstance
  have hDClfp : LocallyOfFinitePresentation (DC.subschemeι ≫ g) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr hDClft
  -- the generic fibre of the marks is étale
  have hetM : Etale ((DC.subschemeι ≫ g).fiberToSpecResidueField (genericPoint S₁)) := by
    have hQ : Etale ((pullback.snd (Dh.subschemeι ≫ f) ψ₁).fiberToSpecResidueField
        (genericPoint S₁)) := by
      have hY : Etale ((Dh.subschemeι ≫ f).fiberToSpecResidueField (ψ₁ (genericPoint S₁))) := by
        rw [hψη]
        have h := hss.etale
        rw [← fiberMarksIso_hom_fiberToSpecResidueField f Dh (genericPoint Y)] at h
        exact (MorphismProperty.cancel_left_of_respectsIso @Etale _ _).mp h
      exact MorphismProperty.of_isPullback (isPullback_fiberToSpecResidueField_of_isPullback
        (IsPullback.of_hasPullback (Dh.subschemeι ≫ f) ψ₁) (genericPoint S₁)) hY
    have hMη : Etale (gM.fiberToSpecResidueField (genericPoint S₁)) := by
      rw [← strictTransformFiberIso_hom_fiberToSpecResidueField (Dh.subschemeι ≫ f) ψ₁]
      infer_instance
    rw [← fiberIsoOfIso_hom_fiberToSpecResidueField eM (DC.subschemeι ≫ g) gM heMg
      (genericPoint S₁)]
    infer_instance
  have hetDC : Etale ((fiberMarks g DC (genericPoint S₁)).subschemeι ≫
      g.fiberToSpecResidueField (genericPoint S₁)) := by
    rw [← fiberMarksIso_hom_fiberToSpecResidueField]
    infer_instance
  -- the bad set
  have : IsNoetherian Q := by
    have : LocallyOfFiniteType (pullback.snd (Dh.subschemeι ≫ f) ψ₁ ≫ ψ₁ ≫ pY) := inferInstance
    have : QuasiCompact (pullback.snd (Dh.subschemeι ≫ f) ψ₁ ≫ ψ₁ ≫ pY) := inferInstance
    have : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (Dh.subschemeι ≫ f) ψ₁ ≫ ψ₁ ≫ pY)
    have : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (Dh.subschemeι ≫ f) ψ₁ ≫ ψ₁ ≫ pY)
    exact ⟨⟩
  obtain ⟨E₁, hE₁, hηE₁, hE₁cov⟩ :=
    exists_closed_forall_mem_strictTransform_support (Dh.subschemeι ≫ f) ψ₁
  have hηT : genericPoint Y ∉ (T : Set Y) := by
    intro h
    apply hT
    ext1
    rw [Closeds.coe_top, ← Set.univ_subset_iff, ← genericPoint_spec Y]
    exact T.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  let bad : Closeds S₁ := ⟨E₁ ∪ ψ₁ ⁻¹' (T : Set Y), hE₁.union (T.isClosed.preimage ψ₁.continuous)⟩
  -- the alteration `C → X`
  have hdomg : IsDominant g := isDominant_of_geometricallyIntegral_genericFiber g hgiC
  have hdomfst : IsDominant (ιC ≫ pullback.fst f ψ₁) := by
    apply isDominant_of_genericPoint_mem_range
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ψ₁)
      (genericPoint X') (genericPoint S₁) (by rw [genericPoint_map_of_isDominant f, hψη])
    have hzC : z ∈ Set.range ιC := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      apply closure_fiber_subset_strictTransform_support f ψ₁
      exact subset_closure hz₂
    obtain ⟨c, rfl⟩ := hzC
    exact ⟨c, hz₁⟩
  have : IsDominant (ιC ≫ pullback.snd f ψ₁) := hdomg
  have hfstC : IsAlteration (ιC ≫ pullback.fst f ψ₁) :=
    Geometry.AlterationDominatingBaseChange.first_isAlteration f ψ₁ ιC
  have hmapC : IsAlteration ((ιC ≫ pullback.fst f ψ₁) ≫ φ) := IsAlteration.comp _ _
  -- projectivity of `C`
  have hCproj : IsProjectiveOver (g ≫ ψ₁ ≫ pY) := by
    have H := isProjectiveOver_pullback f ψ₁ pY (by rw [hfY]; exact hX'proj) hS₁proj
    have H' := IsProjectiveOver.comp_isClosedImmersion H ιC
    have e : ιC ≫ pullback.fst f ψ₁ ≫ f ≫ pY = g ≫ ψ₁ ≫ pY := by
      dsimp [g, strictTransformHom]
      rw [pullback.condition_assoc, Category.assoc]
    rwa [e] at H'
  -- the generic fibre of `C` has dimension one
  have hdimC : topologicalKrullDim C = d := by
    rw [topologicalKrullDim_eq_of_isAlteration p ((ιC ≫ pullback.fst f ψ₁) ≫ φ), hXdim]
  have hdimS₁ : topologicalKrullDim S₁ = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_of_isAlteration pY ψ₁, hYdim]
  have hgen1 : topologicalKrullDim (g.fiber (genericPoint S₁)) = 1 := by
    let := Geometry.SeparableGenericSmoothness.functionFieldAlgebra (ψ₁ ≫ pY)
    let := Geometry.SeparableGenericSmoothness.functionFieldAlgebra (g ≫ ψ₁ ≫ pY)
    let := Geometry.FiniteBirationalNormal.functionFieldAlgebra g
    let := Geometry.VarietyFunctionFieldDimension.functionFieldScalarTower (ψ₁ ≫ pY) g
    obtain ⟨nS, hS, htrS⟩ := Geometry.FunctionFieldDimension.exists_dimension_and_trdeg (ψ₁ ≫ pY)
    obtain ⟨nC, hC, htrC⟩ :=
      Geometry.FunctionFieldDimension.exists_dimension_and_trdeg (g ≫ ψ₁ ≫ pY)
    obtain ⟨r, hr, hrel⟩ := Geometry.SteinGenericFiber.exists_dimension_and_trdeg g
    have hsum := trdeg_add_eq k S₁.functionField (A := C.functionField)
    rw [htrS, hrel, htrC] at hsum
    have h1 : nS = d - 1 := by exact_mod_cast hS.symm.trans hdimS₁
    have h2 : nC = d := by exact_mod_cast hC.symm.trans hdimC
    have hnat : nS + r = nC := by exact_mod_cast hsum
    rw [hr]
    norm_cast
    omega
  have : IsIntegral (g.fiber (genericPoint S₁)) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (g.fiberToSpecResidueField _)
  -- the input of Temkin's theorem
  refine ⟨{
    base := S₁
    baseStructure := ψ₁ ≫ pY
    baseVariety := inferInstance
    baseNormal := hS₁n
    baseProjective := hS₁proj
    baseDim := ?_
    curve := C
    fibration := g
    marks := DC
    curveProjective := hCproj
    multipointed := ?_
    genericSmooth := hsmC
    genericSemistable := ?_
    genericFiber := hgiC
    proper := inferInstance
    map := (ιC ≫ pullback.fst f ψ₁) ≫ φ
    mapAlteration := hmapC
    mapOver := ?_
    bad := bad
    genericPoint_not_mem_bad := ?_
    cover := ?_ }⟩
  · rw [topologicalKrullDim_eq_of_isAlteration pY ψ₁, hYdim]
  · exact {
      flat := hflat0
      locallyOfFinitePresentation := hlfpg
      pureFibers := hFD k S₁ C (ψ₁ ≫ pY) g 1 (fun Z hZ ↦ by
        rw [topologicalKrullDim_eq_of_mem_irreducibleComponents hZ, hgen1]; rfl)
      marksFlat := hDCflat
      marksLocallyOfFinitePresentation := hDClfp
      marksPureFibers := by
        have : QuasiCompact (DC.subschemeι ≫ g) := inferInstance
        refine hFD k S₁ DC.subscheme (ψ₁ ≫ pY) _ 0 ?_
        have := locallyQuasiFinite_of_formallyUnramified
          ((DC.subschemeι ≫ g).fiberToSpecResidueField (genericPoint S₁))
        exact dim_irreducibleComponents_of_locallyQuasiFinite
          ((DC.subschemeι ≫ g).fiberToSpecResidueField (genericPoint S₁)) }
  · exact {
      nodal := hnodC
      etale := hetDC
      smoothAlong := fun x _ ↦ by
        rw [isSmoothAt_iff_mem_smoothLocus, Scheme.Hom.smoothLocus_eq_top]
        trivial }
  · rw [Category.assoc, Category.assoc, ← hfY]
    dsimp [g, strictTransformHom]
    rw [pullback.condition_assoc, Category.assoc]
  · intro h
    rcases h with h | h
    · exact hηE₁ h
    · exact hηT (by rw [Set.mem_preimage, hψη] at h; exact h)
  · intro x hx
    have hx' : (ιC ≫ pullback.fst f ψ₁) x ∈ φ ⁻¹' (D.support : Set X) := hx
    have hgx : ψ₁ (g x) = f ((ιC ≫ pullback.fst f ψ₁) x) := by
      change (ιC ≫ pullback.snd f ψ₁ ≫ ψ₁) x = (ιC ≫ pullback.fst f ψ₁ ≫ f) x
      rw [pullback.condition]
    rcases hcov hx' with hDh | hTx
    · by_cases hE : g x ∈ E₁
      · exact Or.inr (Or.inl hE)
      · left
        have hrange : ιC x ∈ Set.range iQP := by
          rw [Scheme.Pullback.range_map]
          refine ⟨?_, ⟨g x, rfl⟩⟩
          rw [Set.mem_preimage, Scheme.IdealSheafData.range_subschemeι]
          exact hDh
        obtain ⟨y, hy⟩ := hrange
        have hyE : pullback.snd (Dh.subschemeι ≫ f) ψ₁ y ∉ E₁ := by
          rw [← hiQPsnd, Scheme.Hom.comp_apply, hy]
          exact hE
        have hyM := hE₁cov y hyE
        rw [← Scheme.IdealSheafData.range_subschemeι] at hyM
        obtain ⟨μ, rfl⟩ := hyM
        have : l μ = x := by
          apply ιC.isClosedEmbedding.injective
          rw [← Scheme.Hom.comp_apply, hl]
          exact hy
        rw [← this]
        exact Scheme.Hom.range_subset_ker_support l ⟨μ, rfl⟩
    · right
      right
      rw [Set.mem_preimage, hgx]
      exact hTx

end DeJongAlterations.StableModification.DeJong
