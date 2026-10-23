import DeJongAlterations.Geometry.ProperSteinProjectiveCechAffineExactness

/-!
# Actual native local finite type produces finite original affine sections

Native-only adaptation of selected closed proofs from
`EnvelopeProperty/deps/aintlib-ep33/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean`,
SHA256 a8dc9bd99f712c3e5e4dbbd0ed5237f8e205ec957695689df4147c3ceed00d7d.
Every original affine-chart finiteness and localization property is derived.
-/

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {X : Scheme.{u}} {R : CommRingCat.{u}}

private abbrev originalSpecBasicOpen (R : CommRingCat.{u}) (f : R) : (Spec R).Opens :=
  PrimeSpectrum.basicOpen f

private theorem affineOpen_restrictGeneratorsSections_finite
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) := by
  let : IsAffine U.toScheme := hU
  let F := (Scheme.Modules.overEquiv U).functor
  let : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    (Scheme.Modules.overEquiv U).toAdjunction.leftAdjoint_preservesColimits
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF (Iso.refl _)
  let G'' := SheafOfModules.GeneratingSections.equivOfIso
    ((Scheme.Modules.overFunctorEquiv U).app M) G'
  have : G''.IsFiniteType := ⟨by
    change Finite G.I
    infer_instance⟩
  exact affineQuasicoherent_generatorsGlobalSections_finite
    (M.restrict U.ι) G''

theorem affineOpen_generatorsSections_finite
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, U) Γ(M, U) := by
  have hfinite : Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) :=
    affineOpen_restrictGeneratorsSections_finite M U hU G
  let eR' := U.ι.appIso (⊤ : U.toScheme.Opens)
  let eR : Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) ≃+* Γ(U.toScheme, ⊤) :=
    eR'.commRingCatIsoToRingEquiv
  let eM' := M.restrictAppIso U.ι ⊤
  let σ : Γ(U.toScheme, ⊤) →+*
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := eR'.inv.hom
  let eM : Γ(M.restrict U.ι, ⊤) →ₛₗ[σ]
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    { toFun := eM'.hom
      map_add' := eM'.hom.hom.map_add
      map_smul' := by
        intro r x
        change eM'.hom (r • x) = eR'.inv.hom r • eM'.hom x
        exact Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M ⊤ r x }
  have hσ : Function.Surjective σ := by
    change Function.Surjective
      (eR.symm : Γ(U.toScheme, ⊤) →+*
        Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)))
    exact eR.symm.surjective
  let : RingHomSurjective σ := ⟨hσ⟩
  have heM : Function.Bijective eM := by
    change Function.Bijective eM'.hom
    exact ConcreteCategory.bijective_of_isIso eM'.hom
  have htarget : Module.Finite
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens))
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    (eM.finite_iff_of_bijective heM).mp hfinite
  rw [U.ι_image_top] at htarget
  exact htarget

theorem affineSubopen_generatorsSections_finite
    (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hVU : V ≤ U) (hV : IsAffineOpen V)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, V) Γ(M, V) := by
  let i : V ⟶ U := homOfLE hVU
  let F := SheafOfModules.overMap X.ringCatSheaf i
  let : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    (SheafOfModules.overMapPushforwardAdj X.ringCatSheaf i).leftAdjoint_preservesColimits
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF
      (SheafOfModules.overMapUnitIso i).symm
  let G'' := SheafOfModules.GeneratingSections.equivOfIso
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M) G'
  have : G''.IsFiniteType := ⟨by
    change Finite G.I
    infer_instance⟩
  exact affineOpen_generatorsSections_finite M V hV G''

/-- A finite-type quasicoherent module on an affine spectrum has finite global sections. -/
theorem affineQuasicoherentSpec_globalSections_finite
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R Γ(M, ⊤) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let : q.IsFiniteType := hq
  let t : Set R := { f | ∃ i, originalSpecBasicOpen R f ≤ q.X i }
  have hqcover : ⨆ i, q.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (T := Spec R) q.X).mp q.coversTop
  have hopen : ⨆ f ∈ t, originalSpecBasicOpen R f = ⊤ := by
    apply top_unique
    rw [← hqcover]
    refine iSup_le fun i ↦ ?_
    rintro x hx
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx (q.X i).2
    have hle : originalSpecBasicOpen R f ≤ ⨆ f ∈ t, originalSpecBasicOpen R f :=
      le_iSup_of_le f (le_iSup_of_le (show f ∈ t from ⟨i, hf⟩) le_rfl)
    exact hle hxf
  have ht : Ideal.span t = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hopen
  let φ : (g : t) → Γ(M, ⊤) →ₗ[R] Γ(M, originalSpecBasicOpen R g.1) :=
    fun g ↦ ((modulesSpecToSheaf.obj M).obj.map
      (originalSpecBasicOpen R g.1).leTop.op).hom
  have hlocal : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  let (g : t) : Algebra R Γ(Spec R, originalSpecBasicOpen R g.1) :=
    inferInstance
  let (g : t) : IsLocalization.Away g.1
      Γ(Spec R, originalSpecBasicOpen R g.1) := inferInstance
  let (g : t) : IsScalarTower R
      Γ(Spec R, originalSpecBasicOpen R g.1) Γ(M, originalSpecBasicOpen R g.1) :=
    inferInstance
  let : ∀ g : t, IsLocalizedModule.Away g.1 (φ g) :=
    fun g ↦ hlocal g.1
  refine Module.Finite.of_localizationSpan'
    (Mₚ := fun g : t ↦ Γ(M, originalSpecBasicOpen R g.1))
    (Rₚ := fun g : t ↦ Γ(Spec R, originalSpecBasicOpen R g.1))
    t ht φ ?_
  intro g
  obtain ⟨i, hi⟩ := g.2
  let : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact affineSubopen_generatorsSections_finite M hi
    (IsAffineOpen.Spec_basicOpen g.1) (q.generators i)


private theorem affineQuasicoherentSpec_existsFiniteGenerators_ofFiniteSections
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R Γ(M, ⊤)] :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  let : Module.Finite R (moduleSpecΓFunctor.obj M) := by
    change Module.Finite R Γ(M, ⊤)
    infer_instance
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin
    (R := R) (M := moduleSpecΓFunctor.obj M)
  let ι := ULift.{u} (Fin n)
  let v : ι → moduleSpecΓFunctor.obj M := fun i ↦ s i.down
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    have hrange : Set.range v = Set.range s := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨ULift.up i, rfl⟩
    rw [hrange, hs]
  let p' : ModuleCat.of R (ι →₀ R) ⟶ moduleSpecΓFunctor.obj M := by
    change ModuleCat.of R (ι →₀ R) ⟶
      ModuleCat.of R (moduleSpecΓFunctor.obj M)
    exact ModuleCat.ofHom (Finsupp.linearCombination R v)
  let : Epi p' := (ModuleCat.epi_iff_surjective p').mpr
    ((span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp hv)
  let : (tilde.functor R).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction tilde.adjunction
  have hmap : Epi ((tilde.functor R).map p') :=
    Functor.map_epi (tilde.functor R) p'
  let : IsIso M.fromTildeΓ := inferInstance
  have hfrom : Epi M.fromTildeΓ := IsIso.epi_of_iso M.fromTildeΓ
  let e := tildeFinsupp (R := R) ι
  let : IsIso e.inv := e.isIso_inv
  have he : Epi e.inv := IsIso.epi_of_iso e.inv
  let f : SheafOfModules.free (R := (Spec R).ringCatSheaf) ι ⟶ M :=
    e.inv ≫ (tilde.functor R).map p' ≫ M.fromTildeΓ
  have : Epi f := by
    have hleft : Epi (e.inv ≫ (tilde.functor R).map p') :=
      epi_comp' he hmap
    have hfull : Epi ((e.inv ≫ (tilde.functor R).map p') ≫ M.fromTildeΓ) :=
      epi_comp' hleft hfrom
    exact hfull
  let G : M.GeneratingSections :=
    { I := ι
      s := M.freeHomEquiv f
      epi := by
        rw [Equiv.symm_apply_apply]
        infer_instance }
  have : G.IsFiniteType := ⟨inferInstance⟩
  exact ⟨G, inferInstance⟩


/-- Native original local finite type internally gives actual finite original global generators. -/
theorem affineQuasicoherentSpec_existsFiniteGenerators
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  let := affineQuasicoherentSpec_globalSections_finite M
  exact affineQuasicoherentSpec_existsFiniteGenerators_ofFiniteSections M

end
end DeJongAlterations.Geometry.ProperSteinProjectiveCech
