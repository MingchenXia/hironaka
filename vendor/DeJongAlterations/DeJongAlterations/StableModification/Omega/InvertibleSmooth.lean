import DeJongAlterations.StableModification.Omega.InvertibleNode
import DeJongAlterations.Algebra.RegularSmoothConverseResidue
import DeJongAlterations.Geometry.RegularSmooth
import DeJongAlterations.StableModification.Curves.SemistableNormalScheme

/-!
# Relative dimension one at smooth points, and `ω` on the smooth locus

Step 2 of `lem:sm-omega-invertible` (blueprint `sm-omega-invertible.tex`; M. Temkin, *Stable
modification of relative curves*, §1.2, T:1691–1712). Let `f : X ⟶ S` be locally of finite
presentation with geometric fibres of pure dimension one (`PureOneDimensionalFibres`, Temkin's
`S`-curves, T:1672). At a point `x` of the smooth locus, `f` is standard smooth of relative
dimension one on an affine neighbourhood of `x` (`exists_isStandardSmoothOfRelativeDimension_one`);
hence `Ω¹_{X/S}` and `ω_{X/S}` are invertible at `x`
(`isInvertibleAt_dualizingSheaf_of_mem_smoothLocus`), and `f` restricted to its smooth locus is
smooth of relative dimension one (`smoothOfRelativeDimension_one_smoothLocus`).

The relative dimension `n` of a standard smooth chart `R → B` is computed on a geometric fibre:
for a closed point `z` of `K ⊗_R B` (`K` algebraically closed), `K ⊗_R B` is standard smooth of
relative dimension `n` over `K`, so `κ(z) ⊗ Ω` has dimension `n`; the local ring at `z` is
regular (smooth over a field) with residue field `K`, so `κ(z) ⊗ Ω ≅ m_z/m_z²` has dimension
`dim 𝒪_z`, which is one because the components of the geometric fibre are curves
(`relDim_eq_one_of_ringKrullDim`, `relDim_eq_one_of_pure`).
-/

noncomputable section

open IsLocalRing TensorProduct AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace DeJongAlterations.StableModification.Omega

/-- **Relative dimension from the dimension of a closed fibre point.** If `T` is standard smooth of
relative dimension `n` over an algebraically closed field `K` and the local ring of `T` at a maximal
ideal `z` has dimension one, then `n = 1`. -/
theorem relDim_eq_one_of_ringKrullDim {K T : Type u} [Field K] [IsAlgClosed K] [CommRing T]
    [Algebra K T] {n : ℕ} [Algebra.IsStandardSmoothOfRelativeDimension n K T] (z : Ideal T)
    [z.IsMaximal] (hdim : ringKrullDim (Localization.AtPrime z) = 1) : n = 1 := by
  let L := Localization.AtPrime z
  have : Nontrivial T := nontrivial_of_ne 0 1 fun h =>
    (Ideal.IsMaximal.ne_top ‹_›) ((Ideal.eq_top_iff_one z).mpr (h ▸ z.zero_mem))
  have : Algebra.IsStandardSmooth K T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have hrank : Module.finrank T Ω[T⁄K] = n :=
    Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)
  -- `Ω_{L/K} = L ⊗_T Ω_{T/K}`
  let eL : L ⊗[T] Ω[T⁄K] ≃ₗ[L] Ω[L⁄K] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K T L
  have : Module.Free L Ω[L⁄K] := Module.Free.of_equiv eL
  have : Module.Finite L Ω[L⁄K] := Module.Finite.equiv eL
  have hrankL : Module.finrank L Ω[L⁄K] = n := by
    rw [← eL.finrank_eq, Module.finrank_baseChange, hrank]
  have hrankκ : Module.finrank (ResidueField L) (ResidueField L ⊗[L] Ω[L⁄K]) = n := by
    rw [Module.finrank_baseChange, hrankL]
  -- regularity and the residue field
  have : Algebra.Smooth K T := inferInstance
  have hreg : IsRegularRing T := Geometry.RegularSmooth.isRegularRing_of_smooth K T
  have : IsRegularLocalRing L := (isRegularRing_iff.mp hreg) z
  have : Algebra.FiniteType K T := inferInstance
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.comp K T L
  have hformula :=
    Algebra.RegularSmoothConverseResidue.finrank_residueTensorKaehler_eq_of_isRegularLocalRing
    K L
  have hsurj : Function.Surjective (algebraMap K (ResidueField L)) := by
    have h1 := Curves.SemistableOpen.algebraMap_quotient_surjective_of_isAlgClosed K T z
    have h2 := z.bijective_algebraMap_quotient_residueField.surjective
    rw [IsScalarTower.algebraMap_eq K (T ⧸ z) z.ResidueField]
    exact h2.comp h1
  have : Subsingleton Ω[ResidueField L⁄K] :=
    KaehlerDifferential.subsingleton_of_surjective K _ hsurj
  rw [hrankκ, hdim, Module.finrank_zero_of_subsingleton] at hformula
  exact_mod_cast hformula


section Scheme

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Curves.SemistableOpen.locallyOfFinitePresentation_spec

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]

/-- A standard smooth algebra over an affine chart of a scheme with geometric fibres of pure
dimension one has relative dimension one. -/
theorem relDim_eq_one_of_pure (hpure : Curves.SemistableOpen.PureOneDimensionalFibres f)
    {V : S.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V)
    (s : Γ(X, W)) (𝔭 : Ideal (Localization.Away s)) [𝔭.IsPrime] {n : ℕ}
    (hn : letI := (f.appLE V W hWV).hom.toAlgebra
      Algebra.IsStandardSmoothOfRelativeDimension n Γ(S, V) (Localization.Away s)) :
    n = 1 := by
  let := (f.appLE V W hWV).hom.toAlgebra
  let R := Γ(S, V)
  let B := Localization.Away s
  obtain ⟨K, _, _, _, z, hz, -⟩ := Curves.SemistableNormal.exists_geometricPoint (R := R) 𝔭
  have hsq₀ : hW.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))) ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hWV).symm
  have hsq := Curves.SemistableOpen.localization_chart_sq f hsq₀ s
  let a : Spec (.of K) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ hV.fromSpec
  have hpureT : ∀ Z ∈ irreducibleComponents (Spec (.of (K ⊗[R] B))), topologicalKrullDim Z = 1 :=
    Curves.SemistableOpen.pure_of_etale (q' := pullback.snd f a)
      (Curves.SemistableOpen.tensorChart f hsq (a := a) rfl) (hpure K a)
  let zP : PrimeSpectrum (K ⊗[R] B) := ⟨z, hz.isPrime⟩
  have hzc : IsClosed ({zP} : Set (Spec (.of (K ⊗[R] B)))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal zP).mpr hz
  have hdim := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT zP hzc
  have hdim' : ringKrullDim (Localization.AtPrime z) = 1 := by
    let := Scheme.stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] B)))) zP
    let ε := (Geometry.NodeCompletedLocalSpecLocalization.stalkEquiv K (K ⊗[R] B) zP).toRingEquiv
    rw [← ringKrullDim_eq_of_ringEquiv ε]
    exact hdim
  have : Algebra.IsStandardSmoothOfRelativeDimension n K (K ⊗[R] B) := inferInstance
  exact relDim_eq_one_of_ringKrullDim (K := K) (T := K ⊗[R] B) z hdim'


/-- **Relative dimension one at smooth points** (step 2 of `lem:sm-omega-invertible`). Let
`f : X ⟶ S` be locally of finite presentation with geometric fibres of pure dimension one. At a
point of the smooth locus, `f` is standard smooth of relative dimension one on an affine
neighbourhood contained in the smooth locus. -/
theorem exists_isStandardSmoothOfRelativeDimension_one
    (hpure : Curves.SemistableOpen.PureOneDimensionalFibres f) {x : X} (hx : x ∈ f.smoothLocus) :
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (W : X.Opens) (_ : IsAffineOpen W)
      (hWV : W ≤ f ⁻¹ᵁ V), x ∈ W ∧ W ≤ f.smoothLocus ∧
        (f.appLE V W hWV).hom.IsStandardSmoothOfRelativeDimension 1 := by
  obtain ⟨V, hV, W₀, hW₀, hW₀V, hxW₀, hsm⟩ := exists_smooth_of_formallySmooth_stalk f x hx
  let := (f.appLE V W₀ hW₀V).hom.toAlgebra
  have : Algebra.Smooth Γ(S, V) Γ(X, W₀) := hsm
  set p := hW₀.primeIdealOf ⟨x, hxW₀⟩
  have hloc : ∀ y (hy : y ∈ W₀), y ∈ f.smoothLocus := by
    intro y hy
    rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff V hV W₀ hW₀ hW₀V hy,
      Algebra.smoothLocus_eq_univ]
    trivial
  have : Algebra.IsSmoothAt Γ(S, V) p.asIdeal := by
    have h : p ∈ Algebra.smoothLocus Γ(S, V) Γ(X, W₀) := by
      rw [Algebra.smoothLocus_eq_univ]; trivial
    exact h
  obtain ⟨s, hs, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth Γ(S, V) p.asIdeal
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hstd.out
  have hn : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(S, V)
      (Localization.Away s) := ⟨ι, σ, inferInstance, inferInstance, P, rfl⟩
  have hdisj : Disjoint (Submonoid.powers s : Set Γ(X, W₀)) (p.asIdeal : Set Γ(X, W₀)) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  have : (p.asIdeal.map (algebraMap Γ(X, W₀) (Localization.Away s))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) _ _ inferInstance hdisj
  have h1 := relDim_eq_one_of_pure f hpure hV hW₀ hW₀V s
    (p.asIdeal.map (algebraMap Γ(X, W₀) (Localization.Away s))) hn
  rw [h1] at hn
  have hle : X.basicOpen s ≤ f ⁻¹ᵁ V := (X.basicOpen_le s).trans hW₀V
  refine ⟨V, hV, X.basicOpen s, hW₀.basicOpen s, hle, (mem_basicOpen_iff_notMem hW₀ hxW₀ s).mpr hs,
    fun y hy => hloc y (X.basicOpen_le s hy), ?_⟩
  let : Algebra Γ(X, W₀) Γ(X, X.basicOpen s) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.toAlgebra
  have := hW₀.isLocalization_basicOpen s
  let : Algebra Γ(S, V) Γ(X, X.basicOpen s) := (f.appLE V (X.basicOpen s) hle).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, W₀) Γ(X, X.basicOpen s) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change f.appLE V (X.basicOpen s) hle r =
        X.presheaf.map (homOfLE (X.basicOpen_le s)).op (f.appLE V W₀ hW₀V r)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map])
  let e : Localization.Away s ≃ₐ[Γ(X, W₀)] Γ(X, X.basicOpen s) :=
    IsLocalization.algEquiv (Submonoid.powers s) _ _
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1 (e.restrictScalars Γ(S, V))


/-- **`ω_{X/S}` at smooth points.** If the geometric fibres of `f` have pure dimension one,
then `ω_{X/S}` is invertible at every point of the smooth locus. -/
theorem isInvertibleAt_dualizingSheaf_of_mem_smoothLocus
    (hpure : Curves.SemistableOpen.PureOneDimensionalFibres f) {x : X} (hx : x ∈ f.smoothLocus) :
    IsInvertibleAt (dualizingSheaf f) x := by
  obtain ⟨V, hV, W, hW, hWV, hxW, hWU, h⟩ :=
    exists_isStandardSmoothOfRelativeDimension_one f hpure hx
  exact isInvertibleAt_dualizingSheaf f hV hW hxW hWU hWV h

/-- **`Ω¹_{X/S}` at smooth points.** If the geometric fibres of `f` have pure dimension one,
then `Ω¹_{X/S}` is invertible at every point of the smooth locus. -/
theorem isInvertibleAt_relativeDifferentials_of_mem_smoothLocus
    (hpure : Curves.SemistableOpen.PureOneDimensionalFibres f) {x : X} (hx : x ∈ f.smoothLocus) :
    IsInvertibleAt (relativeDifferentials f) x := by
  obtain ⟨V, hV, W, hW, hWV, hxW, -, h⟩ := exists_isStandardSmoothOfRelativeDimension_one f hpure hx
  have : Nontrivial Γ(X, W) := nontrivial_sections_of_mem hxW
  obtain ⟨eΩ⟩ := kaehler_linearEquiv_of_isStandardSmoothOfRelativeDimension_one _ h
  exact ⟨W, hW, hxW, restrict_iso_unit_of_linearEquiv f hW hV hWV eΩ⟩

omit [LocallyOfFinitePresentation f] in
/-- Standard smoothness of `appLE` is insensitive to replacing the open by an equal one. -/
theorem isStandardSmoothOfRelativeDimension_appLE_congr {n : ℕ} {V : S.Opens} {W W₁ : X.Opens}
    (h : W₁ = W) (hWV : W ≤ f ⁻¹ᵁ V) (hW₁V : W₁ ≤ f ⁻¹ᵁ V)
    (hs : (f.appLE V W hWV).hom.IsStandardSmoothOfRelativeDimension n) :
    (f.appLE V W₁ hW₁V).hom.IsStandardSmoothOfRelativeDimension n := by
  subst h
  exact hs

/-- **The smooth locus is smooth of relative dimension one** (step 2 of
`lem:sm-omega-invertible`): if the geometric fibres of `f` have pure dimension one, then `f`
restricted to its smooth locus is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_smoothLocus
    (hpure : Curves.SemistableOpen.PureOneDimensionalFibres f) :
    SmoothOfRelativeDimension 1 (f.smoothLocus.ι ≫ f) := by
  constructor
  intro y
  obtain ⟨V, hV, W, hW, hWV, hxW, hWU, h⟩ :=
    exists_isStandardSmoothOfRelativeDimension_one f hpure (x := f.smoothLocus.ι y) y.2
  set ι := f.smoothLocus.ι
  have hW' : IsAffineOpen (ι ⁻¹ᵁ W) :=
    hW.preimage_of_isOpenImmersion ι (by rw [Scheme.Opens.opensRange_ι]; exact hWU)
  have himage : ι ''ᵁ (ι ⁻¹ᵁ W) = W := by
    rw [ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWU]
  have e : ι ⁻¹ᵁ W ≤ (ι ≫ f) ⁻¹ᵁ V := fun z hz => hWV hz
  refine ⟨V, hV, ι ⁻¹ᵁ W, hW', hxW, e, ?_⟩
  have hle : ι ''ᵁ (ι ⁻¹ᵁ W) ≤ f ⁻¹ᵁ V := himage.le.trans hWV
  have h1 : (ι ≫ f).appLE V (ι ⁻¹ᵁ W) e =
      f.appLE V (ι ''ᵁ (ι ⁻¹ᵁ W)) hle ≫ (ι.appIso (ι ⁻¹ᵁ W)).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  rw [h1, CommRingCat.hom_comp]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left _
    (ι.appIso (ι ⁻¹ᵁ W)).commRingCatIsoToRingEquiv
    (isStandardSmoothOfRelativeDimension_appLE_congr f himage hWV hle h)

end Scheme

end DeJongAlterations.StableModification.Omega
