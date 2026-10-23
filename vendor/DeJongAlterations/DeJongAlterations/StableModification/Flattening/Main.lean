import DeJongAlterations.StableModification.Flattening.Valuation
import DeJongAlterations.StableModification.Flattening.Chart
import DeJongAlterations.StableModification.RiemannZariski.Refinement
import DeJongAlterations.Composition
import DeJongAlterations.Geometry.GenericallyEtaleComposition
import DeJongAlterations.Geometry.NormalizationFiniteArbitraryField
import DeJongAlterations.Geometry.NormalizationProjective
import DeJongAlterations.Geometry.ProjectiveReduction

/-!
# Flattening after a generically étale alteration

This file proves the producer proposition `DeJong.FlatteningAfterGEAlteration k`
(`StableModification/DeJong/Interface.lean`, blueprint `thm:sm-flat`): for a normal projective
variety `S` over a field `k` and finitely many morphisms of finite type `wᵢ : Wᵢ → S`, there is a
generically étale alteration `ψ : S₁ → S`, with `S₁` normal and projective over `k`, such that
every strict transform of `Wᵢ` along `ψ` is flat over `S₁`. This is a weak form of de Jong 2.19
(Raynaud–Gruson, `dejong96-alterations:page-0011`), proved by Temkin's `P`-modification method
(*Stable modification of relative curves*, §3.4, `semi-stable.tex` l.2486–2568) with `P` =
flatness:

* (i) uniqueness: the strict transform is canonical (`DeJong.strictTransform`);
* (ii)–(v) valuation rings: over a valuation ring `V` of `K = k(S)` centred on an affine open `U`
  of `S`, the strict transform is torsion free, hence flat, and finitely presented, and it spreads
  to a finitely generated `F ⊆ V` (`Flattening.exists_flat_local_model`, from
  `Flattening.exists_flat_quotient_torsion`);
* (vi) Riemann–Zariski: the open sets `RZ_K(Spec F)` cover the quasi-compact `RZ_K(S)`; finitely
  many pieces become opens of one proper `p : S' → S` with dominant maps to the `Spec F`
  (`RiemannZariskiSpace.exists_refinement_genericallyEtale`, Temkin 3.2.6), and the strict
  transform is flat over each piece (`Flattening.flat_strictTransform_of_forall`).

Finally Chow's lemma and normalization make `S'` normal and projective
(`Flattening.exists_normal_projective_alteration`). The flatness of the strict transform over the
resulting `S₁` is checked on affine charts `O ⊆ S₁` mapping dominantly to some `Spec F`: there the
strict transform is the base change of the flat model over `F` modulo torsion
(`Flattening.flat_quotient_torsion_baseChange`). We work with `L = K` itself rather than Temkin's
`K^s`: for flatness no extension of the function field is needed. Neither the normality of `S` nor
the algebraic closedness of `k` is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open Set.Notation

namespace DeJongAlterations.StableModification.Flattening

universe u

open RiemannZariskiSpace DeJong

/-- A compact open of a scheme is covered by finitely many affine opens contained in it. -/
lemma exists_finset_affineOpens {X : Scheme.{u}} (V : X.Opens) (hV : IsCompact (V : Set X)) :
    ∃ c : Finset X.affineOpens, (∀ U ∈ c, (U : X.Opens) ≤ V) ∧
      ∀ x ∈ V, ∃ U ∈ c, x ∈ (U : X.Opens) := by
  classical
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover
    (fun U : {U : X.affineOpens // (U : X.Opens) ≤ V} => ((U.1 : X.Opens) : Set X))
    (fun U => U.1.1.isOpen) (by
      intro x hx
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
      exact Set.mem_iUnion.2 ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩)
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro U hU
    obtain ⟨U', -, rfl⟩ := Finset.mem_image.1 hU
    exact U'.2
  · intro x hx
    have := ht hx
    simp only [Set.mem_iUnion] at this
    obtain ⟨U, hU, hxU⟩ := this
    exact ⟨U.1, Finset.mem_image_of_mem _ hU, hxU⟩

/-- **The local flat models** (`lem:sm-strict-transform-spread` in the form used for the
refinement). Let `U` be an affine open of a locally noetherian scheme `S`, `s : Γ(S, U) → K` a
ring map to a field and `V ⊆ K` a valuation ring containing its image. For finitely many
morphisms `wᵢ : Wᵢ → S` locally of finite type and quasi-compact there are a domain `F` of finite
type over `Γ(S, U)` and an injective map `σ : F → K` over `Γ(S, U)` landing in `V`, such that for
affine opens `U_W` covering `wᵢ⁻¹ U` the strict transform `(F ⊗_{Γ(U)} Γ(U_W)) ⧸ torsion` is flat
over `F`. -/
theorem exists_flat_local_model {S : Scheme.{u}} [IsLocallyNoetherian S] {n : ℕ}
    {W : Fin n → Scheme.{u}} (w : ∀ i, W i ⟶ S) [∀ i, LocallyOfFiniteType (w i)]
    [∀ i, QuasiCompact (w i)] {K : Type u} [Field K] (U : S.Opens) (hU : IsAffineOpen U)
    (s : Γ(S, U) →+* K) (V : ValuationSubring K) (hV : ∀ a, s a ∈ V) :
    ∃ (F : Type u) (_ : CommRing F) (_ : IsDomain F) (_ : Algebra Γ(S, U) F) (σ : F →+* K),
      Function.Injective σ ∧ (∀ x, σ x ∈ V) ∧ (algebraMap Γ(S, U) F).FiniteType ∧
      σ.comp (algebraMap Γ(S, U) F) = s ∧
      ∀ i, ∀ y ∈ (w i) ⁻¹ᵁ U, ∃ (UW : (W i).Opens) (_ : IsAffineOpen UW) (_ : y ∈ UW)
        (hUWU : UW ≤ (w i) ⁻¹ᵁ U),
        letI := ((w i).appLE U UW hUWU).hom.toAlgebra
        Module.Flat F ((F ⊗[Γ(S, U)] Γ(W i, UW)) ⧸
          Submodule.torsion F (F ⊗[Γ(S, U)] Γ(W i, UW))) := by
  classical
  let _ : Algebra Γ(S, U) K := s.toAlgebra
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  -- finite affine covers of the preimages of `U`
  have hcov : ∀ i, ∃ c : Finset (W i).affineOpens, (∀ UW ∈ c, (UW : (W i).Opens) ≤ (w i) ⁻¹ᵁ U) ∧
      ∀ y ∈ (w i) ⁻¹ᵁ U, ∃ UW ∈ c, y ∈ (UW : (W i).Opens) := fun i =>
    exists_finset_affineOpens _ (QuasiCompact.isCompact_preimage (f := w i) _ U.isOpen
      hU.isCompact)
  choose c hcle hcmem using hcov
  let ι := Σ i : Fin n, c i
  let B : ι → Type u := fun l => Γ(W l.1, (l.2.1 : (W l.1).Opens))
  let _ : ∀ l, Algebra Γ(S, U) (B l) := fun l =>
    ((w l.1).appLE U l.2.1 (hcle l.1 l.2.1 l.2.2)).hom.toAlgebra
  have : ∀ l, Algebra.FiniteType Γ(S, U) (B l) := fun l =>
    HasRingHomProperty.appLE @LocallyOfFiniteType (w l.1) inferInstance ⟨U, hU⟩ l.2.1
      (hcle l.1 l.2.1 l.2.2)
  obtain ⟨F, hFfg, hFV, hFflat⟩ := exists_flat_quotient_torsion V hV B
  refine ⟨F, inferInstance, inferInstance, inferInstance, F.val.toRingHom, Subtype.val_injective,
    fun x => hFV _ x.2, RingHom.finiteType_algebraMap.2 ((Subalgebra.fg_iff_finiteType F).1 hFfg),
    RingHom.ext fun _ => rfl, fun i y hy => ?_⟩
  obtain ⟨UW, hUWc, hyUW⟩ := hcmem i y hy
  exact ⟨UW.1, UW.2, hyUW, hcle i UW hUWc, hFflat ⟨i, ⟨UW, hUWc⟩⟩⟩

/-- A dominant morphism `m : O → Spec F` from an affine open of `Y`, compatible over `S` with
`ψ : Y → S` and `Spec F → U ⊆ S`, gives an injective ring map `F → Γ(Y, O)` over `Γ(S, U)`. -/
theorem exists_ringHom_of_isDominant {S Y : Scheme.{u}} (ψ : Y ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {F : Type u} [CommRing F] [IsDomain F] [Algebra Γ(S, U) F]
    {O : Y.Opens} (hO : IsAffineOpen O) (m : O.toScheme ⟶ Spec (.of F)) [IsDominant m]
    (hm : m ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) F)) ≫ hU.fromSpec = O.ι ≫ ψ) :
    ∃ (hOU : O ≤ ψ ⁻¹ᵁ U) (σ : F →+* Γ(Y, O)), Function.Injective σ ∧
      σ.comp (algebraMap Γ(S, U) F) = (ψ.appLE U O hOU).hom := by
  have hOU : O ≤ ψ ⁻¹ᵁ U := by
    intro x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      exact hx
    change (O.ι ≫ ψ) y ∈ U
    rw [← hm]
    have : (m ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) F)) ≫ hU.fromSpec) y ∈
        Set.range hU.fromSpec := by
      simp only [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rwa [hU.range_fromSpec] at this
  let m' : Spec Γ(Y, O) ⟶ Spec (.of F) := hO.isoSpec.inv ≫ m
  let σ := Spec.preimage m'
  refine ⟨hOU, σ.hom, ?_, ?_⟩
  · have hd : IsDominant (Spec.map σ) := by
      rw [Spec.map_preimage]
      infer_instance
    have hdr : DenseRange (PrimeSpectrum.comap σ.hom) := (Spec.map σ).denseRange
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical] at hdr
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact IsNilpotent.eq_zero (hdr ha)
  · suffices h : CommRingCat.ofHom (algebraMap Γ(S, U) F) ≫ σ = ψ.appLE U O hOU from
      congrArg CommRingCat.Hom.hom h
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
      IsAffineOpen.SpecMap_appLE_fromSpec ψ hU hO hOU, Category.assoc, hm, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_ι]

/-- **Normal projective models.** For a generically étale alteration `p : S' → S` of a
projective variety `S` over `k`, there is a dominant `q : S₁ → S'` with `S₁` integral, normal and
projective over `k`, such that `q ≫ p` is a generically étale alteration (Chow's lemma followed by
normalization). -/
theorem exists_normal_projective_alteration {k : Type u} [Field k] {S S' : Scheme.{u}}
    (pS : S ⟶ Spec (.of k)) [IsVariety pS] (hproj : IsProjectiveOver pS) (p : S' ⟶ S)
    [hp : IsAlteration p] (hge : IsGenericallyEtale p) :
    ∃ (S₁ : Scheme.{u}) (_ : IsIntegral S₁) (q : S₁ ⟶ S'), IsDominant q ∧
      IsAlteration (q ≫ p) ∧ IsGenericallyEtale (q ≫ p) ∧ IsNormalScheme S₁ ∧
      IsProjectiveOver ((q ≫ p) ≫ pS) := by
  have : IsIntegral S' := hp.sourceIntegral
  have : IsProper pS := hproj.isProper
  have : IsVariety (p ≫ pS) := {}
  obtain ⟨Sp, χ, hχ, hvarp, hprojp⟩ :=
    Geometry.ProjectiveReduction.exists_projective_modification_of_isProper (p ≫ pS)
  have := hχ
  have : IsIntegral Sp := hχ.sourceIntegral
  let ν := Geometry.NormalizationGluing.normalizationStructure Sp
  have : IsIntegral (Geometry.NormalizationGluing.normalization Sp) :=
    Geometry.NormalizationFinite.isIntegral_normalization
  have hν : IsModification ν :=
    Geometry.NormalizationFiniteArbitraryField.normalizationStructure_isModification (χ ≫ p ≫ pS)
  have : IsAlteration (ν ≫ χ) := IsAlteration.comp ν χ
  refine ⟨Geometry.NormalizationGluing.normalization Sp, inferInstance, ν ≫ χ, inferInstance,
    IsAlteration.comp (ν ≫ χ) p, ?_, Geometry.NormalizationGluing.normalization_isNormalScheme Sp,
    ?_⟩
  · exact ((Geometry.NormalizationFiniteArbitraryField.normalizationStructure_isGenericallyEtale
      (χ ≫ p ≫ pS)).comp (isGenericallyEtale_of_birationalOver_id χ hχ.birational)).comp hge
  · have := Geometry.NormalizationProjective.normalization_isProjectiveOver (χ ≫ p ≫ pS) hprojp
    simpa only [Category.assoc] using this

/-- **The flat local models cover the Riemann–Zariski space.** For a separated, quasi-compact,
locally noetherian integral scheme `S` with function field `K` and finitely many morphisms of
finite type `wᵢ : Wᵢ → S`, there are finitely many affine opens `U j` of `S` with local flat models
`F j` (as in `exists_flat_local_model`) whose spectra `T j = Spec (F j) → U j` have
Riemann–Zariski spaces `RZ_K(T j)` covering `RZ_K(S)` (Temkin 3.2.1 and 3.2.7). -/
theorem exists_flat_local_models (S : Scheme.{u}) [IsIntegral S] [S.IsSeparated] [CompactSpace S]
    [IsLocallyNoetherian S] {n : ℕ} {W : Fin n → Scheme.{u}} (w : ∀ i, W i ⟶ S)
    [∀ i, LocallyOfFiniteType (w i)] [∀ i, QuasiCompact (w i)] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → S.Opens) (hU : ∀ j, IsAffineOpen (U j))
      (F : ι → Type u) (_ : ∀ j, CommRing (F j)) (_ : ∀ j, IsDomain (F j))
      (_ : ∀ j, Algebra Γ(S, U j) (F j)) (σ : ∀ j, F j →+* S.functionField),
      (∀ j, Function.Injective (σ j)) ∧ (∀ j, (algebraMap Γ(S, U j) (F j)).FiniteType) ∧
      (∀ j, Spec.map (CommRingCat.ofHom (σ j)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U j) (F j))) ≫ (hU j).fromSpec =
          functionFieldPoint S S.functionField) ∧
      (ofScheme (functionFieldPoint S S.functionField) ⊆
        ⋃ j, ofScheme (Spec.map (CommRingCat.ofHom (σ j)))) ∧
      ∀ j i, ∀ y ∈ (w i) ⁻¹ᵁ U j, ∃ (UW : (W i).Opens) (_ : IsAffineOpen UW) (_ : y ∈ UW)
        (hUWU : UW ≤ (w i) ⁻¹ᵁ U j),
        letI := ((w i).appLE (U j) UW hUWU).hom.toAlgebra
        Module.Flat (F j) ((F j ⊗[Γ(S, U j)] Γ(W i, UW)) ⧸
          Submodule.torsion (F j) (F j ⊗[Γ(S, U j)] Γ(W i, UW))) := by
  classical
  set K := S.functionField
  set η := functionFieldPoint S K
  -- a local flat model at every point of `RZ_K(S)`
  have hloc : ∀ V : ofScheme η, ∃ (U : S.Opens) (hU : IsAffineOpen U) (hηU : η ⁻¹ᵁ U = ⊤)
      (F : Type u) (_ : CommRing F) (_ : IsDomain F) (_ : Algebra Γ(S, U) F) (σ : F →+* K),
      Function.Injective σ ∧ (∀ x, σ x ∈ V.1.valuationSubring) ∧
      (algebraMap Γ(S, U) F).FiniteType ∧ σ.comp (algebraMap Γ(S, U) F) = sectionsToField η U hηU ∧
      ∀ i, ∀ y ∈ (w i) ⁻¹ᵁ U, ∃ (UW : (W i).Opens) (_ : IsAffineOpen UW) (_ : y ∈ UW)
        (hUWU : UW ≤ (w i) ⁻¹ᵁ U),
        letI := ((w i).appLE U UW hUWU).hom.toAlgebra
        Module.Flat F ((F ⊗[Γ(S, U)] Γ(W i, UW)) ⧸
          Submodule.torsion F (F ⊗[Γ(S, U)] Γ(W i, UW))) := fun V => by
    obtain ⟨U, hηU, hVU⟩ := mem_ofScheme_iff.1 V.2
    exact ⟨U, U.2, hηU, exists_flat_local_model w U U.2 _ V.1.valuationSubring
      (mem_ofRingHom.1 hVU)⟩
  choose U hU hηU F instR instD instA σ hσinj hσV hσft hσcomp hflat using hloc
  -- the affine pieces
  have hηT : ∀ V, Spec.map (CommRingCat.ofHom (σ V)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U V) (F V))) ≫ (hU V).fromSpec = η := by
    intro V
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hσcomp V]
    exact SpecMap_sectionsToField_fromSpec η (hU V) (hηU V)
  have hlft : ∀ V, LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, U V) (F V))) ≫ (hU V).fromSpec) := by
    intro V
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U V) (F V)))) :=
      HasRingHomProperty.Spec_iff.2 (hσft V)
    infer_instance
  have hmem : ∀ V : ofScheme η, V.1 ∈ ofScheme (Spec.map (CommRingCat.ofHom (σ V))) := by
    intro V
    refine ⟨Spec.map (CommRingCat.ofHom ((σ V).codRestrict V.1.valuationSubring (hσV V))), ?_⟩
    rw [toSpecValuationSubring, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  -- quasi-compactness of `RZ_K(S)`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : ofScheme η => ofScheme η ↓∩ ofScheme (Spec.map (CommRingCat.ofHom (σ V))))
    (fun V => isOpen_ofScheme_of_locallyOfFiniteType _ (hηT V)) (fun V _ =>
      Set.mem_iUnion.2 ⟨V, hmem V⟩)
  refine ⟨t, inferInstance, fun j => U j.1, fun j => hU j.1, fun j => F j.1, fun j => instR j.1,
    fun j => instD j.1, fun j => instA j.1, fun j => σ j.1, fun j => hσinj j.1,
    fun j => hσft j.1, fun j => hηT j.1, ?_, fun j => hflat j.1⟩
  intro V hV
  have := ht (Set.mem_univ ⟨V, hV⟩)
  simp only [Set.mem_iUnion] at this
  obtain ⟨j, hj, hVj⟩ := this
  exact Set.mem_iUnion.2 ⟨⟨j, hj⟩, hVj⟩

/-- **FLAT** (`thm:sm-flat`, weak de Jong 2.19 after a generically étale alteration, by
Temkin's method of §3.4). For a normal projective variety `S` over a field `k` and finitely many
morphisms of finite type `wᵢ : Wᵢ → S`, there is a generically étale alteration `ψ : S₁ → S`
with `S₁` integral, normal and projective over `k`, such that every strict transform
`strictTransform (wᵢ) ψ` is flat over `S₁`. -/
theorem flatteningAfterGEAlteration (k : Type u) [Field k] [IsAlgClosed k] :
    FlatteningAfterGEAlteration k := by
  intro S pS hvar _ hproj n W w hlft hqc
  have : IsIntegral S := hvar.toIsIntegral
  have : S.IsSeparated := ⟨by rw [← terminal.comp_from pS]; infer_instance⟩
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace pS
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian pS
  have : ∀ i, LocallyOfFiniteType (w i) := hlft
  have : ∀ i, QuasiCompact (w i) := hqc
  obtain ⟨ι, _, U, hU, F, _, _, _, σ, hσinj, hσft, hηT, hcov, hflat⟩ :=
    exists_flat_local_models S w
  -- the refinement
  have : ∀ j, LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, U j) (F j))) ≫ (hU j).fromSpec) := by
    intro j
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U j) (F j)))) :=
      HasRingHomProperty.Spec_iff.2 (hσft j)
    infer_instance
  have hgU : ∀ j, (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U j) (F j))) ≫
      (hU j).fromSpec) ⁻¹ᵁ U j = ⊤ := by
    intro j
    rw [Scheme.Hom.comp_preimage, (hU j).fromSpec_preimage_self, Scheme.Hom.preimage_top]
  obtain ⟨S', p, η', Wj, h, halt, hge, -, -, hh, -, hcov'⟩ :=
    exists_refinement_genericallyEtale (L := S.functionField) (fun j => Spec (.of (F j)))
      (fun j => Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U j) (F j))) ≫ (hU j).fromSpec)
      (fun j => Spec.map (CommRingCat.ofHom (σ j))) hηT U hU hgU
  have hWtop : ⨆ j, Wj j = ⊤ := hcov' hcov
  -- the normal projective model
  obtain ⟨S₁, _, q, hqd, halt₁, hge₁, hnorm₁, hproj₁⟩ :=
    exists_normal_projective_alteration pS hproj p hge
  refine ⟨S₁, inferInstance, q ≫ p, halt₁, hge₁, hnorm₁, hproj₁, fun i => ?_⟩
  -- flatness of the strict transform, chart by chart
  refine flat_strictTransform_of_forall (w i) (q ≫ p) fun s => ?_
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show q s ∈ ⨆ j, Wj j by rw [hWtop]; trivial)
  obtain ⟨O, hO, hsO, hOle⟩ : ∃ O : S₁.Opens, IsAffineOpen O ∧ s ∈ O ∧ O ≤ q ⁻¹ᵁ Wj j := by
    obtain ⟨_, ⟨O, hO, rfl⟩, hsO, hOle⟩ := S₁.isBasis_affineOpens.exists_subset_of_mem_open
      (show s ∈ q ⁻¹ᵁ Wj j from hj) (q ⁻¹ᵁ Wj j).isOpen
    exact ⟨O, hO, hsO, hOle⟩
  obtain ⟨hhp, hhg, e, he₁, he₂, hed⟩ := hh j
  let m : O.toScheme ⟶ Spec (.of (F j)) := q.resLE (Wj j) O hOle ≫ h j
  have hm : m ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U j) (F j))) ≫ (hU j).fromSpec =
      O.ι ≫ (q ≫ p) := by
    simp only [m, Category.assoc]
    rw [hhg, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have hmd : IsDominant m := by
    have : IsDominant (Spec.map (CommRingCat.ofHom (σ j))) :=
      isDominant_SpecMap_of_injective _ (hσinj j)
    have : IsDominant (e ≫ h j) := by
      rw [he₂]
      infer_instance
    have : IsDominant (h j) := IsDominant.of_comp e (h j)
    have : Nonempty O := ⟨⟨s, hsO⟩⟩
    have : IsDominant O.ι := Opens.isDominant_ι (O.isOpen.dense ⟨s, hsO⟩)
    have : IsDominant (q.resLE (Wj j) O hOle ≫ (Wj j).ι) := by
      rw [Scheme.Hom.resLE_comp_ι]
      infer_instance
    have : IsDominant (q.resLE (Wj j) O hOle) :=
      IsDominant.of_comp_of_isOpenImmersion _ (Wj j).ι
    infer_instance
  obtain ⟨hOU, σ', hσ'inj, hσ'comp⟩ := exists_ringHom_of_isDominant (q ≫ p) (hU j) hO m hm
  exact ⟨U j, hU j, O, hO, hsO, hOU, F j, inferInstance, inferInstance, inferInstance, σ',
    hσ'inj, hσ'comp, hflat j i⟩

end DeJongAlterations.StableModification.Flattening
