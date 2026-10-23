/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3B)
-/
import DeJongAlterations.StableModification.CurvesField.AmpleTwoChart
import DeJongAlterations.Geometry.ProperSteinProjectiveCechAffineFiniteType

/-!
# Serre ampleness from two sections with affine non-vanishing loci

Let `L` be line-bundle data on a quasi-compact scheme `X` with affine diagonal, and let `s₀`, `s₁`
be global sections of `𝓛^N` (`N > 0`) whose non-vanishing loci `D(s₀)`, `D(s₁)` are affine and
cover `X`. If the first cohomology of every coherent module is a finite module over some
coefficient ring (for instance `X` projective over a Noetherian ring,
`Cohomology.finite_cohomology_of_isProjectiveOver`), then `L` is **ample in Serre's sense**
(`serreAmple_of_two_sections`): for every quasi-coherent `F` of finite type and all `m ≫ 0`, the
twist `F ⊗ 𝓛^m` has vanishing first Čech cohomology for every finite affine cover and is generated
by global sections (OM3A's `Projectivity.LineBundleData.SerreAmple`; Hartshorne II.7.5, III.5.3,
EGA II 4.5.2 in the case of two sections). Blueprint `sm-curves-fields-ample.tex`,
`prop:sm-ample-two-sections`.

## The argument

With `U = D(s₀)`, `V = D(s₁)`, the twists `F ⊗ 𝓛^{Nk}` are the divisor twists `F(kD)` along
`(U, V)` by `f = s₀ / s₁ ∈ Γ(V, 𝒪)` (`LineBundleData.twoChartIso`), and `U ∩ V = D(f)` inside the
affine `V`. Lane COH4's Serre vanishing (`CurvesField.serre_vanishing_cohomology`) gives
`H¹(F(kD)) = 0` for `k ≫ 0`, and its global generation on `U`
(`CurvesField.exists_global_section_extending`) shows that every section of `F` over `U` times
`s₀^k` extends to a global section of `F ⊗ 𝓛^{Nk}`; with finitely many generators of `Γ(U, F)` the
global sections generate `F ⊗ 𝓛^{Nk}` over `U`, and symmetrically over `V`. Generation over the two
affine opens is generation in the sense of `Projectivity.IsGloballyGenerated`
(`isGloballyGenerated_of_affine_cover`, by quasi-coherence). Finally every `m` is `r + N k` with
`0 ≤ r < N`, and `F ⊗ 𝓛^m ≅ (F ⊗ 𝓛^r) ⊗ 𝓛^{Nk}` with `F ⊗ 𝓛^r` again coherent
(`finite_sections_twist`).

## Main results

* `isZero_cechCohomology_succ_iff_coeff`: the vanishing of `Ȟ^{p+1}` does not depend on the
  coefficient ring.
* `finite_sections_of_basicOpen`, `finite_sections_of_isFiniteType`, `finite_sections_twist`:
  quasi-coherent modules of finite type (and their twists) have finite sections over affine opens.
* `isGloballyGenerated_of_affine_cover`.
* `exists_twist_vanishing_generated`: the statement for the multiples `N k`.
* `serreAmple_of_two_sections`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField.Ample

noncomputable section

variable {X : Scheme.{u}}

/-! ### Coefficients of Čech cohomology -/

lemma cechComplex_d_val (F : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (p : ℕ) (x : (cechComplex F U c).X p) :
    (((cechComplex F U c).d p (p + 1)).hom x).1 =
      Geometry.ProperSteinProjectiveCech.subsetCechDifferential (cechDiagram F U c) x.1 := by
  change (((Geometry.ProperSteinProjectiveCech.subsetCechComplex (cechDiagram F U c)).d p
    (p + 1)).hom x).1 = _
  rw [subsetCechComplex_d]
  rfl

lemma subsetCechDifferential_cechDiagram_coeff (F : X.Modules) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) {R R' : Type u} [CommRing R] [CommRing R'] (c : R →+* Γ(X, ⊤))
    (c' : R' →+* Γ(X, ⊤))
    (v : Geometry.ProperSteinProjectiveCech.subsetCechCube (cechDiagram F U c)) :
    Geometry.ProperSteinProjectiveCech.subsetCechDifferential (cechDiagram F U c) v =
      Geometry.ProperSteinProjectiveCech.subsetCechDifferential (cechDiagram F U c') v := by
  funext S
  rfl

/-- The vanishing of `Ȟ^{p+1}(U, F)` does not depend on the coefficients `c`. -/
theorem isZero_cechCohomology_succ_iff_coeff (F : X.Modules) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) {R R' : Type u} [CommRing R] [CommRing R'] (c : R →+* Γ(X, ⊤))
    (c' : R' →+* Γ(X, ⊤)) (p : ℕ) :
    IsZero (cechCohomology F U c (p + 1)) ↔ IsZero (cechCohomology F U c' (p + 1)) := by
  suffices H : ∀ {R R' : Type u} [CommRing R] [CommRing R'] (c : R →+* Γ(X, ⊤))
      (c' : R' →+* Γ(X, ⊤)),
      IsZero (cechCohomology F U c (p + 1)) → IsZero (cechCohomology F U c' (p + 1)) from
    ⟨H c c', H c' c⟩
  intro R R' _ _ c c' h
  rw [isZero_homology_succ_iff] at h ⊢
  intro x hx
  let x' : (cechComplex F U c).X (p + 1) := ⟨x.1, x.2⟩
  have hx' : ((cechComplex F U c).d (p + 1) (p + 2)).hom x' = 0 := by
    apply Subtype.ext
    have e := congrArg Subtype.val hx
    rw [cechComplex_d_val F U c' (p + 1)] at e
    rw [cechComplex_d_val F U c (p + 1), subsetCechDifferential_cechDiagram_coeff F U c c']
    exact e
  obtain ⟨y, hy⟩ := h x' hx'
  refine ⟨⟨y.1, y.2⟩, Subtype.ext ?_⟩
  have e1 := cechComplex_d_val F U c' p ⟨y.1, y.2⟩
  have e2 := subsetCechDifferential_cechDiagram_coeff F U c c' y.1
  have e3 := cechComplex_d_val F U c p y
  have e4 := congrArg Subtype.val hy
  exact e1.trans (e2.symm.trans (e3.symm.trans e4))

/-! ### Finite sections -/

/-- Finiteness of the sections of a quasi-coherent module over an affine open is local on basic
opens. -/
theorem finite_sections_of_basicOpen (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W)
    (h : ∀ x ∈ W, ∃ g : Γ(X, W), x ∈ X.basicOpen g ∧
      Module.Finite Γ(X, X.basicOpen g) Γ(M, X.basicOpen g)) :
    Module.Finite Γ(X, W) Γ(M, W) := by
  let t : Set Γ(X, W) := {g | Module.Finite Γ(X, X.basicOpen g) Γ(M, X.basicOpen g)}
  have ht : Ideal.span t = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨g, hxg, hg⟩ := h x hx
    exact Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  let _ : ∀ g : t, Module Γ(X, W) Γ(M, X.basicOpen g.1) := fun g =>
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le g.1)).op).hom
  have : ∀ g : t, IsLocalization.Away g.1 Γ(X, X.basicOpen g.1) := fun g =>
    hW.isLocalization_basicOpen g.1
  have : ∀ g : t, IsScalarTower Γ(X, W) Γ(X, X.basicOpen g.1) Γ(M, X.basicOpen g.1) :=
    fun g => ⟨fun r a m => by
      change (X.presheaf.map (homOfLE (X.basicOpen_le g.1)).op r * a) • m =
        X.presheaf.map (homOfLE (X.basicOpen_le g.1)).op r • (a • m)
      rw [mul_smul]⟩
  have : ∀ g : t, IsLocalizedModule.Away g.1 (restrictLinearNative M (X.basicOpen_le g.1)) :=
    fun g => isLocalizedModule_restrictLinearNative M hW g.1
  exact Module.Finite.of_localizationSpan' t ht
    (fun g => restrictLinearNative M (X.basicOpen_le g.1)) (fun g => g.2)

/-- A quasi-coherent module of finite type has finite sections over affine opens. -/
theorem finite_sections_of_isFiniteType (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    {W : X.Opens} (hW : IsAffineOpen W) : Module.Finite Γ(X, W) Γ(M, W) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  have hcov : ⨆ i, q.X i = ⊤ := by
    simpa only [IsOpenCover] using (Opens.coversTop_iff (T := X) q.X).mp q.coversTop
  apply finite_sections_of_basicOpen M hW
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, x ∈ q.X i := Opens.mem_iSup.mp (by rw [hcov]; trivial)
  obtain ⟨g, hgle, hxg⟩ := hW.exists_basicOpen_le ⟨x, hi⟩ hx
  refine ⟨g, hxg, ?_⟩
  have := hq.isFiniteType i
  exact Geometry.ProperSteinProjectiveCech.affineSubopen_generatorsSections_finite M hgle
    (hW.basicOpen g) (q.generators i)

/-- Twists of a module with finite sections over affine opens have finite sections over affine
opens. -/
theorem finite_sections_twist (L : LineBundleData X) (F : X.Modules) [F.IsQuasicoherent]
    (hF : ∀ W : X.Opens, IsAffineOpen W → Module.Finite Γ(X, W) Γ(F, W)) (m : ℤ) {W : X.Opens}
    (hW : IsAffineOpen W) : Module.Finite Γ(X, W) Γ(L.twist F m, W) := by
  apply finite_sections_of_basicOpen (L.twist F m) hW
  intro x hx
  obtain ⟨i, hi⟩ := L.exists_mem_U x
  obtain ⟨g, hgle, hxg⟩ := hW.exists_basicOpen_le ⟨x, hi⟩ hx
  refine ⟨g, hxg, ?_⟩
  have := hF _ (hW.basicOpen g)
  exact Module.Finite.equiv (LineBundleData.localEquiv F m hgle).symm

/-! ### Global generation over an affine cover -/

/-- If, on every member of a cover by affine opens, the restrictions of global sections generate
the sections of a quasi-coherent module, the module is generated by global sections. -/
theorem isGloballyGenerated_of_affine_cover (M : X.Modules) [M.IsQuasicoherent] {ι : Type*}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (haff : ∀ i, IsAffineOpen (U i))
    (hgen : ∀ i (y : Γ(M, U i)), y ∈ Submodule.span Γ(X, U i)
      (Set.range fun t : Γ(M, ⊤) => M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op t)) :
    IsGloballyGenerated M := by
  intro W t x hxW
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := Opens.mem_iSup.mp (by rw [hU]; trivial)
  obtain ⟨g, hgW, hxg⟩ := (haff i).exists_basicOpen_le ⟨x, hxW⟩ hi
  refine ⟨X.basicOpen g, hgW, hxg, ?_⟩
  set D := X.basicOpen g
  set S : Submodule Γ(X, D) Γ(M, D) := Submodule.span Γ(X, D)
    (Set.range fun t : Γ(M, ⊤) => M.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op t)
  let _ : Module Γ(X, U i) Γ(M, D) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  have hloc := isLocalizedModule_restrictLinearNative M (haff i) g
  obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, hy⟩ := hloc.surj (M.presheaf.map (homOfLE hgW).op t)
  -- the restriction of `y` lies in `S`
  have hyS : M.presheaf.map (homOfLE (X.basicOpen_le g)).op y ∈ S := by
    refine Submodule.span_induction (p := fun y _ =>
      M.presheaf.map (homOfLE (X.basicOpen_le g)).op y ∈ S) ?_ ?_ ?_ ?_ (hgen i y)
    · rintro _ ⟨t', rfl⟩
      refine Submodule.subset_span ⟨t', ?_⟩
      exact (presheaf_map_map M _ _ _ t').symm
    · rw [map_zero]
      exact S.zero_mem
    · intro a b _ _ ha hb
      rw [map_add]
      exact S.add_mem ha hb
    · intro r a _ ha
      rw [Scheme.Modules.map_smul]
      exact S.smul_mem _ ha
  change X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) •
      M.presheaf.map (homOfLE hgW).op t = M.presheaf.map (homOfLE (X.basicOpen_le g)).op y at hy
  obtain ⟨v, hv⟩ : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n)) := by
    rw [map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen g).pow n
  have ht : M.presheaf.map (homOfLE hgW).op t =
      ((v⁻¹ : Γ(X, D)ˣ) : Γ(X, D)) • M.presheaf.map (homOfLE (X.basicOpen_le g)).op y := by
    rw [← hy, ← hv, smul_smul, Units.inv_mul, one_smul]
  rw [ht]
  exact S.smul_mem _ hyS

/-! ### Two sections with affine non-vanishing loci -/

section TwoSections

open LineBundleData in
/-- **Global generation over `D(s₀)`**: if `D(s₀)`, `D(s₁)` are affine and cover `X`, then for
`k ≫ 0` the sections of `G ⊗ 𝓛^{Nk}` over `D(s₀)` are combinations of restrictions of global
sections. -/
theorem exists_forall_mem_span_of_two_sections {L : LineBundleData X} {N : ℤ}
    (s₀ s₁ : L.Sections N ⊤) (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (h₁ : IsAffineOpen s₁.nonvanishingLocus)
    (G : X.Modules) [G.IsQuasicoherent] (hG : Module.Finite Γ(X, s₀.nonvanishingLocus)
      Γ(G, s₀.nonvanishingLocus)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ y : Γ(L.twist G (N * k), s₀.nonvanishingLocus),
      y ∈ Submodule.span Γ(X, s₀.nonvanishingLocus)
        (Set.range fun t : Γ(L.twist G (N * k), ⊤) =>
          (L.twist G (N * k)).presheaf.map (homOfLE (le_top : s₀.nonvanishingLocus ≤ ⊤)).op t) := by
  classical
  set U := s₀.nonvanishingLocus with hUdef
  set V := s₁.nonvanishingLocus with hVdef
  set σ : L.Sections N V := s₁.restrict (le_top : V ≤ ⊤)
  have hσ : σ.nonvanishingLocus = V := by
    rw [Sections.nonvanishingLocus_restrict]
    exact inf_idem V
  have hU : U ≤ s₀.nonvanishingLocus := le_rfl
  have hf := isUnit_ratio s₀ hσ hU
  have hUVb : U ⊓ V = X.basicOpen (ratio s₀ hσ) := by
    rw [basicOpen_ratio]
    exact inf_comm U V
  obtain ⟨r, a, ha⟩ := Module.Finite.exists_fin (R := Γ(X, U)) (M := Γ(G, U))
  have hext := fun j : Fin r => exists_global_section_extending G U V (RingHom.id Γ(X, ⊤)) hf h₁
    hUVb (a j)
  choose m hm using hext
  refine ⟨Finset.univ.sup m, fun k hk y => ?_⟩
  let e := twoChartIso s₀ hσ G hU k hcov
  -- the global sections extending the generators
  have hT : ∀ j : Fin r, ∃ T : Γ(L.twist G (N * k), ⊤),
      mulSec G ((s₀.npow k).restrict (le_top : U ≤ ⊤)) (a j) =
        L.twistRestrict G _ (le_top : U ≤ ⊤) T := by
    intro j
    obtain ⟨p, hp⟩ := hm j k ((Finset.le_sup (Finset.mem_univ j)).trans hk)
    let T : Γ(L.twist G (N * k), ⊤) := e.inv.app ⊤ p
    have hTp : e.hom.app ⊤ T = p := by
      change (e.inv ≫ e.hom).app ⊤ p = p
      rw [e.inv_hom_id]
      rfl
    refine ⟨T, ?_⟩
    have h1 : (toPair s₀ G hσ hU k ⊤ T).1 =
        G.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ U ≤ U)).op (a j) := by
      have e1 : toPair s₀ G hσ hU k ⊤ T =
          (show twistSubgroup G U V ((isUnit_ratio s₀ hσ hU).unit ^ (k : ℤ)) ⊤ from p).1 := by
        rw [← twoChartHom_app s₀ hσ G hU k ⊤ T]
        exact congrArg (fun z => (show twistSubgroup G U V
          ((isUnit_ratio s₀ hσ hU).unit ^ (k : ℤ)) ⊤ from z).1) hTp
      rw [e1, ← hp]
      exact (presheaf_map_map_self G _ _ _).symm
    have h2 := mulSec_toPair_fst s₀ hσ G hU k ⊤ T
    rw [h1] at h2
    have h3 := congrArg (L.twistRestrict G _ (le_inf le_top le_rfl : U ≤ ⊤ ⊓ U)) h2
    rw [mulSec_restrict, presheaf_map_map_self, Sections.restrict_restrict] at h3
    exact h3.trans (twistRestrict_twistRestrict G _ _ _ T)
  choose T hT using hT
  set σ₀ : L.Sections (N * k) U := (s₀.npow k).restrict (le_top : U ≤ ⊤)
  have hσ₀ : σ₀.nonvanishingLocus = U := by
    rw [Sections.nonvanishingLocus_restrict]
    exact inf_eq_left.mpr (Sections.le_nonvanishingLocus_npow s₀ le_rfl k)
  obtain ⟨b, rfl⟩ := (mulSecEquiv G hσ₀).surjective y
  have hb : b ∈ Submodule.span Γ(X, U) (Set.range a) := by rw [ha]; trivial
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(X, U)).mp hb
  rw [← hcf, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨T j, ?_⟩)
  exact (hT j).symm

open LineBundleData in
/-- **Serre vanishing and global generation for the multiples `N k`**: if `D(s₀)`, `D(s₁)` are
affine and cover `X` (quasi-compact with affine diagonal), and `H¹(X, G)` is a finite `R`-module,
then for `k ≫ 0` the twist `G ⊗ 𝓛^{Nk}` has `H¹ = 0` and is generated by global sections. -/
theorem exists_twist_vanishing_generated [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] {L : LineBundleData X} {N : ℤ}
    (s₀ s₁ : L.Sections N ⊤) (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (h₀ : IsAffineOpen s₀.nonvanishingLocus) (h₁ : IsAffineOpen s₁.nonvanishingLocus)
    {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (G : X.Modules) [G.IsQuasicoherent]
    (hG : ∀ W : X.Opens, IsAffineOpen W → Module.Finite Γ(X, W) Γ(G, W))
    [Module.Finite R (cohomology G c 1)] :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      IsZero (cohomology (L.twist G (N * k)) c 1) ∧ IsGloballyGenerated (L.twist G (N * k)) := by
  set U := s₀.nonvanishingLocus
  set V := s₁.nonvanishingLocus
  set σ : L.Sections N V := s₁.restrict (le_top : V ≤ ⊤)
  have hσ : σ.nonvanishingLocus = V := by
    rw [Sections.nonvanishingLocus_restrict]
    exact inf_idem V
  have hU : U ≤ s₀.nonvanishingLocus := le_rfl
  have hf := isUnit_ratio s₀ hσ hU
  have hUVb : U ⊓ V = X.basicOpen (ratio s₀ hσ) := by
    rw [basicOpen_ratio]
    exact inf_comm U V
  have h₀₁ : IsAffineOpen (U ⊓ V) := h₀.inf h₁
  obtain ⟨k₁, hk₁⟩ := serre_vanishing_cohomology G U V c hf hcov h₀ h₁ h₀₁ hUVb
  obtain ⟨k₂, hk₂⟩ := exists_forall_mem_span_of_two_sections s₀ s₁ hcov h₁ G (hG _ h₀)
  obtain ⟨k₃, hk₃⟩ := exists_forall_mem_span_of_two_sections s₁ s₀ (by rw [sup_comm]; exact hcov)
    h₀ G (hG _ h₁)
  refine ⟨max k₁ (max k₂ k₃), fun k hk => ⟨?_, ?_⟩⟩
  · exact (isZero_cechCohomology_iff_of_iso (twoChartIso s₀ hσ G hU k hcov) _ c 1).mpr
      (hk₁ k (le_of_max_le_left hk))
  · refine isGloballyGenerated_of_affine_cover (L.twist G (N * k)) (fun b : Bool => cond b U V)
      (by rw [iSup_bool_eq]; exact hcov) (fun b => by cases b <;> assumption) ?_
    rintro (_ | _) y
    · exact hk₃ k ((le_max_right _ _).trans ((le_max_right _ _).trans hk)) y
    · exact hk₂ k ((le_max_left _ _).trans ((le_max_right _ _).trans hk)) y

open LineBundleData in
/-- **Serre ampleness from two sections with affine non-vanishing loci** (blueprint
`prop:sm-ample-two-sections`): let `X` be quasi-compact with affine diagonal, `s₀`, `s₁` global
sections of `𝓛^N`, `N > 0`, with `D(s₀)`, `D(s₁)` affine and covering `X`, and suppose that the
first cohomology of every quasi-coherent module with finite sections over affine opens is a finite
`R`-module (for instance `X` projective over a Noetherian ring `R`). Then `𝓛` is ample in Serre's
sense. -/
theorem serreAmple_of_two_sections [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] {L : LineBundleData X} {N : ℕ}
    (hN : 0 < N) (s₀ s₁ : L.Sections N ⊤)
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (h₀ : IsAffineOpen s₀.nonvanishingLocus) (h₁ : IsAffineOpen s₁.nonvanishingLocus)
    {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (hfin : ∀ (G : X.Modules) [G.IsQuasicoherent],
      (∀ W : X.Opens, IsAffineOpen W → Module.Finite Γ(X, W) Γ(G, W)) →
        Module.Finite R (cohomology G c 1)) :
    L.SerreAmple := by
  intro F _ _
  have hF : ∀ W : X.Opens, IsAffineOpen W → Module.Finite Γ(X, W) Γ(F, W) := fun W hW =>
    finite_sections_of_isFiniteType F hW
  have key : ∀ r : Fin N, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      IsZero (cohomology (L.twist (L.twist F ((r : ℕ) : ℤ)) ((N : ℤ) * k)) c 1) ∧
        IsGloballyGenerated (L.twist (L.twist F ((r : ℕ) : ℤ)) ((N : ℤ) * k)) := by
    intro r
    have hG : ∀ W : X.Opens, IsAffineOpen W →
        Module.Finite Γ(X, W) Γ(L.twist F ((r : ℕ) : ℤ), W) := fun W hW =>
      finite_sections_twist L F hF ((r : ℕ) : ℤ) hW
    have := hfin (L.twist F ((r : ℕ) : ℤ)) hG
    exact exists_twist_vanishing_generated s₀ s₁ hcov h₀ h₁ c (L.twist F ((r : ℕ) : ℤ)) hG
  choose k₀ hk₀ using key
  refine ⟨N * Finset.univ.sup k₀, fun m hm => ?_⟩
  set r : Fin N := ⟨m % N, Nat.mod_lt m hN⟩
  set k := m / N
  have hk : k₀ r ≤ k := by
    have h1 : Finset.univ.sup k₀ ≤ k :=
      (Nat.le_div_iff_mul_le hN).mpr (by rw [mul_comm]; exact hm)
    exact (Finset.le_sup (Finset.mem_univ r)).trans h1
  have hm' : ((m : ℕ) : ℤ) = ((r : ℕ) : ℤ) + (N : ℤ) * (k : ℤ) := by
    have := Nat.mod_add_div m N
    simp only [r, k]
    exact_mod_cast this.symm
  let e : L.twist F m ≅ L.twist (L.twist F ((r : ℕ) : ℤ)) ((N : ℤ) * k) :=
    L.twistCongr F hm' ≪≫ (L.twistTwistIso F ((r : ℕ) : ℤ) ((N : ℤ) * k)).symm
  obtain ⟨hv, hg⟩ := hk₀ r k hk
  refine ⟨fun 𝒰 => ?_, hg.of_iso e.symm⟩
  have h1 : IsZero (cechCohomology (L.twist (L.twist F ((r : ℕ) : ℤ)) ((N : ℤ) * k)) 𝒰.U c 1) :=
    hv.of_iso (cohomologyIsoCech _ c 𝒰 1).symm
  have h2 := (isZero_cechCohomology_succ_iff_coeff _ 𝒰.U c (RingHom.id Γ(X, ⊤)) 0).mp h1
  exact (isZero_cechCohomology_iff_of_iso e 𝒰.U _ 1).mpr h2

end TwoSections

end

end DeJongAlterations.StableModification.CurvesField.Ample
