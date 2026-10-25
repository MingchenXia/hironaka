/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3E)
-/
import DeJongAlterations.StableModification.CurvesField.AmplePositiveBasic
import DeJongAlterations.StableModification.CurvesField.GenusNormalization

/-!
# Positive degree on an integral curve gives a section with a zero

Let `X` be an integral scheme, projective over an infinite field `K`, of dimension at most one, and
`𝓛` line-bundle data on `X` of positive degree `deg 𝓛 = χ(𝓛) - χ(𝒪_X) > 0`. Then for some `n > 0`
the bundle `𝓛^n` has a global section which does not vanish at the generic point and vanishes at
some closed point (`exists_section_of_degree_pos_of_isIntegral`): this is the hypothesis of lane
OM3B's ampleness criterion, so `𝓛` is ample in Serre's sense
(`serreAmple_of_degree_pos_of_isIntegral`).

## The argument (blueprint `sm-curves-fields-ample-positive.tex`, `lem:sm-ample-positive-integral`)

1. (`exists_presentation_of_isIntegral`) `X` has a two-chart presentation of `𝓛` (`Presentation`):
   an affine `U` inside a chart of `𝓛` containing the generic point; its complement is a finite set
   `Z` of closed points; a section `σ` of `𝓛` over an affine open `W ⊇ Z` without zero on `Z`
   (OM3B's semilocal triviality) and a function `h` on `D(σ)` separating `Z` from the other zeros of
   an equation `f` of `Z` give `V = D(h) ⊆ D(σ)` with `U ∩ V = D(f|_V)`.
2. (`Presentation.eulerCharOf_twist_eq`) Riemann–Roch: `χ(𝓛^k) = χ(𝒪) + k · deg 𝓛`; the
   hypotheses (non-zero-divisors with finite-dimensional quotients) hold on the integral curve
   (`injective_fMul_of_ne_zero`, `finiteDimensional_quotient_fMul`).
3. `h⁰(𝓛^k) ≥ χ(𝓛^k) > h⁰(𝒪)` for `k = h¹(𝒪) + 1`. A nowhere vanishing section of `𝓛^k` would
   give `Γ(𝒪) ≅ Γ(𝓛^k)`, so every global section of `𝓛^k` has a zero, and a nonzero one does not
   vanish at the generic point (`Sections.eq_zero_of_genericPoint_not_mem`).

This is the curve case of Hartshorne IV.1 / IV.3.3 ("a divisor of positive degree on a curve is
ample") in the form used for M. Temkin, *Stable modification of relative curves*, J. Algebraic
Geom. 19 (2010), proof of Thm 1.1 (`references/temkin10-stable-modification/source/
semi-stable.tex`, lines 1735--1741).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits Module
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField.Positive

noncomputable section

open Ample Ample.LineBundleData Projectivity.LineBundleData

variable {X : Scheme.{u}}

/-- The **degree** `χ(𝓛) - χ(𝒪_X)` of line-bundle data on a scheme over a ring `R`
(Euler characteristics of the Čech cohomology of a chosen finite affine cover; OM1D's degree,
`Omega.RosenlichtComponent.degree_eq_of_simplePoles`, for the module of sections of `𝓛`). -/
def degree [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (L : Projectivity.LineBundleData X) {K : Type u} [Field K] (c : K →+* Γ(X, ⊤)) : ℤ :=
  DualityScheme.eulerCharOf (L.twist (unitModule X) 1) c -
    DualityScheme.eulerCharOf (unitModule X) c

/-! ### The two-chart presentation of a line bundle on an integral curve -/

/-- **Two-chart presentations exist on integral projective curves**: for line-bundle data `𝓛` on an
integral scheme `X`, projective of dimension at most one over an infinite field, there is a
two-chart presentation of `𝓛` whose charts both contain the generic point. -/
theorem exists_presentation_of_isIntegral {K : Type u} [Field K] [Infinite K] [IsIntegral X]
    {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    (L : Projectivity.LineBundleData X) :
    ∃ P : Presentation L, genericPoint X ∈ P.U ⊓ P.V := by
  classical
  have : IsProper p := hp.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := compactSpace_of_quasiCompact p
  have : IsNoetherian X := ⟨⟩
  set η := genericPoint X
  -- the chart `U` around the generic point
  obtain ⟨i, hi⟩ := L.exists_mem_U η
  obtain ⟨U, hU, hηU, hUi⟩ := exists_isAffineOpen_mem_and_subset (x := η) (U := L.U i) hi
  let τ : L.Sections 1 U := ofLocal (unitModule X) 1 hUi (1 : Γ(X, U))
  have hτ : τ.nonvanishingLocus = U := nonvanishingLocus_ofLocal_one 1 hUi
  -- its complement `Z` is a finite set of closed points
  have hcl : ∀ x : X, x ≠ η → IsClosed ({x} : Set X) := fun x hx => by
    by_contra h
    exact hx (eq_genericPoint_of_not_isClosed hdim h)
  set Z : Set X := (U : Set X)ᶜ
  have hZcl : ∀ z ∈ Z, IsClosed ({z} : Set X) := fun z hz =>
    hcl z fun h => hz (h ▸ hηU)
  have hZ : Z.Finite := finite_of_forall_isClosed_singleton U.isOpen.isClosed_compl hZcl
  by_cases hZe : Z = ∅
  · -- `U = X`
    have hUtop : U = ⊤ := by
      apply top_unique
      intro x _
      by_contra hx
      have : x ∈ Z := hx
      rw [hZe] at this
      exact this
    have hsup : U ⊔ U = ⊤ := by rw [sup_idem, hUtop]
    have hf1 : X.basicOpen (1 : Γ(X, U)) = U ⊓ U := by rw [Scheme.basicOpen_one, inf_idem]
    exact ⟨⟨U, U, hU, hU, hsup, 1, hf1, τ, hτ, τ, hτ⟩, hηU, hηU⟩
  -- an affine open `W ⊇ Z` and a section `σ₁` over it without zero on `Z`
  obtain ⟨W, hW, hZW⟩ := exists_isAffineOpen_mem_of_isProjectiveOver hp hZ.toFinset
  obtain ⟨σ₁, hσ₁⟩ := exists_section_nonvanishing L 1 hW hZ (fun z hz => hZW z
    (hZ.mem_toFinset.mpr hz)) hZcl
  set V' : X.Opens := σ₁.nonvanishingLocus
  have hV' : IsAffineOpen V' := isAffineOpen_nonvanishingLocus_of_isAffineOpen hW σ₁
  have hZV' : Z ⊆ V' := hσ₁
  have hηV' : η ∈ V' := by
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hZe
    exact genericPoint_mem_of_nonempty ⟨z, hZV' hz⟩
  -- an equation `f'` of `Z` in `V'`
  obtain ⟨f', hf'le, hηf'⟩ := hV'.exists_basicOpen_le (V := V' ⊓ U) ⟨η, hηV', hηU⟩ hηV'
  -- the other zeros `F` of `f'`
  set F : Set X := (X.basicOpen f' : Set X)ᶜ \ Z
  have hFcl : ∀ w ∈ F, IsClosed ({w} : Set X) := fun w hw =>
    hcl w fun h => hw.1 (h ▸ hηf')
  have hF : F.Finite := (finite_of_forall_isClosed_singleton
    (X.basicOpen f').isOpen.isClosed_compl fun w hw => hcl w fun h => hw (h ▸ hηf')).subset
      Set.sdiff_subset
  obtain ⟨h, hhZ, hhF⟩ := exists_separating hV' hZ.toFinset hF.toFinset
    (fun z hz => hZV' (hZ.mem_toFinset.mp hz)) (fun z hz => hZcl z (hZ.mem_toFinset.mp hz))
    (fun w hw => hFcl w (hF.mem_toFinset.mp hw))
    (fun z hz hzF => (hF.mem_toFinset.mp hzF).2 (hZ.mem_toFinset.mp hz))
  set V : X.Opens := X.basicOpen h
  have hVV' : V ≤ V' := X.basicOpen_le h
  have hVW : V ≤ W := hVV'.trans (Sections.nonvanishingLocus_le σ₁)
  have hσ : (σ₁.restrict hVW).nonvanishingLocus = V := by
    rw [Sections.nonvanishingLocus_restrict]
    exact inf_eq_left.mpr hVV'
  set f : Γ(X, V) := X.presheaf.map (homOfLE hVV').op f'
  have hf : X.basicOpen f = U ⊓ V := by
    rw [Scheme.basicOpen_res]
    apply le_antisymm
    · exact le_inf (inf_le_right.trans (hf'le.trans inf_le_right)) inf_le_left
    · rintro x ⟨hxU, hxV⟩
      refine ⟨hxV, ?_⟩
      by_contra hx
      exact hhF x (hF.mem_toFinset.mpr ⟨hx, fun h => h hxU⟩) hxV
  have hsup : U ⊔ V = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ U
    · exact Opens.mem_sup.mpr (Or.inl hx)
    · exact Opens.mem_sup.mpr (Or.inr (hhZ x (hZ.mem_toFinset.mpr hx)))
  have hηV : η ∈ V := by
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hZe
    exact genericPoint_mem_of_nonempty ⟨z, hhZ z (hZ.mem_toFinset.mpr hz)⟩
  exact ⟨⟨U, V, hU, hV'.basicOpen h, hsup, f, hf, τ, hτ, σ₁.restrict hVW, hσ⟩, hηU, hηV⟩

/-! ### The hypotheses of Riemann–Roch on an integral curve -/

section Integral

variable {K : Type u} [Field K] {p : X ⟶ Spec (.of K)}

/-- On an integral scheme, multiplication by a nonzero function on a nonempty open is injective. -/
lemma injective_fMul_of_ne_zero [IsIntegral X] {V : X.Opens} [Nonempty V] {b : Γ(X, V)}
    (hb : b ≠ 0) : Function.Injective (fMul (unitModule X) V (structureCoeff p) b) := by
  have : IsDomain Γ(X, V) := IsIntegral.component_integral V
  intro s t hst
  have e : ∀ x : sectionsModuleCat (unitModule X) (structureCoeff p) V le_top,
      fMul (unitModule X) V (structureCoeff p) b x = (b * (id x : Γ(X, V)) : Γ(X, V)) :=
    fun _ => rfl
  rw [e, e] at hst
  have h := mul_left_cancel₀ hb hst
  exact h

/-- On an integral scheme of finite type and dimension at most one over a field, the quotient of
the functions on a nonempty affine open by a nonzero function is finite-dimensional. -/
lemma finiteDimensional_quotient_fMul [IsIntegral X] [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1) {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V]
    {b : Γ(X, V)} (hb : b ≠ 0) :
    FiniteDimensional K (sectionsModuleCat (unitModule X) (structureCoeff p) V le_top ⧸
      LinearMap.range (fMul (unitModule X) V (structureCoeff p) b)) := by
  let := (Geometry.NormalizationFinite.affineCoefficientMap p ⟨V, hV⟩).toAlgebra
  have : Algebra.FiniteType K Γ(X, V) :=
    Geometry.NormalizationFinite.affineSections_finiteType p ⟨V, hV⟩
  have : IsDomain Γ(X, V) := IsIntegral.component_integral V
  have : Ring.KrullDimLE 1 Γ(X, V) :=
    Geometry.NormalizationFinite.affineSections_krullDimLE_one ⟨V, hV⟩ hdim
  have hfin : Module.Finite K (Γ(X, V) ⧸ Ideal.span {b}) :=
    Genus.finite_quotient_span_singleton K hb
  let φ : Γ(X, V) →ₗ[K] sectionsModuleCat (unitModule X) (structureCoeff p) V le_top :=
    { toFun := fun a => a
      map_add' := fun _ _ => rfl
      map_smul' := fun r a => by
        change (sectionsRingHom (structureCoeff p) le_top r) * a = _
        rfl }
  let ψ := (LinearMap.range (fMul (unitModule X) V (structureCoeff p) b)).mkQ ∘ₗ φ
  have hker : (Ideal.span {b}).restrictScalars K ≤ LinearMap.ker ψ := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [LinearMap.mem_ker]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨(show sectionsModuleCat (unitModule X) (structureCoeff p) V le_top from y), ?_⟩
    have e : b * y = y * b := mul_comm _ _
    exact e
  let Ψ : (Γ(X, V) ⧸ Ideal.span {b}) →ₗ[K] _ ⧸ LinearMap.range
      (fMul (unitModule X) V (structureCoeff p) b) :=
    ((Ideal.span {b}).restrictScalars K).liftQ ψ hker
  have hΨ : Function.Surjective Ψ := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
    exact ⟨Submodule.Quotient.mk (show Γ(X, V) from y), rfl⟩
  exact Module.Finite.of_surjective Ψ hΨ

/-- On a nonempty open of an integral scheme, a function which is a unit on a nonempty smaller open
is nonzero. -/
lemma ne_zero_of_isUnit_res [IsIntegral X] {V W : X.Opens} (hWV : W ≤ V)
    (hW : (W : Set X).Nonempty) {b : Γ(X, V)} (hb : IsUnit (X.presheaf.map (homOfLE hWV).op b)) :
    b ≠ 0 := by
  have : Nonempty W := hW.to_subtype
  have : IsDomain Γ(X, W) := IsIntegral.component_integral W
  rintro rfl
  rw [map_zero] at hb
  exact not_isUnit_zero hb

end Integral

/-! ### Positive degree gives a section with a zero -/

/-- **A line bundle of positive degree on an integral curve has a power with a section that has a
zero** (blueprint `lem:sm-ample-positive-integral`): if `X` is integral, projective over an
infinite field `K`, of dimension at most one, and `deg 𝓛 > 0`, then some `𝓛^n`, `n > 0`, has a
global section which does not vanish at the non-closed points and vanishes at a specialization of
each of them. -/
theorem exists_section_of_degree_pos_of_isIntegral {K : Type u} [Field K] [Infinite K]
    [IsIntegral X] {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p)
    (hdim : topologicalKrullDim X ≤ 1) [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (L : Projectivity.LineBundleData X) (hdeg : 0 < degree L (structureCoeff p)) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : L.Sections n ⊤,
      (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  classical
  have : IsProper p := hp.isProper
  set c := structureCoeff p
  set η := genericPoint X
  obtain ⟨P, hηU, hηV⟩ := exists_presentation_of_isIntegral hp hdim L
  obtain ⟨a, j, ha⟩ := P.exists_numerator
  have : FiniteDimensional K (cohomology (unitModule X) c 0) :=
    finite_cohomology_of_isProjectiveOver hp (unitModule X) (fun W _ => Module.Finite.self _) 0
  have : FiniteDimensional K (cohomology (unitModule X) c 1) :=
    finite_cohomology_of_isProjectiveOver hp (unitModule X) (fun W _ => Module.Finite.self _) 1
  have hUV : ((P.U ⊓ P.V : X.Opens) : Set X).Nonempty := ⟨η, hηU, hηV⟩
  have : Nonempty P.V := ⟨⟨η, hηV⟩⟩
  have ha0 : a ≠ 0 := ne_zero_of_isUnit_res inf_le_right hUV (P.isUnit_resV_of_numerator ha)
  have hf0 : P.f ≠ 0 := ne_zero_of_isUnit_res inf_le_right hUV P.isUnit_resV_f
  have := finiteDimensional_quotient_fMul (p := p) hdim P.isAffineOpen_V ha0
  have := finiteDimensional_quotient_fMul (p := p) hdim P.isAffineOpen_V hf0
  have hRR := P.eulerCharOf_twist_eq c ha (injective_fMul_of_ne_zero ha0)
    (injective_fMul_of_ne_zero hf0)
  -- the power `k = h¹(𝒪) + 1`
  set k : ℕ := finrank K (cohomology (unitModule X) c 1) + 1
  have hk : 0 < k := Nat.succ_pos _
  have hχk := hRR k
  have hχO := DualityScheme.eulerCharOf_eq_of_pair (unitModule X) c P.sup_eq P.isAffineOpen_U
    P.isAffineOpen_V P.isAffineOpen_inf
  have hχL := DualityScheme.eulerCharOf_eq_of_pair (L.twist (unitModule X) k) c P.sup_eq
    P.isAffineOpen_U P.isAffineOpen_V P.isAffineOpen_inf
  have hdeg' : 1 ≤ DualityScheme.eulerCharOf (L.twist (unitModule X) 1) c -
      DualityScheme.eulerCharOf (unitModule X) c := hdeg
  -- `h⁰(𝓛^k) > h⁰(𝒪)`
  have hbig : finrank K (cohomology (unitModule X) c 0) <
      finrank K (cohomology (L.twist (unitModule X) k) c 0) := by
    have h1 : ((finrank K (cohomology (unitModule X) c 1) : ℕ) : ℤ) + 1 = (k : ℤ) := by
      push_cast [k]; ring
    have : (k : ℤ) * 1 ≤ (k : ℤ) * (DualityScheme.eulerCharOf (L.twist (unitModule X) 1) c -
        DualityScheme.eulerCharOf (unitModule X) c) :=
      mul_le_mul_of_nonneg_left hdeg' (Int.natCast_nonneg k)
    have h2 : (0 : ℤ) ≤ finrank K (cohomology (L.twist (unitModule X) k) c 1) :=
      Int.natCast_nonneg _
    omega
  -- global sections
  let eO := (cohomologyZeroIso (unitModule X) c).toLinearEquiv
  let eL := (cohomologyZeroIso (L.twist (unitModule X) k) c).toLinearEquiv
  rw [← eO.finrank_eq, ← eL.finrank_eq] at hbig
  -- no global section of `𝓛^k` vanishes nowhere
  have hnv : ∀ s : L.Sections k ⊤, s.nonvanishingLocus ≠ ⊤ := by
    intro s hs
    let e : sectionsModuleCat (unitModule X) c ⊤ le_top ≃ₗ[K]
        sectionsModuleCat (L.twist (unitModule X) k) c ⊤ le_top :=
      { toFun := fun a => mulSec (unitModule X) s a
        invFun := fun t => (mulSecEquiv (unitModule X) hs).symm t
        left_inv := fun a => (mulSecEquiv (unitModule X) hs).symm_apply_apply a
        right_inv := fun t => (mulSecEquiv (unitModule X) hs).apply_symm_apply t
        map_add' := fun a b => mulSec_add (unitModule X) s a b
        map_smul' := fun r a => mulSec_smul (unitModule X) s (sectionsRingHom c le_top r) a }
    rw [e.finrank_eq] at hbig
    exact lt_irrefl _ hbig
  -- a nonzero global section
  have : Nontrivial (sectionsModuleCat (L.twist (unitModule X) k) c ⊤ le_top) :=
    Module.nontrivial_of_finrank_pos (R := K) (lt_of_le_of_lt (Nat.zero_le _) hbig)
  obtain ⟨s, hs0⟩ := exists_ne (0 : sectionsModuleCat (L.twist (unitModule X) k) c ⊤ le_top)
  let s' : L.Sections k ⊤ := s
  have hs' : s' ≠ 0 := hs0
  have hηs : η ∈ s'.nonvanishingLocus := by
    by_contra h
    exact hs' (Sections.eq_zero_of_genericPoint_not_mem s' h)
  refine ⟨k, hk, s', fun x hx => ?_, fun x hx => ?_⟩
  · rw [eq_genericPoint_of_not_isClosed hdim hx]
    exact hηs
  · obtain ⟨z, hz⟩ : ∃ z, z ∉ s'.nonvanishingLocus := by
      by_contra h
      push Not at h
      exact hnv s' (top_unique fun z _ => h z)
    refine ⟨z, ?_, hz⟩
    rw [eq_genericPoint_of_not_isClosed hdim hx]
    exact (genericPoint_spec X).specializes (Set.mem_univ z)

/-- **A line bundle of positive degree on an integral projective curve over an infinite field is
ample in Serre's sense** (blueprint `thm:sm-ample-positive-integral`). -/
theorem serreAmple_of_degree_pos_of_isIntegral {K : Type u} [Field K] [Infinite K]
    [IsIntegral X] {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p)
    (hdim : topologicalKrullDim X ≤ 1) [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (L : Projectivity.LineBundleData X) (hdeg : 0 < degree L (structureCoeff p)) :
    L.SerreAmple := by
  obtain ⟨n, hn, s, hgen, hzero⟩ := exists_section_of_degree_pos_of_isIntegral hp hdim L hdeg
  exact serreAmple_of_section hp hdim hn s hgen hzero

end

end DeJongAlterations.StableModification.CurvesField.Positive
