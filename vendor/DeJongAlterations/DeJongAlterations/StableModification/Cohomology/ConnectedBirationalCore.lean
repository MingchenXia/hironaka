/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.ConnectedStep

/-!
# Zariski connectedness for birational morphisms: the two-chart core

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (T:3133): "`Z` is connected because otherwise `C` is not normal at `x` by Zariski
connectedness theorem". This file contains the algebraic core of our proof of this statement
(blueprint `sm-cohomology-connected-birational.tex`, `prop:sm-connbir-core`), which replaces the
theorem on formal functions over the non-noetherian two-dimensional base `𝒪_{C,x}` (blueprint
remark `rem:sm-conn-birational`) by a single thickening.

Let `f : X → Spec R`, `Q ⊆ R` an ideal, and suppose

* `X = W₁ ∪ W₂` with `W₁`, `W₂`, `W₁ ∩ W₂` affine (two charts);
* `R → Γ(X, 𝒪_X)` is surjective (in the application: the Stein property `π_* 𝒪_{C'} = 𝒪_C` of a
  proper birational morphism onto a normal scheme);
* `Q ^ N` kills the first Čech cohomology `Γ(W₁ ∩ W₂) / (Γ(W₁) + Γ(W₂))` of the cover (in the
  application: `H¹(X, 𝒪_X)` is a finite `R`-module supported on `V(Q)`);
* all primes containing `Q` lie in one proper ideal `m` (in the application `m` is the prime of
  the point `x` and `V(Q)` consists of generizations of `x`).

Then `f⁻¹(V(Q))` is preconnected (`isPreconnected_preimage_zeroLocus_of_twoCharts`).

## The argument

A clopen decomposition of `f⁻¹(V(Q))` is an idempotent `e` of `Γ(T, 𝒪_T)` for the thickening
`T = X ×_R Spec (R ⧸ Q ^ (N + 1))`, whose underlying set is `f⁻¹(V(Q))`
(`range_bcFst_quotient_eq`). On the affine charts `e` lifts to `aᵢ ∈ Γ(Wᵢ)`, and
`a₂ - a₁ ∈ Q ^ (N + 1) Γ(W₁ ∩ W₂)`. Writing an element of `Q ^ (N + 1) = Q · Q ^ N` as a sum of
`q r y` with `q ∈ Q`, `r ∈ Q ^ N`, the hypothesis on `Q ^ N` makes each `r y` a coboundary, so
`a₂ - a₁ = t₂ - t₁` with `tᵢ ∈ Q Γ(Wᵢ)` (`exists_coboundary_of_mem_map_pow_succ`); the
`aᵢ - tᵢ` glue to a global function `g ≡ e` modulo nilpotents on `T`
(`exists_isNilpotent_appTop_sub_of_twoCharts`). By surjectivity `g` is a constant `r ∈ R`;
`r (r - 1)` vanishes at all points of `T`, so `r` or `r - 1` lies in all their primes (all
contained in `m`), and `e` is `0` or `1` (`eq_zero_or_eq_one_of_twoCharts`). Since there are two
charts, every `1`-cochain is a cocycle: this replaces the Artin–Rees lemma of the noetherian
proof.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Cohomology.ConnectedBirational

open Connected

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The underlying set of `X ×_R Spec (R ⧸ I)` is the preimage of `V(I)`. -/
theorem range_bcFst_quotient_eq (I : Ideal R) :
    Set.range (bcFst (Ideal.Quotient.mk I) f) = f ⁻¹' PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [Scheme.Pullback.range_fst]
  congr 1
  ext P
  change P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) ↔ _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

section Coboundary

variable (W₁ W₂ : X.Opens)

/-- The restriction `Γ(W₁) → Γ(W₁ ⊓ W₂)`. -/
abbrev res₁ : Γ(X, W₁) →+* Γ(X, W₁ ⊓ W₂) := (X.presheaf.map (homOfLE inf_le_left).op).hom

/-- The restriction `Γ(W₂) → Γ(W₁ ⊓ W₂)`. -/
abbrev res₂ : Γ(X, W₂) →+* Γ(X, W₁ ⊓ W₂) := (X.presheaf.map (homOfLE inf_le_right).op).hom

theorem res₁_sectionsRingHom (r : R) :
    res₁ W₁ W₂ (sectionsRingHom (structureCoeff f) (le_top : W₁ ≤ ⊤) r) =
      sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) r := by
  simp only [res₁, sectionsRingHom, RingHom.coe_comp, Function.comp_apply]
  exact presheaf_map_map_apply _ _ _

theorem res₂_sectionsRingHom (r : R) :
    res₂ W₁ W₂ (sectionsRingHom (structureCoeff f) (le_top : W₂ ≤ ⊤) r) =
      sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) r := by
  simp only [res₂, sectionsRingHom, RingHom.coe_comp, Function.comp_apply]
  exact presheaf_map_map_apply _ _ _

/-- **Coboundaries of `Q`-multiples.** If `Q ^ N` kills the first cohomology of the two-chart
cover `W₁, W₂` (every `r z`, `r ∈ Q ^ N`, is a difference of restrictions), then every element
of `Q ^ (N + 1) Γ(W₁ ⊓ W₂)` is a difference `t₂ - t₁` of restrictions of elements
`tᵢ ∈ Q Γ(Wᵢ)`. -/
theorem exists_coboundary_of_mem_map_pow_succ (Q : Ideal R) (N : ℕ)
    (hN : ∀ r ∈ Q ^ N, ∀ z : Γ(X, W₁ ⊓ W₂), ∃ a₁ : Γ(X, W₁), ∃ a₂ : Γ(X, W₂),
      sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) r * z =
        res₂ W₁ W₂ a₂ - res₁ W₁ W₂ a₁)
    {w : Γ(X, W₁ ⊓ W₂)}
    (hw : w ∈ (Q ^ (N + 1)).map (sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤))) :
    ∃ t₁ ∈ Q.map (sectionsRingHom (structureCoeff f) (le_top : W₁ ≤ ⊤)),
      ∃ t₂ ∈ Q.map (sectionsRingHom (structureCoeff f) (le_top : W₂ ≤ ⊤)),
        w = res₂ W₁ W₂ t₂ - res₁ W₁ W₂ t₁ := by
  set φ := sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤)
  set φ₁ := sectionsRingHom (structureCoeff f) (le_top : W₁ ≤ ⊤)
  set φ₂ := sectionsRingHom (structureCoeff f) (le_top : W₂ ≤ ⊤)
  let S : Set Γ(X, W₁ ⊓ W₂) := {w | ∃ t₁ ∈ Q.map φ₁, ∃ t₂ ∈ Q.map φ₂,
    w = res₂ W₁ W₂ t₂ - res₁ W₁ W₂ t₁}
  have hS0 : (0 : Γ(X, W₁ ⊓ W₂)) ∈ S := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  have hSadd : ∀ a b, a ∈ S → b ∈ S → a + b ∈ S := by
    rintro a b ⟨t₁, ht₁, t₂, ht₂, rfl⟩ ⟨s₁, hs₁, s₂, hs₂, rfl⟩
    exact ⟨t₁ + s₁, add_mem ht₁ hs₁, t₂ + s₂, add_mem ht₂ hs₂, by simp only [map_add]; ring⟩
  -- products `φ (q r) y` with `q ∈ Q`, `r ∈ Q ^ N`
  have hprod : ∀ j ∈ Q ^ (N + 1), ∀ y : Γ(X, W₁ ⊓ W₂), φ j * y ∈ S := by
    intro j hj
    rw [pow_succ'] at hj
    refine Submodule.mul_induction_on (C := fun j => ∀ y : Γ(X, W₁ ⊓ W₂), φ j * y ∈ S) hj ?_ ?_
    · intro q hq r hr y
      obtain ⟨a₁, a₂, ha⟩ := hN r hr y
      refine ⟨φ₁ q * a₁, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hq),
        φ₂ q * a₂, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hq), ?_⟩
      rw [map_mul, map_mul, map_mul, mul_assoc, ha, res₁_sectionsRingHom, res₂_sectionsRingHom]
      ring
    · intro a b iha ihb y
      rw [map_add, add_mul]
      exact hSadd _ _ (iha y) (ihb y)
  -- elements of the extended ideal
  have key : ∀ y : Γ(X, W₁ ⊓ W₂), y * w ∈ S := by
    refine Submodule.span_induction (p := fun w _ => ∀ y : Γ(X, W₁ ⊓ W₂), y * w ∈ S)
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨j, hj, rfl⟩ y
      rw [mul_comm]
      exact hprod j hj y
    · intro y
      rw [mul_zero]
      exact hS0
    · intro a b _ _ ha hb y
      rw [mul_add]
      exact hSadd _ _ (ha y) (hb y)
    · intro a b _ hb y
      rw [smul_eq_mul, ← mul_assoc]
      exact hb _
  have := key 1
  rwa [one_mul] at this

end Coboundary

section Lift

variable (W₁ W₂ : X.Opens) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
  (hW₁₂ : IsAffineOpen (W₁ ⊓ W₂)) (hcov : W₁ ⊔ W₂ = ⊤) (Q : Ideal R) (N : ℕ)
  (hN : ∀ r ∈ Q ^ N, ∀ z : Γ(X, W₁ ⊓ W₂), ∃ a₁ : Γ(X, W₁), ∃ a₂ : Γ(X, W₂),
      sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) r * z =
        res₂ W₁ W₂ a₂ - res₁ W₁ W₂ a₁)

include hW₁ hW₂ hW₁₂ hcov hN in
/-- **Functions on the thickening lift up to nilpotents** (two-chart form of
`lem:sm-conn-lift`). Let `X` be covered by two affine opens `W₁, W₂` with affine intersection such
that `Q ^ N` kills the first Čech cohomology of this cover, and let `ι : T → X` be such that over
every affine open `W` the map `ι^* : Γ(W, 𝒪_X) → Γ(ι⁻¹W, 𝒪_T)` is surjective with kernel
`Q ^ (N + 1) Γ(W, 𝒪_X)` (for instance `T = X ×_R Spec (R ⧸ Q ^ (N + 1))`). Then every global
function `e` of `T` is congruent modulo nilpotents to `ι^* g` for a global function `g` of `X`. -/
theorem exists_isNilpotent_appTop_sub_of_twoCharts {T : Scheme.{u}} (ι : T ⟶ X)
    (hρ : ∀ W : X.Opens, IsAffineOpen W → Function.Surjective (ι.app W) ∧
      ∀ x : Γ(X, W), ι.app W x = 0 ↔
        x ∈ (Q ^ (N + 1)).map (sectionsRingHom (structureCoeff f) (le_top : W ≤ ⊤)))
    (e : Γ(T, ⊤)) : ∃ g : Γ(X, ⊤), IsNilpotent (ι.appTop g - e) := by
  classical
  obtain ⟨hs₁, hk₁⟩ := hρ W₁ hW₁
  obtain ⟨hs₂, hk₂⟩ := hρ W₂ hW₂
  obtain ⟨-, hk₁₂⟩ := hρ _ hW₁₂
  obtain ⟨a₁, ha₁⟩ := hs₁ (T.presheaf.map (homOfLE (le_top : ι ⁻¹ᵁ W₁ ≤ ⊤)).op e)
  obtain ⟨a₂, ha₂⟩ := hs₂ (T.presheaf.map (homOfLE (le_top : ι ⁻¹ᵁ W₂ ≤ ⊤)).op e)
  -- the difference of the lifts vanishes on `T`
  have hd : ι.app (W₁ ⊓ W₂) (res₂ W₁ W₂ a₂ - res₁ W₁ W₂ a₁) = 0 := by
    rw [map_sub, res₂, res₁, app_presheaf_map_apply, app_presheaf_map_apply, ha₁, ha₂,
      presheaf_map_map_apply, presheaf_map_map_apply, sub_self]
  obtain ⟨t₁, ht₁, t₂, ht₂, hdt⟩ :=
    exists_coboundary_of_mem_map_pow_succ f W₁ W₂ Q N hN ((hk₁₂ _).mp hd)
  -- glue the corrected lifts
  have hcompat : res₁ W₁ W₂ (a₁ - t₁) = res₂ W₁ W₂ (a₂ - t₂) := by
    rw [map_sub, map_sub]
    linear_combination -hdt
  let g₀ : Γ(X, W₁ ⊔ W₂) :=
    (X.sheaf.objSupIsoProdEqLocus W₁ W₂).inv ⟨(a₁ - t₁, a₂ - t₂), hcompat⟩
  have hg₁ : X.presheaf.map (homOfLE le_sup_left).op g₀ = a₁ - t₁ :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf W₁ W₂ _
  have hg₂ : X.presheaf.map (homOfLE le_sup_right).op g₀ = a₂ - t₂ :=
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf W₁ W₂ _
  let g : Γ(X, ⊤) := X.presheaf.map (homOfLE hcov.ge).op g₀
  have hgW₁ : X.presheaf.map (homOfLE (le_top : W₁ ≤ ⊤)).op g = a₁ - t₁ := by
    rw [presheaf_map_map_apply]
    exact hg₁
  have hgW₂ : X.presheaf.map (homOfLE (le_top : W₂ ≤ ⊤)).op g = a₂ - t₂ := by
    rw [presheaf_map_map_apply]
    exact hg₂
  refine ⟨g, N + 1, ?_⟩
  -- the nilpotency is checked on the two charts
  have hloc : ∀ (W : X.Opens) (a t : Γ(X, W)), t ∈ Q.map (sectionsRingHom (structureCoeff f)
      (le_top : W ≤ ⊤)) → ι.app W a = T.presheaf.map (homOfLE le_top).op e →
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op g = a - t →
      (∀ x : Γ(X, W), ι.app W x = 0 ↔
        x ∈ (Q ^ (N + 1)).map (sectionsRingHom (structureCoeff f) (le_top : W ≤ ⊤))) →
      T.presheaf.map (homOfLE (le_top : ι ⁻¹ᵁ W ≤ ⊤)).op ((ι.appTop g - e) ^ (N + 1)) = 0 := by
    intro W a t ht ha hg hk
    have h1 : T.presheaf.map (homOfLE (le_top : ι ⁻¹ᵁ W ≤ ⊤)).op (ι.appTop g) =
        ι.app W (a - t) := by
      rw [← hg]
      exact (app_presheaf_map_apply ι le_top g).symm
    have htn : ι.app W (t ^ (N + 1)) = 0 := by
      rw [hk, Ideal.map_pow]
      exact Ideal.pow_mem_pow ht _
    rw [map_pow, map_sub, h1, ← ha, map_sub, sub_sub_cancel_left, neg_pow, ← map_pow, htn,
      mul_zero]
  apply TopCat.Sheaf.eq_of_locally_eq₂ T.sheaf (homOfLE (le_top : ι ⁻¹ᵁ W₁ ≤ ⊤))
    (homOfLE (le_top : ι ⁻¹ᵁ W₂ ≤ ⊤))
  · intro x _
    have : ι x ∈ W₁ ⊔ W₂ := by rw [hcov]; trivial
    rcases Opens.mem_sup.mp this with h | h
    · exact Opens.mem_sup.mpr (Or.inl h)
    · exact Opens.mem_sup.mpr (Or.inr h)
  · rw [map_zero]
    exact hloc W₁ a₁ t₁ ht₁ ha₁ hgW₁ hk₁
  · rw [map_zero]
    exact hloc W₂ a₂ t₂ ht₂ ha₂ hgW₂ hk₂

end Lift

section Points

/-- A constant of `R` whose image in `Γ(T, 𝒪_T)` is nilpotent lies in the prime of every point of
`T`, for `h : T → Spec R`. -/
theorem mem_asIdeal_of_isNilpotent_structureCoeff {T : Scheme.{u}}
    (h : T ⟶ Spec (CommRingCat.of R)) {a : R} (ha : IsNilpotent (structureCoeff h a)) (z : T) :
    a ∈ (h z).asIdeal := by
  have hb : T.basicOpen (structureCoeff h a) = ⊥ :=
    T.toLocallyRingedSpace.basicOpen_eq_bot_of_isNilpotent ⊤ _ ha
  have hpre : T.basicOpen (structureCoeff h a) =
      h ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
    rw [Scheme.preimage_basicOpen]
    rfl
  have hz : z ∉ h ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
    rw [← hpre, hb]
    exact fun h => h
  rw [Scheme.Hom.mem_preimage, basicOpen_eq_of_affine] at hz
  by_contra ha'
  exact hz ha'

/-- Conversely, on a quasi-compact `T`, a constant lying in the primes of all points of `T` is
nilpotent in `Γ(T, 𝒪_T)`. -/
theorem isNilpotent_structureCoeff_of_forall_mem {T : Scheme.{u}} [CompactSpace T]
    (h : T ⟶ Spec (CommRingCat.of R)) {a : R} (ha : ∀ z : T, a ∈ (h z).asIdeal) :
    IsNilpotent (structureCoeff h a) := by
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot]
  have hpre : T.basicOpen (structureCoeff h a) =
      h ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
    rw [Scheme.preimage_basicOpen]
    rfl
  rw [hpre]
  refine eq_bot_iff.mpr fun z hz => ?_
  rw [Scheme.Hom.mem_preimage, basicOpen_eq_of_affine] at hz
  exact (hz (ha z)).elim

end Points

section Idempotents

variable (W₁ W₂ : X.Opens) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
  (hW₁₂ : IsAffineOpen (W₁ ⊓ W₂)) (hcov : W₁ ⊔ W₂ = ⊤) (Q : Ideal R) (N : ℕ)
  (hN : ∀ r ∈ Q ^ N, ∀ z : Γ(X, W₁ ⊓ W₂), ∃ a₁ : Γ(X, W₁), ∃ a₂ : Γ(X, W₂),
      sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) r * z =
        res₂ W₁ W₂ a₂ - res₁ W₁ W₂ a₁)

include hW₁ hW₂ hW₁₂ hcov hN in
/-- **Idempotents of the thickening are trivial** (blueprint `prop:sm-connbir-core`). In the
situation of `exists_isNilpotent_appTop_sub_of_twoCharts`, suppose moreover that
`R → Γ(X, 𝒪_X)` is surjective, that `T` is quasi-compact and lies over `V(Q)`, and that every
prime containing `Q` lies in a proper ideal `m`. Then `0` and `1` are the only idempotents of
`Γ(T, 𝒪_T)`. -/
theorem eq_zero_or_eq_one_of_twoCharts {T : Scheme.{u}} [CompactSpace T] (ι : T ⟶ X)
    (hρ : ∀ W : X.Opens, IsAffineOpen W → Function.Surjective (ι.app W) ∧
      ∀ x : Γ(X, W), ι.app W x = 0 ↔
        x ∈ (Q ^ (N + 1)).map (sectionsRingHom (structureCoeff f) (le_top : W ≤ ⊤)))
    (hT : ∀ z : T, Q ≤ (f (ι z)).asIdeal) (hS : Function.Surjective (structureCoeff f))
    (m : Ideal R) (hm : m ≠ ⊤) (hQm : ∀ P : Ideal R, P.IsPrime → Q ≤ P → P ≤ m)
    (e : Γ(T, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  classical
  obtain ⟨g, hg⟩ :=
    exists_isNilpotent_appTop_sub_of_twoCharts f W₁ W₂ hW₁ hW₂ hW₁₂ hcov Q N hN ι hρ e
  obtain ⟨r, rfl⟩ := hS g
  let c : R →+* Γ(T, ⊤) := (ι.appTop).hom.comp (structureCoeff f)
  have hc : ∀ a, c a = structureCoeff (ι ≫ f) a := by
    intro a
    simp only [c, structureCoeff, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply]
  have hmem : ∀ a, IsNilpotent (c a) → ∀ z : T, a ∈ (f (ι z)).asIdeal := fun a ha z => by
    rw [hc] at ha
    exact mem_asIdeal_of_isNilpotent_structureCoeff (ι ≫ f) ha z
  have hnil : ∀ a, (∀ z : T, a ∈ (f (ι z)).asIdeal) → IsNilpotent (c a) := fun a ha => by
    rw [hc]
    exact isNilpotent_structureCoeff_of_forall_mem (ι ≫ f) ha
  have hle : ∀ z : T, (f (ι z)).asIdeal ≤ m := fun z =>
    hQm _ (f (ι z)).isPrime (hT z)
  -- `r (r - 1)` vanishes at every point of `T`
  set n := c r - e with hn
  have hn' : IsNilpotent n := hg
  have hsq : IsNilpotent (c (r * (r - 1))) := by
    have : c (r * (r - 1)) = n * (2 * e + n - 1) := by
      have he' : e * e = e := he.eq
      rw [map_mul, map_sub, map_one]
      have hcr : c r = e + n := by rw [hn]; ring
      rw [hcr]
      linear_combination he'
    rw [this]
    exact (Commute.all _ _).isNilpotent_mul_right hn'
  have hor : ∀ z : T, r ∈ (f (ι z)).asIdeal ∨ r - 1 ∈ (f (ι z)).asIdeal := fun z =>
    (f (ι z)).isPrime.mem_or_mem (hmem _ hsq z)
  by_cases hrm : r ∈ m
  · left
    have hall : ∀ z : T, r ∈ (f (ι z)).asIdeal := by
      intro z
      rcases hor z with h | h
      · exact h
      · exfalso
        apply hm
        rw [Ideal.eq_top_iff_one]
        have : r - (r - 1) ∈ m := m.sub_mem hrm (hle z h)
        simpa using this
    have hcr := hnil r hall
    have he0 : IsNilpotent e := by
      have : e = c r - n := by rw [hn]; ring
      rw [this]
      exact (Commute.all _ _).isNilpotent_sub hcr hn'
    obtain ⟨k, hk⟩ := he0
    rw [← he.pow_succ_eq k, pow_succ, hk, zero_mul]
  · right
    have hall : ∀ z : T, r - 1 ∈ (f (ι z)).asIdeal := by
      intro z
      rcases hor z with h | h
      · exact absurd (hle z h) hrm
      · exact h
    have hcr := hnil (r - 1) hall
    have he1 : IsNilpotent (1 - e) := by
      have : 1 - e = n - c (r - 1) := by rw [hn, map_sub, map_one]; ring
      rw [this]
      exact (Commute.all _ _).isNilpotent_sub hn' hcr
    obtain ⟨k, hk⟩ := he1
    have : 1 - e = 0 := by rw [← he.one_sub.pow_succ_eq k, pow_succ, hk, zero_mul]
    exact (sub_eq_zero.mp this).symm

include hW₁ hW₂ hW₁₂ hcov hN in
/-- **Preconnectedness of the fibre over `V(Q)`** (blueprint `prop:sm-connbir-core`). Let
`f : X → Spec R` with `R → Γ(X, 𝒪_X)` surjective, `X` covered by two affine opens `W₁, W₂` with
affine intersection, and `Q ⊆ R` an ideal such that `Q ^ N` kills the first Čech cohomology of
the cover and all primes containing `Q` lie in a proper ideal `m`. Then `f⁻¹(V(Q))` is
preconnected. -/
theorem isPreconnected_preimage_zeroLocus_of_twoCharts
    (hS : Function.Surjective (structureCoeff f)) (m : Ideal R) (hm : m ≠ ⊤)
    (hQm : ∀ P : Ideal R, P.IsPrime → Q ≤ P → P ≤ m) :
    _root_.IsPreconnected (f ⁻¹' PrimeSpectrum.zeroLocus (Q : Set R)) := by
  classical
  let φ := Ideal.Quotient.mk (Q ^ (N + 1))
  let T : Scheme.{u} := pullback f (Spec.map (CommRingCat.ofHom φ))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : CompactSpace X := by
    refine ⟨?_⟩
    have h : (Set.univ : Set X) = (W₁ : Set X) ∪ W₂ := by
      rw [← Opens.coe_sup, hcov]
      rfl
    rw [h]
    exact hW₁.isCompact.union hW₂.isCompact
  have : CompactSpace T := (bcFst φ f).isClosedEmbedding.compactSpace
  have hrange := range_bcFst_quotient_eq f (Q ^ (N + 1))
  rw [PrimeSpectrum.zeroLocus_pow _ (Nat.succ_ne_zero N)] at hrange
  have hT : ∀ z : T, Q ≤ (f (bcFst φ f z)).asIdeal := by
    intro z
    have : bcFst φ f z ∈ Set.range (bcFst φ f) := ⟨z, rfl⟩
    rw [hrange] at this
    exact this
  have hidem := eq_zero_or_eq_one_of_twoCharts f W₁ W₂ hW₁ hW₂ hW₁₂ hcov Q N hN (bcFst φ f)
    (fun W hW => ⟨(bcFst_app_surjective_and_ker f _ hW).1,
      (bcFst_app_surjective_and_ker f _ hW).2⟩) hT hS m hm hQm
  have hpre : _root_.IsPreconnected (Set.univ : Set T) := by
    by_cases hTn : Nonempty T
    · have : ConnectedSpace T :=
        (DeJongAlterations.Geometry.ProperSteinGlobalIdempotents.connectedSpace_iff_idempotents
          T).mpr ⟨hTn, hidem⟩
      exact isPreconnected_univ
    · rw [not_nonempty_iff] at hTn
      rw [Set.univ_eq_empty_iff.mpr hTn]
      exact isPreconnected_empty
  rw [← hrange, ← Set.image_univ]
  exact hpre.image _ (bcFst φ f).continuous.continuousOn

end Idempotents

end

end DeJongAlterations.StableModification.Cohomology.ConnectedBirational
