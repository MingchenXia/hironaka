/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.ConnectedAlgebra
import DeJongAlterations.StableModification.Cohomology.Valuation
import DeJongAlterations.StableModification.Cohomology.SteinFinite
import DeJongAlterations.Geometry.ProperSteinGlobalIdempotents

/-!
# Connectedness of the closed fibre over a valuation ring of height one

Let `W` be a valuation ring whose only primes are `0` and the maximal ideal `𝔪`, `c ∈ 𝔪` nonzero,
and `f : X → Spec W` projective and flat. This file proves that the closed fibre `f⁻¹(𝔪)` is
connected provided every global function `g` of `X` is a constant up to nilpotents on the generic
fibre, in the form `b g ^ m - a` nilpotent for some `m ≥ 1`, `a, b ∈ W`, `b ≠ 0`
(`isPreconnected_closedFibre_of_heightOne`, blueprint `prop:sm-conn-height-one`). This is the
inductive step of Zariski's connectedness theorem over a valuation ring of finite height
(`Connected.lean`), which replaces the appeal to Zariski's connectedness theorem "over a noetherian
base" in Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Lemma 4.4.2 (`semi-stable.tex` lines 3125–3133).

## The argument

The closed fibre is the underlying space of each thickening `T = X ×_W Spec (W ⧸ c ^ n)`, since
`c` generates `𝔪` up to radical. A clopen decomposition of the closed fibre is an idempotent `e`
of `Γ(T, 𝒪)`. On the affine charts `U_i` of `X` (projective coordinates) the sections of `T` are
`Γ(U_i, 𝒪_X) ⧸ c ^ n` (`bcFst_app_surjective_and_ker`, from `isPushout_baseChange_sections`), so
`e` lifts to a `0`-cochain `a` whose coboundary is divisible by `c ^ n`: `d a = c ^ n b` with `b`
a cocycle (the Čech terms have no `c`-torsion since `X` is flat). The first Čech cohomology of
`X` is a finitely presented `W`-module (`finitePresentation_cechCohomology_valuation`), so its
`c`-power torsion is killed by a fixed `c ^ N`
(`exists_d_eq_pow_smul_of_finitePresentation_homology`); for `n = N + 1` we get `c ^ N b = d t`
and `a - c t` is a cocycle, i.e. a global function `g` of `X` with `g ≡ e` modulo nilpotents on
`T` (`exists_isNilpotent_appTop_sub`; a formal function statement for the single thickening
`T`). The hypothesis on `g` and the torsion-freeness
of `Γ(X, 𝒪)` give `g ^ m ≡ λ` modulo nilpotents for some `λ ∈ W` (or `Γ(T, 𝒪) = 0`); since the
constants of `𝔪` are nilpotent on `T` and `W` is local, `e ≡ λ ≡ 0` or `1`, so `e` is trivial.

No noetherian approximation is used: the finiteness input is the coherence of the valuation ring
`W` (lane COH3A).

## Main results

* `bcFst_app_surjective_and_ker`: sections of `X ×_W Spec (W ⧸ I)` over the preimage of an affine
  open `U` are `Γ(U, 𝒪_X) ⧸ I`.
* `range_bcFst_quotient`: the thickening has the closed fibre as underlying set.
* `exists_isNilpotent_appTop_sub` (blueprint `lem:sm-conn-lift`): global functions of the
  thickening lift to `X` up to nilpotents.
* `eq_zero_or_eq_one_of_isIdempotentElem`: hence the thickening has no nontrivial idempotents.
* `isPreconnected_closedFibre_of_heightOne` (blueprint `prop:sm-conn-height-one`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.Geometry.ProperSteinProjectiveCech
open scoped TensorProduct

namespace DeJongAlterations.StableModification.Cohomology.Connected

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Pushout

/-- If `B` is the pushout of `A` along `R → R ⧸ I`, then `A → B` is surjective with kernel
`I A`. -/
theorem algebraMap_surjective_and_ker_of_isPushout {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] (I : Ideal R) [Algebra R A] [Algebra (R ⧸ I) B] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R (R ⧸ I) B] [h : Algebra.IsPushout R (R ⧸ I) A B] :
    Function.Surjective (algebraMap A B) ∧
      ∀ x : A, algebraMap A B x = 0 ↔ x ∈ I.map (algebraMap R A) := by
  have h' : Algebra.IsPushout R A (R ⧸ I) B := h.symm
  let e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[A] B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).trans
      (Algebra.IsPushout.equiv R A (R ⧸ I) B)
  have he : ∀ x : A, e (Ideal.Quotient.mk _ x) = algebraMap A B x := by
    intro x
    simp [e, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, Algebra.IsPushout.equiv_tmul]
  refine ⟨fun y => ?_, fun x => ?_⟩
  · obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, (he x).symm⟩
  · rw [← he, map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]

end Pushout

section Thickening

variable {W : Type u} [CommRing W] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of W))

/-- **Sections of a quotient base change over affine opens** (blueprint `lem:sm-conn-thickening`):
for `I ⊆ W` and an affine open `U ⊆ X`, the map `Γ(U, 𝒪_X) → Γ(q⁻¹U, 𝒪)` to the base change
`X ×_W Spec (W ⧸ I)` is surjective with kernel `I Γ(U, 𝒪_X)`. -/
theorem bcFst_app_surjective_and_ker (I : Ideal W) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((bcFst (Ideal.Quotient.mk I) f).app U) ∧
    ∀ x : Γ(X, U), (bcFst (Ideal.Quotient.mk I) f).app U x = 0 ↔
      x ∈ I.map (sectionsRingHom (structureCoeff f) (le_top : U ≤ ⊤)) := by
  let φ := Ideal.Quotient.mk I
  let T := pullback f (Spec.map (CommRingCat.ofHom φ))
  let _ : Algebra W Γ(X, U) := (sectionsRingHom (structureCoeff f) (le_top : U ≤ ⊤)).toAlgebra
  let _ : Algebra (W ⧸ I) Γ(T, bcFst φ f ⁻¹ᵁ U) :=
    (sectionsRingHom (structureCoeff (bcSnd φ f)) (le_top : bcFst φ f ⁻¹ᵁ U ≤ ⊤)).toAlgebra
  let _ : Algebra Γ(X, U) Γ(T, bcFst φ f ⁻¹ᵁ U) :=
    ((bcFst φ f).appLE U (bcFst φ f ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  let _ : Algebra W Γ(T, bcFst φ f ⁻¹ᵁ U) :=
    ((algebraMap Γ(X, U) Γ(T, bcFst φ f ⁻¹ᵁ U)).comp (algebraMap W Γ(X, U))).toAlgebra
  have : IsScalarTower W Γ(X, U) Γ(T, bcFst φ f ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower W (W ⧸ I) Γ(T, bcFst φ f ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change (bcFst φ f).appLE U _ le_rfl _ = _
      rw [Scheme.Hom.appLE_eq_app]
      exact bcFst_app_sectionsRingHom φ f U a
  have : Algebra.IsPushout W (W ⧸ I) Γ(X, U) Γ(T, bcFst φ f ⁻¹ᵁ U) := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    exact isPushout_baseChange_sections φ f hU
  obtain ⟨h1, h2⟩ := algebraMap_surjective_and_ker_of_isPushout (A := Γ(X, U))
    (B := Γ(T, bcFst φ f ⁻¹ᵁ U)) I
  have hmap : ∀ x, (bcFst φ f).app U x = algebraMap Γ(X, U) Γ(T, bcFst φ f ⁻¹ᵁ U) x := by
    intro x
    change _ = (bcFst φ f).appLE U _ le_rfl x
    rw [Scheme.Hom.appLE_eq_app]
  refine ⟨fun y => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := h1 y
    exact ⟨x, (hmap x).trans hx⟩
  · rw [hmap, h2]
    rfl

/-- Elements of `(c) Γ(U, 𝒪_X)` are multiples of the constant `c`. -/
theorem exists_eq_mul_of_mem_map_span {U : X.Opens} {c : W} {x : Γ(X, U)}
    (hx : x ∈ (Ideal.span {c}).map (sectionsRingHom (structureCoeff f) (le_top : U ≤ ⊤))) :
    ∃ y : Γ(X, U), x = sectionsRingHom (structureCoeff f) (le_top : U ≤ ⊤) c * y := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, by rw [← hy, mul_comm]⟩

/-- The underlying set of `X ×_W Spec (W ⧸ I)` is the closed fibre, if the closed point is the only
prime containing `I`. -/
theorem range_bcFst_quotient [IsLocalRing W] {I : Ideal W}
    (hI : ∀ P : PrimeSpectrum W, I ≤ P.asIdeal → P = IsLocalRing.closedPoint W)
    (hI' : I ≤ IsLocalRing.maximalIdeal W) :
    Set.range (bcFst (Ideal.Quotient.mk I) f) = f ⁻¹' {IsLocalRing.closedPoint W} := by
  rw [Scheme.Pullback.range_fst]
  congr 1
  ext P
  change P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) ↔ _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    PrimeSpectrum.mem_zeroLocus, Set.mem_singleton_iff]
  constructor
  · exact hI P
  · rintro rfl
    exact hI'

/-- Constants with a power in `I` are nilpotent on `X ×_W Spec (W ⧸ I)`. -/
theorem isNilpotent_bcFst_appTop_structureCoeff {I : Ideal W} {w : W} (hw : ∃ n : ℕ, w ^ n ∈ I) :
    IsNilpotent ((bcFst (Ideal.Quotient.mk I) f).appTop (structureCoeff f w)) := by
  rw [structureCoeff_bc]
  obtain ⟨n, hn⟩ := hw
  refine IsNilpotent.map ⟨n, ?_⟩ _
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact hn

end Thickening

section Restriction

/-- Naturality of `φ.app` with respect to restriction, elementwise. -/
theorem app_presheaf_map_apply {X Y : Scheme.{u}} (φ : X ⟶ Y) {U U' : Y.Opens} (h : U' ≤ U)
    (x : Γ(Y, U)) :
    φ.app U' (Y.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE (fun _ hy => h hy : φ ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ U)).op (φ.app U x) := by
  have := congrArg (fun g => g.hom x) (φ.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

/-- Composition of restrictions, elementwise. -/
theorem presheaf_map_map_apply {X : Scheme.{u}} {U₁ U₂ U₃ : X.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂)
    (x : Γ(X, U₁)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op x) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction along `U ≤ U` is the identity. -/
theorem presheaf_map_self_apply {X : Scheme.{u}} {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op x = x := by
  change X.presheaf.map (𝟙 (op U)) x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

end Restriction

section Flat

variable {W : Type u} [CommRing W] [IsDomain W] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of W)) [Flat f]

/-- The structure sheaf of a scheme, as a module over itself. -/
abbrev unitModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- **Flat schemes over a domain have no torsion**, in terms of the structure coefficients. -/
theorem eq_zero_of_sectionsRingHom_mul_eq_zero {v : W} (hv : v ≠ 0) {U : X.Opens} (s : Γ(X, U))
    (hs : sectionsRingHom (structureCoeff f) (le_top : U ≤ ⊤) v * s = 0) : s = 0 := by
  have ha : (Scheme.ΓSpecIso (CommRingCat.of W)).inv v ≠ 0 := by
    intro h
    apply hv
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom h
    rwa [← ConcreteCategory.comp_apply, Iso.inv_hom_id, map_zero] at this
  exact eq_zero_of_mul_eq_zero_of_flat f ha s hs

/-- The same for global sections. -/
theorem eq_zero_of_structureCoeff_mul_eq_zero {v : W} (hv : v ≠ 0) (s : Γ(X, ⊤))
    (hs : structureCoeff f v * s = 0) : s = 0 := by
  apply eq_zero_of_sectionsRingHom_mul_eq_zero f hv s
  change X.presheaf.map (homOfLE le_top).op (structureCoeff f v) * s = 0
  rw [presheaf_map_self_apply]
  exact hs

/-- Nilpotency can be cancelled against a nonzero constant. -/
theorem isNilpotent_of_isNilpotent_structureCoeff_mul {v : W} (hv : v ≠ 0) {s : Γ(X, ⊤)}
    (hs : IsNilpotent (structureCoeff f v * s)) : IsNilpotent s := by
  obtain ⟨k, hk⟩ := hs
  refine ⟨k, eq_zero_of_structureCoeff_mul_eq_zero f (pow_ne_zero k hv) _ ?_⟩
  rw [map_pow, ← mul_pow]
  exact hk

variable [ValuationRing W]

/-- The sections of a flat scheme over a valuation ring are flat. -/
theorem flat_sectionsModuleCat (U : X.Opens) :
    Module.Flat W (sectionsModuleCat (unitModule X) (structureCoeff f) U le_top) := by
  rw [ValuationRing.flat_iff_forall_smul_eq_zero]
  intro v hv s hs
  exact eq_zero_of_sectionsRingHom_mul_eq_zero f hv (show Γ(X, U) from s) hs

end Flat


section Lift

variable {W : Type u} [CommRing W] [IsDomain W] [ValuationRing W] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of W)) [Flat f]

/-- **Global functions of a thickening lift up to nilpotents** (blueprint `lem:sm-conn-lift`).
Let `X` be flat over the valuation ring `W` with projective coordinates `D`, and `c ≠ 0` in `W`
such that a cocycle `b` of the Čech complex with `c ^ k b` a coboundary has `c ^ N b` a
coboundary. Let `ι : T → X` be a morphism such that on every intersection `U_S` of charts,
`ι^* : Γ(U_S, 𝒪_X) → Γ(ι⁻¹ U_S, 𝒪_T)` is surjective with kernel inside `c ^ (N + 1) Γ(U_S, 𝒪_X)`,
and `c ^ (N + 1)` vanishes on `T` (for instance `T = X ×_W Spec (W ⧸ c ^ (N + 1))`). Then every
global function `e` of `T` is congruent modulo nilpotents to `ι^* g` for a global function `g` of
`X`. -/
theorem exists_isNilpotent_appTop_sub (D : ProjectiveCoordinates X W (structureCoeff f))
    {c : W} (hc0 : c ≠ 0) {N : ℕ}
    (hN : ∀ b : (cechComplex (unitModule X) D.U (structureCoeff f)).X 1,
      ((cechComplex (unitModule X) D.U (structureCoeff f)).d 1 2).hom b = 0 → ∀ (k : ℕ)
      (a : (cechComplex (unitModule X) D.U (structureCoeff f)).X 0),
      ((cechComplex (unitModule X) D.U (structureCoeff f)).d 0 1).hom a = c ^ k • b →
      ∃ t : (cechComplex (unitModule X) D.U (structureCoeff f)).X 0,
        ((cechComplex (unitModule X) D.U (structureCoeff f)).d 0 1).hom t = c ^ N • b)
    {T : Scheme.{u}} (ι : T ⟶ X)
    (hρ : ∀ S : Finset D.ι, S.Nonempty → Function.Surjective (ι.app (S.inf D.U)) ∧
      ∀ x : Γ(X, S.inf D.U), ι.app (S.inf D.U) x = 0 →
        ∃ y : Γ(X, S.inf D.U),
          x = sectionsRingHom (structureCoeff f) (le_top : S.inf D.U ≤ ⊤) (c ^ (N + 1)) * y)
    (hcn : ι.appTop (structureCoeff f c) ^ (N + 1) = 0) (e : Γ(T, ⊤)) :
    ∃ g : Γ(X, ⊤), IsNilpotent (ι.appTop g - e) := by
  classical
  let O := unitModule X
  let Dg := cechDiagram O D.U (structureCoeff f)
  have hflatT : ∀ S : Finset D.ι, S.Nonempty → Module.Flat W (Dg.obj S) := fun S _ =>
    flat_sectionsModuleCat f (S.inf D.U)
  let eres : ∀ S : Finset D.ι, Γ(T, ι ⁻¹ᵁ (S.inf D.U)) := fun S =>
    T.presheaf.map (homOfLE le_top).op e
  have heres : ∀ (S S' : Finset D.ι) (h : S'.inf D.U ≤ S.inf D.U),
      T.presheaf.map (homOfLE (fun _ hy => h hy : ι ⁻¹ᵁ (S'.inf D.U) ≤ ι ⁻¹ᵁ (S.inf D.U))).op
        (eres S) = eres S' := fun S S' h => presheaf_map_map_apply _ _ e
  have hsurj1 : ∀ S : Finset D.ι, S.card = 1 →
      ∃ x : Γ(X, S.inf D.U), ι.app (S.inf D.U) x = eres S := fun S hS =>
    (hρ S (Finset.card_pos.mp (by omega))).1 (eres S)
  -- the `0`-cochain lifting `e`
  let a : subsetCechCardPiece Dg 1 :=
    ⟨fun S => if h : S.card = 1 then
      (show Dg.obj S from (Classical.choose (hsurj1 S h) : Γ(X, S.inf D.U))) else 0,
      fun S hS => dif_neg hS⟩
  have ha : ∀ (S : Finset D.ι) (h : S.card = 1),
      ι.app (S.inf D.U) (show Γ(X, S.inf D.U) from a.val S) = eres S := by
    intro S h
    change ι.app (S.inf D.U) (show Γ(X, S.inf D.U) from
      (if h : S.card = 1 then (show Dg.obj S from
        (Classical.choose (hsurj1 S h) : Γ(X, S.inf D.U))) else 0)) = eres S
    rw [dif_pos h]
    exact Classical.choose_spec (hsurj1 S h)
  -- its coboundary vanishes on `T`
  have hpair : ∀ i j : D.ι, i < j →
      ι.app (({i, j} : Finset D.ι).inf D.U)
        (show Γ(X, ({i, j} : Finset D.ι).inf D.U) from subsetCechDifferential Dg a.val {i, j}) =
        0 := by
    intro i j hij
    rw [subsetCechDifferential_pair' Dg a.val hij]
    change ι.app _ (X.presheaf.map _ (show Γ(X, ({j} : Finset D.ι).inf D.U) from a.val {j}) -
      X.presheaf.map _ (show Γ(X, ({i} : Finset D.ι).inf D.U) from a.val {i})) = 0
    rw [map_sub, app_presheaf_map_apply, app_presheaf_map_apply, ha _ (Finset.card_singleton j),
      ha _ (Finset.card_singleton i), heres, heres, sub_self]
  have hd2 : ∀ S : Finset D.ι, S.card = 2 →
      ∃ y : Γ(X, S.inf D.U), (show Γ(X, S.inf D.U) from subsetCechDifferential Dg a.val S) =
        sectionsRingHom (structureCoeff f) (le_top : S.inf D.U ≤ ⊤) (c ^ (N + 1)) * y := by
    intro S hS
    have hS' : S.Nonempty := Finset.card_pos.mp (by omega)
    apply (hρ S hS').2
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hS
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpair i j h
    · have := hpair j i h
      rwa [Finset.pair_comm] at this
  -- the `1`-cocycle `b` with `d a = c ^ (N + 1) b`
  let b : subsetCechCardPiece Dg 2 :=
    ⟨fun S => if h : S.card = 2 then
      (show Dg.obj S from (Classical.choose (hd2 S h) : Γ(X, S.inf D.U))) else 0,
      fun S hS => dif_neg hS⟩
  have hcb : c ^ (N + 1) • b = subsetCechCardDifferential Dg 1 a := by
    apply Subtype.ext
    funext S
    by_cases hS : S.card = 2
    · change sectionsRingHom (structureCoeff f) (le_top : S.inf D.U ≤ ⊤) (c ^ (N + 1)) *
          (show Γ(X, S.inf D.U) from (if h : S.card = 2 then (show Dg.obj S from
            (Classical.choose (hd2 S h) : Γ(X, S.inf D.U))) else 0)) =
          (show Γ(X, S.inf D.U) from subsetCechDifferential Dg a.val S)
      rw [dif_pos hS]
      exact (Classical.choose_spec (hd2 S hS)).symm
    · change c ^ (N + 1) • b.val S = subsetCechDifferential Dg a.val S
      rw [b.property S hS, smul_zero]
      exact ((subsetCechCardDifferential Dg 1 a).property S hS).symm
  have hdd : ∀ x : subsetCechCardPiece Dg 1,
      subsetCechCardDifferential Dg 2 (subsetCechCardDifferential Dg 1 x) = 0 := by
    intro x
    have h := congrArg (fun φ => φ.hom x) ((subsetCechComplex Dg).d_comp_d 0 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    rw [subsetCechComplex_d Dg 0, subsetCechComplex_d Dg 1] at h
    exact h
  have hflat2 : Module.Flat W (subsetCechCardPiece Dg 3) := D.flat_cechComplex_X O hflatT 2
  have hdb : subsetCechCardDifferential Dg 2 b = 0 := by
    have h : c ^ (N + 1) • subsetCechCardDifferential Dg 2 b = 0 := by
      rw [← map_smul, hcb, hdd]
    exact (ValuationRing.flat_iff_forall_smul_eq_zero.mp hflat2) _ (pow_ne_zero _ hc0) _ h
  -- the cohomological input
  have hdC : ∀ (p : ℕ) (x : subsetCechCardPiece Dg (p + 1)),
      ((cechComplex O D.U (structureCoeff f)).d p (p + 1)).hom x =
        subsetCechCardDifferential Dg (p + 1) x := by
    intro p x
    change ((subsetCechComplex Dg).d p (p + 1)).hom x = _
    rw [subsetCechComplex_d]
    rfl
  obtain ⟨t, ht⟩ := hN (show (cechComplex O D.U (structureCoeff f)).X 1 from b)
    (by rw [hdC 1]; exact hdb) (N + 1) (show (cechComplex O D.U (structureCoeff f)).X 0 from a)
    (by rw [hdC 0]; exact hcb.symm)
  rw [hdC 0] at ht
  -- the corrected cochain is a cocycle, i.e. a global function
  let t' : subsetCechCardPiece Dg 1 := t
  let a' : subsetCechCardPiece Dg 1 := a - c • t'
  have ha' : a' ∈ LinearMap.ker (subsetCechCardDifferential Dg 1) := by
    rw [LinearMap.mem_ker, map_sub, map_smul]
    change subsetCechCardDifferential Dg 1 a - c • subsetCechCardDifferential Dg (0 + 1) t = 0
    rw [ht, ← hcb, smul_smul, ← pow_succ', sub_self]
  obtain ⟨g, hg⟩ := cechAugmentation_surjective_ker O (structureCoeff f) D.iSup_eq_top a' ha'
  refine ⟨g, N + 1, ?_⟩
  -- check the nilpotency locally on the cover `ι⁻¹ U_i`
  have hloc : ∀ i : D.ι, T.presheaf.map
      (homOfLE (le_top : ι ⁻¹ᵁ (({i} : Finset D.ι).inf D.U) ≤ ⊤)).op
      ((ι.appTop g - e) ^ (N + 1)) = 0 := by
    intro i
    have hgi : X.presheaf.map (homOfLE (le_top : ({i} : Finset D.ι).inf D.U ≤ ⊤)).op
        (show Γ(X, ⊤) from g) =
        (show Γ(X, ({i} : Finset D.ι).inf D.U) from a.val {i}) -
          sectionsRingHom (structureCoeff f) (le_top : ({i} : Finset D.ι).inf D.U ≤ ⊤) c *
            (show Γ(X, ({i} : Finset D.ι).inf D.U) from t'.val {i}) := by
      have := congrArg (fun z : subsetCechCardPiece Dg 1 => z.val {i}) hg
      simp only [cechAugmentation_apply_singleton] at this
      exact this
    have h1 : ι.app (({i} : Finset D.ι).inf D.U)
        (X.presheaf.map (homOfLE (le_top : ({i} : Finset D.ι).inf D.U ≤ ⊤)).op
          (show Γ(X, ⊤) from g)) =
        T.presheaf.map (homOfLE (le_top : ι ⁻¹ᵁ (({i} : Finset D.ι).inf D.U) ≤ ⊤)).op
          (ι.appTop g) :=
      app_presheaf_map_apply ι le_top g
    have h2 : ι.app (({i} : Finset D.ι).inf D.U)
        (sectionsRingHom (structureCoeff f) (le_top : ({i} : Finset D.ι).inf D.U ≤ ⊤) c) =
        T.presheaf.map (homOfLE (le_top : ι ⁻¹ᵁ (({i} : Finset D.ι).inf D.U) ≤ ⊤)).op
          (ι.appTop (structureCoeff f c)) :=
      app_presheaf_map_apply ι le_top (structureCoeff f c)
    have hres : T.presheaf.map
        (homOfLE (le_top : ι ⁻¹ᵁ (({i} : Finset D.ι).inf D.U) ≤ ⊤)).op (ι.appTop g - e) =
        -(T.presheaf.map (homOfLE (le_top : ι ⁻¹ᵁ (({i} : Finset D.ι).inf D.U) ≤ ⊤)).op
            (ι.appTop (structureCoeff f c)) *
          ι.app _ (show Γ(X, ({i} : Finset D.ι).inf D.U) from t'.val {i})) := by
      rw [map_sub, ← h1, ← h2, hgi, map_sub, map_mul, ha _ (Finset.card_singleton i)]
      change eres {i} - _ * _ - eres {i} = _
      ring
    rw [map_pow, hres, neg_pow, mul_pow, ← map_pow, hcn, map_zero, zero_mul, mul_zero]
  apply TopCat.Presheaf.section_ext T.sheaf ⊤
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, ι x ∈ D.U i := by
    have : ι x ∈ ⨆ i, D.U i := by rw [D.iSup_eq_top]; trivial
    exact Opens.mem_iSup.mp this
  have hxi : x ∈ ι ⁻¹ᵁ (({i} : Finset D.ι).inf D.U) := by
    change ι x ∈ ({i} : Finset D.ι).inf D.U
    rw [Finset.inf_singleton]
    exact hi
  change T.presheaf.germ ⊤ x hx ((ι.appTop g - e) ^ (N + 1)) = T.presheaf.germ ⊤ x hx 0
  rw [map_zero, ← TopCat.Presheaf.germ_res_apply T.presheaf
      (homOfLE (le_top : ι ⁻¹ᵁ (({i} : Finset D.ι).inf D.U) ≤ ⊤)) x hxi, hloc i, map_zero]

end Lift

section Step

variable {W : Type u} [CommRing W] [IsDomain W] [ValuationRing W] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of W)) [Flat f]

/-- **Idempotents of a thickening are trivial** (the algebraic core of
`prop:sm-conn-height-one`). Suppose every global function `g` of the flat `W`-scheme `X` has
`b g ^ m - a` nilpotent for some `m ≥ 1` and `a, b ∈ W`, `b ≠ 0`. Let `ι : T → X` be such that
global functions of `T` lift to `X` up to nilpotents and the constants of the maximal ideal of `W`
are nilpotent on `T`. Then `0` and `1` are the only idempotents of `Γ(T, 𝒪_T)`. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem
    (hG : ∀ g : Γ(X, ⊤), ∃ m : ℕ, 0 < m ∧ ∃ a b : W, b ≠ 0 ∧
      IsNilpotent (structureCoeff f b * g ^ m - structureCoeff f a))
    {T : Scheme.{u}} (ι : T ⟶ X)
    (hlift : ∀ e : Γ(T, ⊤), ∃ g : Γ(X, ⊤), IsNilpotent (ι.appTop g - e))
    (hnil : ∀ w ∈ IsLocalRing.maximalIdeal W, IsNilpotent (ι.appTop (structureCoeff f w)))
    (e : Γ(T, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  classical
  let π := Ideal.Quotient.mk (nilradical Γ(T, ⊤))
  have hπ : ∀ z : Γ(T, ⊤), π z = 0 ↔ IsNilpotent z := fun z =>
    Ideal.Quotient.eq_zero_iff_mem.trans mem_nilradical
  have hzero : π 1 = 0 → e = 0 := by
    intro h
    obtain ⟨k, hk⟩ := (hπ 1).mp h
    rw [one_pow] at hk
    rw [← mul_one e, hk, mul_zero]
  have hnil0 : π e = 0 → e = 0 := by
    intro h
    obtain ⟨k, hk⟩ := (hπ e).mp h
    rw [← he.pow_succ_eq k, pow_succ, hk, zero_mul]
  have hnil1 : π e = 1 → e = 1 := by
    intro h
    have h' : π (1 - e) = 0 := by rw [map_sub, map_one, h, sub_self]
    obtain ⟨k, hk⟩ := (hπ (1 - e)).mp h'
    have h1e : 1 - e = 0 := by rw [← he.one_sub.pow_succ_eq k, pow_succ, hk, zero_mul]
    exact (sub_eq_zero.mp h1e).symm
  have hm0 : ∀ w ∈ IsLocalRing.maximalIdeal W, π (ι.appTop (structureCoeff f w)) = 0 :=
    fun w hw => (hπ _).mpr (hnil w hw)
  obtain ⟨g, hg⟩ := hlift e
  have hge : π (ι.appTop g) = π e := by
    rw [← sub_eq_zero, ← map_sub]
    exact (hπ _).mpr hg
  obtain ⟨m, hm, a₀, b₀, hb₀, hν⟩ := hG g
  have hem : π e ^ m = π e := by
    rw [← map_pow, ← Nat.sub_add_cancel hm, he.pow_succ_eq]
  by_cases hdvd : b₀ ∣ a₀
  · -- `g ^ m` is a constant `l` up to nilpotents
    obtain ⟨l, rfl⟩ := hdvd
    have hgl : IsNilpotent (g ^ m - structureCoeff f l) := by
      apply isNilpotent_of_isNilpotent_structureCoeff_mul f hb₀
      rw [mul_sub, ← map_mul]
      exact hν
    have hel : π e = π (ι.appTop (structureCoeff f l)) := by
      have h := (hπ _).mpr (hgl.map ι.appTop.hom)
      simp only [map_sub, map_pow] at h
      rw [hge, sub_eq_zero, hem] at h
      exact h
    by_cases hlm : l ∈ IsLocalRing.maximalIdeal W
    · left
      exact hnil0 (hel.trans (hm0 l hlm))
    · by_cases hl1 : 1 - l ∈ IsLocalRing.maximalIdeal W
      · right
        apply hnil1
        have h := hm0 _ hl1
        simp only [map_sub, map_one] at h
        rw [sub_eq_zero] at h
        exact hel.trans h.symm
      · -- both `l` and `1 - l` are units: then `Γ(T, 𝒪_T)` is zero
        left
        apply hzero
        have hlu : IsUnit l := by
          by_contra h
          exact hlm ((IsLocalRing.mem_maximalIdeal l).mpr h)
        have hl1u : IsUnit (1 - l) := by
          by_contra h
          exact hl1 ((IsLocalRing.mem_maximalIdeal _).mpr h)
        have hidm : π e * (1 - π e) = 0 := by
          rw [mul_sub, mul_one, ← map_mul, he.eq, sub_self]
        have hprod : π (ι.appTop (structureCoeff f (l * (1 - l)))) = 0 := by
          simp only [map_mul, map_sub, map_one]
          rw [← hel]
          exact hidm
        obtain ⟨u, hu⟩ := hlu.mul hl1u
        calc π 1 = π (ι.appTop (structureCoeff f (↑u⁻¹ * (l * (1 - l))))) := by
              rw [← hu, Units.inv_mul]
              simp only [map_one]
          _ = π (ι.appTop (structureCoeff f ↑u⁻¹)) *
              π (ι.appTop (structureCoeff f (l * (1 - l)))) := by
              simp only [map_mul]
          _ = 0 := by rw [hprod, mul_zero]
  · -- otherwise `b₀ = a₀ w` with `w` in the maximal ideal, and `1` is nilpotent on `T`
    left
    apply hzero
    obtain ⟨w, rfl⟩ := (ValuationRing.dvd_total a₀ b₀).resolve_right hdvd
    have ha₀ : a₀ ≠ 0 := left_ne_zero_of_mul hb₀
    have hwm : w ∈ IsLocalRing.maximalIdeal W := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hw
      exact hdvd ⟨↑hw.unit⁻¹, by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
    have hwg : IsNilpotent (structureCoeff f w * g ^ m - 1) := by
      apply isNilpotent_of_isNilpotent_structureCoeff_mul f ha₀
      rw [mul_sub, mul_one, ← mul_assoc, ← map_mul]
      exact hν
    have h := (hπ _).mpr (hwg.map ι.appTop.hom)
    simp only [map_sub, map_one, map_mul] at h
    rw [hm0 w hwm, zero_mul, zero_sub, neg_eq_zero] at h
    exact h

/-- **Connectedness of the closed fibre over a valuation ring of height one** (blueprint
`prop:sm-conn-height-one`). Let `W` be a valuation ring whose primes are `0` and the maximal ideal,
`c ≠ 0` an element of the maximal ideal, and `f : X → Spec W` flat and projective. If every global
function `g` of `X` has `b g ^ m - a` nilpotent for some `m ≥ 1` and `a, b ∈ W` with `b ≠ 0` (on
the generic fibre, global functions are constants up to nilpotents and `p`-th powers), then the
closed fibre `f⁻¹(𝔪)` is preconnected. -/
theorem isPreconnected_closedFibre_of_heightOne (hf : IsProjectiveOver f)
    (hW : ∀ P : Ideal W, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal W) {c : W}
    (hc0 : c ≠ 0) (hcm : c ∈ IsLocalRing.maximalIdeal W)
    (hG : ∀ g : Γ(X, ⊤), ∃ m : ℕ, 0 < m ∧ ∃ a b : W, b ≠ 0 ∧
      IsNilpotent (structureCoeff f b * g ^ m - structureCoeff f a)) :
    _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint W}) := by
  classical
  obtain ⟨D⟩ := nonempty_projectiveCoordinates_of_isProjectiveOver hf
  have hc : ∀ a : W, a ≠ 0 → ∃ n : ℕ, a ∣ c ^ n := fun a ha =>
    exists_dvd_pow_of_ne_zero hW hcm ha
  have hfp : Module.FinitePresentation W
      ((cechComplex (unitModule X) D.U (structureCoeff f)).homology 1) :=
    D.finitePresentation_cechCohomology_valuation (unitModule X) (fun _ => Module.Finite.self _)
      (fun i => flat_sectionsModuleCat f (D.U i)) 1
  obtain ⟨N, hN⟩ := exists_d_eq_pow_smul_of_finitePresentation_homology
    (cechComplex (unitModule X) D.U (structureCoeff f)) hc0 hc
  obtain ⟨I, hI⟩ : ∃ I : Ideal W, I = Ideal.span {c ^ (N + 1)} := ⟨_, rfl⟩
  have hρ : ∀ S : Finset D.ι, S.Nonempty →
      Function.Surjective ((bcFst (Ideal.Quotient.mk I) f).app (S.inf D.U)) ∧
      ∀ x : Γ(X, S.inf D.U), (bcFst (Ideal.Quotient.mk I) f).app (S.inf D.U) x = 0 →
        ∃ y : Γ(X, S.inf D.U),
          x = sectionsRingHom (structureCoeff f) (le_top : S.inf D.U ≤ ⊤) (c ^ (N + 1)) * y := by
    intro S hS
    obtain ⟨h1, h2⟩ := bcFst_app_surjective_and_ker f I (D.isAffineOpen_finsetInf hS)
    refine ⟨h1, fun x hx => exists_eq_mul_of_mem_map_span f ?_⟩
    rw [← hI]
    exact (h2 x).mp hx
  have hcI : c ^ (N + 1) ∈ I := hI ▸ Ideal.mem_span_singleton_self _
  have hcn : (bcFst (Ideal.Quotient.mk I) f).appTop (structureCoeff f c) ^ (N + 1) = 0 := by
    rw [← map_pow, ← map_pow, structureCoeff_bc, Ideal.Quotient.eq_zero_iff_mem.mpr hcI,
      map_zero]
  have hlift := exists_isNilpotent_appTop_sub f D hc0 hN (bcFst (Ideal.Quotient.mk I) f) hρ hcn
  have hnil : ∀ w ∈ IsLocalRing.maximalIdeal W,
      IsNilpotent ((bcFst (Ideal.Quotient.mk I) f).appTop (structureCoeff f w)) := by
    intro w hw
    obtain ⟨k, hk⟩ := dvd_pow_of_mem_maximalIdeal hW hc0 hw
    apply isNilpotent_bcFst_appTop_structureCoeff
    refine ⟨k * (N + 1), ?_⟩
    rw [pow_mul, hI]
    exact Ideal.mem_span_singleton.mpr (pow_dvd_pow_of_dvd hk _)
  have hidem := eq_zero_or_eq_one_of_isIdempotentElem f hG (bcFst (Ideal.Quotient.mk I) f)
    hlift hnil
  -- the closed fibre is the image of the connected thickening
  let T : Scheme.{u} := pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  have hpre : _root_.IsPreconnected (Set.univ : Set T) := by
    by_cases hTn : Nonempty T
    · have : ConnectedSpace T :=
        (DeJongAlterations.Geometry.ProperSteinGlobalIdempotents.connectedSpace_iff_idempotents
          T).mpr ⟨hTn, hidem⟩
      exact isPreconnected_univ
    · rw [not_nonempty_iff] at hTn
      rw [Set.univ_eq_empty_iff.mpr hTn]
      exact isPreconnected_empty
  have hrange : Set.range (bcFst (Ideal.Quotient.mk I) f) =
      f ⁻¹' {IsLocalRing.closedPoint W} := by
    apply range_bcFst_quotient f
    · intro P hP
      have hcP : c ∈ P.asIdeal := P.isPrime.mem_of_pow_mem (N + 1) (hP hcI)
      rcases hW P.asIdeal P.isPrime with h | h
      · exact absurd (Ideal.mem_bot.mp (h ▸ hcP)) hc0
      · exact PrimeSpectrum.ext h
    · rw [hI, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.pow_mem_of_mem _ hcm _ (Nat.succ_pos N)
  rw [← hrange, ← Set.image_univ]
  exact hpre.image _ (bcFst (Ideal.Quotient.mk I) f).continuous.continuousOn

end Step

end

end DeJongAlterations.StableModification.Cohomology.Connected
