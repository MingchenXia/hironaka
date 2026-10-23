/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalCore
import DeJongAlterations.StableModification.Cohomology.SteinCoherent
import DeJongAlterations.StableModification.Cohomology.CechRefinement
import DeJongAlterations.StableModification.Cohomology.CechAcyclic

/-!
# Zariski connectedness for birational morphisms: two-chart Čech cohomology

The cohomological inputs of the two-chart core (`ConnectedBirationalCore.lean`) for a projective
scheme `f : X → Spec R` over a finitely presented algebra `R` over a valuation ring `V`
(Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Lemma 4.4.2, `semi-stable.tex` line 3133; blueprint `sm-cohomology-connected-birational.tex`).
Let `X = W₁ ∪ W₂` with `W₁`, `W₂` affine.

* `twoFamily W₁ W₂` is the two-chart family, indexed by `ULift (Fin 2)`, and `twoH1 f W₁ W₂` the
  first cohomology of its Čech complex (lane COH1's `cechComplex`), as cycles modulo boundaries.
  Every `1`-cochain is a cocycle (`d_two_eq_zero`); a `1`-cochain is a function on `W₁ ∩ W₂`
  (`ev`, `single₂`), a `0`-cochain a pair of functions on `W₁`, `W₂` (`ev₀`, `ev₁`, `single₁`), and
  the differential is the difference of the restrictions (`ev_d`).
* `finite_twoH1` (blueprint `lem:sm-connbir-finite`): `twoH1` is a finite `R`-module, by the
  independence of the cover (`cechCohomologyIsoOfAffineCovers`) and lane COH3A's finite
  presentation of the Čech cohomology of the projective coordinate cover over a finitely
  presented `V`-algebra (`ProjectiveCoordinates.finitePresentation_cechCohomology_fp`).
* `exists_pow_mul_eq_res_sub_res` (blueprint `lem:sm-connbir-support`): if `f⁻¹(D(q))` is affine
  (for instance `f` is an isomorphism over `D(q)`), every `z ∈ Γ(W₁ ∩ W₂)` has a multiple `q ^ k z`
  which is a difference of restrictions: the Čech cohomology of the affine `f⁻¹(D(q))` vanishes
  (lane COH1's `linkDiagram_exact`) and sections over `D(q) ∩ W` are a localization of sections over
  the affine `W` (`isLocalizedModule_sectionsRestrict`).
* `exists_pow_smul_eq_zero_of_finite`: a finite module on which every generator of `Q` acts
  locally nilpotently is killed by a power of `Q`.
* `isPreconnected_preimage_zeroLocus_of_isProjectiveOver` (blueprint
  `thm:sm-connbir-projective`): combining these with the core, `f⁻¹(V(s))` is preconnected when
  `R → Γ(X, 𝒪_X)` is surjective, every `f⁻¹(D(q))`, `q ∈ s`, is affine and all primes containing
  `s` lie in a proper ideal.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Cohomology.ConnectedBirational

open Connected

noncomputable section

set_option backward.isDefEq.respectTransparency false

section TwoFamily

variable {X : Scheme.{u}} (W₁ W₂ : X.Opens)

/-- The first index of the two-chart family. -/
def i₀ : ULift.{u} (Fin 2) := ⟨0⟩

/-- The second index of the two-chart family. -/
def i₁ : ULift.{u} (Fin 2) := ⟨1⟩

theorem i₀_lt_i₁ : i₀ < i₁ := by
  change (0 : Fin 2) < 1
  decide

theorem i₀_ne_i₁ : i₀ ≠ i₁ := ne_of_lt i₀_lt_i₁

theorem univ_eq_pair : (Finset.univ : Finset (ULift.{u} (Fin 2))) = {i₀, i₁} := by
  ext ⟨i⟩
  fin_cases i <;> simp [i₀, i₁]

/-- The two-chart family `W₁, W₂`, indexed by `ULift (Fin 2)`. -/
def twoFamily : ULift.{u} (Fin 2) → X.Opens := fun i => ![W₁, W₂] i.down

theorem twoFamily_i₀ : twoFamily W₁ W₂ i₀ = W₁ := rfl

theorem twoFamily_i₁ : twoFamily W₁ W₂ i₁ = W₂ := rfl

theorem inf_single_i₀ : ({i₀} : Finset (ULift.{u} (Fin 2))).inf (twoFamily W₁ W₂) = W₁ := by
  rw [Finset.inf_singleton]
  rfl

theorem inf_single_i₁ : ({i₁} : Finset (ULift.{u} (Fin 2))).inf (twoFamily W₁ W₂) = W₂ := by
  rw [Finset.inf_singleton]
  rfl

theorem inf_pair : ({i₀, i₁} : Finset (ULift.{u} (Fin 2))).inf (twoFamily W₁ W₂) = W₁ ⊓ W₂ := by
  rw [Finset.inf_insert, Finset.inf_singleton]
  rfl

theorem iSup_twoFamily : ⨆ i, twoFamily W₁ W₂ i = W₁ ⊔ W₂ := by
  apply le_antisymm
  · refine iSup_le fun ⟨i⟩ => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_iSup (twoFamily W₁ W₂) i₀) (le_iSup (twoFamily W₁ W₂) i₁)

theorem eq_pair_of_card_eq_two {S : Finset (ULift.{u} (Fin 2))} (hS : S.card = 2) :
    S = {i₀, i₁} := by
  rw [← univ_eq_pair]
  apply Finset.eq_univ_of_card
  rw [hS]
  rfl

theorem eq_single_of_card_eq_one {S : Finset (ULift.{u} (Fin 2))} (hS : S.card = 1) :
    S = {i₀} ∨ S = {i₁} := by
  obtain ⟨⟨i⟩, rfl⟩ := Finset.card_eq_one.mp hS
  fin_cases i
  · left; rfl
  · right; rfl

theorem card_ne_three (S : Finset (ULift.{u} (Fin 2))) : S.card ≠ 3 := by
  have := Finset.card_le_univ S
  simp only [Fintype.card_ulift, Fintype.card_fin] at this
  omega

end TwoFamily

section Cochains

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (W₁ W₂ : X.Opens)

/-- The Čech diagram of the two-chart family, with coefficients `R`. -/
abbrev twoDiagram : Finset (ULift.{u} (Fin 2)) ⥤ ModuleCat.{u} R :=
  cechDiagram (unitModule X) (twoFamily W₁ W₂) (structureCoeff f)

/-- The Čech complex of the two-chart family. -/
abbrev twoComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  cechComplex (unitModule X) (twoFamily W₁ W₂) (structureCoeff f)

/-- The value of a `1`-cochain of the two-chart family, as a function on `W₁ ⊓ W₂`. -/
def ev (x : subsetCechCardPiece (twoDiagram f W₁ W₂) 2) : Γ(X, W₁ ⊓ W₂) :=
  X.presheaf.map (homOfLE (inf_pair W₁ W₂).ge).op (x.val {i₀, i₁})

theorem ev_apply (x : subsetCechCardPiece (twoDiagram f W₁ W₂) 2) :
    ev f W₁ W₂ x = X.presheaf.map (homOfLE (inf_pair W₁ W₂).ge).op (x.val {i₀, i₁}) := rfl

/-- The `1`-cochain with value `z` on `W₁ ⊓ W₂`. -/
def single₂ (z : Γ(X, W₁ ⊓ W₂)) : subsetCechCardPiece (twoDiagram f W₁ W₂) 2 :=
  ⟨fun S => if h : S = {i₀, i₁} then
      X.presheaf.map (homOfLE (by subst h; exact (inf_pair W₁ W₂).le)).op z else 0, by
    intro S hS
    have : S ≠ {i₀, i₁} := by
      rintro rfl
      exact hS (Finset.card_pair i₀_ne_i₁)
    simp only [dif_neg this]⟩

theorem single₂_apply_pair (z : Γ(X, W₁ ⊓ W₂)) :
    (single₂ f W₁ W₂ z).val {i₀, i₁} =
      X.presheaf.map (homOfLE (inf_pair W₁ W₂).le).op z := by
  simp only [single₂, dif_pos]

theorem ev_single₂ (z : Γ(X, W₁ ⊓ W₂)) : ev f W₁ W₂ (single₂ f W₁ W₂ z) = z := by
  rw [ev_apply, single₂_apply_pair, presheaf_map_map_apply, presheaf_map_self_apply]

theorem ev_injective : Function.Injective (ev f W₁ W₂) := by
  intro x y hxy
  apply Subtype.ext
  funext S
  by_cases hS : S.card = 2
  · obtain rfl := eq_pair_of_card_eq_two hS
    have h := congrArg (X.presheaf.map (homOfLE (inf_pair W₁ W₂).le).op) hxy
    simp only [ev_apply, presheaf_map_map_apply, presheaf_map_self_apply] at h
    exact h
  · rw [x.property S hS, y.property S hS]

theorem ev_smul (r : R) (x : subsetCechCardPiece (twoDiagram f W₁ W₂) 2) :
    ev f W₁ W₂ (r • x) = sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) r *
      ev f W₁ W₂ x := by
  rw [ev_apply, ev_apply]
  change X.presheaf.map _ (sectionsRingHom (structureCoeff f) _ r *
    (show Γ(X, ({i₀, i₁} : Finset (ULift.{u} (Fin 2))).inf (twoFamily W₁ W₂)) from
      x.val {i₀, i₁})) = _
  rw [map_mul]
  congr 1
  simp only [sectionsRingHom, RingHom.coe_comp, Function.comp_apply]
  exact presheaf_map_map_apply _ _ _

/-- The value of a `0`-cochain on `W₁`. -/
def ev₀ (a : subsetCechCardPiece (twoDiagram f W₁ W₂) 1) : Γ(X, W₁) :=
  X.presheaf.map (homOfLE (inf_single_i₀ W₁ W₂).ge).op (a.val {i₀})

/-- The value of a `0`-cochain on `W₂`. -/
def ev₁ (a : subsetCechCardPiece (twoDiagram f W₁ W₂) 1) : Γ(X, W₂) :=
  X.presheaf.map (homOfLE (inf_single_i₁ W₁ W₂).ge).op (a.val {i₁})

/-- The `0`-cochain with values `a₁` on `W₁` and `a₂` on `W₂`. -/
def single₁ (a₁ : Γ(X, W₁)) (a₂ : Γ(X, W₂)) : subsetCechCardPiece (twoDiagram f W₁ W₂) 1 :=
  ⟨fun S => if h : S = {i₀} then
      X.presheaf.map (homOfLE (by subst h; exact (inf_single_i₀ W₁ W₂).le)).op a₁
    else if h' : S = {i₁} then
      X.presheaf.map (homOfLE (by subst h'; exact (inf_single_i₁ W₁ W₂).le)).op a₂
    else 0, by
    intro S hS
    have h0 : S ≠ {i₀} := by rintro rfl; exact hS (Finset.card_singleton _)
    have h1 : S ≠ {i₁} := by rintro rfl; exact hS (Finset.card_singleton _)
    simp only [dif_neg h0, dif_neg h1]⟩

theorem ev₀_single₁ (a₁ : Γ(X, W₁)) (a₂ : Γ(X, W₂)) :
    ev₀ f W₁ W₂ (single₁ f W₁ W₂ a₁ a₂) = a₁ := by
  have h : (single₁ f W₁ W₂ a₁ a₂).val {i₀} =
      X.presheaf.map (homOfLE (inf_single_i₀ W₁ W₂).le).op a₁ := by
    simp only [single₁, dif_pos]
  rw [ev₀, h, presheaf_map_map_apply, presheaf_map_self_apply]

theorem ev₁_single₁ (a₁ : Γ(X, W₁)) (a₂ : Γ(X, W₂)) :
    ev₁ f W₁ W₂ (single₁ f W₁ W₂ a₁ a₂) = a₂ := by
  have hne : ({i₁} : Finset (ULift.{u} (Fin 2))) ≠ {i₀} := by
    intro h
    exact i₀_ne_i₁ (Finset.singleton_injective h).symm
  have h : (single₁ f W₁ W₂ a₁ a₂).val {i₁} =
      X.presheaf.map (homOfLE (inf_single_i₁ W₁ W₂).le).op a₂ := by
    simp only [single₁, dif_neg hne, dif_pos]
  rw [ev₁, h, presheaf_map_map_apply, presheaf_map_self_apply]

/-- **The coboundary of a `0`-cochain** is the difference of its restrictions to `W₁ ⊓ W₂`. -/
theorem ev_d (a : subsetCechCardPiece (twoDiagram f W₁ W₂) 1) :
    ev f W₁ W₂ (subsetCechCardDifferential (twoDiagram f W₁ W₂) 1 a) =
      res₂ W₁ W₂ (ev₁ f W₁ W₂ a) - res₁ W₁ W₂ (ev₀ f W₁ W₂ a) := by
  have hpair := subsetCechDifferential_pair' (twoDiagram f W₁ W₂) a.val i₀_lt_i₁
  have h := congrArg (X.presheaf.map (homOfLE (inf_pair W₁ W₂).ge).op).hom hpair
  refine h.trans ((map_sub (X.presheaf.map (homOfLE (inf_pair W₁ W₂).ge).op).hom _ _).trans ?_)
  simp only [subsetCechRestriction, ev₁, ev₀, res₁, res₂]
  congr 1 <;> exact (presheaf_map_map_apply _ _ _).trans (presheaf_map_map_apply _ _ _).symm

/-- On two charts every `1`-cochain is a cocycle. -/
theorem d_two_eq_zero (x : subsetCechCardPiece (twoDiagram f W₁ W₂) 2) :
    subsetCechCardDifferential (twoDiagram f W₁ W₂) 2 x = 0 := by
  apply Subtype.ext
  funext S
  exact (subsetCechCardDifferential (twoDiagram f W₁ W₂) 2 x).property S (card_ne_three S)

end Cochains

section Homology

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (W₁ W₂ : X.Opens)

/-- The short complex of the two-chart Čech complex around degree one. -/
abbrev twoSc : ShortComplex (ModuleCat.{u} R) := (twoComplex f W₁ W₂).sc' 0 1 2

/-- The first Čech cohomology of the two-chart cover, as cycles modulo boundaries. -/
abbrev twoH1 : Type u :=
  LinearMap.ker (twoSc f W₁ W₂).g.hom ⧸ LinearMap.range (twoSc f W₁ W₂).moduleCatToCycles

/-- The first Čech cohomology of the two-chart cover is `twoH1`. -/
def twoH1Iso : (twoComplex f W₁ W₂).homology 1 ≅ (twoSc f W₁ W₂).moduleCatLeftHomologyData.H :=
  (twoComplex f W₁ W₂).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (twoSc f W₁ W₂).moduleCatHomologyIso

theorem twoComplex_d₀ (a : (twoComplex f W₁ W₂).X 0) :
    ((twoComplex f W₁ W₂).d 0 1).hom a =
      subsetCechCardDifferential (twoDiagram f W₁ W₂) 1 a := by
  change ((subsetCechComplex (twoDiagram f W₁ W₂)).d 0 (0 + 1)).hom a = _
  rw [subsetCechComplex_d]
  rfl

theorem mem_ker_twoSc_g (x : (twoComplex f W₁ W₂).X 1) :
    x ∈ LinearMap.ker (twoSc f W₁ W₂).g.hom := by
  rw [LinearMap.mem_ker]
  change ((subsetCechComplex (twoDiagram f W₁ W₂)).d 1 (1 + 1)).hom x = 0
  rw [subsetCechComplex_d]
  exact d_two_eq_zero f W₁ W₂ x

/-- The class of a `1`-cochain in `twoH1`. -/
def twoClass (x : (twoComplex f W₁ W₂).X 1) : twoH1 f W₁ W₂ :=
  Submodule.Quotient.mk ⟨x, mem_ker_twoSc_g f W₁ W₂ x⟩

theorem twoClass_surjective : Function.Surjective (twoClass f W₁ W₂) := by
  intro m
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact ⟨x, rfl⟩

theorem twoClass_smul (r : R) (x : (twoComplex f W₁ W₂).X 1) :
    r • twoClass f W₁ W₂ x = twoClass f W₁ W₂ (r • x) := rfl

/-- A class vanishes iff the cochain is a coboundary. -/
theorem twoClass_eq_zero_iff (x : (twoComplex f W₁ W₂).X 1) :
    twoClass f W₁ W₂ x = 0 ↔ ∃ a : (twoComplex f W₁ W₂).X 0,
      ((twoComplex f W₁ W₂).d 0 1).hom a = x := by
  rw [twoClass, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

/-- **Annihilators give coboundaries**: if `r` kills `twoH1`, then `r z` is a difference of
restrictions for every `z ∈ Γ(W₁ ⊓ W₂)`. -/
theorem exists_eq_res_sub_res_of_smul_eq_zero {r : R} (hr : ∀ m : twoH1 f W₁ W₂, r • m = 0)
    (z : Γ(X, W₁ ⊓ W₂)) : ∃ a₁ : Γ(X, W₁), ∃ a₂ : Γ(X, W₂),
      sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) r * z =
        res₂ W₁ W₂ a₂ - res₁ W₁ W₂ a₁ := by
  let x : (twoComplex f W₁ W₂).X 1 := single₂ f W₁ W₂ z
  have h := hr (twoClass f W₁ W₂ x)
  rw [twoClass_smul, twoClass_eq_zero_iff] at h
  obtain ⟨a, ha⟩ := h
  rw [twoComplex_d₀] at ha
  let a' : subsetCechCardPiece (twoDiagram f W₁ W₂) 1 := a
  refine ⟨ev₀ f W₁ W₂ a', ev₁ f W₁ W₂ a', ?_⟩
  have h1 := ev_d f W₁ W₂ a'
  have h2 : subsetCechCardDifferential (twoDiagram f W₁ W₂) 1 a' =
      r • single₂ f W₁ W₂ z := ha
  rw [h2, ev_smul, ev_single₂] at h1
  exact h1

/-- **Coboundaries give torsion**: if every `q ^ k z` is (for some `k`) a difference of
restrictions, then every element of `twoH1` is killed by a power of `q`. -/
theorem exists_pow_smul_eq_zero_of_forall {q : R}
    (hq : ∀ z : Γ(X, W₁ ⊓ W₂), ∃ k : ℕ, ∃ a₁ : Γ(X, W₁), ∃ a₂ : Γ(X, W₂),
      sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) (q ^ k) * z =
        res₂ W₁ W₂ a₂ - res₁ W₁ W₂ a₁)
    (m : twoH1 f W₁ W₂) : ∃ k : ℕ, q ^ k • m = 0 := by
  obtain ⟨x, rfl⟩ := twoClass_surjective f W₁ W₂ m
  let x' : subsetCechCardPiece (twoDiagram f W₁ W₂) 2 := x
  obtain ⟨k, a₁, a₂, hk⟩ := hq (ev f W₁ W₂ x')
  refine ⟨k, ?_⟩
  rw [twoClass_smul, twoClass_eq_zero_iff]
  let a : subsetCechCardPiece (twoDiagram f W₁ W₂) 1 := single₁ f W₁ W₂ a₁ a₂
  refine ⟨a, ?_⟩
  rw [twoComplex_d₀]
  apply ev_injective f W₁ W₂
  rw [ev_d, ev₀_single₁, ev₁_single₁, ← hk]
  exact (ev_smul f W₁ W₂ (q ^ k) x').symm

end Homology

section Annihilator

/-- **Finite modules with locally nilpotent generators of `Q`**: if `M` is a finite `R`-module
and every element of the finite set `s` acts locally nilpotently on `M`, then some power of
`Q = (s)` kills `M`. -/
theorem exists_pow_smul_eq_zero_of_finite {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (s : Finset R)
    (hs : ∀ q ∈ s, ∀ m : M, ∃ k : ℕ, q ^ k • m = 0) :
    ∃ N : ℕ, ∀ r ∈ Ideal.span (s : Set R) ^ N, ∀ m : M, r • m = 0 := by
  classical
  have hrad : Ideal.span (s : Set R) ≤ (Module.annihilator R M).radical := by
    rw [Ideal.span_le]
    intro q hq
    obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := M)
    choose k hk using hs q hq
    refine ⟨∑ g ∈ G, k g, ?_⟩
    rw [Module.mem_annihilator]
    have hgen : ∀ g ∈ G, q ^ (∑ g ∈ G, k g) • g = 0 := by
      intro g hg
      have hle : k g ≤ ∑ g ∈ G, k g := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hk g, smul_zero]
    intro m
    have hm : m ∈ Submodule.span R (G : Set M) := by rw [hG]; trivial
    induction hm using Submodule.span_induction with
    | mem g hg => exact hgen g hg
    | zero => exact smul_zero _
    | add a b _ _ ha hb => rw [smul_add, ha, hb, add_zero]
    | smul c a _ ha => rw [smul_comm, ha, smul_zero]
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (Submodule.fg_span (Finset.finite_toSet s))
  refine ⟨N, fun r hr m => ?_⟩
  exact Module.mem_annihilator.mp (hN hr) m

end Annihilator

section Support

/-- On a two-element index set, the differential of a cochain supported on two-element subsets
vanishes (there are no three-element subsets). -/
theorem subsetCechDifferential_eq_zero_of_two {A : Type u} [CommRing A]
    (D : Finset (ULift.{u} (Fin 2)) ⥤ ModuleCat.{u} A) (x : subsetCechCube D)
    (hx : ∀ S, S.card ≠ 2 → x S = 0) : subsetCechDifferential D x = 0 := by
  have h := subsetCechDifferential_mem_cardPiece D 2 ⟨x, hx⟩
  rw [subsetCechCardPiece_eq_bot D 3 (by simp)] at h
  exact h

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- Restrictions of constants are constants. -/
theorem map_sectionsRingHom {V W : X.Opens} (h : W ≤ V) (r : R) :
    X.presheaf.map (homOfLE h).op (sectionsRingHom (structureCoeff f) (le_top : V ≤ ⊤) r) =
      sectionsRingHom (structureCoeff f) (le_top : W ≤ ⊤) r := by
  simp only [sectionsRingHom, RingHom.coe_comp, Function.comp_apply]
  exact presheaf_map_map_apply _ _ _

/-- **Localization on an affine open**, multiplicative form: every function on
`D(q) ∩ W`, `W` affine, becomes the restriction of a function on `W` after multiplication by a
power of `q`. -/
theorem exists_pow_mul_eq_res {W : X.Opens} (hW : IsAffineOpen W) (q : R)
    (y : Γ(X, X.basicOpen (structureCoeff f q) ⊓ W)) :
    ∃ k : ℕ, ∃ b : Γ(X, W),
      sectionsRingHom (structureCoeff f) (le_top : X.basicOpen (structureCoeff f q) ⊓ W ≤ ⊤)
        (q ^ k) * y = X.presheaf.map (homOfLE inf_le_right).op b := by
  have hloc := isLocalizedModule_sectionsRestrict (unitModule X) (structureCoeff f) hW
    (le_top : W ≤ ⊤) q rfl
  obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, h⟩ := hloc.surj y
  exact ⟨k, b, h⟩

/-- **Localization on an affine open**, vanishing form: a function on an affine `W` vanishing on
`D(q) ∩ W` is killed by a power of `q`. -/
theorem exists_pow_mul_eq_zero {W : X.Opens} (hW : IsAffineOpen W) (q : R) (w : Γ(X, W))
    (hw : X.presheaf.map (homOfLE (inf_le_right :
      X.basicOpen (structureCoeff f q) ⊓ W ≤ W)).op w = 0) :
    ∃ k : ℕ, sectionsRingHom (structureCoeff f) (le_top : W ≤ ⊤) (q ^ k) * w = 0 := by
  have hloc := isLocalizedModule_sectionsRestrict (unitModule X) (structureCoeff f) hW
    (le_top : W ≤ ⊤) q rfl
  have h0 : (sectionsRestrict (unitModule X) (structureCoeff f) (le_top : W ≤ ⊤)
      (le_top : X.basicOpen (structureCoeff f q) ⊓ W ≤ ⊤) inf_le_right).hom w =
      (sectionsRestrict (unitModule X) (structureCoeff f) (le_top : W ≤ ⊤)
      (le_top : X.basicOpen (structureCoeff f q) ⊓ W ≤ ⊤) inf_le_right).hom 0 := by
    rw [map_zero]
    exact hw
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hloc.exists_of_eq h0
  refine ⟨k, ?_⟩
  rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero] at hk
  exact hk

/-- `D(q) ∩ A` is affine for affine `A`. -/
theorem isAffineOpen_basicOpen_inf {A : X.Opens} (hA : IsAffineOpen A) (q : R) :
    IsAffineOpen (X.basicOpen (structureCoeff f q) ⊓ A) := by
  have h := Scheme.basicOpen_res X (structureCoeff f q) (homOfLE (le_top : A ≤ ⊤)).op
  rw [inf_comm, ← h]
  exact hA.basicOpen _

variable (W₁ W₂ : X.Opens) [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **Vanishing of the first Čech cohomology over `D(q)`, elementwise** (blueprint
`lem:sm-connbir-support`): if `X = W₁ ∪ W₂` with `W₁, W₂` affine and `D(q) = f⁻¹(D(q))` is
affine, then for every `z ∈ Γ(W₁ ⊓ W₂)` some `q ^ k z` is a difference of restrictions of
functions on `W₁` and `W₂`. -/
theorem exists_pow_mul_eq_res_sub_res (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (hcov : W₁ ⊔ W₂ = ⊤) (q : R) (hq : IsAffineOpen (X.basicOpen (structureCoeff f q)))
    (z : Γ(X, W₁ ⊓ W₂)) : ∃ k : ℕ, ∃ a₁ : Γ(X, W₁), ∃ a₂ : Γ(X, W₂),
      sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) (q ^ k) * z =
        res₂ W₁ W₂ a₂ - res₁ W₁ W₂ a₁ := by
  classical
  set V := X.basicOpen (structureCoeff f q) with hVdef
  let U := twoFamily W₁ W₂
  let 𝒱 := FiniteAffineCover.ofTwo W₁ W₂ hW₁ hW₂ hcov
  have hW₁₂ : IsAffineOpen (W₁ ⊓ W₂) := by
    have := 𝒱.isAffineOpen_inf ({i₀, i₁} : Finset (ULift.{u} (Fin 2))) (by simp)
    change IsAffineOpen (({i₀, i₁} : Finset (ULift.{u} (Fin 2))).inf (twoFamily W₁ W₂)) at this
    rwa [inf_pair] at this
  have haff : ∀ T : Finset (ULift.{u} (Fin 2)), IsAffineOpen (V ⊓ T.inf U) := by
    intro T
    rcases T.eq_empty_or_nonempty with hT | hT
    · rw [hT, Finset.inf_empty, inf_top_eq]
      exact hq
    · exact isAffineOpen_basicOpen_inf f (𝒱.isAffineOpen_inf T hT) q
  have hcovV : V ≤ ⨆ i, U i := by
    rw [iSup_twoFamily, hcov]
    exact le_top
  have hex := linkDiagram_exact (unitModule X) U V hq hcovV haff
  -- the cochain `z|_{V ∩ W₁ ∩ W₂}` of the link diagram
  let Dl := linkDiagram (unitModule X) U V
  let x : subsetCechCube Dl := fun S => if h : S = {i₀, i₁} then
    X.presheaf.map (homOfLE (by subst h; exact inf_le_right.trans (inf_pair W₁ W₂).le)).op z
    else 0
  have hx : subsetCechDifferential Dl x = 0 := by
    apply subsetCechDifferential_eq_zero_of_two
    intro S hS
    have hne : S ≠ {i₀, i₁} := by
      rintro rfl
      exact hS (Finset.card_pair i₀_ne_i₁)
    exact dif_neg hne
  obtain ⟨y, hy⟩ := (hex x).mp hx
  have hpair := (subsetCechDifferential_pair' Dl y i₀_lt_i₁).symm.trans (congrFun hy {i₀, i₁})
  have hx2 : x {i₀, i₁} = X.presheaf.map
      (homOfLE (inf_le_right.trans (inf_pair W₁ W₂).le :
        V ⊓ ({i₀, i₁} : Finset (ULift.{u} (Fin 2))).inf U ≤ W₁ ⊓ W₂)).op z := dif_pos rfl
  -- transport to the charts
  let y₀ : Γ(X, V ⊓ W₁) := X.presheaf.map
    (homOfLE (inf_le_inf_left V (inf_single_i₀ W₁ W₂).ge)).op (y {i₀})
  let y₁ : Γ(X, V ⊓ W₂) := X.presheaf.map
    (homOfLE (inf_le_inf_left V (inf_single_i₁ W₁ W₂).ge)).op (y {i₁})
  have hz : X.presheaf.map (homOfLE (inf_le_right : V ⊓ (W₁ ⊓ W₂) ≤ W₁ ⊓ W₂)).op z =
      X.presheaf.map (homOfLE (inf_le_inf_left V inf_le_right)).op y₁ -
        X.presheaf.map (homOfLE (inf_le_inf_left V inf_le_left)).op y₀ := by
    have h := congrArg (X.presheaf.map (homOfLE (inf_le_inf_left V (inf_pair W₁ W₂).ge)).op).hom
      hpair
    rw [hx2, presheaf_map_map_apply] at h
    refine h.symm.trans ((map_sub _ _ _).trans ?_)
    simp only [subsetCechRestriction, y₀, y₁]
    congr 1 <;> exact (presheaf_map_map_apply _ _ _).trans (presheaf_map_map_apply _ _ _).symm
  obtain ⟨k₀, b₀, hb₀⟩ := exists_pow_mul_eq_res f hW₁ q y₀
  obtain ⟨k₁, b₁, hb₁⟩ := exists_pow_mul_eq_res f hW₂ q y₁
  let w : Γ(X, W₁ ⊓ W₂) := sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤)
      (q ^ (k₀ + k₁)) * z -
    (res₂ W₁ W₂ (sectionsRingHom (structureCoeff f) (le_top : W₂ ≤ ⊤) (q ^ k₀) * b₁) -
      res₁ W₁ W₂ (sectionsRingHom (structureCoeff f) (le_top : W₁ ≤ ⊤) (q ^ k₁) * b₀))
  have hw : X.presheaf.map (homOfLE (inf_le_right : V ⊓ (W₁ ⊓ W₂) ≤ W₁ ⊓ W₂)).op w = 0 := by
    have hb₁' : X.presheaf.map (homOfLE ((inf_le_right : V ⊓ (W₁ ⊓ W₂) ≤ W₁ ⊓ W₂).trans
        inf_le_right)).op b₁ = sectionsRingHom (structureCoeff f) (le_top : V ⊓ (W₁ ⊓ W₂) ≤ ⊤)
          (q ^ k₁) * X.presheaf.map (homOfLE (inf_le_inf_left V
          inf_le_right : V ⊓ (W₁ ⊓ W₂) ≤ V ⊓ W₂)).op y₁ := by
      rw [← presheaf_map_map_apply (homOfLE (inf_le_right : V ⊓ W₂ ≤ W₂)).le
        (homOfLE (inf_le_inf_left V inf_le_right : V ⊓ (W₁ ⊓ W₂) ≤ V ⊓ W₂)).le, ← hb₁,
        map_mul, map_sectionsRingHom]
    have hb₀' : X.presheaf.map (homOfLE ((inf_le_right : V ⊓ (W₁ ⊓ W₂) ≤ W₁ ⊓ W₂).trans
        inf_le_left)).op b₀ = sectionsRingHom (structureCoeff f) (le_top : V ⊓ (W₁ ⊓ W₂) ≤ ⊤)
          (q ^ k₀) * X.presheaf.map (homOfLE (inf_le_inf_left V
          inf_le_left : V ⊓ (W₁ ⊓ W₂) ≤ V ⊓ W₁)).op y₀ := by
      rw [← presheaf_map_map_apply (homOfLE (inf_le_right : V ⊓ W₁ ≤ W₁)).le
        (homOfLE (inf_le_inf_left V inf_le_left : V ⊓ (W₁ ⊓ W₂) ≤ V ⊓ W₁)).le, ← hb₀,
        map_mul, map_sectionsRingHom]
    simp only [w, map_sub, map_mul, res₁, res₂, presheaf_map_map_apply]
    rw [map_sectionsRingHom, map_sectionsRingHom, map_sectionsRingHom, hz, hb₁', hb₀', pow_add,
      map_mul]
    ring
  obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero f hW₁₂ q w hw
  refine ⟨k + (k₀ + k₁),
    sectionsRingHom (structureCoeff f) (le_top : W₁ ≤ ⊤) (q ^ k) *
      (sectionsRingHom (structureCoeff f) (le_top : W₁ ≤ ⊤) (q ^ k₁) * b₀),
    sectionsRingHom (structureCoeff f) (le_top : W₂ ≤ ⊤) (q ^ k) *
      (sectionsRingHom (structureCoeff f) (le_top : W₂ ≤ ⊤) (q ^ k₀) * b₁), ?_⟩
  have hk' : sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) (q ^ k) *
      (sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) (q ^ (k₀ + k₁)) * z) =
      sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) (q ^ k) *
      (res₂ W₁ W₂ (sectionsRingHom (structureCoeff f) (le_top : W₂ ≤ ⊤) (q ^ k₀) * b₁) -
        res₁ W₁ W₂ (sectionsRingHom (structureCoeff f) (le_top : W₁ ≤ ⊤) (q ^ k₁) * b₀)) := by
    rw [← sub_eq_zero, ← mul_sub]
    exact hk
  rw [pow_add, map_mul, mul_assoc, hk']
  simp only [map_mul, res₁_sectionsRingHom, res₂_sectionsRingHom]
  ring

end Support

section Projective

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- A scheme separated over an affine scheme has affine diagonal. -/
theorem isAffineHom_diagonal_of_isSeparated' [IsSeparated f] :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  have e : f ≫ terminal.from _ = terminal.from X := terminal.hom_ext _ _
  have : IsSeparated (terminal.from X) := by rw [← e]; infer_instance
  infer_instance

variable (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra V R]
  [Algebra.FinitePresentation V R]

/-- **The first Čech cohomology of a two-chart cover of a projective scheme over a finitely
presented `V`-algebra is finite** (blueprint `lem:sm-connbir-finite`): it is isomorphic to the
first Čech cohomology of the projective coordinate cover (independence of the cover), which is
finitely presented by lane COH3A's coherence theorem
(`ProjectiveCoordinates.finitePresentation_cechCohomology_fp`). -/
theorem finite_twoH1 (hf : IsProjectiveOver f)
    (htf : ∀ v : V, v ≠ 0 → ∀ (U : X.Opens) (s : Γ(X, U)),
      sectionsRingHom (structureCoeff f) (le_top : U ≤ ⊤) (algebraMap V R v) * s = 0 → s = 0)
    (W₁ W₂ : X.Opens) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂) (hcov : W₁ ⊔ W₂ = ⊤)
    [IsAffineHom (pullback.diagonal (terminal.from X))] :
    Module.Finite R (twoH1 f W₁ W₂) := by
  obtain ⟨D⟩ := nonempty_projectiveCoordinates_of_isProjectiveOver hf
  have hfp := D.finitePresentation_cechCohomology_fp V (unitModule X)
    (fun _ => Module.Finite.self _) (fun i v hv s hs => htf v hv (D.U i) s hs) 1
  have hU2 : ⨆ i, twoFamily W₁ W₂ i = ⊤ := (iSup_twoFamily W₁ W₂).trans hcov
  have hU2aff : ∀ i, IsAffineOpen (twoFamily W₁ W₂ i) := by
    rintro ⟨i⟩
    fin_cases i
    · exact hW₁
    · exact hW₂
  let e := cechCohomologyIsoOfAffineCovers (unitModule X) (structureCoeff f) D.iSup_eq_top hU2
    D.isAffineOpen hU2aff 1 ≪≫ twoH1Iso f W₁ W₂
  have : Module.FinitePresentation R (twoH1 f W₁ W₂) :=
    Module.FinitePresentation.of_equiv e.toLinearEquiv
  infer_instance

/-- **Zariski connectedness, projective form** (blueprint `thm:sm-connbir-projective`). Let `V`
be a valuation ring, `R` a finitely presented `V`-algebra and `f : X → Spec R` projective with
`X` flat over `V` (no `V`-torsion in the sections) and `R → Γ(X, 𝒪_X)` surjective. Suppose `X` is
the union of two affine opens, `s ⊆ R` is a finite set such that every `f⁻¹(D(q))`, `q ∈ s`, is
affine (e.g. `f` is an isomorphism over `D(q)`), and all primes containing `s` lie in a proper
ideal `m`. Then `f⁻¹(V(s))` is preconnected. -/
theorem isPreconnected_preimage_zeroLocus_of_isProjectiveOver (hf : IsProjectiveOver f)
    (htf : ∀ v : V, v ≠ 0 → ∀ (U : X.Opens) (s : Γ(X, U)),
      sectionsRingHom (structureCoeff f) (le_top : U ≤ ⊤) (algebraMap V R v) * s = 0 → s = 0)
    (W₁ W₂ : X.Opens) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂) (hcov : W₁ ⊔ W₂ = ⊤)
    (hS : Function.Surjective (structureCoeff f)) (s : Finset R)
    (hs : ∀ q ∈ s, IsAffineOpen (X.basicOpen (structureCoeff f q))) (m : Ideal R) (hm : m ≠ ⊤)
    (hsm : ∀ P : Ideal R, P.IsPrime → (s : Set R) ⊆ P → P ≤ m) :
    _root_.IsPreconnected (f ⁻¹' PrimeSpectrum.zeroLocus (s : Set R)) := by
  have : IsProper f := hf.isProper
  have := isAffineHom_diagonal_of_isSeparated' f
  have hW₁₂ : IsAffineOpen (W₁ ⊓ W₂) := by
    have := (FiniteAffineCover.ofTwo W₁ W₂ hW₁ hW₂ hcov).isAffineOpen_inf
      ({i₀, i₁} : Finset (ULift.{u} (Fin 2))) (by simp)
    change IsAffineOpen (({i₀, i₁} : Finset (ULift.{u} (Fin 2))).inf (twoFamily W₁ W₂)) at this
    rwa [inf_pair] at this
  have := finite_twoH1 f V hf htf W₁ W₂ hW₁ hW₂ hcov
  obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_finite s fun q hq m =>
    exists_pow_smul_eq_zero_of_forall f W₁ W₂
      (exists_pow_mul_eq_res_sub_res f W₁ W₂ hW₁ hW₂ hcov q (hs q hq)) m
  have hN' : ∀ r ∈ Ideal.span (s : Set R) ^ N, ∀ z : Γ(X, W₁ ⊓ W₂), ∃ a₁ : Γ(X, W₁),
      ∃ a₂ : Γ(X, W₂), sectionsRingHom (structureCoeff f) (le_top : W₁ ⊓ W₂ ≤ ⊤) r * z =
        res₂ W₁ W₂ a₂ - res₁ W₁ W₂ a₁ := fun r hr z =>
    exists_eq_res_sub_res_of_smul_eq_zero f W₁ W₂ (hN r hr) z
  have h := isPreconnected_preimage_zeroLocus_of_twoCharts f W₁ W₂ hW₁ hW₂ hW₁₂ hcov
    (Ideal.span (s : Set R)) N hN' hS m hm fun P hP hsP => hsm P hP (Ideal.span_le.mp hsP)
  rwa [PrimeSpectrum.zeroLocus_span] at h

end Projective

end

end DeJongAlterations.StableModification.Cohomology.ConnectedBirational
