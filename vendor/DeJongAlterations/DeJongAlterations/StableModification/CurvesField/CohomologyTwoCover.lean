/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CechCover

/-!
# Cohomology computed by a cover with two affine opens

Let `X` be a scheme covered by two opens `U₀`, `U₁`. The alternating Čech complex of a module `F`
for the family `(U₀, U₁)` has only two nonzero terms,
`Γ(U₀, F) × Γ(U₁, F) → Γ(U₀ ∩ U₁, F)`, `(a, b) ↦ b|_{U₀ ∩ U₁} - a|_{U₀ ∩ U₁}`
(the map `pairDiff`). Hence `Ȟ⁰ = ker pairDiff`, `Ȟ¹ = coker pairDiff` and `Ȟᵖ = 0` for `p ≥ 2`.
When `U₀`, `U₁` and `U₀ ∩ U₁` are affine and `F` is quasi-coherent, this computes the cohomology
`H^p(X, F)` of the Čech library (`cohomologyPairOneEquiv`, `cohomologyPairZeroEquiv`,
`isZero_cohomology_pair`).

This is the computational entry point of the chapter on curves over a field
(blueprint `sm-curves-fields-cohomology.tex`, `lem:sm-two-cover`): projective curves over a field
(and over a local base) are covered by two affine opens, and Temkin's computations (Prop. 4.4.6 of
M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, lines 3204–3225) are made on
such a cover.

## Main definitions

* `pairCover U₀ U₁`: the family `(U₀, U₁)` indexed by `ULift (Fin 2)`.
* `pairDiff F c U₀ U₁`: the difference map `(a, b) ↦ b| - a|`.
* `FiniteAffineCover.ofPair`: the finite affine cover given by two affine opens with affine
  intersection.

## Main results

* `cechPairOneEquiv`, `cechPairZeroEquiv`: `Ȟ¹(U, F) ≃ Γ(U₀ ∩ U₁, F) ⧸ range pairDiff` and
  `Ȟ⁰(U, F) ≃ ker pairDiff`.
* `cohomologyPairOneEquiv`, `cohomologyPairZeroEquiv`, `isZero_cohomology_pair`: the same for
  `H^p(X, F)` when the cover is affine and `F` quasi-coherent; `H^p = 0` for `p ≥ 2`.
* `homologyOneIsoOfDZero`: for an `ℕ`-indexed cochain complex of modules with `d¹ = 0`,
  `H¹ ≅ C¹ ⧸ range d⁰`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.Geometry.ProperSteinProjectiveCech
open DeJongAlterations.StableModification.Cohomology

namespace DeJongAlterations.StableModification.CurvesField

noncomputable section

section Homology

variable {R : Type u} [CommRing R]

/-- For an `ℕ`-indexed cochain complex of modules whose differential `C¹ → C²` vanishes,
`H¹(C) ≅ C¹ ⧸ range (C⁰ → C¹)`. -/
def homologyOneIsoOfDZero (C : CochainComplex (ModuleCat.{u} R) ℕ) (h : C.d 1 2 = 0) :
    C.homology 1 ≅ ModuleCat.of R (C.X 1 ⧸ LinearMap.range (C.d 0 1).hom) :=
  C.isoHomologyι 1 2 (by simp) h ≪≫ C.opcyclesIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (C.sc' 0 1 2).moduleCatOpcyclesIso

end Homology

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- The two opens `(U₀, U₁)` as a family indexed by `ULift (Fin 2)`. -/
def pairCover (U₀ U₁ : X.Opens) : ULift.{u} (Fin 2) → X.Opens := fun i => ![U₀, U₁] i.down

/-- The first index. -/
abbrev i₀ : ULift.{u} (Fin 2) := ⟨0⟩

/-- The second index. -/
abbrev i₁ : ULift.{u} (Fin 2) := ⟨1⟩

lemma i₀_lt_i₁ : (i₀ : ULift.{u} (Fin 2)) < i₁ := by
  change (0 : Fin 2) < 1
  decide

lemma i₀_ne_i₁ : (i₀ : ULift.{u} (Fin 2)) ≠ i₁ := ne_of_lt i₀_lt_i₁

lemma eq_i₀_or_eq_i₁ (i : ULift.{u} (Fin 2)) : i = i₀ ∨ i = i₁ := by
  rcases i with ⟨i⟩
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma finset_card_one (T : Finset (ULift.{u} (Fin 2))) (hT : T.card = 1) :
    T = {i₀} ∨ T = {i₁} := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hT
  rcases eq_i₀_or_eq_i₁ a with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma finset_card_two (T : Finset (ULift.{u} (Fin 2))) (hT : T.card = 2) : T = {i₀, i₁} := by
  have huniv : T = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hT]
    rfl
  rw [huniv]
  ext a
  rcases eq_i₀_or_eq_i₁ a with rfl | rfl <;> simp

variable (U₀ U₁ : X.Opens)

@[simp] lemma pairCover_i₀ : pairCover U₀ U₁ i₀ = U₀ := rfl

@[simp] lemma pairCover_i₁ : pairCover U₀ U₁ i₁ = U₁ := rfl

lemma inf_singleton_i₀ : ({i₀} : Finset (ULift.{u} (Fin 2))).inf (pairCover U₀ U₁) = U₀ := by
  simp

lemma inf_singleton_i₁ : ({i₁} : Finset (ULift.{u} (Fin 2))).inf (pairCover U₀ U₁) = U₁ := by
  simp

lemma inf_pair : ({i₀, i₁} : Finset (ULift.{u} (Fin 2))).inf (pairCover U₀ U₁) = U₀ ⊓ U₁ := by
  simp

lemma iSup_pairCover : ⨆ i, pairCover U₀ U₁ i = U₀ ⊔ U₁ := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rcases eq_i₀_or_eq_i₁ i with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_iSup (pairCover U₀ U₁) i₀) (le_iSup (pairCover U₀ U₁) i₁)

variable (F : X.Modules) (c : R →+* Γ(X, ⊤))

/-- The difference map `Γ(U₀, F) × Γ(U₁, F) → Γ(U₀ ∩ U₁, F)`, `(a, b) ↦ b| - a|`: the only
differential of the Čech complex of a two-open family. -/
def pairDiff :
    (sectionsModuleCat F c U₀ le_top × sectionsModuleCat F c U₁ le_top) →ₗ[R]
      sectionsModuleCat F c (U₀ ⊓ U₁) le_top where
  toFun p := sectionsRestrict F c le_top le_top inf_le_right p.2 -
    sectionsRestrict F c le_top le_top inf_le_left p.1
  map_add' p q := by
    change sectionsRestrict F c le_top le_top inf_le_right (p.2 + q.2) -
        sectionsRestrict F c le_top le_top inf_le_left (p.1 + q.1) = _
    rw [map_add, map_add]
    abel
  map_smul' r p := by
    change sectionsRestrict F c le_top le_top inf_le_right (r • p.2) -
        sectionsRestrict F c le_top le_top inf_le_left (r • p.1) = _
    rw [map_smul, map_smul, smul_sub]
    rfl

lemma pairDiff_apply (p : sectionsModuleCat F c U₀ le_top × sectionsModuleCat F c U₁ le_top) :
    pairDiff U₀ U₁ F c p = sectionsRestrict F c le_top le_top inf_le_right p.2 -
      sectionsRestrict F c le_top le_top inf_le_left p.1 :=
  rfl

omit [CommRing R] in
lemma _root_.DeJongAlterations.StableModification.Cohomology.sectionsRestrict_self_apply
    {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {V : X.Opens} (hV : V ≤ ⊤) (h : V ≤ V)
    (s : sectionsModuleCat F c V hV) : sectionsRestrict F c hV hV h s = s := by
  rw [sectionsRestrict_id]
  rfl

/-- The Čech diagram of the pair. -/
abbrev pairDiagram : Finset (ULift.{u} (Fin 2)) ⥤ ModuleCat.{u} R :=
  cechDiagram F (pairCover U₀ U₁) c

/-- Degree-zero Čech cochains of the pair are pairs of sections. -/
def pairPieceOneEquiv :
    subsetCechCardPiece (pairDiagram U₀ U₁ F c) 1 ≃ₗ[R]
      (sectionsModuleCat F c U₀ le_top × sectionsModuleCat F c U₁ le_top) where
  toFun x := (sectionsRestrict F c le_top le_top (inf_singleton_i₀ U₀ U₁).ge (x.val {i₀}),
    sectionsRestrict F c le_top le_top (inf_singleton_i₁ U₀ U₁).ge (x.val {i₁}))
  invFun p := ⟨fun T =>
      if h : T = {i₀} then
        sectionsRestrict F c le_top le_top (by rw [h]; exact (inf_singleton_i₀ U₀ U₁).le) p.1
      else if h' : T = {i₁} then
        sectionsRestrict F c le_top le_top (by rw [h']; exact (inf_singleton_i₁ U₀ U₁).le) p.2
      else 0, by
    intro T hT
    have h0 : T ≠ {i₀} := by rintro rfl; exact hT rfl
    have h1 : T ≠ {i₁} := by rintro rfl; exact hT rfl
    simp only [dif_neg h0, dif_neg h1]⟩
  left_inv x := by
    apply Subtype.ext
    funext T
    by_cases h : T = {i₀}
    · subst h
      simp only [dif_pos]
      rw [sectionsRestrict_restrict]
      exact (sectionsRestrict_congr_index F c (A := fun S => S.inf (pairCover U₀ U₁))
        (fun _ => le_top) x.val rfl le_top _ le_rfl).trans
        (by rw [sectionsRestrict_id]; rfl)
    · by_cases h' : T = {i₁}
      · subst h'
        have hne : ({i₁} : Finset (ULift.{u} (Fin 2))) ≠ {i₀} := by
          intro e
          exact i₀_ne_i₁ (Finset.singleton_injective e).symm
        simp only [dif_neg hne, dif_pos]
        rw [sectionsRestrict_restrict]
        exact (sectionsRestrict_congr_index F c (A := fun S => S.inf (pairCover U₀ U₁))
          (fun _ => le_top) x.val rfl le_top _ le_rfl).trans
          (by rw [sectionsRestrict_id]; rfl)
      · simp only [dif_neg h, dif_neg h']
        have hT : T.card ≠ 1 := by
          intro hc
          rcases finset_card_one T hc with e | e
          · exact h e
          · exact h' e
        exact (x.property T hT).symm
  right_inv p := by
    have hne : ({i₁} : Finset (ULift.{u} (Fin 2))) ≠ {i₀} := by
      intro e
      exact i₀_ne_i₁ (Finset.singleton_injective e).symm
    ext
    · dsimp only
      rw [dif_pos rfl, sectionsRestrict_restrict, sectionsRestrict_self_apply]
    · dsimp only
      rw [dif_neg hne, dif_pos rfl, sectionsRestrict_restrict, sectionsRestrict_self_apply]
  map_add' x y := by
    ext
    · exact LinearMap.map_add _ _ _
    · exact LinearMap.map_add _ _ _
  map_smul' r x := by
    ext
    · exact LinearMap.map_smul _ _ _
    · exact LinearMap.map_smul _ _ _

lemma pairPieceOneEquiv_apply (x : subsetCechCardPiece (pairDiagram U₀ U₁ F c) 1) :
    pairPieceOneEquiv U₀ U₁ F c x =
      (sectionsRestrict F c le_top le_top (inf_singleton_i₀ U₀ U₁).ge (x.val {i₀}),
        sectionsRestrict F c le_top le_top (inf_singleton_i₁ U₀ U₁).ge (x.val {i₁})) :=
  rfl

/-- Degree-one Čech cochains of the pair are sections over the intersection. -/
def pairPieceTwoEquiv :
    subsetCechCardPiece (pairDiagram U₀ U₁ F c) 2 ≃ₗ[R] sectionsModuleCat F c (U₀ ⊓ U₁) le_top where
  toFun x := sectionsRestrict F c le_top le_top (inf_pair U₀ U₁).ge (x.val {i₀, i₁})
  invFun s := ⟨fun T =>
      if h : T = {i₀, i₁} then
        sectionsRestrict F c le_top le_top (by rw [h]; exact (inf_pair U₀ U₁).le) s
      else 0, by
    intro T hT
    have h0 : T ≠ {i₀, i₁} := by
      rintro rfl
      exact hT (Finset.card_pair i₀_ne_i₁)
    simp only [dif_neg h0]⟩
  left_inv x := by
    apply Subtype.ext
    funext T
    by_cases h : T = {i₀, i₁}
    · subst h
      simp only [dif_pos]
      rw [sectionsRestrict_restrict]
      exact (sectionsRestrict_congr_index F c (A := fun S => S.inf (pairCover U₀ U₁))
        (fun _ => le_top) x.val rfl le_top _ le_rfl).trans
        (by rw [sectionsRestrict_id]; rfl)
    · simp only [dif_neg h]
      have hT : T.card ≠ 2 := fun hc => h (finset_card_two T hc)
      exact (x.property T hT).symm
  right_inv s := by
    dsimp only
    rw [dif_pos rfl, sectionsRestrict_restrict, sectionsRestrict_self_apply]
  map_add' x y := LinearMap.map_add _ _ _
  map_smul' r x := LinearMap.map_smul _ _ _

lemma pairPieceTwoEquiv_apply (x : subsetCechCardPiece (pairDiagram U₀ U₁ F c) 2) :
    pairPieceTwoEquiv U₀ U₁ F c x =
      sectionsRestrict F c le_top le_top (inf_pair U₀ U₁).ge (x.val {i₀, i₁}) :=
  rfl

/-- The Čech differential of the pair is `pairDiff`. -/
lemma pairPieceTwoEquiv_differential (x : subsetCechCardPiece (pairDiagram U₀ U₁ F c) 1) :
    pairPieceTwoEquiv U₀ U₁ F c (subsetCechCardDifferential (pairDiagram U₀ U₁ F c) 1 x) =
      pairDiff U₀ U₁ F c (pairPieceOneEquiv U₀ U₁ F c x) := by
  rw [pairPieceTwoEquiv_apply, pairPieceOneEquiv_apply, pairDiff_apply,
    subsetCechCardDifferential_coe]
  erw [subsetCechDifferential_pair' _ _ i₀_lt_i₁, map_sub]
  simp only [subsetCechRestriction]
  congr 1
  · exact (sectionsRestrict_restrict F c _ _ _ _ _ _).trans
      (sectionsRestrict_restrict F c _ _ _ _ _ _).symm
  · exact (sectionsRestrict_restrict F c _ _ _ _ _ _).trans
      (sectionsRestrict_restrict F c _ _ _ _ _ _).symm

/-- The second differential of the Čech complex of a pair vanishes: there are no subsets with three
elements. -/
lemma cechComplex_pair_d_one_two : (cechComplex F (pairCover U₀ U₁) c).d 1 2 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext T
  have : T.card ≠ 3 := by
    intro h
    have := Finset.card_le_univ T
    rw [h] at this
    exact absurd this (by decide)
  exact ((subsetCechCardDifferential (pairDiagram U₀ U₁ F c) 2 x).property T this)

/-- **`Ȟ¹` of a pair**: `Ȟ¹((U₀, U₁), F) ≃ Γ(U₀ ∩ U₁, F) ⧸ range pairDiff`. -/
def cechPairOneEquiv :
    cechCohomology F (pairCover U₀ U₁) c 1 ≃ₗ[R]
      (sectionsModuleCat F c (U₀ ⊓ U₁) le_top ⧸ LinearMap.range (pairDiff U₀ U₁ F c)) :=
  (homologyOneIsoOfDZero _ (cechComplex_pair_d_one_two U₀ U₁ F c)).toLinearEquiv.trans
    (Submodule.Quotient.equiv _ _ (pairPieceTwoEquiv U₀ U₁ F c) (by
      have hd : (cechComplex F (pairCover U₀ U₁) c).d 0 1 =
          ModuleCat.ofHom (subsetCechCardDifferential (pairDiagram U₀ U₁ F c) 1) :=
        subsetCechComplex_d _ 0
      rw [hd]
      ext y
      simp only [Submodule.mem_map, LinearMap.mem_range]
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨pairPieceOneEquiv U₀ U₁ F c x, (pairPieceTwoEquiv_differential U₀ U₁ F c x).symm⟩
      · rintro ⟨p, rfl⟩
        refine ⟨_, ⟨(pairPieceOneEquiv U₀ U₁ F c).symm p, rfl⟩, ?_⟩
        change pairPieceTwoEquiv U₀ U₁ F c
          (subsetCechCardDifferential _ 1 ((pairPieceOneEquiv U₀ U₁ F c).symm p)) = _
        rw [pairPieceTwoEquiv_differential, LinearEquiv.apply_symm_apply]))

/-- **`Ȟ⁰` of a pair**: `Ȟ⁰((U₀, U₁), F) ≃ ker pairDiff`. -/
def cechPairZeroEquiv :
    cechCohomology F (pairCover U₀ U₁) c 0 ≃ₗ[R] LinearMap.ker (pairDiff U₀ U₁ F c) :=
  (subsetCechZeroCocyclesIso (pairDiagram U₀ U₁ F c)).symm.toLinearEquiv.trans
    ((pairPieceOneEquiv U₀ U₁ F c).ofSubmodules _ _ (by
      ext p
      simp only [Submodule.mem_map, LinearMap.mem_ker]
      constructor
      · rintro ⟨x, hx, rfl⟩
        change pairDiff U₀ U₁ F c (pairPieceOneEquiv U₀ U₁ F c x) = 0
        rw [← pairPieceTwoEquiv_differential, hx, map_zero]
      · intro hp
        refine ⟨(pairPieceOneEquiv U₀ U₁ F c).symm p, ?_, by simp⟩
        apply (pairPieceTwoEquiv U₀ U₁ F c).injective
        rw [pairPieceTwoEquiv_differential, LinearEquiv.apply_symm_apply, hp, map_zero]))

/-- `Ȟᵖ((U₀, U₁), F) = 0` for `p ≥ 2`. -/
theorem isZero_cechCohomology_pair (p : ℕ) (hp : 2 ≤ p) :
    Limits.IsZero (cechCohomology F (pairCover U₀ U₁) c p) :=
  isZero_cechCohomology_of_card_le F _ c p (by simpa using hp)

section AffineCover

variable {U₀ U₁}

/-- Two affine opens with affine intersection covering `X` form a finite affine cover. -/
def FiniteAffineCover.ofPair (h : U₀ ⊔ U₁ = ⊤) (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
    (h₀₁ : IsAffineOpen (U₀ ⊓ U₁)) : FiniteAffineCover X where
  ι := ULift.{u} (Fin 2)
  U := pairCover U₀ U₁
  iSup_eq_top := by rw [iSup_pairCover, h]
  isAffineOpen_inf T hT := by
    by_cases h0 : i₀ ∈ T <;> by_cases h1 : i₁ ∈ T
    · have : T = {i₀, i₁} := by
        ext a
        rcases eq_i₀_or_eq_i₁ a with rfl | rfl <;> simp [h0, h1]
      rw [this, inf_pair]
      exact h₀₁
    · have : T = {i₀} := by
        ext a
        rcases eq_i₀_or_eq_i₁ a with rfl | rfl <;> simp [h0, h1, i₀_ne_i₁.symm]
      rw [this, inf_singleton_i₀]
      exact h₀
    · have : T = {i₁} := by
        ext a
        rcases eq_i₀_or_eq_i₁ a with rfl | rfl <;> simp [h0, h1]
      rw [this, inf_singleton_i₁]
      exact h₁
    · exfalso
      obtain ⟨a, ha⟩ := hT
      rcases eq_i₀_or_eq_i₁ a with rfl | rfl
      · exact h0 ha
      · exact h1 ha

@[simp]
lemma FiniteAffineCover.ofPair_U (h : U₀ ⊔ U₁ = ⊤) (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
    (h₀₁ : IsAffineOpen (U₀ ⊓ U₁)) : (FiniteAffineCover.ofPair h h₀ h₁ h₀₁).U = pairCover U₀ U₁ :=
  rfl

variable [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  [F.IsQuasicoherent] (h : U₀ ⊔ U₁ = ⊤) (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
  (h₀₁ : IsAffineOpen (U₀ ⊓ U₁))

/-- **`H¹` from two affine opens** (blueprint `lem:sm-two-cover`): if `U₀`, `U₁`, `U₀ ∩ U₁` are
affine and cover `X`, then for quasi-coherent `F`,
`H¹(X, F) ≃ Γ(U₀ ∩ U₁, F) ⧸ {b| - a| : a ∈ Γ(U₀, F), b ∈ Γ(U₁, F)}`. -/
def cohomologyPairOneEquiv :
    cohomology F c 1 ≃ₗ[R]
      (sectionsModuleCat F c (U₀ ⊓ U₁) le_top ⧸ LinearMap.range (pairDiff U₀ U₁ F c)) :=
  (cohomologyIsoCech F c (FiniteAffineCover.ofPair h h₀ h₁ h₀₁) 1).toLinearEquiv.trans
    (cechPairOneEquiv U₀ U₁ F c)

/-- **`H⁰` from two affine opens**: `H⁰(X, F) ≃ ker pairDiff`. -/
def cohomologyPairZeroEquiv :
    cohomology F c 0 ≃ₗ[R] LinearMap.ker (pairDiff U₀ U₁ F c) :=
  (cohomologyIsoCech F c (FiniteAffineCover.ofPair h h₀ h₁ h₀₁) 0).toLinearEquiv.trans
    (cechPairZeroEquiv U₀ U₁ F c)

include h h₀ h₁ h₀₁ in
/-- `H^p(X, F) = 0` for `p ≥ 2` when `X` is covered by two affine opens with affine intersection. -/
theorem isZero_cohomology_pair (p : ℕ) (hp : 2 ≤ p) : Limits.IsZero (cohomology F c p) :=
  (isZero_cechCohomology_pair U₀ U₁ F c p hp).of_iso
    (cohomologyIsoCech F c (FiniteAffineCover.ofPair h h₀ h₁ h₀₁) p)

include h h₀ h₁ h₀₁ in
/-- `H¹(X, F) = 0` iff every section over `U₀ ∩ U₁` is a difference `b| - a|`. -/
theorem isZero_cohomology_one_pair_iff :
    Limits.IsZero (cohomology F c 1) ↔ Function.Surjective (pairDiff U₀ U₁ F c) := by
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff,
    ModuleCat.isZero_iff_subsingleton]
  constructor
  · intro hz
    exact (cohomologyPairOneEquiv F c h h₀ h₁ h₀₁).symm.injective.subsingleton
  · intro hs
    exact (cohomologyPairOneEquiv F c h h₀ h₁ h₀₁).injective.subsingleton

end AffineCover

end

end DeJongAlterations.StableModification.CurvesField
