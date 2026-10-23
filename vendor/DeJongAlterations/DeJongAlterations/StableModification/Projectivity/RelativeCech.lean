/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Cohomology.CechCover

/-!
# Čech cohomology of a cover by two opens

Blueprint `sm-projectivity-relative.tex`, `lem:sm-ltg-two-cech`. For two opens `U₀, U₁` of a
scheme `Z` (indexed by `ULift (Fin 2)`, `pairOpens`), a module `F` and coefficients
`c : R →+* Γ(Z, ⊤)`, the alternating Čech complex has `Č⁰ = Γ(U₀) × Γ(U₁)`, `Č¹ = Γ(U₀ ∩ U₁)`
and `Čᵖ = 0` for `p ≥ 2`, so `Ȟ¹({U₀, U₁}, F)` is the cokernel of the difference of the
restrictions `pairDiff : (a, b) ↦ b|_{U₀ ∩ U₁} - a|_{U₀ ∩ U₁}`:

* `surjective_pairDiff_of_isZero`: if `Ȟ¹ = 0`, then `pairDiff` is onto;
* `finite_coker_pairDiff`: if `Ȟ¹` is a finite `R`-module, so is `coker pairDiff`;
* `pairCover`: the two opens as a `FiniteAffineCover` when `U₀`, `U₁`, `U₀ ∩ U₁` are affine and
  cover `Z`.

These are the two-term complexes of the lifting lemma `lem:sm-ltg-onto` (local-to-global
projectivity, Temkin, *Stable modification of relative curves*, Thm 1.1).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

open Cohomology

variable {Z : Scheme.{u}} {R : Type u} [CommRing R]

/-- The two indices. -/
abbrev pairIdx₀ : ULift.{u} (Fin 2) := ⟨0⟩

/-- The two indices. -/
abbrev pairIdx₁ : ULift.{u} (Fin 2) := ⟨1⟩

/-- Two opens as a family indexed by `ULift (Fin 2)`. -/
def pairOpens (U₀ U₁ : Z.Opens) : ULift.{u} (Fin 2) → Z.Opens := fun i =>
  if i.down = 0 then U₀ else U₁

variable (U₀ U₁ : Z.Opens)

@[simp] lemma pairOpens_zero : pairOpens U₀ U₁ pairIdx₀ = U₀ := rfl

@[simp] lemma pairOpens_one : pairOpens U₀ U₁ pairIdx₁ = U₁ := rfl

lemma pairIdx_cases (i : ULift.{u} (Fin 2)) : i = pairIdx₀ ∨ i = pairIdx₁ := by
  rcases i with ⟨i⟩
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma pairIdx₀_lt : (pairIdx₀ : ULift.{u} (Fin 2)) < pairIdx₁ := by decide

lemma univ_eq_pair : (Finset.univ : Finset (ULift.{u} (Fin 2))) = {pairIdx₀, pairIdx₁} := by
  ext i
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact pairIdx_cases i

lemma inf_le_pair_inf (T : Finset (ULift.{u} (Fin 2))) : U₀ ⊓ U₁ ≤ T.inf (pairOpens U₀ U₁) := by
  refine Finset.le_inf fun i _ => ?_
  rcases pairIdx_cases i with rfl | rfl
  · exact inf_le_left
  · exact inf_le_right

lemma pair_inf_le_of_card (T : Finset (ULift.{u} (Fin 2))) (h : T.card = 2) :
    T.inf (pairOpens U₀ U₁) ≤ U₀ ⊓ U₁ := by
  have hT : T = Finset.univ := Finset.eq_univ_of_card T (by simpa using h)
  subst hT
  exact le_inf (Finset.inf_le (Finset.mem_univ pairIdx₀))
    (Finset.inf_le (Finset.mem_univ pairIdx₁))

lemma pair_inf_eq_of_card (T : Finset (ULift.{u} (Fin 2))) (h : T.card = 2) :
    T.inf (pairOpens U₀ U₁) = U₀ ⊓ U₁ :=
  le_antisymm (pair_inf_le_of_card U₀ U₁ T h) (inf_le_pair_inf U₀ U₁ T)

variable (F : Z.Modules) (c : R →+* Γ(Z, ⊤))

/-- The difference of the restrictions `(a, b) ↦ b|_{U₀ ∩ U₁} - a|_{U₀ ∩ U₁}`. -/
def pairDiff : (sectionsModuleCat F c U₀ le_top × sectionsModuleCat F c U₁ le_top) →ₗ[R]
    sectionsModuleCat F c (U₀ ⊓ U₁) le_top :=
  (sectionsRestrict F c le_top le_top inf_le_right).hom ∘ₗ LinearMap.snd _ _ _ -
    (sectionsRestrict F c le_top le_top inf_le_left).hom ∘ₗ LinearMap.fst _ _ _

lemma pairDiff_apply (a : sectionsModuleCat F c U₀ le_top) (b : sectionsModuleCat F c U₁ le_top) :
    pairDiff U₀ U₁ F c (a, b) =
      F.presheaf.map (homOfLE inf_le_right).op b - F.presheaf.map (homOfLE inf_le_left).op a :=
  rfl

/-- The two-element subset `{i, j}`, with the decidable equality of the linear order (as in
`subsetCechDifferential_pair'`). -/
abbrev finsetPair {ι : Type*} [LinearOrder ι] (i j : ι) : Finset ι := {i, j}

/-- The two-element subset. -/
abbrev pairIdxs : Finset (ULift.{u} (Fin 2)) := finsetPair pairIdx₀ pairIdx₁

lemma card_pairIdxs : (pairIdxs.{u}).card = 2 := rfl


/-- The value of a degree-one Čech cochain on `U₀ ∩ U₁`. -/
def pairEval : subsetCechCardPiece (cechDiagram F (pairOpens U₀ U₁) c) 2 →ₗ[R]
    sectionsModuleCat F c (U₀ ⊓ U₁) le_top :=
  (sectionsRestrict F c le_top le_top (inf_le_pair_inf U₀ U₁ pairIdxs)).hom ∘ₗ
    (LinearMap.proj (R := R) (φ := fun T => (cechDiagram F (pairOpens U₀ U₁) c).obj T)
      pairIdxs) ∘ₗ (subsetCechCardPiece (cechDiagram F (pairOpens U₀ U₁) c) 2).subtype

/-- A section over `U₀ ∩ U₁` as a degree-one Čech cochain. -/
def pairCochain (t : sectionsModuleCat F c (U₀ ⊓ U₁) le_top) :
    subsetCechCardPiece (cechDiagram F (pairOpens U₀ U₁) c) 2 :=
  ⟨fun T => if h : T.card = 2 then
      sectionsRestrict F c le_top le_top (pair_inf_le_of_card U₀ U₁ T h) t else 0, by
    intro T hT
    simp only [dif_neg hT]⟩

lemma pairEval_pairCochain (t : sectionsModuleCat F c (U₀ ⊓ U₁) le_top) :
    pairEval U₀ U₁ F c (pairCochain U₀ U₁ F c t) = t := by
  simp only [pairEval, pairCochain, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, LinearMap.coe_proj, Function.eval, dif_pos card_pairIdxs]
  change F.presheaf.map _ (F.presheaf.map _ t) = t
  exact presheaf_map_map_self F _ _ t

/-- The component of a degree-zero Čech cochain on `U₀`. -/
def pairVal₀ (y : subsetCechCardPiece (cechDiagram F (pairOpens U₀ U₁) c) 1) :
    sectionsModuleCat F c U₀ le_top :=
  sectionsRestrict F c le_top le_top
    (le_of_eq (by simp [Finset.inf_singleton]) : U₀ ≤ ({pairIdx₀} : Finset _).inf (pairOpens U₀ U₁))
    (y.val {pairIdx₀})

/-- The component of a degree-zero Čech cochain on `U₁`. -/
def pairVal₁ (y : subsetCechCardPiece (cechDiagram F (pairOpens U₀ U₁) c) 1) :
    sectionsModuleCat F c U₁ le_top :=
  sectionsRestrict F c le_top le_top
    (le_of_eq (by simp [Finset.inf_singleton]) : U₁ ≤ ({pairIdx₁} : Finset _).inf (pairOpens U₀ U₁))
    (y.val {pairIdx₁})

/-- The value of the Čech differential of a degree-zero cochain on `U₀ ∩ U₁`. -/
lemma pairEval_differential (y : subsetCechCardPiece (cechDiagram F (pairOpens U₀ U₁) c) 1) :
    pairEval U₀ U₁ F c (subsetCechCardDifferential _ 1 y) =
      pairDiff U₀ U₁ F c (pairVal₀ U₀ U₁ F c y, pairVal₁ U₀ U₁ F c y) := by
  have key : subsetCechDifferential (cechDiagram F (pairOpens U₀ U₁) c) y.val pairIdxs = _ :=
    subsetCechDifferential_pair' (cechDiagram F (pairOpens U₀ U₁) c) y.val pairIdx₀_lt.{u}
  simp only [pairEval, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.coe_proj, Function.eval, subsetCechCardDifferential_coe]
  rw [key, pairDiff_apply, map_sub]
  congr 1
  · exact (presheaf_map_map F _ _ (inf_le_pair_inf U₀ U₁ {pairIdx₁}) _).trans
      (presheaf_map_map F _ _ (inf_le_pair_inf U₀ U₁ {pairIdx₁}) _).symm
  · exact (presheaf_map_map F _ _ (inf_le_pair_inf U₀ U₁ {pairIdx₀}) _).trans
      (presheaf_map_map F _ _ (inf_le_pair_inf U₀ U₁ {pairIdx₀}) _).symm

lemma subsingleton_cardPiece_three :
    Subsingleton (subsetCechCardPiece (cechDiagram F (pairOpens U₀ U₁) c) 3) := by
  rw [subsetCechCardPiece_eq_bot _ 3 (by simp)]
  infer_instance

/-- **Vanishing of `Ȟ¹` of two opens**: the difference of the restrictions is onto. -/
theorem surjective_pairDiff_of_isZero
    (h : IsZero (cechCohomology F (pairOpens U₀ U₁) c 1)) :
    Function.Surjective (pairDiff U₀ U₁ F c) := by
  intro t
  have H := (isZero_homology_succ_iff (cechComplex F (pairOpens U₀ U₁) c) 0).mp h
  obtain ⟨y, hy⟩ := H (pairCochain U₀ U₁ F c t) (by
    have : Subsingleton ((cechComplex F (pairOpens U₀ U₁) c).X (0 + 2)) :=
      subsingleton_cardPiece_three U₀ U₁ F c
    exact Subsingleton.elim _ _)
  have hd : (cechComplex F (pairOpens U₀ U₁) c).d 0 (0 + 1) =
      ModuleCat.ofHom (subsetCechCardDifferential (cechDiagram F (pairOpens U₀ U₁) c) 1) :=
    subsetCechComplex_d _ 0
  rw [hd] at hy
  let y' : subsetCechCardPiece (cechDiagram F (pairOpens U₀ U₁) c) 1 := y
  have hy' : subsetCechCardDifferential _ 1 y' = pairCochain U₀ U₁ F c t := hy
  refine ⟨(pairVal₀ U₀ U₁ F c y', pairVal₁ U₀ U₁ F c y'), ?_⟩
  rw [← pairEval_differential U₀ U₁ F c y', hy']
  exact pairEval_pairCochain U₀ U₁ F c t

/-- **Finiteness of `Ȟ¹` of two opens**: if `Ȟ¹({U₀, U₁}, F)` is finite, so is the cokernel of
the difference of the restrictions. -/
theorem finite_coker_pairDiff [Module.Finite R (cechCohomology F (pairOpens U₀ U₁) c 1)] :
    Module.Finite R (sectionsModuleCat F c (U₀ ⊓ U₁) le_top ⧸
      LinearMap.range (pairDiff U₀ U₁ F c)) := by
  set C := cechComplex F (pairOpens U₀ U₁) c
  let S := C.sc' 0 1 2
  let e : C.homology 1 ≅ ModuleCat.of R (LinearMap.ker S.g.hom ⧸
      LinearMap.range S.moduleCatToCycles) :=
    C.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫ S.moduleCatHomologyIso
  have : Module.Finite R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    Module.Finite.equiv e.toLinearEquiv
  let ev : LinearMap.ker S.g.hom →ₗ[R] sectionsModuleCat F c (U₀ ⊓ U₁) le_top ⧸
      LinearMap.range (pairDiff U₀ U₁ F c) :=
    (LinearMap.range (pairDiff U₀ U₁ F c)).mkQ ∘ₗ pairEval U₀ U₁ F c ∘ₗ
      (LinearMap.ker S.g.hom).subtype
  have hle : LinearMap.range S.moduleCatToCycles ≤ LinearMap.ker ev := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [ev, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hd : C.d 0 1 =
        ModuleCat.ofHom (subsetCechCardDifferential (cechDiagram F (pairOpens U₀ U₁) c) 1) :=
      subsetCechComplex_d _ 0
    change pairEval U₀ U₁ F c (S.f.hom y) ∈ _
    change pairEval U₀ U₁ F c ((C.d 0 1).hom y) ∈ _
    rw [hd]
    exact ⟨_, (pairEval_differential U₀ U₁ F c y).symm⟩
  let ψ := (LinearMap.range S.moduleCatToCycles).liftQ ev hle
  refine Module.Finite.of_surjective ψ ?_
  intro q
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hmem : (show S.X₂ from pairCochain U₀ U₁ F c t) ∈ LinearMap.ker S.g.hom := by
    have : Subsingleton S.X₃ := subsingleton_cardPiece_three U₀ U₁ F c
    exact LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
  refine ⟨Submodule.Quotient.mk ⟨_, hmem⟩, ?_⟩
  simp only [ψ, Submodule.liftQ_apply, ev, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply]
  congr 1
  exact pairEval_pairCochain U₀ U₁ F c t

/-- Two affine opens with affine intersection covering `Z`, as a finite affine cover. -/
def pairCover (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁) (h₀₁ : IsAffineOpen (U₀ ⊓ U₁))
    (hcov : U₀ ⊔ U₁ = ⊤) : FiniteAffineCover Z where
  ι := ULift.{u} (Fin 2)
  U := pairOpens U₀ U₁
  iSup_eq_top := by
    rw [eq_top_iff, ← hcov]
    exact sup_le (le_iSup (pairOpens U₀ U₁) pairIdx₀) (le_iSup (pairOpens U₀ U₁) pairIdx₁)
  isAffineOpen_inf T hT := by
    by_cases h2 : T.card = 2
    · rw [pair_inf_eq_of_card U₀ U₁ T h2]
      exact h₀₁
    · have hT1 : T.card = 1 := by
        have := Finset.card_le_univ T
        have := hT.card_pos
        simp only [Fintype.card_ulift, Fintype.card_fin] at *
        omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hT1
      rw [Finset.inf_singleton]
      rcases pairIdx_cases i with rfl | rfl
      · exact h₀
      · exact h₁

@[simp] lemma pairCover_U (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
    (h₀₁ : IsAffineOpen (U₀ ⊓ U₁)) (hcov : U₀ ⊔ U₁ = ⊤) :
    (pairCover U₀ U₁ h₀ h₁ h₀₁ hcov).U = pairOpens U₀ U₁ :=
  rfl

end

end DeJongAlterations.StableModification.Projectivity
