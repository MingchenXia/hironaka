/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.FiniteComparison
import DeJongAlterations.StableModification.Cohomology.BaseChange
import DeJongAlterations.Geometry.FiniteProjectiveCharts
import DeJongAlterations.Geometry.ProperSteinProjectiveCechStructureCoefficients
import DeJongAlterations.Projective

/-!
# Finiteness of the cohomology of coherent modules on projective schemes

Let `A` be a Noetherian ring, `X → Spec A` projective (`IsProjectiveOver`: a closed immersion
`i : X → ℙⁿ_A` over `A`) and `F` a coherent module on `X` (quasi-coherent with finite sections on
affine opens). Then every `H^q(X, F)` is a finite `A`-module
(`finite_cohomology_of_isProjectiveOver`, blueprint `thm:sm-finite-projective`; Hartshorne III.5.2,
EGA III 2.2.1, Stacks 0B5U). This is the finiteness statement used by Temkin, *Stable modification
of relative curves*, Lemma 4.4.2 and Proposition 4.4.6.

The pulled-back coordinate charts `U_j = i⁻¹ D₊(x_j)` with the pulled-back ratios `x_l / x_j`
(Codex's `FiniteProjective.chartOpen`, `FiniteProjective.chartRatio`) are projective coordinates
(`ProjectiveCoordinates.ofClosedImmersion`), so the theorem follows from
`ProjectiveCoordinates.finite_cechCohomology` and the independence of the cover.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.Geometry.FiniteProjective DeJongAlterations.Geometry.ProjectiveIdeal
  DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {n : ℕ}

/-- The constants `A → Γ(ℙⁿ_A, 𝒪)`. -/
abbrev projectiveConstants (A : Type u) [CommRing A] (n : ℕ) :
    A →+* Γ(projectiveSpace A n, ⊤) :=
  gradedProjectiveConstants (projectiveSpaceGrading A n) ⊤

variable (i : X ⟶ projectiveSpace A n)

/-- The constants of `X`, pulled back from `ℙⁿ_A` along `i`. -/
def closedConstants : A →+* Γ(X, ⊤) := i.appTop.hom.comp (projectiveConstants A n)

/-- Dehomogenization at `x_j` followed by pullback, as a ring homomorphism. -/
def chartFormHom (j : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) A →+* Γ(X, chartOpen i j) :=
  (i.app (nativeCoordinateOpen j)).hom.comp
    ((nativeCoordinateSectionsIso (R := A) j).hom.hom.comp (coordinateDehom j).toRingHom)

lemma chartFormHom_apply (j : Fin (n + 1)) (F : MvPolynomial (Fin (n + 1)) A) :
    chartFormHom i j F = chartForm i j F := rfl

/-- Restricting a constant of `ℙⁿ_A` to `D₊(x_j)` gives the dehomogenized constant. -/
lemma projectiveConstants_res (j : Fin (n + 1)) (a : A) :
    (projectiveSpace A n).presheaf.map (homOfLE (le_top : nativeCoordinateOpen j ≤ ⊤)).op
      (projectiveConstants A n a) = nativeFormSection j (MvPolynomial.C a) := by
  let _ := homogeneousChartAlgebra (R := A) j
  refine (gradedProjectiveConstants_basicOpen (projectiveSpaceGrading A n)
    (MvPolynomial.X j) a).trans ?_
  change _ = (nativeHomogeneousChartSectionsIso (R := A) j).hom
    ((homogeneousChartEquiv (R := A) j).symm (coordinateDehom j (MvPolynomial.C a)))
  rw [nativeHomogeneousChartSectionsIso_hom]
  congr 1
  change _ = homogeneousChartRatioHom j (coordinateDehom j (MvPolynomial.C a))
  rw [MvPolynomial.algHom_C, AlgHom.commutes]
  rfl

/-- The pulled-back dehomogenized constants are the constants of `X`. -/
lemma chartForm_C (j : Fin (n + 1)) (a : A) :
    chartForm i j (MvPolynomial.C a) =
      sectionsRingHom (closedConstants i) (le_top : chartOpen i j ≤ ⊤) a := by
  change i.app (nativeCoordinateOpen j) (nativeFormSection j (MvPolynomial.C a)) =
    X.presheaf.map (homOfLE (le_top : chartOpen i j ≤ ⊤)).op (i.appTop (projectiveConstants A n a))
  rw [← projectiveConstants_res]
  have h := congrArg (fun f => f (projectiveConstants A n a))
    (i.naturality (homOfLE (le_top : nativeCoordinateOpen j ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact h

/-- The cocycle identity for the pulled-back ratios. -/
lemma chartRatio_mul (j l k : Fin (n + 1)) :
    X.presheaf.map (homOfLE (inf_le_left : chartOpen i j ⊓ chartOpen i l ≤ chartOpen i j)).op
        (chartRatio i j l) *
      X.presheaf.map (homOfLE (inf_le_right : chartOpen i j ⊓ chartOpen i l ≤ chartOpen i l)).op
        (chartRatio i l k) =
      X.presheaf.map (homOfLE (inf_le_left : chartOpen i j ⊓ chartOpen i l ≤ chartOpen i j)).op
        (chartRatio i j k) := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x hx
  change X.presheaf.germ _ x hx (_ * _) = X.presheaf.germ _ x hx _
  rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply,
    X.presheaf.germ_res_apply]
  have h1 := chartForm_germ_ratio i j l x hx.1 hx.2 (MvPolynomial.isHomogeneous_X A k)
  have h2 := chartForm_germ_ratio i j l x hx.1 hx.2 (MvPolynomial.isHomogeneous_X A l)
  change X.presheaf.germ _ x hx.2 (chartRatio i l k) =
    X.presheaf.germ _ x hx.1 (chartRatio i j k) * X.presheaf.germ _ x hx.2 (chartRatio i l j) ^ 1
    at h1
  change X.presheaf.germ _ x hx.2 (chartRatio i l l) =
    X.presheaf.germ _ x hx.1 (chartRatio i j l) * X.presheaf.germ _ x hx.2 (chartRatio i l j) ^ 1
    at h2
  rw [chartRatio_self, map_one, pow_one] at h2
  rw [pow_one] at h1
  rw [h1, ← mul_assoc, mul_comm (X.presheaf.germ _ x hx.1 (chartRatio i j l)), mul_assoc, ← h2,
    mul_one]

variable [IsClosedImmersion i]

/-- A closed subscheme of `ℙⁿ_A` carries projective coordinates: the pulled-back charts
`i⁻¹ D₊(x_j)` and ratios `x_l / x_j` (blueprint `lem:sm-projective-coordinates-closed`). -/
def ProjectiveCoordinates.ofClosedImmersion :
    ProjectiveCoordinates X A (closedConstants i) where
  ι := ULift.{u} (Fin (n + 1))
  U j := chartOpen i j.down
  isAffineOpen j := chartOpen_isAffine i j.down
  iSup_eq_top := by
    have h : (⨆ j : Fin (n + 1), chartOpen i j) = ⊤ := by
      simp only [chartOpen]
      rw [← Scheme.Hom.preimage_iSup, iSup_nativeCoordinateOpen_eq_top, Scheme.Hom.preimage_top]
    rw [← h]
    exact le_antisymm (iSup_le fun j => le_iSup (fun j : Fin (n + 1) => chartOpen i j) j.down)
      (iSup_le fun j => le_iSup (fun j : ULift.{u} (Fin (n + 1)) => chartOpen i j.down) ⟨j⟩)
  ratio j l := chartRatio i j.down l.down
  inf_eq_basicOpen j l := (chartRatio_basicOpen i j.down l.down).symm
  ratio_self j := chartRatio_self i j.down
  ratio_mul j l k := chartRatio_mul i j.down l.down k.down
  surjective j := by
    intro y
    obtain ⟨s, rfl⟩ := i.app_surjective (nativeCoordinateOpen j.down)
      (nativeCoordinateOpen_isAffine j.down) y
    obtain ⟨q, rfl⟩ := (nativeCoordinateSectionsIso (R := A) j.down).commRingCatIsoToRingEquiv.surjective s
    refine ⟨MvPolynomial.rename ULift.up (MvPolynomial.rename Subtype.val q), ?_⟩
    have hdehom : coordinateDehom j.down (MvPolynomial.rename Subtype.val q) = q := by
      have : (coordinateDehom (R := A) j.down).comp (MvPolynomial.rename Subtype.val) =
          AlgHom.id A _ := by
        ext l
        simp [coordinateDehom, coordinateDehomCoord_ne]
      exact AlgHom.congr_fun this q
    have hring : (MvPolynomial.eval₂Hom (sectionsRingHom (closedConstants i)
        (le_top : chartOpen i j.down ≤ ⊤)) (fun l : ULift.{u} (Fin (n + 1)) =>
          chartRatio i j.down l.down)).comp
        (MvPolynomial.rename (R := A) (ULift.up : Fin (n + 1) → ULift.{u} (Fin (n + 1)))).toRingHom =
        chartFormHom i j.down := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, MvPolynomial.rename_C, MvPolynomial.eval₂Hom_C]
        rw [chartFormHom_apply, chartForm_C]
      · intro l
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, MvPolynomial.rename_X, MvPolynomial.eval₂Hom_X']
        rfl
    have := congrArg (fun f => f (MvPolynomial.rename Subtype.val q)) hring
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] at this
    rw [this, chartFormHom_apply]
    change i.app _ ((nativeCoordinateSectionsIso (R := A) j.down).hom
      (coordinateDehom j.down (MvPolynomial.rename Subtype.val q))) = _
    rw [hdehom]
    rfl

omit [IsClosedImmersion i] in
/-- The pulled-back constants are the structure coefficients of `i ≫ (ℙⁿ_A → Spec A)`. -/
lemma closedConstants_eq_structureCoeff {p : X ⟶ Spec (CommRingCat.of A)}
    (hcomp : i ≫ projectiveSpaceStructure A n = p) :
    closedConstants i = structureCoeff p := by
  subst hcomp
  have hzero : CommRingCat.ofHom (gradedCoefficientZero (projectiveSpaceGrading A n)) =
      (projectiveSpaceDegreeZeroEquiv A n).toCommRingCatIso.hom := by
    ext a
    rfl
  have hκ : projectiveConstants A n =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (projectiveSpaceStructure A n).appTop).hom := by
    rw [projectiveConstants, gradedProjectiveConstants_structure, hzero]
    rfl
  rw [closedConstants, structureCoeff, hκ, Scheme.Hom.comp_appTop]
  rfl

/-- **Finiteness of coherent cohomology on projective schemes** (blueprint
`thm:sm-finite-projective`; Hartshorne III.5.2): for `A` Noetherian, `p : X → Spec A` projective
and `F` coherent (quasi-coherent with finite sections on affine opens), every `H^q(X, F)` is a
finite `A`-module. -/
theorem finite_cohomology_of_isProjectiveOver [IsNoetherianRing A]
    {p : X ⟶ Spec (CommRingCat.of A)} (hp : IsProjectiveOver p) [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (F : X.Modules) [F.IsQuasicoherent]
    (hF : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)) (q : ℕ) :
    Module.Finite A (cohomology F (structureCoeff p) q) := by
  obtain ⟨n, i, hi, hcomp⟩ := hp
  have := hi
  let D := ProjectiveCoordinates.ofClosedImmersion i
  rw [← closedConstants_eq_structureCoeff i hcomp]
  have h : Module.Finite A (cechCohomology F D.toFiniteAffineCover.U (closedConstants i) q) :=
    D.finite_cechCohomology F (fun j => hF _ (D.isAffineOpen j)) q
  exact Module.Finite.equiv
    (cohomologyIsoCech F (closedConstants i) D.toFiniteAffineCover q).toLinearEquiv.symm

/-- For a projective morphism `p : X → Spec A` there are projective coordinates whose coefficient
map is the structure map `A → Γ(X, 𝒪_X)` of `p` (the input of the Mumford complex,
`ProjectiveCoordinates.exists_mumfordComplex_baseChange`). -/
theorem nonempty_projectiveCoordinates_of_isProjectiveOver {p : X ⟶ Spec (CommRingCat.of A)}
    (hp : IsProjectiveOver p) : Nonempty (ProjectiveCoordinates X A (structureCoeff p)) := by
  obtain ⟨n, i, hi, hcomp⟩ := hp
  have := hi
  exact ⟨closedConstants_eq_structureCoeff i hcomp ▸ ProjectiveCoordinates.ofClosedImmersion i⟩

end

end DeJongAlterations.StableModification.Cohomology
