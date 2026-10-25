/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ProperSteinProjectiveCechFiniteGraded
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Coordinate Čech cohomology of free graded modules is finitely presented

Let `K` be any commutative ring and `I` a finite linearly ordered set. The coordinate Čech complex
of `K[T_i]_{i ∈ I}(m)` (the cover of `ℙ^{I}_K` by the `D₊(T_i)`) is Codex's Laurent complex
`polynomialLaurentCechComplex m`: on the intersection `U_S` its term is spanned by the Laurent
monomials `T^α` of degree `m` with `α_i ≥ 0` for `i ∉ S`. Codex's contraction
(`polynomialLaurentCechContraction`, the simplex contraction on every exponent with a nonnegative
coordinate) shows that every cocycle is a coboundary plus its *survivor*, the part supported on
exponents with all coordinates negative (`polynomialLaurentCechContraction_identity`). Codex uses
this to prove finiteness over Noetherian rings. Here we read off the cohomology exactly, over any
ring:

* in the top degree `#I - 1` (for `#I ≥ 2`) the cohomology is free on the monomials `T^α`, `α < 0`,
  of degree `m` (`laurentTopClass_bijective`);
* in degree `0` (for `#I ≥ 2`) it is the module of degree-`m` polynomials
  (`bijective_polynomialLaurentCechCardToCycles_zero`); for `#I = 1` it is the chart itself;
* in the other degrees it vanishes (Codex).

Consequently all cohomology modules are finitely presented
(`finitePresentation_polynomialLaurentCechComplex_homology`), and so are those of every finite
shifted free graded module (`finitePresentation_shiftedFree_homology`). These are the base cases
of the coherence argument of `ValuationCoherent.lean`, which proves the finiteness of coherent
cohomology over a non-Noetherian valuation ring without Noetherian approximation (blueprint
`sm-cohomology-valuation.tex`, `lem:sm-val-laurent`; the classical computation is Hartshorne,
*Algebraic Geometry*, III.5.1).
-/

universe u

open CategoryTheory
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Supported

variable {K I : Type u} [CommRing K]

/-- A supported submodule of the Laurent algebra on a finite set of exponents is finitely
presented: it is free on the corresponding monomials. -/
theorem finitePresentation_supported {s : Set (I → ℤ)} (hs : s.Finite) :
    Module.FinitePresentation K (AddMonoidAlgebra.supported K K s) := by
  have := hs.to_subtype
  let b : Module.Basis s K (AddMonoidAlgebra.supported K K s) :=
    ⟨AddMonoidAlgebra.supportedEquivFinsupp s⟩
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  exact Module.finitePresentation_of_projective K _

end Supported

section Laurent

variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]

omit [LinearOrder I] in
/-- The all-negative monomials of degree `m` live on the top intersection. -/
theorem negativeIntegralLaurentModule_le (m : ℤ) :
    negativeIntegralLaurentModule (K := K) (I := I) m ≤
      subsetHomogeneousLaurentModule m Finset.univ := by
  apply AddMonoidAlgebra.supported_mono
  intro α hα
  exact ⟨hα.1, fun i hi => (hi (Finset.mem_univ i)).elim⟩

/-- The cochain concentrated on the top intersection `U_I` with a given all-negative value. -/
def laurentTopCochain (m : ℤ) :
    negativeIntegralLaurentModule (K := K) (I := I) m →ₗ[K]
      subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m) :=
  LinearMap.pi fun S =>
    if h : S = Finset.univ then
      ((negativeIntegralLaurentModule (K := K) (I := I) m).subtype.codRestrict
        (subsetHomogeneousLaurentModule m S) fun f => by
          subst h
          exact negativeIntegralLaurentModule_le m f.property)
    else 0

lemma laurentTopCochain_univ (m : ℤ) (f : negativeIntegralLaurentModule (K := K) (I := I) m) :
    (laurentTopCochain m f Finset.univ).val = f.val := by
  simp only [laurentTopCochain, LinearMap.pi_apply]
  rfl

lemma laurentTopCochain_of_ne (m : ℤ) (f : negativeIntegralLaurentModule (K := K) (I := I) m)
    {S : Finset I} (hS : S ≠ Finset.univ) : laurentTopCochain m f S = 0 := by
  simp [laurentTopCochain, hS]

lemma laurentTopCochain_mem (m : ℤ) (f : negativeIntegralLaurentModule (K := K) (I := I) m) :
    laurentTopCochain m f ∈
      subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) (Fintype.card I) := by
  intro S hS
  apply laurentTopCochain_of_ne
  rintro rfl
  exact hS Finset.card_univ

/-- The cocycle of the top degree with a given all-negative value. -/
def laurentTopCycle (m : ℤ) (n : ℕ) (hn : n + 2 = Fintype.card I) :
    negativeIntegralLaurentModule (K := K) (I := I) m →ₗ[K]
      polynomialLaurentCechCardCycles (K := K) (I := I) m (n + 1) :=
  (((laurentTopCochain m).codRestrict
    (subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 2))
      fun f => hn ▸ laurentTopCochain_mem m f)).codRestrict _ fun f => by
    change subsetCechCardDifferential _ (n + 1 + 1) _ = 0
    have : subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1 + 1 + 1)
        = ⊥ := subsetCechCardPiece_eq_bot _ _ (by omega)
    exact (Submodule.eq_bot_iff _).mp this _ (Submodule.coe_mem _) |> Subtype.ext

/-- The class of the top cocycle with a given all-negative value. -/
def laurentTopClass (m : ℤ) (n : ℕ) (hn : n + 2 = Fintype.card I) :
    negativeIntegralLaurentModule (K := K) (I := I) m →ₗ[K]
      polynomialLaurentCechCardHomology (K := K) (I := I) m (n + 1) :=
  (polynomialLaurentCechCardToCycles (K := K) (I := I) m (n + 1)).range.mkQ.comp
    (laurentTopCycle m n hn)

lemma laurentTopCycle_val (m : ℤ) (n : ℕ) (hn : n + 2 = Fintype.card I)
    (f : negativeIntegralLaurentModule (K := K) (I := I) m) :
    (laurentTopCycle m n hn f).val.val = laurentTopCochain m f := rfl

omit [LinearOrder I] in
/-- A Laurent element supported in degree `m` on a proper intersection has no all-negative
monomial. -/
lemma coeff_eq_zero_of_ne_univ (m : ℤ) {S : Finset I} (hS : S ≠ Finset.univ)
    (x : subsetHomogeneousLaurentModule (K := K) (I := I) m S) {α : I → ℤ}
    (hα : ∀ i, α i < 0) : x.val.coeff α = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : I, i ∉ S := by
    by_contra h
    apply hS
    apply Finset.eq_univ_iff_forall.mpr
    simpa only [not_exists, not_not] using h
  by_contra hcoeff
  have hallowed := (AddMonoidAlgebra.mem_supported.mp x.property)
    (Finsupp.mem_support_iff.mpr hcoeff)
  exact (not_lt_of_ge (hallowed.2 i hi)) (hα i)

/-- **The top cohomology is free on the all-negative monomials**: the class map from the
all-negative monomials of degree `m` to the top cohomology is bijective. -/
theorem laurentTopClass_bijective (m : ℤ) (n : ℕ) (hn : n + 2 = Fintype.card I) :
    Function.Bijective (laurentTopClass (K := K) m n hn) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hmem : laurentTopCycle m n hn f ∈
        (polynomialLaurentCechCardToCycles (K := K) (I := I) m (n + 1)).range :=
      (Submodule.Quotient.mk_eq_zero _).mp hf
    obtain ⟨b, hb⟩ := hmem
    have hb' : subsetCechDifferential (polynomialLaurentCechDiagram m) b.val =
        laurentTopCochain m f := congrArg (fun z => z.val.val) hb
    apply Subtype.ext
    apply (AddMonoidAlgebra.coeffLinearEquiv K).injective
    apply Finsupp.ext
    intro α
    change f.val.coeff α = (0 : projectiveLaurentAlgebra K I).coeff α
    rw [show (0 : projectiveLaurentAlgebra K I).coeff α = 0 from rfl]
    by_cases hα : ∀ i, α i < 0
    · rw [← laurentTopCochain_univ m f, ← hb']
      have h := congrFun (polynomialLaurentCechCoefficient_differential m α b.val) Finset.univ
      rw [polynomialLaurentCechCoefficient_apply] at h
      rw [h, scalarSubsetCechDifferential_apply]
      apply Finset.sum_eq_zero
      intro i _
      rw [polynomialLaurentCechCoefficient_apply,
        coeff_eq_zero_of_ne_univ m (S := Finset.univ.erase i) (by
          intro h
          exact (Finset.notMem_erase i Finset.univ) (by rw [h]; exact Finset.mem_univ i)) _ hα,
        smul_zero]
    · by_contra hcoeff
      have hmemα := (AddMonoidAlgebra.mem_supported.mp f.property)
        (Finsupp.mem_support_iff.mpr hcoeff)
      exact hα hmemα.2
  · intro q
    obtain ⟨⟨r, c, rfl⟩, hr⟩ :=
      polynomialLaurentCechRepresentativesToHomology_surjective (K := K) (I := I) m (n + 1) q
    let f : negativeIntegralLaurentModule (K := K) (I := I) m :=
      ⟨(polynomialLaurentCechSurvivor m c.val.val Finset.univ).val,
        polynomialLaurentCechSurvivor_mem_negative m c.val.val Finset.univ⟩
    refine ⟨f, ?_⟩
    rw [← hr]
    change (polynomialLaurentCechCardToCycles m (n + 1)).range.mkQ (laurentTopCycle m n hn f) =
      (polynomialLaurentCechCardToCycles m (n + 1)).range.mkQ
        (polynomialLaurentCechCardCyclesSurvivor m (n + 1) c)
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext S
    rw [laurentTopCycle_val]
    by_cases hS : S = Finset.univ
    · subst hS
      apply Subtype.ext
      rw [laurentTopCochain_univ]
      rfl
    · rw [laurentTopCochain_of_ne m f hS]
      exact (polynomialLaurentCechSurvivor_eq_zero_of_ne_univ m c.val.val S hS).symm

omit [LinearOrder I] in
/-- The polynomials of degree `m` are finitely presented. -/
theorem finitePresentation_laurentModule_empty (m : ℤ) :
    Module.FinitePresentation K (subsetHomogeneousLaurentModule (K := K) (I := I) m ∅) := by
  rw [subsetHomogeneousLaurentModule_empty]
  exact finitePresentation_supported (nonnegativeIntegralHomogeneousExponents_finite m)

/-- The cardinality-zero cochains are the degree-`m` polynomials on the empty intersection. -/
theorem bijective_polynomialLaurentCechCardZeroEvaluation (m : ℤ) :
    Function.Bijective (polynomialLaurentCechCardZeroEvaluation (K := K) (I := I) m) := by
  refine ⟨polynomialLaurentCechCardZeroEvaluation_injective m, fun a => ?_⟩
  classical
  refine ⟨⟨fun S => if h : S = ∅ then h ▸ a else 0, fun S hS => ?_⟩, ?_⟩
  · have : S ≠ ∅ := fun h => hS (by rw [h, Finset.card_empty])
    simp [this]
  · show (if h : (∅ : Finset I) = ∅ then h ▸ a else 0) = a
    rw [dif_pos rfl]

/-- The cardinality-zero cochains are finitely presented. -/
theorem finitePresentation_laurentCardZero (m : ℤ) :
    Module.FinitePresentation K
      (subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) 0) := by
  have := finitePresentation_laurentModule_empty (K := K) (I := I) m
  exact Module.FinitePresentation.of_equiv
    (LinearEquiv.ofBijective _ (bijective_polynomialLaurentCechCardZeroEvaluation m)).symm

/-- **The bottom cohomology** (for `#I ≥ 2`): the augmentation from the degree-`m` polynomials to
the degree-zero cocycles is bijective. -/
theorem bijective_polynomialLaurentCechCardToCycles_zero (m : ℤ)
    (hI : 1 ≠ Fintype.card I) (hI₀ : 0 < Fintype.card I) :
    Function.Bijective (polynomialLaurentCechCardToCycles (K := K) (I := I) m 0) := by
  refine ⟨?_, polynomialLaurentCechCardToCycles_surjective_of_ne_top m 0 hI⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have hd : subsetCechDifferential (polynomialLaurentCechDiagram m) a.val = 0 :=
    congrArg (fun z => z.val.val) ha
  have hid := polynomialLaurentCechContraction_identity m a.val
  have hh : polynomialLaurentCechContraction m a.val = 0 := by
    funext S
    simp only [polynomialLaurentCechContraction, LinearMap.pi_apply, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    change subsetCechSign S j • polynomialLaurentCechContractionTerm m S j
      (a.val (insert j S)) = 0
    rw [a.property (insert j S) (Finset.insert_nonempty j S).card_pos.ne', map_zero, smul_zero]
  have hs : polynomialLaurentCechSurvivor m a.val = 0 := by
    funext S
    by_cases hS : S = Finset.univ
    · subst hS
      change polynomialLaurentCechSurvivorTerm m Finset.univ (a.val Finset.univ) = 0
      rw [a.property Finset.univ (by rw [Finset.card_univ]; omega), map_zero]
    · exact polynomialLaurentCechSurvivor_eq_zero_of_ne_univ m a.val S hS
  rw [hd, hh, map_zero, map_zero, hs, zero_add, zero_add] at hid
  exact Subtype.ext hid.symm

omit [LinearOrder I] in
/-- For a single coordinate, the degree-`m` exponents form a subsingleton. -/
lemma subsetHomogeneousLaurentExponents_finite_of_card_eq_one (m : ℤ) (S : Finset I)
    (hI : Fintype.card I = 1) : (subsetHomogeneousLaurentExponents (I := I) m S).Finite := by
  obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp hI
  apply Set.Subsingleton.finite
  intro α hα β hβ
  funext i
  rw [hi₀ i]
  have hsum : ∀ γ : I → ℤ, ∑ j, γ j = γ i₀ := fun γ => by
    rw [Fintype.sum_eq_single i₀ fun j hj => (hj (hi₀ j)).elim]
  rw [← hsum α, ← hsum β, hα.1, hβ.1]

/-- **Finite presentation of the cohomology of the Laurent complexes**: for every commutative ring
`K`, every degree `m` and every `p`, `Hᵖ` of the coordinate Čech complex of `K[T](m)` is a
finitely presented `K`-module. -/
theorem finitePresentation_polynomialLaurentCechComplex_homology (m : ℤ) (p : ℕ) :
    Module.FinitePresentation K ((polynomialLaurentCechComplex (K := K) (I := I) m).homology p) := by
  by_cases hp : Fintype.card I ≤ p
  · have : Subsingleton ((polynomialLaurentCechComplex (K := K) (I := I) m).homology p) :=
      ModuleCat.subsingleton_of_isZero (subsetCechComplex_homology_isZero_of_card_le
        (polynomialLaurentCechDiagram (K := K) (I := I) m) p hp)
    exact Module.FinitePresentation.of_subsingleton _
  rcases p with _ | n
  · -- degree zero
    have hiso := actualSubsetCechZeroCocyclesIso (polynomialLaurentCechDiagram (K := K) (I := I) m)
    suffices h : Module.FinitePresentation K (LinearMap.ker (subsetCechCardDifferential
        (polynomialLaurentCechDiagram (K := K) (I := I) m) 1)) from
      Module.FinitePresentation.of_equiv hiso.toLinearEquiv
    by_cases h1 : Fintype.card I = 1
    · have hbot : subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) 2 = ⊥ :=
        subsetCechCardPiece_eq_bot _ _ (by omega)
      have hker : LinearMap.ker (subsetCechCardDifferential
          (polynomialLaurentCechDiagram (K := K) (I := I) m) 1) = ⊤ := by
        refine LinearMap.ker_eq_top.mpr (LinearMap.ext fun c => Subtype.ext ?_)
        exact (Submodule.eq_bot_iff _).mp hbot _ (subsetCechCardDifferential _ 1 c).property
      have : ∀ S : {S : Finset I // S.card = 1}, Module.FinitePresentation K
          ((polynomialLaurentCechDiagram (K := K) (I := I) m).obj S.val) := fun S =>
        finitePresentation_supported (subsetHomogeneousLaurentExponents_finite_of_card_eq_one m
          S.val h1)
      have : Module.FinitePresentation K
          (subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) 1) :=
        Module.FinitePresentation.of_equiv (subsetCechCardProductEquiv _ 1).symm
      exact Module.FinitePresentation.of_equiv
        ((LinearEquiv.ofTop _ hker).symm)
    · have := finitePresentation_laurentCardZero (K := K) (I := I) m
      exact Module.FinitePresentation.of_equiv
        (LinearEquiv.ofBijective _ (bijective_polynomialLaurentCechCardToCycles_zero m
          (Ne.symm h1) (by omega)))
  · by_cases htop : n + 2 = Fintype.card I
    · have : Module.FinitePresentation K (negativeIntegralLaurentModule (K := K) (I := I) m) :=
        finitePresentation_supported (negativeIntegralHomogeneousExponents_finite (I := I) m)
      have hH : Module.FinitePresentation K
          (polynomialLaurentCechCardHomology (K := K) (I := I) m (n + 1)) :=
        Module.FinitePresentation.of_equiv
          (LinearEquiv.ofBijective _ (laurentTopClass_bijective (K := K) m n htop))
      have hsc : Module.FinitePresentation K
          ((polynomialLaurentCechComplex (K := K) (I := I) m).sc' n (n + 1) (n + 2)).homology := by
        rw [polynomialLaurentCechComplex_sc'_eq]
        exact Module.FinitePresentation.of_equiv
          (polynomialLaurentCechCardHomologyEquiv (K := K) (I := I) m (n + 1)).symm
      exact Module.FinitePresentation.of_equiv
        ((polynomialLaurentCechComplex (K := K) (I := I) m).homologyIsoSc' n (n + 1) (n + 2)
          (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).toLinearEquiv.symm
    · have : Subsingleton ((polynomialLaurentCechComplex (K := K) (I := I) m).homology (n + 1)) :=
        ModuleCat.subsingleton_of_isZero
          (polynomialLaurentCechComplex_homology_isZero_of_ne_top (K := K) (I := I) m n htop)
      exact Module.FinitePresentation.of_subsingleton _

/-- **Finite presentation for shifted free modules**: for a finite shifted free graded module
`⊕_a K[T](-δ a)`, every coordinate Čech cohomology module is finitely presented over `K`. -/
theorem finitePresentation_shiftedFree_homology {A : Type u} [Fintype A] [DecidableEq A]
    (δ : A → ℤ) (m : ℤ) (p : ℕ) :
    Module.FinitePresentation K
      ((homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
        (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ)
        (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m).homology
          p) := by
  have : ∀ a, Module.FinitePresentation K ((subsetCechComplex
      (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) (m - δ a))).homology p) := by
    intro a
    have := finitePresentation_polynomialLaurentCechComplex_homology (K := K) (I := I) (m - δ a) p
    exact Module.FinitePresentation.of_equiv (HomologicalComplex.homologyMapIso
      (polynomialCoordinateHomogeneousCechLaurentIso (m - δ a)) p).toLinearEquiv.symm
  have : Module.FinitePresentation K ((subsetCechComplex (actualModuleSubsetDiagramPi
      (fun a => polynomialCoordinateHomogeneousDiagram (K := K) (I := I) (m - δ a)))).homology p) :=
    Module.FinitePresentation.of_equiv (actualFiniteProductCechHomologyPiIso _ p).toLinearEquiv.symm
  exact Module.FinitePresentation.of_equiv (HomologicalComplex.homologyMapIso
    (finiteShiftedPolynomialCoordinateCechProductIso (K := K) (I := I) δ m) p).toLinearEquiv.symm

end Laurent

end

end DeJongAlterations.StableModification.Cohomology
