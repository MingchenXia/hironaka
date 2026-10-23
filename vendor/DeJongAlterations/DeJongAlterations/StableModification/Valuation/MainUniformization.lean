import DeJongAlterations.StableModification.Valuation.MainUniformizationAnalytic
import DeJongAlterations.StableModification.Valuation.MainUniformizationHeight
import DeJongAlterations.StableModification.Valuation.SepClosed
import DeJongAlterations.StableModification.Valuation.FunctionField.PoleNorm

/-!
# Uniformization of one-dimensional valued fields (Temkin, Theorem 2.1.8)

This file proves Theorem 2.1.8 (`valunif`) of M. Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), §2.1–§2.2 (`semi-stable.tex`, statement lines 2056–2061,
proof lines 2177–2232), in the form of the interface `UniformizationHypotheses`
(`InterfaceStatement.lean`) and in the strengthened form used for the induction (plan
`PLAN-SM-VAL.md`, node M2): there are `T ∈ L` transcendental over `K` and a
standard-unramified generator `y` of `L/K(T)` at `O` which is a unit of `O`.
Blueprint chapter `sm-val-main.tex`, `thm:sm-val-uniformization`.

## The proof

By induction on the height `h` of `O ∩ K` (finite by hypothesis).

* **Unbounded case** (`K·O ≠ L`; Temkin l. 2188–2196): `K·O` is a discrete valuation ring with
  residue field `K`, and a uniformizer is an étale coordinate (`DVRCoordinate`).
* **Bounded, `h = 0`** (l. 2201–2203): then `O = L` and a separating transcendental element
  works.
* **Bounded, `h > 0`** (l. 2205–2232): `O` has finite height
  (`finite_primeSpectrum_of_trdeg_le_one`); let `O₁` be its height-one coarsening, so that `O` is composed from `O₁` and the valuation ring
  `Õ = O/𝔪_{O₁}` of `κ(O₁)`; `O₁ ∩ K ≠ K` by boundedness.
  - If `κ(O₁) = κ(O₁ ∩ K)` (l. 2213–2223), Theorem 2.1.10(i)(ii), density and decompletion give
    `x` with a generator of residue `1` at `O₁` (`exists_adapted_of_surjective`), and the
    composition criterion transports it to `O`.
  - Otherwise (l. 2224–2232), `κ(O₁)/κ(O₁ ∩ K)` is a function field of one variable over an
    algebraically closed field (`finiteDimensional_residueField_adjoin`, the fix of LI-2), so the
    residue extension satisfies the hypotheses with smaller height
    (`uniformizationHypotheses_residue`); the induction hypothesis gives `Tr` and a unit generator
    `z̃` of `κ(O₁)/κ(O₁ ∩ K)(Tr)` at `Õ`. A lift `T ∉ K Lᵖ` of `Tr` (`exists_lift_of_rankOne`), the
    Gauss lemma (`residueFieldAdjoinEquiv`), Theorem 2.1.10(iii), decompletion with prescribed
    residue `z̃` (`exists_adapted_of_transcendental`) and the composition criterion finish.

## Main results

* `StdUnramifiedConclusion`: the strengthened conclusion.
* `stdUnramifiedConclusion` (**Theorem 2.1.8**): `UniformizationHypotheses K L O` implies
  `StdUnramifiedConclusion K L O`.
-/

noncomputable section

open IsLocalRing Polynomial
open scoped IntermediateField

namespace DeJongAlterations.StableModification.Valuation.MainUniformization

open DeJongAlterations.StableModification.Valuation.FunctionField

universe u v

/-- **The strengthened conclusion of Theorem 2.1.8** (plan `PLAN-SM-VAL.md`, node M2): some
`T ∈ L` transcendental over `K` and a standard-unramified generator `y` of `L/K(T)` at `O` which
is a unit of `O`. -/
def StdUnramifiedConclusion (K L : Type*) [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring L) : Prop :=
  ∃ T : L, Transcendental K T ∧ ∃ y : L, IsStdUnramifiedGenerator K⟮T⟯ O y ∧ O.valuation y = 1

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring L}

/-! ### The unbounded case and height zero -/

set_option linter.style.haveILetI false in
/-- **The unbounded case** (Temkin, l. 2188–2196): if `K·O` is a discrete valuation ring with
residue field `K`, a uniformizer `x` of `K·O` has a unit standard-unramified generator. -/
theorem stdUnramifiedConclusion_of_isDiscreteValuationRing (h : UniformizationHypotheses K L O)
    (hdvr : IsDiscreteValuationRing (baseLocalization K O))
    (hres : Function.Bijective ((residue (baseLocalization K O)).comp
      (toBaseLocalization K O))) :
    StdUnramifiedConclusion K L O := by
  set D := baseLocalization K O
  have hK : ∀ c : K, algebraMap K L c ∈ D := algebraMap_mem_baseLocalization K O
  have hres' : ∀ z : ResidueField D, ∃ c : K, residue D ⟨algebraMap K L c, hK c⟩ = z :=
    fun z ↦ hres.2 z
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D
  obtain ⟨t, ht, hsep⟩ := h.exists_separating
  have hx : (ϖ : L) ∈ D := ϖ.2
  have hirr : Irreducible (⟨(ϖ : L), hx⟩ : D) := hϖ
  obtain ⟨htx, hfin, hsepx⟩ :=
    DVRCoordinate.finiteDimensional_isSeparable_of_irreducible hK hres' hx hirr h.fg ht
  haveI := hfin
  haveI := hsepx
  obtain ⟨y, hy, hy1, hfac⟩ := DVRCoordinate.exists_isStdUnramifiedGenerator_dvr hK hres' hx hirr
  have hO : O ≤ D := le_baseLocalization K O
  have hyO := DVRCoordinate.isStdUnramifiedGenerator_of_le hK hres' hy hy1 hfac hO
  refine ⟨_, htx, y, hyO, ?_⟩
  have := (valuation_compose_eq_one_iff D (decompose D hO) ⟨y, hy.mem⟩).mpr
    ⟨(residue_ne_zero_iff_isUnit _).mp (by rw [hy1]; exact one_ne_zero), by rw [hy1, map_one]⟩
  rwa [compose_decompose] at this

set_option linter.style.haveILetI false in
/-- **Height zero** (Temkin, l. 2201–2203): if `K·O = L` and `O ∩ K = K`, then `O = L` and a
separating transcendental element works. -/
theorem stdUnramifiedConclusion_of_comap_eq_top (h : UniformizationHypotheses K L O)
    (hb : baseLocalization K O = ⊤) (hA : O.comap (algebraMap K L) = ⊤) :
    StdUnramifiedConclusion K L O := by
  have hO : O = ⊤ := by rw [← baseLocalization_eq_self K O hA]; exact hb
  subst hO
  obtain ⟨t, ht, hsep⟩ := h.exists_separating
  haveI : Algebra.IsAlgebraic K⟮t⟯ L := Algebra.IsSeparable.isAlgebraic _ _
  haveI := DVRCoordinate.finiteDimensional_adjoin_of_transcendental h.fg (y := t)
  obtain ⟨y, hy0, hy⟩ := exists_isStdUnramifiedGenerator_top (F₁ := K⟮t⟯) (l := L)
  refine ⟨t, ht, y, hy, ?_⟩
  exact ((⊤ : ValuationSubring L).valuation_eq_one_iff ⟨y, trivial⟩).mp
    (isUnit_iff_ne_zero.mpr fun h0 ↦ hy0 (congrArg Subtype.val h0))

/-! ### The height-one step -/

/-- Surjectivity of `κ(O₁ ∩ K) → κ(O₁)` passes to `κ(O₁ ∩ K(x)) → κ(O₁)`. -/
theorem surjective_algebraMap_residueField_adjoin {O₁ : ValuationSubring L} (x : L)
    (hsurj : Function.Surjective
      (algebraMap (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁))) :
    Function.Surjective
      (algebraMap (ResidueField (O₁.comap (algebraMap K⟮x⟯ L))) (ResidueField O₁)) := by
  intro z
  obtain ⟨a, rfl⟩ := hsurj z
  obtain ⟨a, rfl⟩ := residue_surjective a
  exact ⟨_, algebraMap_residue_comap (T := x) a⟩

/-- A standard-unramified generator at `O` composed from `O₁` and `Õ` is a unit of `O` when its
residue is a unit of `Õ`. -/
theorem valuation_eq_one_of_le {O₁ : ValuationSubring L} (hle : O ≤ O₁) {y : L} (hy : y ∈ O₁)
    (hy1 : (decompose O₁ hle).valuation (residue O₁ ⟨y, hy⟩) = 1) : O.valuation y = 1 := by
  have h0 : residue O₁ ⟨y, hy⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy1
    exact zero_ne_one hy1
  have := (valuation_compose_eq_one_iff O₁ (decompose O₁ hle) ⟨y, hy⟩).mpr
    ⟨(residue_ne_zero_iff_isUnit _).mp h0, hy1⟩
  rwa [compose_decompose] at this

set_option linter.style.haveILetI false in
/-- **The height-one step, trivial residue extension** (Temkin, l. 2213–2223): if `O ⊆ O₁` with
`O₁` of rank one, `O₁ ∩ K ≠ K` and `κ(O₁) = κ(O₁ ∩ K)`, the conclusion holds for `O`. -/
theorem stdUnramifiedConclusion_of_surjective (h : UniformizationHypotheses K L O)
    {O₁ : ValuationSubring L} [O₁.valuation.RankOne] (hle : O ≤ O₁)
    (hA₁ : O₁.comap (algebraMap K L) ≠ ⊤) (p : ℕ) [ExpChar K p]
    [ExpChar (ResidueField (O₁.comap (algebraMap K L))) p]
    (hsurj : Function.Surjective
      (algebraMap (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁))) :
    StdUnramifiedConclusion K L O := by
  haveI := h.isSepClosed
  obtain ⟨t, ht, hsep⟩ := h.exists_separating
  haveI : Algebra.IsAlgebraic K⟮t⟯ L := Algebra.IsSeparable.isAlgebraic _ _
  haveI := DVRCoordinate.finiteDimensional_adjoin_of_transcendental h.fg (y := t)
  obtain ⟨x, hxK, -, -, y, hy, hy1, hfac⟩ := exists_adapted_of_surjective hA₁ p h.fg ht hsurj
  set B' := decompose O₁ hle
  have hres : IsStdUnramifiedGenerator (ResidueField (O₁.comap (algebraMap K⟮x⟯ L))) B'
      (residue O₁ ⟨y, hy.mem⟩) := by
    rw [hy1]
    exact isStdUnramifiedGenerator_one_of_surjective B'
      (surjective_algebraMap_residueField_adjoin x hsurj)
  have hunit : B'.valuation (residue O₁ ⟨y, hy.mem⟩) = 1 := by rw [hy1, map_one]
  have hfac' : ∃ m : ℕ, (minpoly (O₁.comap (algebraMap K⟮x⟯ L)) y).map
      (residue (O₁.comap (algebraMap K⟮x⟯ L))) =
      minpoly (ResidueField (O₁.comap (algebraMap K⟮x⟯ L))) (residue O₁ ⟨y, hy.mem⟩) * X ^ m := by
    rw [hy1]
    exact hfac
  have hcomp := hy.compose_of_adapted hres hunit hfac'
  rw [compose_decompose] at hcomp
  exact ⟨x, hxK, y, hcomp, valuation_eq_one_of_le hle hy.mem hunit⟩

/-! ### The residue extension -/

section Residue

variable {O₁ : ValuationSubring L} (hle : O ≤ O₁)

/-- The trace of `O ∩ K` on the residue field: `Õ ∩ κ(O₁ ∩ K)` is induced by `O ∩ K`. -/
theorem comap_decompose_eq :
    (decompose O₁ hle).comap
        (algebraMap (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁)) =
      decompose (O₁.comap (algebraMap K L)) (comap_le_comap (algebraMap K L) hle) :=
  (comap_decompose (K := K) O₁ hle).symm

/-- **The induction on the height** (Temkin, l. 2226–2227): the base of the residue extension has
smaller height. -/
theorem height_comap_decompose_lt [Finite (PrimeSpectrum (O.comap (algebraMap K L)))]
    (hA₁ : O₁.comap (algebraMap K L) ≠ ⊤) :
    height ((decompose O₁ hle).comap
        (algebraMap (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁))) <
      height (O.comap (algebraMap K L)) := by
  rw [comap_decompose_eq]
  exact height_decompose_lt _ hA₁

set_option linter.style.haveILetI false in
/-- **The residue extension is a function field of one variable** (Temkin, l. 2224–2227 and the
fix of LI-2): if `κ(O₁) ≠ κ(O₁ ∩ K)` with `O₁ ∩ K ≠ K` and `L/K` finitely generated of
transcendence degree one, then `κ(O₁)/κ(O₁ ∩ K)` is finitely generated of transcendence degree
one. -/
theorem isFunctionFieldOneVar_residueField [IsSepClosed K] (hfg : (⊤ : IntermediateField K L).FG)
    {t : L} (ht : Transcendental K t) [Algebra.IsSeparable K⟮t⟯ L]
    (hA₁ : O₁.comap (algebraMap K L) ≠ ⊤)
    (hnsurj : ¬ Function.Surjective
      (algebraMap (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁))) :
    IsFunctionFieldOneVar (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁) := by
  haveI := isAlgClosed_residueField_of_ne_top _ hA₁
  obtain ⟨τ, hτ⟩ : ∃ τ : ResidueField O₁, τ ∉ (algebraMap
      (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁)).range := by
    by_contra hc
    push Not at hc
    exact hnsurj fun z ↦ hc z
  have htr : Transcendental (ResidueField (O₁.comap (algebraMap K L))) τ :=
    fun halg ↦ hτ (mem_range_of_isAlgebraic halg)
  obtain ⟨t₁, rfl⟩ := residue_surjective τ
  have ht₁ : Transcendental K (t₁ : L) := transcendental_of_transcendental_residue t₁.2 htr
  haveI : Algebra.IsAlgebraic K⟮(t₁ : L)⟯ L :=
    DVRCoordinate.isAlgebraic_adjoin_of_transcendental ht (Algebra.IsSeparable.isAlgebraic _ _)
      ht₁
  haveI := DVRCoordinate.finiteDimensional_adjoin_of_transcendental hfg (y := (t₁ : L))
  haveI := finiteDimensional_residueField_adjoin t₁.2 htr
  exact IsFunctionFieldOneVar.of_finiteDimensional_adjoin htr

set_option linter.style.haveILetI false in
/-- **The residue extension satisfies the hypotheses of Theorem 2.1.8** (Temkin, l. 2224–2227;
the centre condition holds because `κ(O₁ ∩ K)` is algebraically closed, plan node F1). -/
theorem uniformizationHypotheses_residue (h : UniformizationHypotheses K L O)
    (hA₁ : O₁.comap (algebraMap K L) ≠ ⊤)
    (hnsurj : ¬ Function.Surjective
      (algebraMap (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁))) :
    UniformizationHypotheses (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁)
      (decompose O₁ hle) := by
  haveI := h.isSepClosed
  haveI := h.finite_primeSpectrum
  obtain ⟨p, hpK, hpA⟩ := h.expChar
  obtain ⟨t, ht, hsep⟩ := h.exists_separating
  haveI := isAlgClosed_residueField_of_ne_top _ hA₁
  have hF := isFunctionFieldOneVar_residueField h.fg ht hA₁ hnsurj
  have hAA₁ := comap_le_comap (algebraMap K L) hle
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [comap_decompose_eq]
    exact finite_primeSpectrum_decompose _
  · refine ⟨p, expChar_residueField_of_le hAA₁, ?_⟩
    rw [comap_decompose_eq]
    exact expChar_residueField_decompose hAA₁
  · haveI := hF.essFiniteType
    exact IntermediateField.fg_top _ _
  · obtain ⟨τ, hτ, -, hτsep⟩ := hF.exists_isSeparable
    exact ⟨τ, hτ, hτsep⟩
  · by_cases hD : baseLocalization (ResidueField (O₁.comap (algebraMap K L))) (decompose O₁ hle) = ⊤
    · exact Or.inl hD
    · have hP : IsPlace (ResidueField (O₁.comap (algebraMap K L)))
          (baseLocalization (ResidueField (O₁.comap (algebraMap K L))) (decompose O₁ hle)) :=
        ⟨algebraMap_mem_baseLocalization _ _, hD⟩
      refine Or.inr ⟨hP.isDiscreteValuationRing hF, (RingHom.injective _), fun z ↦ ?_⟩
      obtain ⟨c, hc⟩ := hP.residue_surjective hF z
      exact ⟨c, hc⟩

set_option linter.style.haveILetI false in
/-- **The height-one step, transcendental residue case** (Temkin, l. 2224–2232): if `O ⊆ O₁`
with `O₁` of rank one and `O₁ ∩ K ≠ K`, `κ(O₁) ≠ κ(O₁ ∩ K)`, and the conclusion holds for the
residue extension `κ(O₁)/κ(O₁ ∩ K)` with the valuation ring `Õ = O/𝔪_{O₁}`, then it holds for
`O`. -/
theorem stdUnramifiedConclusion_of_residue (h : UniformizationHypotheses K L O)
    [O₁.valuation.RankOne] (hA₁ : O₁.comap (algebraMap K L) ≠ ⊤) (p : ℕ) [ExpChar K p]
    [ExpChar (ResidueField (O₁.comap (algebraMap K L))) p]
    (hIH : StdUnramifiedConclusion (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁)
      (decompose O₁ hle)) :
    StdUnramifiedConclusion K L O := by
  haveI := h.isSepClosed
  obtain ⟨t, ht, hsep⟩ := h.exists_separating
  haveI : Algebra.IsAlgebraic K⟮t⟯ L := Algebra.IsSeparable.isAlgebraic _ _
  haveI := DVRCoordinate.finiteDimensional_adjoin_of_transcendental h.fg (y := t)
  obtain ⟨Tr, hTr, z, hz, hz1⟩ := hIH
  obtain ⟨T₀, rfl⟩ := residue_surjective Tr
  obtain ⟨T, hT, hresT, hTK, hfinT, hsepT⟩ := exists_lift_of_rankOne hA₁ p h.fg ht T₀.2 hTr
  haveI := hfinT
  haveI := hsepT
  have htrT : Transcendental (ResidueField (O₁.comap (algebraMap K L)))
      (residue O₁ ⟨T, hT⟩) := by
    rw [hresT]
    exact hTr
  have hz₁ : IsStdUnramifiedGenerator (IntermediateField.adjoin
      (ResidueField (O₁.comap (algebraMap K L))) {residue O₁ ⟨T, hT⟩}) (decompose O₁ hle) z := by
    rw [hresT]
    exact hz
  -- change of base field along the Gauss lemma
  set e := residueFieldAdjoinEquiv hT htrT
  have hz' : IsStdUnramifiedGenerator (ResidueField (O₁.comap (algebraMap K⟮T⟯ L)))
      (decompose O₁ hle) z :=
    isStdUnramifiedGenerator_of_ringEquiv e.symm (fun a ↦ by
      rw [← coe_residueFieldAdjoinEquiv hT htrT, RingEquiv.apply_symm_apply]
      rfl) hz₁
  haveI : Algebra.IsSeparable (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) (ResidueField O₁) :=
    hz'.isSeparable
  have hz0 : z ≠ 0 := fun h0 ↦ by
    rw [h0, map_zero] at hz1
    exact zero_ne_one hz1
  obtain ⟨y, hy, hyres, hfac⟩ := exists_adapted_of_transcendental hA₁ p hT htrT hz0
    hz'.adjoin_eq_top hz'.isSeparable_elem
  have hres : IsStdUnramifiedGenerator (ResidueField (O₁.comap (algebraMap K⟮T⟯ L)))
      (decompose O₁ hle) (residue O₁ ⟨y, hy.mem⟩) := by
    rw [hyres]
    exact hz'
  have hunit : (decompose O₁ hle).valuation (residue O₁ ⟨y, hy.mem⟩) = 1 := by
    rw [hyres]
    exact hz1
  have hfac' : ∃ m : ℕ, (minpoly (O₁.comap (algebraMap K⟮T⟯ L)) y).map
      (residue (O₁.comap (algebraMap K⟮T⟯ L))) =
      minpoly (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) (residue O₁ ⟨y, hy.mem⟩) * X ^ m := by
    rw [hyres]
    exact hfac
  have hcomp := hy.compose_of_adapted hres hunit hfac'
  rw [compose_decompose] at hcomp
  exact ⟨T, hTK, y, hcomp, valuation_eq_one_of_le hle hy.mem hunit⟩

end Residue

/-! ### The induction -/

set_option linter.style.haveILetI false in
/-- **The induction step of Theorem 2.1.8**: the conclusion holds for `O` if it holds for every
extension satisfying the hypotheses whose base valuation ring has smaller height. -/
theorem stdUnramifiedConclusion_step {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {O : ValuationSubring L} (h : UniformizationHypotheses K L O)
    (IH : ∀ (K' : Type u) (L' : Type v) [Field K'] [Field L'] [Algebra K' L']
      (O' : ValuationSubring L'), UniformizationHypotheses K' L' O' →
        height (O'.comap (algebraMap K' L')) < height (O.comap (algebraMap K L)) →
          StdUnramifiedConclusion K' L' O') :
    StdUnramifiedConclusion K L O := by
  by_cases hb : baseLocalization K O = ⊤
  swap
  · obtain ⟨hdvr, hres⟩ := h.center.resolve_left hb
    exact stdUnramifiedConclusion_of_isDiscreteValuationRing h hdvr hres
  by_cases hA : O.comap (algebraMap K L) = ⊤
  · exact stdUnramifiedConclusion_of_comap_eq_top h hb hA
  haveI := h.isSepClosed
  haveI := h.finite_primeSpectrum
  obtain ⟨p, hpK, hpA⟩ := h.expChar
  -- `O` has finite height
  haveI : Finite (PrimeSpectrum O) :=
    finite_primeSpectrum_of_trdeg_le_one (K := K) O h.trdeg_eq_one.le
  have hO : O ≠ ⊤ := by
    rintro rfl
    exact hA (eq_top_iff.mpr fun c _ ↦ trivial)
  -- the height-one coarsening
  obtain ⟨P₁, hP₁, hht, -⟩ := exists_height_ofPrime_eq_one O hO
  set O₁ := O.ofPrime P₁.asIdeal
  letI : O₁.valuation.RankOne := rankOneOfHeightEqOne O₁ hht
  have hle : O ≤ O₁ := O.le_ofPrime P₁.asIdeal
  have hA₁ : O₁.comap (algebraMap K L) ≠ ⊤ := by
    intro hA₁
    have hK : ∀ c : K, algebraMap K L c ∈ O₁ := fun c ↦ by
      have : c ∈ O₁.comap (algebraMap K L) := hA₁ ▸ trivial
      exact this
    have htop : O₁ = ⊤ := top_unique (hb ▸ baseLocalization_le K O hle hK)
    exact hP₁ ((ofPrime_eq_top_iff O P₁.asIdeal).mp htop)
  haveI : ExpChar (ResidueField (O₁.comap (algebraMap K L))) p :=
    expChar_residueField_of_le (comap_le_comap (algebraMap K L) hle)
  by_cases hsurj : Function.Surjective
      (algebraMap (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁))
  · exact stdUnramifiedConclusion_of_surjective h hle hA₁ p hsurj
  · exact stdUnramifiedConclusion_of_residue hle h hA₁ p
      (IH _ _ _ (uniformizationHypotheses_residue hle h hA₁ hsurj)
        (height_comap_decompose_lt hle hA₁))

/-- **Temkin, Theorem 2.1.8** (uniformization of one-dimensional valued fields,
`semi-stable.tex` l. 2056–2061, proof l. 2177–2232; blueprint `thm:sm-val-uniformization`), in
the strengthened form of plan node M2: under `UniformizationHypotheses K L O` there are
`T ∈ L` transcendental over `K` and a standard-unramified generator `y` of `L/K(T)` at `O` with
`y` a unit of `O`. -/
theorem stdUnramifiedConclusion {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {O : ValuationSubring L} (h : UniformizationHypotheses K L O) :
    StdUnramifiedConclusion K L O := by
  suffices H : ∀ (n : ℕ) (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
      (O : ValuationSubring L), UniformizationHypotheses K L O →
        height (O.comap (algebraMap K L)) = n → StdUnramifiedConclusion K L O from
    H _ K L O h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K L _ _ _ O h hn
    exact stdUnramifiedConclusion_step h fun K' L' _ _ _ O' h' hlt ↦
      ih _ (hn ▸ hlt) K' L' O' h' rfl

end DeJongAlterations.StableModification.Valuation.MainUniformization
