import DeJongAlterations.StableModification.Valuation.MainInterface
import DeJongAlterations.StableModification.Valuation.DVRCoordinate
import DeJongAlterations.StableModification.Valuation.FunctionField.Places
import DeJongAlterations.StableModification.LocalUniformization.GlobalBase

/-!
# The uniformization property at the call site of Proposition 4.3.3

Temkin's Proposition 4.3.3 (`locunifprop`, M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), `semi-stable.tex` lines 3048–3081) applies Theorem 2.1.8
(`valunif`, l. 2056–2061) and Lemma 2.1.1 (`finhtlem`) at l. 3059–3061 to a valuation ring `O` of
the function field `L` of a curve over a valuation ring `R ⊆ K`. The integrated form of this
black box is `Valuation.uniformizationEtaleStatement` (lane MAIN-VAL), the **uniformization
property** (`def:sm-uniformization-property`, a pointer to `Valuation.UniformizationEtaleStatement`).
This file discharges its hypotheses `Valuation.UniformizationHypotheses K L O` at the call site
(`uniformizationHypotheses_of_le`, blueprint `lem:sm-lu-curve-hypotheses`):

* finite height of `O ∩ K`: it is an overring of `R`, which has finite height;
* equal characteristic: passes from `R` to its overrings (`expChar_residueField_of_le`);
* `L/K` finitely generated with a separating transcendence element: hypotheses (for the function
  field of a curve of finite type with smooth generic fibre);
* the centre condition: if `K·O ≠ L`, then `K·O` is a place of the function field of one variable
  `L/K`, hence a discrete valuation ring (`IsPlace.isDiscreteValuationRing`), and its residue field
  is `K` under the hypothesis that all places of `L/K` have residue field `K`
  (`AllPlacesRational`), which holds for `K` algebraically closed
  (`allPlacesRational_of_isAlgClosed`).

## The centre condition for separably closed `K`

The integrated black box asks the residue field of `K·O` to be `K`. Temkin's Theorem 2.1.8 only
asks `K·O` to be centred on a smooth point of the normal projective model; for `K` separably
closed but not perfect, a smooth closed point can have a purely inseparable residue field
(`𝔸¹_K` at `T^p - c`, `c ∉ K^p`), and Temkin's proof treats this case separately (l. 2190–2196).
Hence the hypothesis `AllPlacesRational K L` below; see the blueprint remark
`rem:sm-lu-curve-literature`.
-/

noncomputable section

open IsLocalRing
open scoped IntermediateField

universe u v

namespace DeJongAlterations.StableModification.LocalUniformization.Curve

open DeJongAlterations.StableModification.Valuation
open Valuation.FunctionField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- **All places of `L/K` have residue field `K`**: every valuation ring `D ≠ L` of `L`
containing `K` has residue field `K` (true for `K` algebraically closed and `L/K` a function field
of one variable). -/
def AllPlacesRational : Prop :=
  ∀ (D : ValuationSubring L) (hD : ∀ c : K, algebraMap K L c ∈ D), D ≠ ⊤ →
    Function.Surjective fun c : K ↦ residue D ⟨algebraMap K L c, hD c⟩

variable {K L}

/-- `L/K` is a function field of one variable when it is finitely generated with a separating
transcendental element. -/
theorem isFunctionFieldOneVar_of_separating (hfg : (⊤ : IntermediateField K L).FG) {x : L}
    (hx : Transcendental K x) [Algebra.IsSeparable K⟮x⟯ L] : IsFunctionFieldOneVar K L := by
  have : Algebra.IsAlgebraic K⟮x⟯ L := Algebra.IsSeparable.isAlgebraic _ _
  have := DVRCoordinate.finiteDimensional_adjoin_of_transcendental hfg (y := x)
  exact IsFunctionFieldOneVar.of_finiteDimensional_adjoin hx

/-- For `K` algebraically closed, all places of a function field of one variable are rational. -/
theorem allPlacesRational_of_isAlgClosed [IsAlgClosed K] (hfg : (⊤ : IntermediateField K L).FG)
    (hsep : ∃ x : L, Transcendental K x ∧ Algebra.IsSeparable K⟮x⟯ L) :
    AllPlacesRational K L := by
  obtain ⟨x, hx, hxs⟩ := hsep
  have hF := isFunctionFieldOneVar_of_separating hfg hx
  intro D hD hne
  exact IsPlace.residue_surjective hF ⟨hD, hne⟩

/-- **The hypotheses of the uniformization property at the call site** (blueprint
`lem:sm-lu-curve-hypotheses`; Temkin, proof of Proposition 4.3.3, l. 3059–3061). Let `R` be a
valuation ring of finite height of the separably closed field `K`, of equal characteristic, `L/K`
finitely generated with a separating transcendence element, all places of `L/K` rational, and
`O` a valuation ring of `L` with `R ⊆ O ∩ K`. Then `O` satisfies `UniformizationHypotheses`. -/
theorem uniformizationHypotheses_of_le [IsSepClosed K] {R : ValuationSubring K}
    [Finite (PrimeSpectrum R)] (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField R) p)
    (hfg : (⊤ : IntermediateField K L).FG)
    (hsep : ∃ x : L, Transcendental K x ∧ Algebra.IsSeparable K⟮x⟯ L)
    (hrat : AllPlacesRational K L) (O : ValuationSubring L)
    (hRO : R ≤ O.comap (algebraMap K L)) : UniformizationHypotheses K L O where
  isSepClosed := inferInstance
  finite_primeSpectrum := finite_primeSpectrum R _ hRO
  expChar := by
    obtain ⟨p, hK, hR⟩ := hchar
    exact ⟨p, hK, MainUniformization.expChar_residueField_of_le hRO⟩
  fg := hfg
  exists_separating := hsep
  center := by
    by_cases h : baseLocalization K O = ⊤
    · exact Or.inl h
    right
    obtain ⟨x, hx, hxs⟩ := hsep
    have hF := isFunctionFieldOneVar_of_separating hfg hx
    have hP : IsPlace K (baseLocalization K O) := ⟨algebraMap_mem_baseLocalization K O, h⟩
    refine ⟨hP.isDiscreteValuationRing hF, (RingHom.injective _), fun z ↦ ?_⟩
    obtain ⟨c, hc⟩ := hrat _ (algebraMap_mem_baseLocalization K O) h z
    refine ⟨c, ?_⟩
    rw [← hc]
    rfl

/-- **The uniformization property at the call site**: under the hypotheses of
`uniformizationHypotheses_of_le`, there is `T ∈ L` transcendental over `K` such that `O` is
standard étale over `O ∩ K(T)` (Temkin, Theorem 2.1.8 with Lemma 2.1.1, as integrated in
`Valuation.uniformizationEtaleStatement`). -/
theorem exists_isStandardEtale_of_le [IsSepClosed K] {R : ValuationSubring K}
    [Finite (PrimeSpectrum R)] (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField R) p)
    (hfg : (⊤ : IntermediateField K L).FG)
    (hsep : ∃ x : L, Transcendental K x ∧ Algebra.IsSeparable K⟮x⟯ L)
    (hrat : AllPlacesRational K L) (O : ValuationSubring L)
    (hRO : R ≤ O.comap (algebraMap K L)) :
    ∃ T : L, Transcendental K T ∧
      Algebra.IsStandardEtale (O.comap (algebraMap K⟮T⟯ L)) O :=
  (uniformizationHypotheses_of_le hchar hfg hsep hrat O hRO).uniformizationConclusion

end DeJongAlterations.StableModification.LocalUniformization.Curve
