import DeJongAlterations.Algebra.NodeFormalMorseCoefficientLimit
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Actual complete-local evaluation from native nilpotent quotient substitutions

The chosen actual target coordinates belong to the original ideal `J`.
Native substitutions are used only modulo its powers, where the coordinate
constants are actually nilpotent. The complete target map preserves the
original coefficient algebra and chosen actual coordinates.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFlatPresentation

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {σ : Type w} [Finite σ]

/-- The actual constant coordinate series in the literal target quotient. -/
def quotientCoordinates (J : Ideal B) (b : σ → B) (N : ℕ) :
    σ → MvPowerSeries Empty (B ⧸ J ^ N) :=
  fun i => C (Ideal.Quotient.mk (J ^ N) (b i))

/-- Original ideal membership supplies genuine nilpotence in every finite target quotient. -/
theorem quotientCoordinates_hasSubst (J : Ideal B) (b : σ → B)
    (hb : ∀ i, b i ∈ J) (N : ℕ) : HasSubst (quotientCoordinates J b N) where
  const_coeff i := by
    refine ⟨N, ?_⟩
    simp only [quotientCoordinates, constantCoeff_C]
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow (hb i) N)
  coeff_zero _ := Set.toFinite _

/-- Native quotient-level evaluation after the literal original coefficient map. -/
def finiteRingEvaluation (J : Ideal B) (b : σ → B) (hb : ∀ i, b i ∈ J) (N : ℕ) :
    MvPowerSeries σ A →+* B ⧸ J ^ N :=
  (constantCoeff.comp
    (MvPowerSeries.substAlgHom (R := B ⧸ J ^ N) (S := B ⧸ J ^ N)
      (quotientCoordinates_hasSubst J b hb N)).toRingHom).comp
    (MvPowerSeries.map ((Ideal.Quotient.mk (J ^ N)).comp (algebraMap A B)))

@[simp]
theorem finiteRingEvaluation_C (J : Ideal B) (b : σ → B) (hb : ∀ i, b i ∈ J)
    (N : ℕ) (a : A) :
    finiteRingEvaluation J b hb N (C a) = Ideal.Quotient.mk (J ^ N) (algebraMap A B a) := by
  simp [finiteRingEvaluation, RingHom.comp_apply, MvPowerSeries.substAlgHom_apply]

@[simp]
theorem finiteRingEvaluation_X (J : Ideal B) (b : σ → B) (hb : ∀ i, b i ∈ J)
    (N : ℕ) (i : σ) :
    finiteRingEvaluation J b hb N (X i : MvPowerSeries σ A) = Ideal.Quotient.mk (J ^ N) (b i) := by
  unfold finiteRingEvaluation
  simp only [RingHom.comp_apply, MvPowerSeries.map_X]
  change constantCoeff (MvPowerSeries.substAlgHom (R := B ⧸ J ^ N) (S := B ⧸ J ^ N)
    (quotientCoordinates_hasSubst J b hb N) (X i)) = _
  rw [MvPowerSeries.substAlgHom_X]
  rfl

/-- Finite evaluation preserves the original actual coefficient algebra. -/
def evaluationAt (J : Ideal B) (b : σ → B) (hb : ∀ i, b i ∈ J) (N : ℕ) :
    MvPowerSeries σ A →ₐ[A] B ⧸ J ^ N where
  toRingHom := finiteRingEvaluation J b hb N
  commutes' a := by
    change finiteRingEvaluation J b hb N (C a) = algebraMap A (B ⧸ J ^ N) a
    rw [finiteRingEvaluation_C]
    rfl

/-- Every native finite evaluation commutes with the actual quotient transition. -/
theorem finiteRingEvaluation_compatible (J : Ideal B) (b : σ → B)
    (hb : ∀ i, b i ∈ J) {M N : ℕ} (hMN : M ≤ N) (g : MvPowerSeries σ A) :
    Ideal.Quotient.factorPow J hMN (finiteRingEvaluation J b hb N g) =
      finiteRingEvaluation J b hb M g := by
  unfold finiteRingEvaluation
  simp only [RingHom.comp_apply]
  change Ideal.Quotient.factorPow J hMN
    (constantCoeff (MvPowerSeries.substAlgHom (R := B ⧸ J ^ N) (S := B ⧸ J ^ N)
      (quotientCoordinates_hasSubst J b hb N)
      (MvPowerSeries.map ((Ideal.Quotient.mk (J ^ N)).comp (algebraMap A B)) g))) =
    constantCoeff (MvPowerSeries.substAlgHom (R := B ⧸ J ^ M) (S := B ⧸ J ^ M)
      (quotientCoordinates_hasSubst J b hb M)
      (MvPowerSeries.map ((Ideal.Quotient.mk (J ^ M)).comp (algebraMap A B)) g))
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply]
  rw [← constantCoeff_map,
    MvPowerSeries.map_subst (quotientCoordinates_hasSubst J b hb N)]
  have hc : (fun i => MvPowerSeries.map (Ideal.Quotient.factorPow J hMN) (quotientCoordinates J b N i)) =
      quotientCoordinates J b M := by
    funext i
    simp [quotientCoordinates]
  rw [hc]
  congr 2

theorem evaluationAt_compatible (J : Ideal B) (b : σ → B) (hb : ∀ i, b i ∈ J)
    {M N : ℕ} (hMN : M ≤ N) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hMN)).comp (evaluationAt J b hb N) =
      evaluationAt J b hb M := by
  apply AlgHom.ext
  intro g
  exact finiteRingEvaluation_compatible J b hb hMN g

/-- The actual complete-target ring map from the internally compatible native finite evaluations. -/
def evaluationRingHom (J : Ideal B) [IsAdicComplete J B] (b : σ → B) (hb : ∀ i, b i ∈ J) :
    MvPowerSeries σ A →+* B :=
  IsAdicComplete.liftRingHom J (fun N => finiteRingEvaluation (A := A) J b hb N)
    (fun hMN => RingHom.ext (finiteRingEvaluation_compatible J b hb hMN))

@[simp]
theorem evaluationRingHom_reduction (J : Ideal B) [IsAdicComplete J B]
    (b : σ → B) (hb : ∀ i, b i ∈ J) (N : ℕ) (g : MvPowerSeries σ A) :
    Ideal.Quotient.mk (J ^ N) (evaluationRingHom J b hb g) = finiteRingEvaluation J b hb N g :=
  IsAdicComplete.mk_liftRingHom J (fun N => finiteRingEvaluation (A := A) J b hb N)
    (fun hMN => RingHom.ext (finiteRingEvaluation_compatible J b hb hMN)) N g

/-- The actual original coefficient-preserving algebra map, with no evaluation certificate input. -/
def evaluation (J : Ideal B) [IsAdicComplete J B] (b : σ → B) (hb : ∀ i, b i ∈ J) :
    MvPowerSeries σ A →ₐ[A] B where
  toRingHom := evaluationRingHom J b hb
  commutes' a := by
    change evaluationRingHom J b hb (C a) = algebraMap A B a
    apply NodeFormalMorse.CoefficientLimit.scalar_ext J
    intro N
    rw [evaluationRingHom_reduction, finiteRingEvaluation_C]

@[simp]
theorem evaluation_reduction (J : Ideal B) [IsAdicComplete J B]
    (b : σ → B) (hb : ∀ i, b i ∈ J) (N : ℕ) (g : MvPowerSeries σ A) :
    Ideal.Quotient.mk (J ^ N) (evaluation J b hb g) = finiteRingEvaluation J b hb N g :=
  evaluationRingHom_reduction J b hb N g

@[simp]
theorem evaluation_C (J : Ideal B) [IsAdicComplete J B]
    (b : σ → B) (hb : ∀ i, b i ∈ J) (a : A) : evaluation J b hb (C a) = algebraMap A B a := by
  apply NodeFormalMorse.CoefficientLimit.scalar_ext J
  intro N
  rw [evaluation_reduction, finiteRingEvaluation_C]

@[simp]
theorem evaluation_X (J : Ideal B) [IsAdicComplete J B]
    (b : σ → B) (hb : ∀ i, b i ∈ J) (i : σ) :
    evaluation J b hb (X i : MvPowerSeries σ A) = b i := by
  apply NodeFormalMorse.CoefficientLimit.scalar_ext J
  intro N
  rw [evaluation_reduction, finiteRingEvaluation_X]

/-- The actual evaluation sends the original variable ideal into the original target ideal. -/
theorem evaluation_variables_image_le (J : Ideal B) [IsAdicComplete J B]
    (b : σ → B) (hb : ∀ i, b i ∈ J) :
    (Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ A)))).map
      (evaluation J b hb).toRingHom ≤ J := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change evaluation J b hb (X i : MvPowerSeries σ A) ∈ J
  rw [evaluation_X]
  exact hb i

/-- Continuity uses actual ideal powers, and does not assume any global native substitution. -/
theorem evaluation_continuous (J : Ideal B) [IsAdicComplete J B]
    (b : σ → B) (hb : ∀ i, b i ∈ J) :
    @Continuous (MvPowerSeries σ A) B
      (Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ A)))).adicTopology
      J.adicTopology (evaluation J b hb) := by
  let : WithIdeal (MvPowerSeries σ A) := ⟨Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ A)))⟩
  let : WithIdeal B := ⟨J⟩
  have hmap := evaluation_variables_image_le (A := A) (σ := σ) J b hb
  have hc := WithIdeal.uniformContinuous_of_map_le
    (R := MvPowerSeries σ A) (S := B) (f := (evaluation (A := A) J b hb).toRingHom) hmap
  exact hc.continuous

end DeJongAlterations.Algebra.NodeFlatPresentation
