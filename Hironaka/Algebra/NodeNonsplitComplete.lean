import Hironaka.Algebra.NodeNonsplitFiniteLevels
import Hironaka.Algebra.NodeFormalMorseComplete
import Hironaka.Algebra.NodeFormalMorseTopology
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The actual complete separated quadratic Morse automorphism

The only inputs are the original complete separated coefficient ring, ideal,
and original error coefficients. Every finite normal form and its compatibility
is constructed internally. The final map is the limit of the actual quotient
maps, not a native substitution with nonnilpotent constants over the base.
-/

noncomputable section

namespace Hironaka.Algebra.NodeNonsplit

open MvPowerSeries NodeFormalMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] (Q : Quadratic R)

/-- The internally constructed finite maps act as an actual automorphism on compatible families. -/
def compatibleEquiv (I : Ideal R) (H : Series R) (hH : ∀ d, coeff d H ∈ I) :
    CoefficientLimit.CompatibleSeries I (Fin 2) ≃ₐ[R]
      CoefficientLimit.CompatibleSeries I (Fin 2) where
  toFun f := ⟨fun N => (finiteState Q I H hH N).equiv (f.val N), by
    change CoefficientLimit.Compatible I (Fin 2) _
    intro M N hMN
    change MvPowerSeries.map (Ideal.Quotient.factorPow I hMN)
      ((finiteState Q I H hH N).equiv (f.val N)) = (finiteState Q I H hH M).equiv (f.val M)
    rw [(finiteState_compatible Q I H hH hMN).2.1]
    exact congrArg (finiteState Q I H hH M).equiv (CoefficientLimit.compatible I (Fin 2) f hMN)⟩
  invFun f := ⟨fun N => (finiteState Q I H hH N).equiv.symm (f.val N), by
    change CoefficientLimit.Compatible I (Fin 2) _
    intro M N hMN
    change MvPowerSeries.map (Ideal.Quotient.factorPow I hMN)
      ((finiteState Q I H hH N).equiv.symm (f.val N)) = (finiteState Q I H hH M).equiv.symm (f.val M)
    rw [(finiteState_compatible Q I H hH hMN).2.2]
    exact congrArg (finiteState Q I H hH M).equiv.symm (CoefficientLimit.compatible I (Fin 2) f hMN)⟩
  left_inv f := by
    apply Subtype.ext
    funext N
    exact (finiteState Q I H hH N).equiv.symm_apply_apply (f.val N)
  right_inv f := by
    apply Subtype.ext
    funext N
    exact (finiteState Q I H hH N).equiv.apply_symm_apply (f.val N)
  map_mul' f g := by
    apply Subtype.ext
    funext N
    exact map_mul (finiteState Q I H hH N).equiv (f.val N) (g.val N)
  map_add' f g := by
    apply Subtype.ext
    funext N
    exact map_add (finiteState Q I H hH N).equiv (f.val N) (g.val N)
  commutes' r := by
    apply Subtype.ext
    funext N
    change (finiteState Q I H hH N).equiv (algebraMap R (Series (R ⧸ I ^ N)) r) =
      algebraMap R (Series (R ⧸ I ^ N)) r
    simp only [MvPowerSeries.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
    simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
      (finiteState Q I H hH N).equiv.commutes (Ideal.Quotient.mk (I ^ N) r)

/-- The actual base-coefficient-preserving automorphism of the original series ring. -/
def completeEquiv (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) : Series R ≃ₐ[R] Series R :=
  ((CoefficientLimit.equivalence I (Fin 2)).trans (compatibleEquiv Q I H hH)).trans
    (CoefficientLimit.equivalence I (Fin 2)).symm

/-- The literal coefficient reduction of the limiting forward map is the internally computed finite map. -/
theorem completeEquiv_reduction (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) (completeEquiv Q I H hH f) =
      (finiteState Q I H hH N).equiv (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f) := by
  change MvPowerSeries.map (Ideal.Quotient.mk (I ^ N))
    ((CoefficientLimit.equivalence I (Fin 2)).symm
      (compatibleEquiv Q I H hH (CoefficientLimit.equivalence I (Fin 2) f))) = _
  rw [CoefficientLimit.equivalence_symm_reduction]
  rfl

/-- The actual limiting inverse has the corresponding literal finite inverse maps. -/
theorem completeEquiv_symm_reduction (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) ((completeEquiv Q I H hH).symm f) =
      (finiteState Q I H hH N).equiv.symm (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f) := by
  change MvPowerSeries.map (Ideal.Quotient.mk (I ^ N))
    ((CoefficientLimit.equivalence I (Fin 2)).symm
      ((compatibleEquiv Q I H hH).symm (CoefficientLimit.equivalence I (Fin 2) f))) = _
  rw [CoefficientLimit.equivalence_symm_reduction]
  rfl

@[simp]
theorem completeEquiv_C (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (r : R) : completeEquiv Q I H hH (C r) = C r := by
  simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    (completeEquiv Q I H hH).commutes r

/-- The actual constant smoothing parameter is the unique lift of the computed finite scalars. -/
def completeParameter (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) : R :=
  CoefficientLimit.scalarLimit I (fun N => (finiteState Q I H hH N).scalar)
    (fun hMN => (finiteState_compatible Q I H hH hMN).1)

@[simp]
theorem completeParameter_reduction (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) :
    Ideal.Quotient.mk (I ^ N) (completeParameter Q I H hH) = (finiteState Q I H hH N).scalar :=
  CoefficientLimit.mk_scalarLimit I (fun N => (finiteState Q I H hH N).scalar)
    (fun hMN => (finiteState_compatible Q I H hH hMN).1) N

/-- The limiting parameter actually belongs to the original base ideal. -/
theorem completeParameter_mem (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) : completeParameter Q I H hH ∈ I := by
  have hq := completeParameter_reduction Q I H hH 1
  rw [finiteState_one_scalar Q I H hH] at hq
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hq
  simpa only [pow_one] using hm

/-- The limiting automorphism reduces to the original identity on every series modulo `I`. -/
theorem completeEquiv_mod_ideal (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk I) (completeEquiv Q I H hH f) =
      MvPowerSeries.map (Ideal.Quotient.mk I) f := by
  apply reduction_of_pow_one
  rw [completeEquiv_reduction Q I H hH 1 f, finiteState_one_equiv Q I H hH]
  rfl

/-- The exact completed quadratic equation, proved through every original coefficient quotient. -/
theorem completeEquiv_equation (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) :
    completeEquiv Q I H hH (Q.series - H) = Q.series - C (completeParameter Q I H hH) := by
  apply CoefficientLimit.series_ext I (Fin 2)
  intro N
  rw [completeEquiv_reduction Q, finiteState_equation Q I H hH N]
  simp only [map_sub, Quadratic.map_series, MvPowerSeries.map_C, completeParameter_reduction Q]

/-- Both actual directions are continuous for the full base-and-variable adic topology. -/
theorem completeEquiv_continuous (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) :
    @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology
      (completeEquiv Q I H hH) ∧
    @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology
      (completeEquiv Q I H hH).symm :=
  ⟨continuous_fullIdeal I _ (completeEquiv_mod_ideal Q I H hH),
    continuous_symm_fullIdeal I _ (completeEquiv_mod_ideal Q I H hH)⟩

/-- Source-facing complete separated same-ring quadratic normal form, with no compatible-family output premise. -/
theorem exists_complete_normal_form (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) :
    ∃ (h : R) (e : Series R ≃ₐ[R] Series R), h ∈ I ∧
      e (Q.series - H) = Q.series - C h ∧
      (∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e f) = MvPowerSeries.map (Ideal.Quotient.mk I) f) ∧
      (∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e.symm f) = MvPowerSeries.map (Ideal.Quotient.mk I) f) ∧
      @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology e ∧
      @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology e.symm := by
  refine ⟨completeParameter Q I H hH, completeEquiv Q I H hH, completeParameter_mem Q I H hH,
    completeEquiv_equation Q I H hH, completeEquiv_mod_ideal Q I H hH,
    inverse_reduction_of_reduction I _ (completeEquiv_mod_ideal Q I H hH), ?_⟩
  exact completeEquiv_continuous Q I H hH

/-- The source-facing original coefficient statement has only the actual discriminant-unit hypothesis. -/
theorem exists_complete_quadratic_normal_form (I : Ideal R) [IsAdicComplete I R]
    (a0 a1 a2 : R) (hΔ : IsUnit (a1 ^ 2 - 4 * a0 * a2)) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) :
    ∃ (h : R) (e : Series R ≃ₐ[R] Series R), h ∈ I ∧
      e (C a0 * X 0 ^ 2 + C a1 * X 0 * X 1 + C a2 * X 1 ^ 2 - H) =
        C a0 * X 0 ^ 2 + C a1 * X 0 * X 1 + C a2 * X 1 ^ 2 - C h ∧
      (∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e f) = MvPowerSeries.map (Ideal.Quotient.mk I) f) ∧
      (∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e.symm f) = MvPowerSeries.map (Ideal.Quotient.mk I) f) ∧
      @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology e ∧
      @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology e.symm := by
  simpa only [Quadratic.series, Quadratic.value, Quadratic.map, Quadratic.ofCoefficients] using
    exists_complete_normal_form (Quadratic.ofCoefficients a0 a1 a2 hΔ) I H hH

/-- The paper's nonzero residue discriminant gives the actual lifted unit internally. -/
theorem unit_discriminant_of_residue [IsLocalRing R] (a0 a1 a2 : R)
    (hΔ : (IsLocalRing.residue R a1) ^ 2 - 4 * IsLocalRing.residue R a0 * IsLocalRing.residue R a2 ≠ 0) :
    IsUnit (a1 ^ 2 - 4 * a0 * a2) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  simpa only [map_sub, map_pow, map_mul, map_ofNat] using hΔ

end Hironaka.Algebra.NodeNonsplit
