import DeJongAlterations.Algebra.NodeFormalMorseFiniteLevels
import DeJongAlterations.Algebra.NodeFormalMorseTopology

/-!
# The actual complete separated split-node Morse automorphism

The only inputs are the original complete separated coefficient ring, ideal,
and original error coefficients. Every finite normal form and its compatibility
is constructed internally. The final map is the limit of the actual quotient
maps, not a native substitution with nonnilpotent constants over the base.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFormalMorse

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

/-- The internally constructed finite maps act as an actual automorphism on compatible families. -/
def compatibleEquiv (I : Ideal R) (H : Series R) (hH : ∀ d, coeff d H ∈ I) :
    CoefficientLimit.CompatibleSeries I (Fin 2) ≃ₐ[R]
      CoefficientLimit.CompatibleSeries I (Fin 2) where
  toFun f := ⟨fun N => (finiteState I H hH N).equiv (f.val N), by
    change CoefficientLimit.Compatible I (Fin 2) _
    intro M N hMN
    change MvPowerSeries.map (Ideal.Quotient.factorPow I hMN)
      ((finiteState I H hH N).equiv (f.val N)) = (finiteState I H hH M).equiv (f.val M)
    rw [(finiteState_compatible I H hH hMN).2.1]
    exact congrArg (finiteState I H hH M).equiv (CoefficientLimit.compatible I (Fin 2) f hMN)⟩
  invFun f := ⟨fun N => (finiteState I H hH N).equiv.symm (f.val N), by
    change CoefficientLimit.Compatible I (Fin 2) _
    intro M N hMN
    change MvPowerSeries.map (Ideal.Quotient.factorPow I hMN)
      ((finiteState I H hH N).equiv.symm (f.val N)) = (finiteState I H hH M).equiv.symm (f.val M)
    rw [(finiteState_compatible I H hH hMN).2.2]
    exact congrArg (finiteState I H hH M).equiv.symm (CoefficientLimit.compatible I (Fin 2) f hMN)⟩
  left_inv f := by
    apply Subtype.ext
    funext N
    exact (finiteState I H hH N).equiv.symm_apply_apply (f.val N)
  right_inv f := by
    apply Subtype.ext
    funext N
    exact (finiteState I H hH N).equiv.apply_symm_apply (f.val N)
  map_mul' f g := by
    apply Subtype.ext
    funext N
    exact map_mul (finiteState I H hH N).equiv (f.val N) (g.val N)
  map_add' f g := by
    apply Subtype.ext
    funext N
    exact map_add (finiteState I H hH N).equiv (f.val N) (g.val N)
  commutes' r := by
    apply Subtype.ext
    funext N
    change (finiteState I H hH N).equiv (algebraMap R (Series (R ⧸ I ^ N)) r) =
      algebraMap R (Series (R ⧸ I ^ N)) r
    simp only [MvPowerSeries.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
    simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
      (finiteState I H hH N).equiv.commutes (Ideal.Quotient.mk (I ^ N) r)

/-- The actual base-coefficient-preserving automorphism of the original series ring. -/
def completeEquiv (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) : Series R ≃ₐ[R] Series R :=
  ((CoefficientLimit.equivalence I (Fin 2)).trans (compatibleEquiv I H hH)).trans
    (CoefficientLimit.equivalence I (Fin 2)).symm

/-- The literal coefficient reduction of the limiting forward map is the internally computed finite map. -/
theorem completeEquiv_reduction (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) (completeEquiv I H hH f) =
      (finiteState I H hH N).equiv (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f) := by
  change MvPowerSeries.map (Ideal.Quotient.mk (I ^ N))
    ((CoefficientLimit.equivalence I (Fin 2)).symm
      (compatibleEquiv I H hH (CoefficientLimit.equivalence I (Fin 2) f))) = _
  rw [CoefficientLimit.equivalence_symm_reduction]
  rfl

/-- The actual limiting inverse has the corresponding literal finite inverse maps. -/
theorem completeEquiv_symm_reduction (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) ((completeEquiv I H hH).symm f) =
      (finiteState I H hH N).equiv.symm (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f) := by
  change MvPowerSeries.map (Ideal.Quotient.mk (I ^ N))
    ((CoefficientLimit.equivalence I (Fin 2)).symm
      ((compatibleEquiv I H hH).symm (CoefficientLimit.equivalence I (Fin 2) f))) = _
  rw [CoefficientLimit.equivalence_symm_reduction]
  rfl

@[simp]
theorem completeEquiv_C (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (r : R) : completeEquiv I H hH (C r) = C r := by
  simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    (completeEquiv I H hH).commutes r

/-- The actual constant smoothing parameter is the unique lift of the computed finite scalars. -/
def completeParameter (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) : R :=
  CoefficientLimit.scalarLimit I (fun N => (finiteState I H hH N).scalar)
    (fun hMN => (finiteState_compatible I H hH hMN).1)

@[simp]
theorem completeParameter_reduction (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (N : ℕ) :
    Ideal.Quotient.mk (I ^ N) (completeParameter I H hH) = (finiteState I H hH N).scalar :=
  CoefficientLimit.mk_scalarLimit I (fun N => (finiteState I H hH N).scalar)
    (fun hMN => (finiteState_compatible I H hH hMN).1) N

/-- The limiting parameter actually belongs to the original base ideal. -/
theorem completeParameter_mem (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) : completeParameter I H hH ∈ I := by
  have hq := completeParameter_reduction I H hH 1
  rw [finiteState_one_scalar I H hH] at hq
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hq
  simpa only [pow_one] using hm

/-- Equality modulo the original ideal follows from equality modulo its literal first power. -/
theorem reduction_of_pow_one {I : Ideal R} {f g : Series R}
    (h : MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) f =
      MvPowerSeries.map (Ideal.Quotient.mk (I ^ 1)) g) :
    MvPowerSeries.map (Ideal.Quotient.mk I) f = MvPowerSeries.map (Ideal.Quotient.mk I) g := by
  ext d
  rw [coeff_map, coeff_map]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have he := congrArg (coeff d) h
  simp only [coeff_map] at he
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp (show
    Ideal.Quotient.mk (I ^ 1) (coeff d f - coeff d g) = 0 by rw [map_sub, he, sub_self])
  simpa only [pow_one] using hm

/-- The limiting automorphism reduces to the original identity on every series modulo `I`. -/
theorem completeEquiv_mod_ideal (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) (f : Series R) :
    MvPowerSeries.map (Ideal.Quotient.mk I) (completeEquiv I H hH f) =
      MvPowerSeries.map (Ideal.Quotient.mk I) f := by
  apply reduction_of_pow_one
  rw [completeEquiv_reduction I H hH 1 f, finiteState_one_equiv I H hH]
  rfl

/-- The exact completed split-node equation, proved through every original coefficient quotient. -/
theorem completeEquiv_equation (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) :
    completeEquiv I H hH (X 0 * X 1 - H) = X 0 * X 1 - C (completeParameter I H hH) := by
  apply CoefficientLimit.series_ext I (Fin 2)
  intro N
  rw [completeEquiv_reduction, finiteState_equation I H hH N]
  simp only [map_sub, map_mul, MvPowerSeries.map_X, MvPowerSeries.map_C, completeParameter_reduction]

/-- Both actual directions are continuous for the full base-and-variable adic topology. -/
theorem completeEquiv_continuous (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) :
    @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology
      (completeEquiv I H hH) ∧
    @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology
      (completeEquiv I H hH).symm :=
  ⟨continuous_fullIdeal I _ (completeEquiv_mod_ideal I H hH),
    continuous_symm_fullIdeal I _ (completeEquiv_mod_ideal I H hH)⟩

/-- Source-facing complete separated split normal form, with no compatible-family output premise. -/
theorem exists_complete_normal_form (I : Ideal R) [IsAdicComplete I R] (H : Series R)
    (hH : ∀ d, coeff d H ∈ I) :
    ∃ (h : R) (e : Series R ≃ₐ[R] Series R), h ∈ I ∧
      e (X 0 * X 1 - H) = X 0 * X 1 - C h ∧
      (∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e f) = MvPowerSeries.map (Ideal.Quotient.mk I) f) ∧
      (∀ f, MvPowerSeries.map (Ideal.Quotient.mk I) (e.symm f) = MvPowerSeries.map (Ideal.Quotient.mk I) f) ∧
      @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology e ∧
      @Continuous (Series R) (Series R) (fullIdeal I).adicTopology (fullIdeal I).adicTopology e.symm := by
  refine ⟨completeParameter I H hH, completeEquiv I H hH, completeParameter_mem I H hH,
    completeEquiv_equation I H hH, completeEquiv_mod_ideal I H hH,
    inverse_reduction_of_reduction I _ (completeEquiv_mod_ideal I H hH), ?_⟩
  exact completeEquiv_continuous I H hH

end DeJongAlterations.Algebra.NodeFormalMorse
