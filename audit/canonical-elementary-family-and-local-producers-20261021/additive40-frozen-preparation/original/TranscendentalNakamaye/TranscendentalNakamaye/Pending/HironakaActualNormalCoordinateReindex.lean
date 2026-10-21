import TranscendentalNakamaye.Pending.HironakaActualTangentScalingFiltration

/-!
# Actual normal-coordinate reindexing

A prescribed normal pivot is carried to the first normal coordinate while
all tangent coordinates and their whole original germ algebra are fixed.
The genuine original germ, polynomial and formal reindexings have a literal
Taylor square, preserve whole normal/maximal powers, and conjugate the actual
blowup pullbacks, including arbitrary chart constants. No fixed degree-lex
order, canonical vertex family or owner recursion is identified across a
permutation; subsequent division may use a fixed order in the permuted ring.
Blueprint: `hironaka-actual-normal-coordinate-reindex-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace TranscendentalNakamaye.Pending.HironakaActualNormalCoordinateReindex
noncomputable section
open FirstPass HolGerm HironakaHolomorphicJetMonomialSpan HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticFormalNormalPowers HironakaActualTaylorCoordinateNaturality
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalCoordinatePowerDivision HironakaRelativeNormalIdeal
  HironakaHolomorphicJetChartInvariance HironakaActualRelativePointChartFactorization
variable {n : ℕ}

/-- The actual coordinate linear isometry, with pullback indices given by the permutation. -/
def coordinateLinearEquiv (r : Fin n ≃ Fin n) : ComplexModel n ≃L[ℂ] ComplexModel n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ r.symm).toContinuousLinearEquiv

/-- Genuine whole original germ pullback along the actual coordinate linear equivalence. -/
def coordinateGermEquiv (r : Fin n ≃ Fin n) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) where
  toRingEquiv := HolGerm.comapEquiv (coordinateLinearEquiv r)
  commutes' _ := rfl

theorem coordinateGermEquiv_coordinate (r : Fin n ≃ Fin n) (i : Fin n) :
    coordinateGermEquiv r (coordinateGerm i)=coordinateGerm (r i) := by
  change HolGerm.comapEquiv (coordinateLinearEquiv r) (HolGerm.mk (fun z : ComplexModel n => z i) _)=
    HolGerm.mk (fun z : ComplexModel n => z (r i)) _
  rw [HolGerm.comapEquiv_mk]
  exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z => rfl)

/-- Whole Taylor naturality, derived from actual coordinate-local germ algebra maps. -/
theorem actualTaylor_coordinateGermEquiv (r : Fin n ≃ Fin n) :
    (actualUnshiftedTaylorAlgHom n).comp (coordinateGermEquiv r).toAlgHom=
      (MvPowerSeries.rename r).comp (actualUnshiftedTaylorAlgHom n) := by
  apply actualGermAlgHom_eq_of_coordinate_images
  · intro i
    change actualUnshiftedTaylorAlgHom n (coordinateGermEquiv r (coordinateGerm i))=
      MvPowerSeries.rename r (actualUnshiftedTaylorAlgHom n (coordinateGerm i))
    rw [coordinateGermEquiv_coordinate,actualUnshiftedTaylor_coordinate,
      actualUnshiftedTaylor_coordinate,MvPowerSeries.rename_X]
  · intro i
    change actualUnshiftedTaylorAlgHom n (coordinateGermEquiv r (coordinateGerm i))∈_
    rw [coordinateGermEquiv_coordinate,actualUnshiftedTaylor_coordinate]
    exact Ideal.subset_span ⟨r i,mem_univ _,rfl⟩

theorem coordinateGermEquiv_polynomial (r : Fin n ≃ Fin n) (P : MvPolynomial (Fin n) ℂ) :
    coordinateGermEquiv r (MvPolynomial.aeval coordinateGerm P)=
      MvPolynomial.aeval coordinateGerm (MvPolynomial.rename r P) := by
  have h : (coordinateGermEquiv r).toAlgHom.comp (MvPolynomial.aeval coordinateGerm)=
      (MvPolynomial.aeval coordinateGerm).comp (MvPolynomial.rename r) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,MvPolynomial.aeval_X,MvPolynomial.rename_X]
    change coordinateGermEquiv r (coordinateGerm i)=coordinateGerm (r i)
    exact coordinateGermEquiv_coordinate r i
  exact DFunLike.congr_fun h P

/-- The first actual normal coordinate; the prescribed pivot internally supplies `0 < t`. -/
def firstNormalIndex (d t : ℕ) (j : Fin t) : Fin (d+t) :=
  (⟨0,lt_of_le_of_lt (Nat.zero_le j.val) j.isLt⟩ : Fin t).natAdd d

/-- Swap only two normal indices, retaining every tangent coordinate and every raw position. -/
def normalPivotPermutation (d t : ℕ) (j : Fin t) : Fin (d+t) ≃ Fin (d+t) :=
  Equiv.swap (j.natAdd d) (firstNormalIndex d t j)

theorem normalPivotPermutation_pivot (d t : ℕ) (j : Fin t) :
    normalPivotPermutation d t j (j.natAdd d)=firstNormalIndex d t j := by
  exact Equiv.swap_apply_left _ _

theorem normalPivotPermutation_tangent (d t : ℕ) (j : Fin t) (i : Fin d) :
    normalPivotPermutation d t j (i.castAdd t)=i.castAdd t := by
  apply Equiv.swap_apply_of_ne_of_ne <;> intro h
  · have hh := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
    omega
  · have hh := congrArg Fin.val h
    simp only [firstNormalIndex,Fin.val_castAdd,Fin.val_natAdd] at hh
    omega

theorem normalPivotPermutation_normal_set (d t : ℕ) (j : Fin t) :
    normalPivotPermutation d t j '' actualTangentCentreVariables d t=
      actualTangentCentreVariables d t := by
  let S:=actualTangentCentreVariables d t
  have hp : j.natAdd d∈S := ⟨j,rfl⟩
  have h0 : firstNormalIndex d t j∈S := ⟨⟨0,lt_of_le_of_lt (Nat.zero_le j.val) j.isLt⟩,rfl⟩
  have hmem (i : Fin (d+t)) : normalPivotPermutation d t j i∈S ↔ i∈S := by
    by_cases hi : i=j.natAdd d
    · subst i
      simp [normalPivotPermutation_pivot,hp,h0]
    by_cases hi0 : i=firstNormalIndex d t j
    · subst i
      simpa only [normalPivotPermutation,Equiv.swap_apply_right] using (iff_of_true hp h0)
    rw [normalPivotPermutation,Equiv.swap_apply_of_ne_of_ne hi hi0]
  ext i
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact (hmem k).mpr hk
  · intro hi
    refine ⟨(normalPivotPermutation d t j).symm i,?_,by simp⟩
    exact (hmem _).mp (by simpa using hi)

theorem map_analyticCoordinateIdeal_coordinateGermEquiv (r : Fin n ≃ Fin n) (A : Set (Fin n)) :
    Ideal.map (coordinateGermEquiv r).toRingEquiv.toRingHom (actualAnalyticCoordinateIdeal A)=
      actualAnalyticCoordinateIdeal (r '' A) := by
  rw [actualAnalyticCoordinateIdeal,Ideal.map_span,actualAnalyticCoordinateIdeal]
  congr 1
  ext g
  constructor
  · rintro ⟨_,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨r i,⟨i,hi,rfl⟩,(coordinateGermEquiv_coordinate r i).symm⟩
  · rintro ⟨_,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨coordinateGerm i,⟨i,hi,rfl⟩,coordinateGermEquiv_coordinate r i⟩

theorem map_formalCoordinateIdeal_rename (r : Fin n ≃ Fin n) (A : Set (Fin n)) :
    Ideal.map (MvPowerSeries.rename r).toRingHom (actualFormalCoordinateIdeal n A)=
      actualFormalCoordinateIdeal n (r '' A) := by
  rw [actualFormalCoordinateIdeal,Ideal.map_span,actualFormalCoordinateIdeal]
  congr 1
  ext F
  constructor
  · rintro ⟨_,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨r i,⟨i,hi,rfl⟩,(MvPowerSeries.rename_X r i).symm⟩
  · rintro ⟨_,⟨i,hi,rfl⟩,rfl⟩
    exact ⟨MvPowerSeries.X i,⟨i,hi,rfl⟩,MvPowerSeries.rename_X r i⟩

theorem map_normalIdeal_pow_normalPivotPermutation (d t : ℕ) (j : Fin t) (q : ℕ) :
    Ideal.map (coordinateGermEquiv (normalPivotPermutation d t j)).toRingEquiv.toRingHom
      (normalIdeal d t^q)=normalIdeal d t^q := by
  rw [Ideal.map_pow,←actualAnalyticCoordinateIdeal_normal,
    map_analyticCoordinateIdeal_coordinateGermEquiv,normalPivotPermutation_normal_set]

theorem map_maximalIdeal_pow_coordinateGermEquiv (r : Fin n ≃ Fin n) (q : ℕ) :
    Ideal.map (coordinateGermEquiv r).toRingEquiv.toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q)=
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  rw [Ideal.map_pow]
  congr 1
  ext g
  rw [Ideal.mem_map_iff_of_surjective (coordinateGermEquiv r).toRingEquiv.toRingHom
    (coordinateGermEquiv r).surjective]
  constructor
  · rintro ⟨h,hh,rfl⟩
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    change HolGerm.eval (HolGerm.comapEquiv (coordinateLinearEquiv r) h)=0
    rw [HolGerm.eval_comapEquiv]
    exact (HolGerm.mem_maximalIdeal_iff _).mp hh
  · intro hg
    refine ⟨(coordinateGermEquiv r).symm g,?_,by simp⟩
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    have hh : HolGerm.eval (coordinateGermEquiv r ((coordinateGermEquiv r).symm g))=
      HolGerm.eval ((coordinateGermEquiv r).symm g) := HolGerm.eval_comapEquiv _ _
    rw [AlgEquiv.apply_symm_apply] at hh
    exact hh.symm.trans ((HolGerm.mem_maximalIdeal_iff _).mp hg)


theorem map_formal_normal_pow_normalPivotPermutation (d t : ℕ) (j : Fin t) (q : ℕ) :
    Ideal.map (MvPowerSeries.rename (normalPivotPermutation d t j)).toRingHom
      (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)=
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q := by
  rw [Ideal.map_pow,map_formalCoordinateIdeal_rename,normalPivotPermutation_normal_set]

theorem normalPivotPermutation_tangentPullback (d t : ℕ) (j : Fin t)
    (g : HolGerm (ComplexModel d)) :
    coordinateGermEquiv (normalPivotPermutation d t j) (tangentPullback d t g)=
      tangentPullback d t g := by
  apply actualUnshiftedTaylorAlgHom_injective (d+t)
  have h : ((actualUnshiftedTaylorAlgHom (d+t)).comp
      (coordinateGermEquiv (normalPivotPermutation d t j)).toAlgHom).comp (tangentPullback d t)=
        (actualUnshiftedTaylorAlgHom (d+t)).comp (tangentPullback d t) := by
    apply actualGermAlgHom_eq_of_coordinate_images
    · intro i
      change actualUnshiftedTaylorAlgHom (d+t)
        (coordinateGermEquiv (normalPivotPermutation d t j) (tangentPullback d t (coordinateGerm i)))=_
      rw [tangentPullback_coordinateGerm,coordinateGermEquiv_coordinate,normalPivotPermutation_tangent]
      rfl
    · intro i
      change actualUnshiftedTaylorAlgHom (d+t)
        (coordinateGermEquiv (normalPivotPermutation d t j) (tangentPullback d t (coordinateGerm i)))∈_
      rw [tangentPullback_coordinateGerm,coordinateGermEquiv_coordinate,actualUnshiftedTaylor_coordinate]
      exact Ideal.subset_span ⟨_,mem_univ _,rfl⟩
  exact DFunLike.congr_fun h g

/-- The reindexing is linear over the unchanged actual tangent germ algebra. -/
theorem normalPivotPermutation_tangent_mul (d t : ℕ) (j : Fin t)
    (g : HolGerm (ComplexModel d)) (h : HolGerm (ComplexModel (d+t))) :
    coordinateGermEquiv (normalPivotPermutation d t j) (tangentPullback d t g*h)=
      tangentPullback d t g*coordinateGermEquiv (normalPivotPermutation d t j) h := by
  rw [map_mul,normalPivotPermutation_tangentPullback]

private theorem rename_subst (r : Fin n ≃ Fin n) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.rename r F=MvPowerSeries.substAlgHom (MvPowerSeries.HasSubst.X_comp r) F := by
  rw [MvPowerSeries.substAlgHom_apply,MvPowerSeries.rename_eq_subst]

private theorem rename_chart_coordinates (r : Fin n ≃ Fin n) (A : Set (Fin n))
    (e : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    MvPowerSeries.rename r (actualFormalBlowupCoordinates A e b i)=
      actualFormalBlowupCoordinates (r '' A) (r e) (b ∘ r.symm) (r i) := by
  have hie : r i=r e ↔ i=e := r.injective.eq_iff
  by_cases h : i∈A <;> by_cases h' : i=e <;>
    simp [actualFormalBlowupCoordinates,h,h',hie,MvPowerSeries.rename_X]

/-- Actual whole substitution composition gives the literal formal chart square. -/
theorem rename_actualFormalBlowup (r : Fin n ≃ Fin n) (A : Set (Fin n))
    (e : Fin n) (b : Fin n → ℂ) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.rename r (actualFormalBlowup A e b F)=
      actualFormalBlowup (r '' A) (r e) (b ∘ r.symm) (MvPowerSeries.rename r F) := by
  rw [rename_subst,rename_subst]
  dsimp only [actualFormalBlowup]
  rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply,
    MvPowerSeries.substAlgHom_comp_substAlgHom_apply,
    MvPowerSeries.substAlgHom_apply,MvPowerSeries.substAlgHom_apply]
  congr 1
  funext i
  change MvPowerSeries.substAlgHom (MvPowerSeries.HasSubst.X_comp r)
      (actualFormalBlowupCoordinates A e b i)=
    actualFormalBlowup (r '' A) (r e) (b ∘ r.symm) (MvPowerSeries.X (r i))
  rw [←rename_subst,actualFormalBlowup_X]
  exact rename_chart_coordinates r A e b i

theorem coordinateGermEquiv_actualAnalyticBlowupPullback (r : Fin n ≃ Fin n)
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (g : HolGerm (ComplexModel n)) :
    coordinateGermEquiv r (actualAnalyticBlowupPullback A e b g)=
      actualAnalyticBlowupPullback (r '' A) (r e) (b ∘ r.symm) (coordinateGermEquiv r g) := by
  apply actualUnshiftedTaylorAlgHom_injective n
  have hp (g : HolGerm (ComplexModel n)) :
      actualUnshiftedTaylorAlgHom n (coordinateGermEquiv r g)=
        MvPowerSeries.rename r (actualUnshiftedTaylorAlgHom n g) :=
    DFunLike.congr_fun (actualTaylor_coordinateGermEquiv r) g
  have hb (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (g : HolGerm (ComplexModel n)) :
      actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e b g)=
        actualFormalBlowup A e b (actualUnshiftedTaylorAlgHom n g) :=
    DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e b) g
  change actualUnshiftedTaylorAlgHom n (coordinateGermEquiv r
      (actualAnalyticBlowupPullback A e b g))=_
  rw [hp,hb,rename_actualFormalBlowup,←hp,←hb]

/-- Entire genuine analytic chart conjugacy, including every actual chart constant. -/
theorem coordinateGermEquiv_analytic_chart_conjugacy (r : Fin n ≃ Fin n)
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (g : HolGerm (ComplexModel n)) :
    coordinateGermEquiv r (actualAnalyticBlowupPullback A e b ((coordinateGermEquiv r).symm g))=
      actualAnalyticBlowupPullback (r '' A) (r e) (b ∘ r.symm) g := by
  rw [coordinateGermEquiv_actualAnalyticBlowupPullback,AlgEquiv.apply_symm_apply]

theorem image_tangentScalingVariables (r : Fin n ≃ Fin n) (S : Set (Fin n)) (e : Fin n) :
    r '' actualTangentScalingVariables S e=actualTangentScalingVariables (r '' S) (r e) := by
  simp only [actualTangentScalingVariables,image_union,image_singleton]
  rw [Equiv.image_compl]

end
end TranscendentalNakamaye.Pending.HironakaActualNormalCoordinateReindex
