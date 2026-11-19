import Hironaka.Algebra.NodeNonsplitCorrection

/-!
# Coefficient naturality of the actual bounded corrections

The source and target nilpotent coefficient ideals may differ. Every forward
map is the original native substitution; commutation of the actual inverses
is derived from that of the forward maps and their bijectivity.
-/

noncomputable section

namespace Hironaka.Algebra.NodeNonsplit

open MvPowerSeries NodeFormalMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] (Q : Quadratic R)

/-- Both original inverse-Hessian coordinates commute with literal coefficient transport. -/
theorem leftCorrection_map (f : R →+* S) (H : Series R) :
    MvPowerSeries.map f (leftCorrection Q H) = leftCorrection (Q.map f) (MvPowerSeries.map f H) := by
  simp [leftCorrection, Quadratic.map, map_mul, firstPart_map, secondPart_map, map_ofNat]

theorem rightCorrection_map (f : R →+* S) (H : Series R) :
    MvPowerSeries.map f (rightCorrection Q H) = rightCorrection (Q.map f) (MvPowerSeries.map f H) := by
  simp [rightCorrection, Quadratic.map, map_mul, firstPart_map, secondPart_map, map_ofNat]

theorem quadraticError_map (f : R →+* S) (H : Series R) :
    MvPowerSeries.map f (quadraticError Q H) = quadraticError (Q.map f) (MvPowerSeries.map f H) := by
  simp [quadraticError, Quadratic.map, leftCorrection_map, rightCorrection_map]

/-- The actual zero-error coordinate correction is the identity on every formal series. -/
theorem correctionEquiv_zero (J : Ideal R) (hJ : IsNilpotent J)
    (hz : ∀ d, coeff d (0 : Series R) ∈ J) :
    correctionEquiv Q J hJ 0 hz = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro g
  change (correctionEquiv Q J hJ 0 hz).toAlgHom g = g
  rw [correctionEquiv_toAlgHom Q, MvPowerSeries.substAlgHom_apply]
  have he : correctionCoordinates Q (0 : Series R) = (X : Fin 2 → Series R) := by
    funext i
    fin_cases i <;> simp [correctionCoordinates, leftCorrection, rightCorrection]
  rw [he, MvPowerSeries.subst_self]
  rfl

@[simp]
theorem correctedError_zero (J : Ideal R) (hJ : IsNilpotent J)
    (hz : ∀ d, coeff d (0 : Series R) ∈ J) : correctedError Q J hJ 0 hz = 0 := by
  simp [correctedError, quadraticError, leftCorrection, rightCorrection]

@[simp]
theorem correctedConstant_zero (J : Ideal R) (hJ : IsNilpotent J)
    (hz : ∀ d, coeff d (0 : Series R) ∈ J) : correctedConstant Q J hJ 0 hz = 0 := by
  simp [correctedConstant]

@[simp]
theorem correctedResidual_zero (J : Ideal R) (hJ : IsNilpotent J)
    (hz : ∀ d, coeff d (0 : Series R) ∈ J) : correctedResidual Q J hJ 0 hz = 0 := by
  simp [correctedResidual]

/-- Coefficient change commutes with the exact original forward coordinate map. -/
theorem correctionEquiv_map (f : R →+* S) (J : Ideal R) (K : Ideal S)
    (hJ : IsNilpotent J) (hK : IsNilpotent K) (H : Series R) (T : Series S)
    (hH : ∀ d, coeff d H ∈ J) (hT : ∀ d, coeff d T ∈ K)
    (he : MvPowerSeries.map f H = T) (g : Series R) :
    MvPowerSeries.map f (correctionEquiv Q J hJ H hH g) =
      correctionEquiv (Q.map f) K hK T hT (MvPowerSeries.map f g) := by
  subst T
  change MvPowerSeries.map f ((correctionEquiv Q J hJ H hH).toAlgHom g) =
    (correctionEquiv (Q.map f) K hK (MvPowerSeries.map f H) hT).toAlgHom (MvPowerSeries.map f g)
  rw [correctionEquiv_toAlgHom Q, correctionEquiv_toAlgHom (Q.map f),
    MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.map_subst
    (NilpotentPowerSeriesSubstitution.hasSubst J hJ (correctionCoordinates_reduces Q J H hH))]
  have hc : (fun i => MvPowerSeries.map f (correctionCoordinates Q H i)) =
      correctionCoordinates (Q.map f) (MvPowerSeries.map f H) := by
    funext i
    fin_cases i <;> simp [correctionCoordinates, leftCorrection_map, rightCorrection_map]
  rw [hc]

/-- Commutation of the actual inverses is proved on every series, not assumed as data. -/
theorem correctionEquiv_symm_map (f : R →+* S) (J : Ideal R) (K : Ideal S)
    (hJ : IsNilpotent J) (hK : IsNilpotent K) (H : Series R) (T : Series S)
    (hH : ∀ d, coeff d H ∈ J) (hT : ∀ d, coeff d T ∈ K)
    (he : MvPowerSeries.map f H = T) (g : Series R) :
    MvPowerSeries.map f ((correctionEquiv Q J hJ H hH).symm g) =
      (correctionEquiv (Q.map f) K hK T hT).symm (MvPowerSeries.map f g) := by
  apply (correctionEquiv (Q.map f) K hK T hT).injective
  rw [AlgEquiv.apply_symm_apply,
    ← correctionEquiv_map Q f J K hJ hK H T hH hT he, AlgEquiv.apply_symm_apply]

/-- The corrected actual error commutes with the original coefficient map. -/
theorem correctedError_map (f : R →+* S) (J : Ideal R) (K : Ideal S)
    (hJ : IsNilpotent J) (hK : IsNilpotent K) (H : Series R) (T : Series S)
    (hH : ∀ d, coeff d H ∈ J) (hT : ∀ d, coeff d T ∈ K)
    (he : MvPowerSeries.map f H = T) :
    MvPowerSeries.map f (correctedError Q J hJ H hH) = correctedError (Q.map f) K hK T hT := by
  unfold correctedError
  rw [map_add, MvPowerSeries.map_C,
    correctionEquiv_symm_map Q f J K hJ hK H T hH hT he, quadraticError_map, he]
  have hc : f (constantCoeff H) = constantCoeff T := by
    rw [← he, constantCoeff_map]
  rw [hc]

/-- The actual scalar correction commutes with coefficient change. -/
theorem correctedConstant_map (f : R →+* S) (J : Ideal R) (K : Ideal S)
    (hJ : IsNilpotent J) (hK : IsNilpotent K) (H : Series R) (T : Series S)
    (hH : ∀ d, coeff d H ∈ J) (hT : ∀ d, coeff d T ∈ K)
    (he : MvPowerSeries.map f H = T) :
    f (correctedConstant Q J hJ H hH) = correctedConstant (Q.map f) K hK T hT := by
  simpa only [constantCoeff_map, correctedConstant] using
    congrArg constantCoeff (correctedError_map Q f J K hJ hK H T hH hT he)

/-- The new zero-constant residual commutes with the actual coefficient map. -/
theorem correctedResidual_map (f : R →+* S) (J : Ideal R) (K : Ideal S)
    (hJ : IsNilpotent J) (hK : IsNilpotent K) (H : Series R) (T : Series S)
    (hH : ∀ d, coeff d H ∈ J) (hT : ∀ d, coeff d T ∈ K)
    (he : MvPowerSeries.map f H = T) :
    MvPowerSeries.map f (correctedResidual Q J hJ H hH) = correctedResidual (Q.map f) K hK T hT := by
  unfold correctedResidual
  rw [map_sub, MvPowerSeries.map_C, correctedError_map Q f J K hJ hK H T hH hT he,
    correctedConstant_map Q f J K hJ hK H T hH hT he]

end Hironaka.Algebra.NodeNonsplit
