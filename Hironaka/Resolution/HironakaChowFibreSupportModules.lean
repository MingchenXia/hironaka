import Hironaka.Resolution.HironakaChowOriginalFibreSupportedDivision
import Hironaka.Resolution.HironakaChowNormalSupportProjection

/-! Literal assigned quotient/remainder supports depend only on NORMAL
exponents. The actual original fibre heads internally give the zero-base
law, identifying these supported germs with existing native A-submodules.
No A-linearity, basis or direct-sum packet is assumed. Blueprint FIRST:
`hironaka-g10-fibre-support-modules.tex`. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaChowFibreSupportModules
noncomputable section
open HolGerm HironakaRelativeNormalIdeal
  HironakaChowOriginalFibreSupportedDivision HironakaChowNormalSupportProjection
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalNormalSeries
  HironakaActualAnalyticFormalNormalPowers HironakaActualRelativeTaylorCoefficients
  HironakaActualRelativeCoefficientGerms HironakaHolomorphicJetChartInvariance

variable {d t k : ℕ}

private theorem zero_base_le_iff (head beta : Fin (d+t) →₀ ℕ)
    (hBase : ∀ i : Fin d, head (i.castAdd t) = 0) :
    head ≤ beta ↔ actualNormalExponent head ≤ actualNormalExponent beta := by
  constructor
  · intro h i
    exact h (i.natAdd d)
  · intro h i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [hBase]
      exact Nat.zero_le _
    · exact h j

private theorem avoids_eq_of_normal_eq (L : List (CoordinateWord (d+t)))
    (hBase : ∀ w ∈ L, ∀ i : Fin d, wordExponent w (i.castAdd t) = 0)
    (alpha beta : Fin (d+t) →₀ ℕ)
    (hNormal : actualNormalExponent alpha = actualNormalExponent beta) :
    AvoidsCones L alpha ↔ AvoidsCones L beta := by
  apply forall_congr'
  intro w
  apply forall_congr'
  intro hw
  apply not_congr
  rw [zero_base_le_iff _ _ (hBase w hw), zero_base_le_iff _ _ (hBase w hw), hNormal]

/-- The ORIGINAL ordered quotient region, expressed solely in the normal block. -/
def assignedQuotientNormalMask (w : Fin k → CoordinateWord (d+t)) (j : Fin k) :
    Set (Fin t →₀ ℕ) :=
  {gamma | AvoidsCones ((List.ofFn w).take j.val)
    (actualJoinedExponent (0 : Fin d →₀ ℕ) gamma + wordExponent (w j))}

/-- The ORIGINAL entire remainder region, expressed solely in the normal block. -/
def assignedRemainderNormalMask (w : Fin k → CoordinateWord (d+t)) :
    Set (Fin t →₀ ℕ) :=
  {gamma | AvoidsCones (List.ofFn w) (actualJoinedExponent (0 : Fin d →₀ ℕ) gamma)}

theorem quotient_mask_iff (w : Fin k → CoordinateWord (d+t))
    (hBase : ∀ j (i : Fin d), wordExponent (w j) (i.castAdd t) = 0)
    (j : Fin k) (beta : Fin (d+t) →₀ ℕ) :
    actualNormalExponent beta ∈ assignedQuotientNormalMask w j ↔
      AvoidsCones ((List.ofFn w).take j.val) (beta + wordExponent (w j)) := by
  apply avoids_eq_of_normal_eq
  · intro v hv i
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hv)
    exact hBase a i
  · rw [normal_add, normal_add, normal_joined]

theorem remainder_mask_iff (w : Fin k → CoordinateWord (d+t))
    (hBase : ∀ j (i : Fin d), wordExponent (w j) (i.castAdd t) = 0)
    (beta : Fin (d+t) →₀ ℕ) :
    actualNormalExponent beta ∈ assignedRemainderNormalMask w ↔
      AvoidsCones (List.ofFn w) beta := by
  apply avoids_eq_of_normal_eq
  · intro v hv i
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hv
    exact hBase a i
  · exact normal_joined _ _

variable (d t)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/-- Exact WHOLE ORIGINAL Taylor support, in the actual analytic A-submodule. -/
theorem mem_normalSupportSubmodule_iff_whole_taylor
    (Delta : Set (Fin t →₀ ℕ)) (f : HolGerm (ComplexModel (d+t))) :
    f ∈ normalSupportSubmodule d t Delta ↔
      ∀ beta, actualNormalExponent beta ∉ Delta →
        MvPowerSeries.coeff beta (actualUnshiftedTaylorAlgHom (d+t) f) = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ beta hBeta
    rw [taylor_normalSupportProjection, if_neg hBeta]
  · intro hf
    apply (mem_normalSupportSubmodule_iff d t Delta f).mpr
    intro gamma hGamma
    apply actualUnshiftedTaylorAlgHom_injective d
    rw [map_zero]
    apply MvPowerSeries.ext
    intro beta
    have hc := congrArg (MvPowerSeries.coeff beta)
      (actualFormalNormalCoefficient_actualTaylor d t f gamma)
    change MvPowerSeries.coeff (actualJoinedExponent beta gamma)
      (actualUnshiftedTaylorAlgHom (d+t) f) = _ at hc
    rw [← hc]
    exact hf _ (by simpa only [normal_joined] using hGamma)

/-- Zero base heads are DERIVED from the literal actual308 enumeration. -/
theorem fibre_heads_zero_base (I : Ideal (HolGerm (ComplexModel (d+t))))
    (j : Fin (Fintype.card (HironakaActualWeightedVertexSmallTails.ActualVertexIndex t
      (Ideal.map (HironakaActualJointBaseFibre.jointBaseZeroTrace d t).toRingHom I))))
    (i : Fin d) : wordExponent (fibreHeadWords d t I j) (i.castAdd t) = 0 := by
  simp [fibreHeadWords, wordExponent_wordOfExponent, actualJoinedExponent]

/-- The actual assigned quotient support, with its EXISTING native A action. -/
def fibreQuotientModule (I : Ideal (HolGerm (ComplexModel (d+t))))
    (j : Fin (Fintype.card (HironakaActualWeightedVertexSmallTails.ActualVertexIndex t
      (Ideal.map (HironakaActualJointBaseFibre.jointBaseZeroTrace d t).toRingHom I)))) :
    Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  normalSupportSubmodule d t (assignedQuotientNormalMask (fibreHeadWords d t I) j)

/-- The actual assigned remainder support, with its EXISTING native A action. -/
def fibreRemainderModule (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  normalSupportSubmodule d t (assignedRemainderNormalMask (fibreHeadWords d t I))

/-- Native Pi and product modules; no manufactured action or basis is input. -/
abbrev fibreDivisionModule (I : Ideal (HolGerm (ComplexModel (d+t)))) :=
  (∀ j, fibreQuotientModule d t I j) × fibreRemainderModule d t I

theorem mem_fibreQuotientModule_iff (I : Ideal (HolGerm (ComplexModel (d+t))))
    (j : Fin (Fintype.card (HironakaActualWeightedVertexSmallTails.ActualVertexIndex t
      (Ideal.map (HironakaActualJointBaseFibre.jointBaseZeroTrace d t).toRingHom I))))
    (f : HolGerm (ComplexModel (d+t))) :
    f ∈ fibreQuotientModule d t I j ↔
      ∀ beta, ¬ AvoidsCones ((List.ofFn (fibreHeadWords d t I)).take j.val)
        (beta + wordExponent (fibreHeadWords d t I j)) →
        MvPowerSeries.coeff beta (actualUnshiftedTaylorAlgHom (d+t) f) = 0 := by
  simpa only [fibreQuotientModule, quotient_mask_iff _ (fibre_heads_zero_base d t I)] using
    mem_normalSupportSubmodule_iff_whole_taylor d t
      (assignedQuotientNormalMask (fibreHeadWords d t I) j) f

theorem mem_fibreRemainderModule_iff (I : Ideal (HolGerm (ComplexModel (d+t))))
    (f : HolGerm (ComplexModel (d+t))) :
    f ∈ fibreRemainderModule d t I ↔
      ∀ beta, ¬ AvoidsCones (List.ofFn (fibreHeadWords d t I)) beta →
        MvPowerSeries.coeff beta (actualUnshiftedTaylorAlgHom (d+t) f) = 0 := by
  simpa only [fibreRemainderModule, remainder_mask_iff _ (fibre_heads_zero_base d t I)] using
    mem_normalSupportSubmodule_iff_whole_taylor d t
      (assignedRemainderNormalMask (fibreHeadWords d t I)) f

theorem fibre_quotient_tangent_mul_mem (I : Ideal (HolGerm (ComplexModel (d+t))))
    (j : Fin (Fintype.card (HironakaActualWeightedVertexSmallTails.ActualVertexIndex t
      (Ideal.map (HironakaActualJointBaseFibre.jointBaseZeroTrace d t).toRingHom I))))
    (a : HolGerm (ComplexModel d)) (f : HolGerm (ComplexModel (d+t)))
    (hf : f ∈ fibreQuotientModule d t I j) :
    tangentPullback d t a * f ∈ fibreQuotientModule d t I j :=
  (fibreQuotientModule d t I j).smul_mem a hf

theorem fibre_remainder_tangent_mul_mem (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : HolGerm (ComplexModel d)) (f : HolGerm (ComplexModel (d+t)))
    (hf : f ∈ fibreRemainderModule d t I) :
    tangentPullback d t a * f ∈ fibreRemainderModule d t I :=
  (fibreRemainderModule d t I).smul_mem a hf

end
end Hironaka.HironakaChowFibreSupportModules
