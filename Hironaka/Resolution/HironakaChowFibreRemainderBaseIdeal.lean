import Hironaka.Resolution.HironakaChowBaseZeroTaylor
import Hironaka.Resolution.HironakaChowFibreSupportModules
import Hironaka.Resolution.HironakaActualReducedFormalStandardBasis

/-! The ORIGINAL fibre diagram forces actual members of I in the SAME
native normal-complement module into the actual base maximal ideal.
This supplies the missing geometric K⊂m_AN premise internally. -/
set_option autoImplicit false
namespace Hironaka.HironakaChowFibreRemainderBaseIdeal
noncomputable section
open Set Classical HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalFibreHilbertSamuel
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticFormalNormalPowers
  HironakaActualJointBaseFibre HironakaActualWeightedVertexSmallTails
  HironakaChowOriginalFibreSupportedDivision HironakaChowFibreSupportModules
  HironakaChowBaseZeroTaylor HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualRelativeTaylorCoefficients
  HironakaActualRelativeCoefficientGerms HironakaActualCauchyMonomialDivision
  HironakaActualCauchyDiagramPartition HironakaActualCentreJointJets

/-- The WHOLE ORIGINAL fibre ideal and SAME original normal mask DERIVE zero actual trace. -/
theorem fibre_remainder_trace_eq_zero (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (f : HolGerm (ComplexModel (d+t)))
    (hfI : f ∈ I) (hfN : f ∈ fibreRemainderModule d t I) : jointBaseZeroTrace d t f = 0 := by
  let J := Ideal.map (jointBaseZeroTrace d t).toRingHom I
  let Jformal := Ideal.map (actualUnshiftedTaylorAlgHom t).toRingHom J
  have hmember : actualUnshiftedTaylorAlgHom t (jointBaseZeroTrace d t f) ∈ Jformal :=
    Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hfI)
  apply actualUnshiftedTaylorAlgHom_injective t
  rw [map_zero]
  apply eq_zero_of_mem_of_diagram_coefficients_zero MonomialOrder.degLex Jformal _ hmember
  intro γ hγ
  rw [coeff_taylor_jointBaseZeroTrace]
  apply (mem_fibreRemainderModule_iff d t I f).mp hfN
  intro hAvoid
  obtain ⟨a,ha,hle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex Jformal γ).mp hγ
  let a' : ActualVertexIndex t J := ⟨a,ha⟩
  let j := (fibreEnumeration d t I).symm a'
  have hhead : wordExponent (fibreHeadWords d t I j) =
      actualJoinedExponent (0 : Fin d →₀ ℕ) a := by
    change wordExponent (wordOfExponent (actualJoinedExponent (0 : Fin d →₀ ℕ)
      ((fibreEnumeration d t I) j).val)) = _
    rw [wordExponent_wordOfExponent]
    exact congrArg (fun v : ActualVertexIndex t J => actualJoinedExponent (0 : Fin d →₀ ℕ) v.val)
      ((fibreEnumeration d t I).apply_symm_apply a')
  apply hAvoid (fibreHeadWords d t I j) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  rw [hhead]
  intro i
  refine Fin.addCases (fun v => ?_) (fun v => ?_) i
  · simp [actualJoinedExponent]
  · simpa [actualJoinedExponent] using hle v

/-- Native actual base-kernel equality retains the ENTIRE original germ. -/
theorem fibre_remainder_mem_base_ideal (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (f : HolGerm (ComplexModel (d+t)))
    (hfI : f ∈ I) (hfN : f ∈ fibreRemainderModule d t I) :
    f ∈ originalBaseMaximalIdeal d t := by
  rw [baseMaximalIdeal_eq_ker_jointBaseZeroTrace]
  exact fibre_remainder_trace_eq_zero d t I f hfI hfN

end
end Hironaka.HironakaChowFibreRemainderBaseIdeal
