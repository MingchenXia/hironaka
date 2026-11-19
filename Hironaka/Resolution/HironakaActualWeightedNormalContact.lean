import Hironaka.Resolution.HironakaActualWeightedNormalAmbientDerivatives

/-! Genuine mark-d contact for the literal normal coordinate on the original
product open. No canonical-history or coefficient-recoding claim is made.
Blueprint: hironaka-actual-weighted-normal-contact-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWeightedNormalContact
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  GermIdealPullbackCalculus InvertibleIdealQuotient RestrictedIdealExtension
  DerivativeIdeal DerivativeIdealAlong TangentDirectionAlong BlowupDerivativeIdeal
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaActualWeightedNormalPadding HironakaActualWeightedNormalAmbientDerivatives
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaActualCentreJointJets HironakaActualZeroCoordinateContactSeed
  HironakaActualGraphContactCoefficient HironakaRelativeNormalIdeal

private theorem coordinate_holomorphic (n : ℕ) (x : ComplexModel (n+1)) :
    HolomorphicAt (n+1) (addedCoordinate n) x := by
  have h := (zero_coordinate_tangent (univ : Set (ComplexModel n))).mem x (mem_univ x)
  change (zeroIdeal (univ : Set (ComplexModel n))).mem x (addedCoordinate n) at h
  exact h.1

private theorem coordinate_mdifferentiable (n : ℕ) :
    MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (addedCoordinate n) :=
  fun x => (coordinate_holomorphic n x).self_of_nhds

private def coordinatePowerIdeal (n r : ℕ) : GermIdeal (n+1) (ComplexModel (n+1)) :=
  finiteFunctionIdeal (fun _ : Unit => fun z => addedCoordinate n z^r)

private theorem coordinatePower_coherent (n r : ℕ) : (coordinatePowerIdeal n r).IsCoherent :=
  isCoherent_finiteFunctionIdeal _ (fun _ => (coordinate_mdifferentiable n).pow r)

private theorem coordinate_derivative_one (n : ℕ) (x : ComplexModel (n+1)) :
    chartDeriv (complexChartAt x)
      (actualJointNormalInclusion n 1 (EuclideanSpace.single 0 1)) (addedCoordinate n)=fun _ => 1 := by
  funext y
  have h := graphFunction_chartDeriv_eq_one (zeroFunction n) y
    (differentiableAt_const _) (0 : Fin 1)
  simpa only [addedCoordinate,complexChartAt,chartAt_self_eq] using h

private theorem coordinate_power_step (n r : ℕ) :
    (coordinatePowerIdeal n r).Le (derivIdeal (coordinatePowerIdeal n (r+1))) := by
  intro x g hg
  apply HomogenizedIdeal.mem_of_isInSpanAt (isCoherent_derivIdeal (coordinatePower_coherent n (r+1)))
  refine IsInSpanAt.trans ?_ hg
  rintro _ ⟨_i,rfl⟩
  have hp : (coordinatePowerIdeal n (r+1)).mem x (fun z => addedCoordinate n z^(r+1)) :=
    isInSpanAt_self ⟨(),rfl⟩ (holomorphicAt_pow (coordinate_holomorphic n x) (r+1))
  let v := actualJointNormalInclusion n 1 (EuclideanSpace.single 0 1)
  have hd := chartDeriv_mem_derivIdeal (𝔞 := coordinatePowerIdeal n (r+1))
    (e := complexChartAt x) (v := v)
    (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem (coordinatePower_coherent n (r+1)) h)
    (mem_complexChartAt_source x) hp
  have hpow := chartDeriv_pow (v := v) (mem_complexChartAt_source x) (coordinate_holomorphic n x) r
  have hcoef : (r : ℂ)+1≠0 := by exact_mod_cast (Nat.succ_ne_zero r)
  have he : (fun z => ((r : ℂ)+1)⁻¹ *
      chartDeriv (complexChartAt x) v (fun y => addedCoordinate n y^(r+1)) z)=ᶠ[𝓝 x]
      (fun z => addedCoordinate n z^r) := by
    filter_upwards [hpow] with z hz
    rw [hz,coordinate_derivative_one]
    simp only [mul_one]
    rw [←mul_assoc,inv_mul_cancel₀ hcoef,one_mul]
  exact isInSpanAt_of_eq_mul hd (holomorphicAt_pow (coordinate_holomorphic n x) r)
    (holomorphicAt_const (((r : ℂ)+1)⁻¹)) he.symm

private theorem coordinate_power_derivative_le (n : ℕ) :
    ∀ j r,(coordinatePowerIdeal n r).Le (iterDerivIdeal (coordinatePowerIdeal n (r+j)) j)
  | 0,r => fun _ _ hg => hg
  | j+1,r => by
    have hm := derivIdeal_mono (coordinate_power_derivative_le n j (r+1))
    intro x g hg
    have h := hm x g (coordinate_power_step n r x g hg)
    have he : r+1+j=r+(j+1) := by omega
    simpa only [he,iterDerivIdeal_succ] using h

/-- Actual powers of the genuine global normal coordinate descend under every
ambient derivative order, with the original exponent retained literally. -/
theorem coordinate_power_derivative_member (n r j : ℕ) (x : ComplexModel (n+1)) :
    (iterDerivIdeal (finiteFunctionIdeal (n := n+1)
      (fun _ : Unit => fun z => addedCoordinate n z^(r+j))) j).mem x
      (fun z => addedCoordinate n z^r) :=
  coordinate_power_derivative_le n j r x _
    (isInSpanAt_self ⟨(),rfl⟩ (holomorphicAt_pow (coordinate_holomorphic n x) r))

/-- The literal normal coordinate belongs to the genuine ambient contact ideal
of the original normal padding at its actual positive mark. -/
theorem normal_padding_contact_member {n : ℕ} (U : Opens (ComplexModel n))
    (I : GermIdeal n U) (d : ℕ) (hd : 0<d) (x : productOpen U) :
    (iterDerivIdeal (normalPaddingIdeal I d) (d-1)).mem x (relativeNormalCoordinate U) := by
  have hglobal : (iterDerivIdeal (coordinatePowerIdeal n d) (d-1)).mem x.val (addedCoordinate n) := by
    have h := coordinate_power_derivative_member n 1 (d-1) x.val
    have he : 1+(d-1)=d := by omega
    simpa only [coordinatePowerIdeal,he,pow_one] using h
  have hp : (GermIdeal.pullback (m := n+1) (Subtype.val : productOpen U → ComplexModel (n+1))
      (iterDerivIdeal (coordinatePowerIdeal n d) (d-1))).mem x (relativeNormalCoordinate U) :=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨addedCoordinate n,hglobal,rfl⟩
      (Eventually.of_forall fun y => normalCoordinate_mdifferentiable U y))
  rw [HomogenizedEtale.pullback_val_iterDerivIdeal (productOpen U)
    (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem (coordinatePower_coherent n d) h) (d-1)] at hp
  have hinc : (GermIdeal.pullback (m := n+1)
      (Subtype.val : productOpen U → ComplexModel (n+1)) (coordinatePowerIdeal n d)).Le
      (normalPaddingIdeal I d) := by
    rw [coordinatePowerIdeal,finiteFunctionIdeal_pullback
      (fun _ : Unit => fun z : ComplexModel (n+1) => addedCoordinate n z^d)
      (fun _ => (coordinate_mdifferentiable n).pow d)
      (Subtype.val : productOpen U → ComplexModel (n+1)) contMDiff_subtype_val]
    exact le_sumIdeal_right (isCoherent_finiteFunctionIdeal _
      (fun _ => (normalCoordinate_mdifferentiable U).pow d))
  exact iterDerivIdeal_mono hinc (d-1) x _ hp

/-- The same literal normal function has a genuine multiplicity-one field
witness and genuine mark-d contact on the entire actual product. -/
theorem normal_padding_contact {n : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) {d : ℕ} (hd : 0<d) :
    IsTangentDirectionAlong univ (normalPaddingIdeal I d) d univ (relativeNormalCoordinate U) := by
  have hJ : (normalPaddingIdeal I d).IsCoherent :=
    isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hI)
      (isCoherent_finiteFunctionIdeal _ (fun _ => (normalCoordinate_mdifferentiable U).pow d))
  have hz := zero_coordinate_tangent (univ : Set (ComplexModel n))
  have hopen : IsTangentDirectionAlong univ (zeroIdeal (univ : Set (ComplexModel n))) 1
      (productOpen U) (addedCoordinate n) :=
    ⟨(productOpen U).isOpen,fun z _ => hz.mem z (mem_univ z),
      fun z _ h => hz.multiplicity_one z (mem_univ z) h⟩
  have hlocal := ContactEquivalenceAlong.isTangentDirectionAlong_pullback_val (productOpen U)
    (𝔞 := zeroIdeal (univ : Set (ComplexModel n))) (fun _ _ h => h.1) hopen
  have hmult : ∀ x ∈ (univ : Set (productOpen U)),relativeNormalCoordinate U x=0 →
      ∃ (e : ComplexChart (n+1) (productOpen U)) (ξ : Fin (n+1) → productOpen U → ℂ),
        IsTangentField univ e ξ x ∧ fieldDeriv e ξ (relativeNormalCoordinate U) x≠0 := by
    simpa only [preimage_univ,relativeNormalCoordinate] using hlocal.multiplicity_one
  refine ⟨isOpen_univ,?_,hmult⟩
  intro x _
  rw [iterDerivIdealAlong_univ (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hJ h)]
  exact normal_padding_contact_member U I d hd x

/-- Every positive original weighted family gives genuine contact at the SAME
common mark, keeping the actual full ordered boundary in its literal record. -/
theorem weighted_padding_contact {n : ℕ} {ι : Type*} [Fintype ι]
    (U : Opens (ComplexModel n)) (w : ι → ℕ) (hw : ∀ i,0<w i) (c : ι → U → ℂ)
    (hc : ∀ i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i)) (E : List (Set U)) :
    IsTangentDirectionAlong univ (paddingMarked U w c E).ideal (paddingMarked U w c E).d univ
      (relativeNormalCoordinate U) := by
  change IsTangentDirectionAlong univ
    (weightedFunctionIdeal (n := n+1) (paddingWeight w) (paddingFunction U c))
    (weightedCommonMark (paddingWeight w)) univ (relativeNormalCoordinate U)
  rw [entire_padding_ideal U w c hc,padding_common_mark]
  exact normal_padding_contact (isCoherent_weightedFunctionIdeal w c hc) (weightedCommonMark_pos w hw)

end
end Hironaka.HironakaActualWeightedNormalContact
