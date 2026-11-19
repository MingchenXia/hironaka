import Hironaka.Resolution.HironakaActualSameCurrentGeometricStage

/-! The actual selected derivative germs generate the ENTIRE coordinate
contact ideal, by their internally proved nonzero historical Jacobian.
No chosen ideal or contact-carrier comparison is a hypothesis. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSelectedContactCarriers
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan
 HironakaHolomorphicJetChartInvariance HironakaActualCoefficientPresentationCentrePower
 HironakaActualInheritedAnalyticBlockJacobian HironakaActualCauchyCoefficientLimits
 HironakaActualFixedInheritedSelector HironakaActualAnalyticBlockGraphTranslation
 HironakaActualInheritedNextBlockGraph HironakaActualFormalInitialDiagram
 HironakaRelativeNormalMonomialBasis HironakaActualRelativeNormalJetDivision
variable {n : ℕ}

theorem coordinate_derivative_eval_mul_coordinate
    (a : HolGerm (ComplexModel n)) (i j : Fin n) :
    HolGerm.eval (actualAnalyticCoordinateDerivative i (a*coordinateGerm j))=
      if j=i then HolGerm.eval a else 0 := by
  rw [←actualTaylor_coeff_zero,actualTaylor_actualAnalyticCoordinateDerivative,map_mul,
    actualUnshiftedTaylor_coordinate]
  rw [(MvPowerSeries.pderiv ℂ i).leibniz]
  simp only [smul_eq_mul,MvPowerSeries.coeff_zero_eq_constantCoeff_apply,map_add,map_mul,
    MvPowerSeries.constantCoeff_X,zero_mul,add_zero]
  by_cases h : j=i
  · subst j
    simpa using actualTaylor_coeff_zero a
  · rw [MvPowerSeries.pderiv_X_of_ne h,map_zero,mul_zero,if_neg h]

theorem selected_derivative_ideal_eq_coordinate_block_of_det
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n))
    (k : ℕ) (hContact : actualFixedSelectorContactAt S G k)
    (hdet : (actualFixedSelectorJacobian S G k).det≠0) :
    Ideal.span (range (fun j : fixedSelectorBlock V k=>
      actualFixedSelectorDerivative S G (fixedSelectorBlockEssential k j)))=
      actualAnalyticCoordinateBlockIdeal (fixedSelectorBlock V k) := by
  let B:=fixedSelectorBlock V k
  let F : B → HolGerm (ComplexModel n):=fun j=>actualFixedSelectorDerivative S G (fixedSelectorBlockEssential k j)
  let x : B → HolGerm (ComplexModel n):=fun j=>coordinateGerm j.val
  have hCoord : actualAnalyticCoordinateBlockIdeal B=Ideal.span (range x) := by
    unfold actualAnalyticCoordinateBlockIdeal
    congr 1
    ext g
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  have hMem (j : B) : F j∈Ideal.span (range x):=by
    rw [←hCoord]
    exact hContact j
  choose A hA using fun j=>(Ideal.mem_span_range_iff_exists_fun.mp (hMem j))
  have hValues (j i : B) : HolGerm.eval (A j i)=
      HolGerm.eval (actualAnalyticCoordinateDerivative i.val (F j)) := by
    rw [←hA j,map_sum,map_sum]
    dsimp only [x]
    simp_rw [coordinate_derivative_eval_mul_coordinate]
    simp only [Subtype.val_inj,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  let M : Matrix B B (HolGerm (ComplexModel n)):=A
  have hMatrix : Matrix.map M HolGerm.eval=actualFixedSelectorJacobian S G k := by
    ext j i
    exact hValues j i
  have hDet : IsUnit M.det := by
    apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
    rw [HolGerm.eval.map_det M]
    change (Matrix.map M HolGerm.eval).det≠0
    rw [hMatrix]
    exact hdet
  have hVec : Matrix.mulVec M x=F:=funext hA
  have hInvVec : Matrix.mulVec M⁻¹ F=x := by
    rw [←hVec,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul M hDet,Matrix.one_mulVec]
  rw [hCoord]
  apply le_antisymm
  · exact Ideal.span_le.mpr (by rintro _ ⟨j,rfl⟩;exact hMem j)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply Ideal.mem_span_range_iff_exists_fun.mpr
    exact ⟨fun j=>M⁻¹ i j,congrFun hInvVec i⟩

theorem selected_derivative_ideal_eq_coordinate_block
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n))
    (hmonic : ∀a,MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G a))=1)
    (hlower : ∀a β,MonomialOrder.degLex.toSyn β<MonomialOrder.degLex.toSyn a.val →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (G a))=0)
    (k : ℕ) (hContact : actualFixedSelectorContactAt S G k) :
    Ideal.span (range (fun j : fixedSelectorBlock V k=>
      actualFixedSelectorDerivative S G (fixedSelectorBlockEssential k j)))=
      actualAnalyticCoordinateBlockIdeal (fixedSelectorBlock V k) := by
  exact selected_derivative_ideal_eq_coordinate_block_of_det S G k hContact
    (actualFixedSelectorJacobian_det_ne_zero S G hmonic hlower k)

private theorem eventually_zero_of_mem_span {ι : Type} [Fintype ι]
    (f : ComplexModel n → ℂ) (hf : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ f z)
    (g : ι → ComplexModel n → ℂ) (hg : ∀i,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (g i) z)
    (hMem : HolGerm.mk f hf∈Ideal.span (range fun i=>HolGerm.mk (g i) (hg i))) :
    ∀ᶠz in 𝓝 (0 : ComplexModel n),(∀i,g i z=0) → f z=0 := by
  obtain ⟨a,ha⟩:=Ideal.mem_span_range_iff_exists_fun.mp hMem
  choose A hA hGerm using fun i=>HolGerm.exists_eq_mk (a i)
  have hProd (i) : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (fun z=>A i z*g i z) z:=
    (hA i).and (hg i) |>.mono fun _ h=>h.1.mul h.2
  have hSum : HolGerm.mk (fun z=>∑i,A i z*g i z) (eventually_differentiableAt_sum _ hProd)=
      HolGerm.mk f hf := by
    rw [HolGerm.mk_sum Finset.univ (fun i z=>A i z*g i z) hProd]
    calc
      ∑i,HolGerm.mk (fun z=>A i z*g i z) (hProd i)=∑i,a i*HolGerm.mk (g i) (hg i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [HolGerm.mk_mul (A i) (g i) (hA i) (hg i),←hGerm i]
      _=HolGerm.mk f hf:=ha
  have hEq:=HolGerm.mk_eq_mk_iff.mp hSum
  exact hEq.mono fun z hz hzero=>by
    rw [←hz]
    exact Finset.sum_eq_zero fun i _=>by rw [hzero i,mul_zero]

private theorem eventually_zero_loci_eq_of_span {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : ι → ComplexModel n → ℂ) (hf : ∀i,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (f i) z)
    (g : κ → ComplexModel n → ℂ) (hg : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (g j) z)
    (hEq : Ideal.span (range fun i=>HolGerm.mk (f i) (hf i))=
      Ideal.span (range fun j=>HolGerm.mk (g j) (hg j))) :
    ∀ᶠz in 𝓝 (0 : ComplexModel n),(∀i,f i z=0) ↔ ∀j,g j z=0 := by
  have hFG (i) : ∀ᶠz in 𝓝 (0 : ComplexModel n),(∀j,g j z=0) → f i z=0:=by
    apply eventually_zero_of_mem_span (f i) (hf i) g hg
    rw [←hEq]
    exact Ideal.subset_span ⟨i,rfl⟩
  have hGF (j) : ∀ᶠz in 𝓝 (0 : ComplexModel n),(∀i,f i z=0) → g j z=0:=by
    apply eventually_zero_of_mem_span (g j) (hg j) f hf
    rw [hEq]
    exact Ideal.subset_span ⟨j,rfl⟩
  filter_upwards [eventually_all.mpr hFG,eventually_all.mpr hGF] with z hfg hgf
  exact ⟨fun h j=>hgf j h,fun h i=>hfg i h⟩

private theorem fixedSelectorBlock_min (V : Finset (Fin n →₀ ℕ)) (k : ℕ) :
    fixedSelectorBlock V (min k (V.sup normalExponentDegree))=fixedSelectorBlock V k := by
  ext i
  constructor
  · rintro ⟨a,ha,hai⟩
    exact ⟨a,ha.trans (min_le_left _ _),hai⟩
  · rintro ⟨a,ha,hai⟩
    exact ⟨a,le_min ha (Finset.le_sup a.property),hai⟩

/-- ONE actual open identifies EVERY historical selected-derivative contact
carrier with its literal coordinate prefix, using ANY fixed same-germ
function representatives and no new selector choices. -/
theorem exists_actual_selected_contact_flags_neighborhood_of_det
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n))
    (hDet : ∀k,(actualFixedSelectorJacobian S G k).det≠0)
    (hContact : ∀k,actualFixedSelectorContactAt S G k)
    (f : fixedSelectorEssential V → ComplexModel n → ℂ)
    (hf : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (f j) z)
    (hRep : ∀j,HolGerm.mk (f j) (hf j)=actualFixedSelectorDerivative S G j)
    (O : Set (ComplexModel n)) (hO : IsOpen O) (h0O : (0 : ComplexModel n)∈O) :
    ∃U : Set (ComplexModel n),IsOpen U ∧ (0 : ComplexModel n)∈U ∧ U⊆O ∧
      (∀j,DifferentiableOn ℂ (f j) U) ∧ ∀k,∀z∈U,
        (∀j : fixedSelectorEssential V,j.val∈fixedSelectorBlock V k → f j z=0) ↔
          ∀i∈fixedSelectorBlock V k,z i=0 := by
  have hOne (k : ℕ) : ∀ᶠz in 𝓝 (0 : ComplexModel n),
      (∀j : fixedSelectorEssential V,j.val∈fixedSelectorBlock V k → f j z=0) ↔
        ∀i∈fixedSelectorBlock V k,z i=0 := by
    let B:=fixedSelectorBlock V k
    let F : B → ComplexModel n → ℂ:=fun j=>f (fixedSelectorBlockEssential k j)
    let x : B → ComplexModel n → ℂ:=fun j z=>z j.val
    have hF (j : B) : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (F j) z:=hf _
    have hx (j : B) : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (x j) z:=
      Eventually.of_forall fun _=>(EuclideanSpace.proj j.val : ComplexModel n →L[ℂ] ℂ).differentiableAt
    have hIdeal : Ideal.span (range fun j=>HolGerm.mk (F j) (hF j))=
        Ideal.span (range fun j=>HolGerm.mk (x j) (hx j)) := by
      dsimp only [F]
      simp_rw [hRep]
      rw [selected_derivative_ideal_eq_coordinate_block_of_det S G k (hContact k) (hDet k)]
      unfold actualAnalyticCoordinateBlockIdeal
      congr 1
      ext g
      constructor
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,hi⟩,rfl⟩
      · rintro ⟨i,rfl⟩
        exact ⟨i.val,i.property,rfl⟩
    have hNear:=eventually_zero_loci_eq_of_span F hF x hx hIdeal
    refine hNear.mono fun z hz=>?_
    have hLeft : (∀j : B,F j z=0) ↔
        ∀j : fixedSelectorEssential V,j.val∈B → f j z=0 := by
      constructor
      · intro h j hj
        have he : fixedSelectorBlockEssential k (⟨j.val,hj⟩ : B)=j:=Subtype.ext rfl
        exact he ▸ h ⟨j.val,hj⟩
      · intro h j
        exact h (fixedSelectorBlockEssential k j) j.property
    exact hLeft.symm.trans (hz.trans ⟨fun h i hi=>h ⟨i,hi⟩,fun h j=>h j.val j.property⟩)
  let K:=V.sup normalExponentDegree
  have hAll : ∀ᶠz in 𝓝 (0 : ComplexModel n),∀r : Fin (K+1),
      (∀j : fixedSelectorEssential V,j.val∈fixedSelectorBlock V r.val → f j z=0) ↔
        ∀i∈fixedSelectorBlock V r.val,z i=0:=eventually_all.mpr fun r=>hOne r.val
  have hHol : ∀ᶠz in 𝓝 (0 : ComplexModel n),∀j,DifferentiableAt ℂ (f j) z:=eventually_all.mpr hf
  obtain ⟨B,hBsub,hB,h0B⟩:=mem_nhds_iff.mp (hAll.and hHol)
  refine ⟨B∩O,hB.inter hO,⟨h0B,h0O⟩,inter_subset_right,
    (fun j z hz=>(hBsub hz.1).2 j |>.differentiableWithinAt),?_⟩
  intro k z hz
  have h:=(hBsub hz.1).1 (⟨min k K,by omega⟩ : Fin (K+1))
  change (∀j : fixedSelectorEssential V,j.val∈fixedSelectorBlock V (min k K) → f j z=0) ↔
    ∀i∈fixedSelectorBlock V (min k K),z i=0 at h
  simpa only [K,fixedSelectorBlock_min] using h

theorem exists_actual_selected_contact_flags_neighborhood
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n))
    (hmonic : ∀a,MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G a))=1)
    (hlower : ∀a β,MonomialOrder.degLex.toSyn β<MonomialOrder.degLex.toSyn a.val →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (G a))=0)
    (hContact : ∀k,actualFixedSelectorContactAt S G k)
    (f : fixedSelectorEssential V → ComplexModel n → ℂ)
    (hf : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (f j) z)
    (hRep : ∀j,HolGerm.mk (f j) (hf j)=actualFixedSelectorDerivative S G j)
    (O : Set (ComplexModel n)) (hO : IsOpen O) (h0O : (0 : ComplexModel n)∈O) :
    ∃U : Set (ComplexModel n),IsOpen U ∧ (0 : ComplexModel n)∈U ∧ U⊆O ∧
      (∀j,DifferentiableOn ℂ (f j) U) ∧ ∀k,∀z∈U,
        (∀j : fixedSelectorEssential V,j.val∈fixedSelectorBlock V k → f j z=0) ↔
          ∀i∈fixedSelectorBlock V k,z i=0 := by
  exact exists_actual_selected_contact_flags_neighborhood_of_det S G
    (fun k=>actualFixedSelectorJacobian_det_ne_zero S G hmonic hlower k)
    hContact f hf hRep O hO h0O

end
end Hironaka.HironakaActualSelectedContactCarriers
