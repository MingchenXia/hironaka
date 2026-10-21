/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualZeroPointReducedTail
import Hironaka.Resolution.HironakaActualAxisTaylorRigidity
import Hironaka.Resolution.HironakaActualPointOrderRetainingHS
import Hironaka.Resolution.HironakaActualPureNormalVertices

/-!
# Source tangent stability and actual current homogeneous normal independence

Genuine degree lifts and whole current colons give cancellation INSIDE the
entire actual initial ideal. A finite degree induction excludes every actual
current homogeneous member normal on the original source diagram. Natural
SOURCE initial tangent stability internally identifies literal canonical
source forms and the whole current shadow. Actual original point persistence
then implies all canonical normalized orders in the ZERO-direction chart.
No desired family, shadow, graded-regularity, output-order or source/current
diagram-inclusion certificate is input. Source tangent stability is retained
as an explicit geometric qualification; arbitrary directions, relative maximal
standardness and the full history driver remain separate.
Blueprint: `hironaka-actual-initial-pivot-normality-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInitialPivotNormality
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualOriginalFormalHSTransfer HironakaActualHomogeneousInitialHS
  HironakaActualFiniteInitialGeneration HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualExceptionalFilteredDivision
  HironakaActualPointExceptionalInitialForm
variable {n : ℕ}
local notation "R" => MvPowerSeries (Fin n) ℂ
local notation "𝔪" => actualFormalCoordinateIdeal n univ

private theorem pointIdeal_eq_genuineVariables (n : ℕ) :
    actualFormalCoordinateIdeal n univ=genuineFormalVariables n := by
  simp [actualFormalCoordinateIdeal,genuineFormalVariables]

private theorem homogeneous_mem_power (q : ℕ) (G : R) (hG : G.IsHomogeneous q) : G∈𝔪^q := by
  rw [pointIdeal_eq_genuineVariables]
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q G).mpr
  intro β hβ
  apply hG.coeff_eq_zero
  have h : β.degree<q := by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hβ
  omega

private theorem high_power_component_zero (q : ℕ) (G : R) (hG : G∈𝔪^(q+1)) :
    MvPowerSeries.homogeneousComponent q G=0 := by
  apply MvPowerSeries.ext
  intro β
  rw [MvPowerSeries.coeff_homogeneousComponent]
  split_ifs with hβ
  · rw [pointIdeal_eq_genuineVariables] at hG
    exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n (q+1) G).mp hG β
      (by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using (show β.degree<q+1 from by omega))
  · rfl

private theorem component_member_initial (I : Ideal R) (q : ℕ) (G : R) (hI : G∈I) (hG : G∈𝔪^q) :
    MvPowerSeries.homogeneousComponent q G∈actualHomogeneousInitialIdeal I := by
  rw [actualHomogeneousInitialIdeal_eq_initial_vertex_span]
  apply actualFormalMember_component_mem_initial_vertex_span I q G hI
  rwa [←pointIdeal_eq_genuineVariables]

private theorem X_mul_homogeneous (e : Fin n) (q : ℕ) (G : R) (hG : G.IsHomogeneous q) :
    (MvPowerSeries.X e*G).IsHomogeneous (q+1) := by
  have hX : (MvPowerSeries.X e : R).IsHomogeneous 1 := by
    intro β hβ
    have heq : β=Finsupp.single e 1 := by
      by_contra hne
      simp [MvPowerSeries.coeff_X,hne] at hβ
    subst β
    simp [Finsupp.weight_single]
  intro β hc
  have hh : Finsupp.weight (1 : Fin n → ℕ) β=1+q := MvPowerSeries.IsHomogeneous.mul hX hG hc
  omega

/-- Genuine whole colons provide ACTUAL cancellation inside the entire
homogeneous initial ideal, using actual original degree lifts. -/
theorem homogeneous_initial_pivot_cancel (I : Ideal R) (e : Fin n)
    (hCol : ∀ q,(I ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=I ⊔ 𝔪^q)
    (q : ℕ) (G : R) (hG : G.IsHomogeneous q)
    (heG : MvPowerSeries.X e*G∈actualHomogeneousInitialIdeal I) : G∈actualHomogeneousInitialIdeal I := by
  have hProd : (MvPowerSeries.X e*G).IsHomogeneous (q+1) := X_mul_homogeneous e q G hG
  obtain ⟨L,hLI,hLpow,hComp⟩ := actual_homogeneous_initial_ideal_degree_lift I (MvPowerSeries.X e*G) heG (q+1)
  rw [←MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hProd] at hComp
  have hLpow' : L∈𝔪^(q+1) := by rwa [pointIdeal_eq_genuineVariables]
  have hRem := (actual_point_homogeneous_component_and_remainder (q+1) L hLpow').2
  rw [hComp] at hRem
  have heMem : MvPowerSeries.X e*G∈I ⊔ 𝔪^((q+1)+1) := by
    apply Submodule.mem_sup.mpr
    refine ⟨L,hLI,-(L-MvPowerSeries.X e*G), (𝔪^((q+1)+1)).neg_mem hRem,?_⟩
    ring
  have hGM : G∈I ⊔ 𝔪^(q+1) := by
    rw [←hCol (q+1),Submodule.mem_colon_singleton]
    simpa only [smul_eq_mul,mul_comm] using heMem
  obtain ⟨A,hAI,B,hB,hAB⟩ := Submodule.mem_sup.mp hGM
  have hAq : A∈𝔪^q := by
    have hBq : B∈𝔪^q := Ideal.pow_le_pow_right (Nat.le_succ q) hB
    have h := (𝔪^q).sub_mem (homogeneous_mem_power q G hG) hBq
    convert h using 1
    linear_combination hAB
  have hBand : MvPowerSeries.homogeneousComponent q A=G := by
    have hh := congrArg (MvPowerSeries.homogeneousComponent q) hAB
    rw [map_add,high_power_component_zero q B hB,add_zero,
      ←MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hG] at hh
    exact hh
  rw [←hBand]
  exact component_member_initial I q A hAI hAq

private theorem projection_component (e : Fin n) (q : ℕ) (F : R) :
    pivotZeroProjection e (MvPowerSeries.homogeneousComponent q F)=
      MvPowerSeries.homogeneousComponent q (pivotZeroProjection e F) := by
  apply MvPowerSeries.ext
  intro β
  simp only [pivotZeroProjection_coefficient,MvPowerSeries.coeff_homogeneousComponent]
  split_ifs <;> rfl

private theorem component_of_initial_mem (K : Ideal R) (F : R) (hF : F∈actualHomogeneousInitialIdeal K) (q : ℕ) :
    MvPowerSeries.homogeneousComponent q F∈actualHomogeneousInitialIdeal K := by
  obtain ⟨L,hLI,hLq,hBand⟩ := actual_homogeneous_initial_ideal_degree_lift K F hF q
  rw [←hBand]
  apply component_member_initial K q L hLI
  rwa [pointIdeal_eq_genuineVariables]

private theorem projected_homogeneous_initial_mem (I K : Ideal R) (e : Fin n)
    (hProj : Ideal.map (pivotZeroProjection e).toRingHom I≤actualHomogeneousInitialIdeal K)
    (q : ℕ) (F : R) (hF : F∈actualHomogeneousInitialIdeal I) (hHom : F.IsHomogeneous q) :
    pivotZeroProjection e F∈actualHomogeneousInitialIdeal K := by
  obtain ⟨L,hLI,_hLq,hBand⟩ := actual_homogeneous_initial_ideal_degree_lift I F hF q
  have hs : pivotZeroProjection e L∈actualHomogeneousInitialIdeal K := hProj (Ideal.mem_map_of_mem _ hLI)
  have hc := component_of_initial_mem K _ hs q
  rw [←projection_component,hBand,←MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hHom] at hc
  exact hc

private theorem projection_normal_initial_zero (I K : Ideal R) (e : Fin n)
    (hProj : Ideal.map (pivotZeroProjection e).toRingHom I≤actualHomogeneousInitialIdeal K)
    (q : ℕ) (F : R) (hF : F∈actualHomogeneousInitialIdeal I) (hHom : F.IsHomogeneous q)
    (hNormal : ∀ β∈actualInitialDiagram MonomialOrder.degLex K,MvPowerSeries.coeff β F=0) :
    pivotZeroProjection e F=0 := by
  apply eq_zero_of_mem_of_diagram_coefficients_zero MonomialOrder.degLex (actualHomogeneousInitialIdeal K)
  · exact projected_homogeneous_initial_mem I K e hProj q F hF hHom
  · intro β hβ
    rw [actual_homogeneous_initial_ideal_diagram] at hβ
    rw [pivotZeroProjection_coefficient]
    split_ifs
    · exact hNormal β hβ
    · rfl

private theorem coefficient_of_X_factor (e : Fin n) (F G : R) (hFG : F=MvPowerSeries.X e*G)
    (β : Fin n →₀ ℕ) : MvPowerSeries.coeff (Finsupp.single e 1+β) F=MvPowerSeries.coeff β G := by
  rw [hFG,MvPowerSeries.X,MvPowerSeries.coeff_add_monomial_mul,one_mul]

private theorem homogeneous_of_X_factor (e : Fin n) (q : ℕ) (F G : R)
    (hFG : F=MvPowerSeries.X e*G) (hF : F.IsHomogeneous (q+1)) : G.IsHomogeneous q := by
  intro β hc
  have hcf : MvPowerSeries.coeff (Finsupp.single e 1+β) F≠0 := by
    rwa [coefficient_of_X_factor e F G hFG]
  have hdf : (Finsupp.single e 1+β).degree=q+1 := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hF hcf
  have he : (Finsupp.single e 1+β).degree=1+β.degree := by
    simp only [Finsupp.degree_eq_weight_one,map_add,Finsupp.weight_single,one_smul]
  rw [he] at hdf
  have hβ : β.degree=q := by omega
  simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hβ

/-- Genuine current colons and an explicitly disclosed projection containment
force every homogeneous current member NORMAL on the original source diagram
 to vanish; the original-data consumer derives the containment internally. -/
theorem homogeneous_source_normal_current_member_eq_zero (I K : Ideal R) (e : Fin n)
    (hCol : ∀ q,(I ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=I ⊔ 𝔪^q)
    (hProj : Ideal.map (pivotZeroProjection e).toRingHom I≤actualHomogeneousInitialIdeal K)
    (q : ℕ) (F : R) (hF : F∈actualHomogeneousInitialIdeal I) (hHom : F.IsHomogeneous q)
    (hNormal : ∀ β∈actualInitialDiagram MonomialOrder.degLex K,MvPowerSeries.coeff β F=0) : F=0 := by
  induction q generalizing F with
  | zero =>
    have hp := projection_normal_initial_zero I K e hProj 0 F hF hHom hNormal
    apply MvPowerSeries.ext
    intro β
    by_cases hβ : β.degree=0
    · have hz : β=0 := (Finsupp.degree_eq_zero_iff β).mp hβ
      subst β
      have hc := congrArg (MvPowerSeries.coeff (0 : Fin n →₀ ℕ)) hp
      simpa only [pivotZeroProjection_coefficient,Finsupp.zero_apply,ite_true,map_zero] using hc
    · exact hHom.coeff_eq_zero hβ
  | succ q ih =>
    have hp := projection_normal_initial_zero I K e hProj (q+1) F hF hHom hNormal
    obtain ⟨G,hFG⟩ := (pivotZeroProjection_eq_zero_iff e F).mp hp
    have hG : G.IsHomogeneous q := homogeneous_of_X_factor e q F G hFG hHom
    have hGI : G∈actualHomogeneousInitialIdeal I := by
      apply homogeneous_initial_pivot_cancel I e hCol q G hG
      rwa [←hFG]
    have hGN (β : Fin n →₀ ℕ) (hβ : β∈actualInitialDiagram MonomialOrder.degLex K) :
        MvPowerSeries.coeff β G=0 := by
      rw [←coefficient_of_X_factor e F G hFG β]
      apply hNormal
      have h := actualInitialDiagram_add MonomialOrder.degLex K β (Finsupp.single e 1) hβ
      simpa only [add_comm] using h
    have hz := ih G hGI hG hGN
    rw [hFG,hz,mul_zero]

open HironakaActualPointCentreStrictGenerators HironakaActualPointDehomogenizedInitial
  HironakaActualPointOrderRetainingHS HironakaActualFormalFamilyStrictGenerators
  HironakaActualReducedBasisDivision HironakaActualFormalBlowupMemberGeneration

private theorem canonical_point_power (K : Ideal R) (a : actualInitialVertices MonomialOrder.degLex K) :
    actualReducedVertexSeries MonomialOrder.degLex K a∈𝔪^(normalExponentDegree a.val) := by
  have h := actualReducedVertexSeries_mem_point_power n K a
  have hw : Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) a.val=normalExponentDegree a.val := by
    simp [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree]
  rwa [hw] at h

/-- Natural SOURCE tangent stability makes the SAME original canonical degree
form have zero actual pivot derivative, by genuine source normal uniqueness. -/
theorem canonical_source_form_pderiv_zero (K : Ideal R) (e : Fin n)
    (hD : ∀ F∈actualHomogeneousInitialIdeal K,MvPowerSeries.pderiv ℂ e F∈actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    MvPowerSeries.pderiv ℂ e (MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a))=0 := by
  have hForm : MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
      (actualReducedVertexSeries MonomialOrder.degLex K a)∈actualHomogeneousInitialIdeal K :=
    component_member_initial K _ _ (actualReducedVertexSeries_mem MonomialOrder.degLex K a) (canonical_point_power K a)
  apply eq_zero_of_mem_of_diagram_coefficients_zero MonomialOrder.degLex (actualHomogeneousInitialIdeal K) _ (hD _ hForm)
  intro β hβ
  rw [actual_homogeneous_initial_ideal_diagram] at hβ
  rw [MvPowerSeries.coeff_pderiv,MvPowerSeries.coeff_homogeneousComponent]
  by_cases hd : (β+Finsupp.single e 1).degree=normalExponentDegree a.val
  · rw [if_pos hd]
    have hΓ : β+Finsupp.single e 1∈actualInitialDiagram MonomialOrder.degLex K := by
      simpa only [add_comm] using actualInitialDiagram_add MonomialOrder.degLex K β (Finsupp.single e 1) hβ
    have hne : β+Finsupp.single e 1≠a.val := by
      intro heq
      have hm : Minimal (·∈actualInitialDiagram MonomialOrder.degLex K) a.val := by
        simpa [actualInitialVertices] using a.property
      have hb : β≤a.val := by rw [←heq];exact le_add_of_nonneg_right zero_le
      have hback := hm.le_of_le hβ hb
      have he := hback e
      rw [←heq,Finsupp.add_apply,Finsupp.single_eq_same] at he
      omega
    rw [actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex K a _ hΓ,if_neg hne,zero_mul]
  · rw [if_neg hd,zero_mul]

private theorem pivot_coefficient_zero_of_pderiv_zero (e : Fin n) (F : R)
    (hD : MvPowerSeries.pderiv ℂ e F=0) (α : Fin n →₀ ℕ) (hα : α e≠0) : MvPowerSeries.coeff α F=0 := by
  have hle : Finsupp.single e 1≤α := Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hα)
  let β := α-Finsupp.single e 1
  have hβα : β+Finsupp.single e 1=α := tsub_add_cancel_of_le hle
  have hc := congrArg (MvPowerSeries.coeff β) hD
  rw [MvPowerSeries.coeff_pderiv,hβα,map_zero] at hc
  have hn : ((β e : ℂ)+1)≠0 := by exact_mod_cast Nat.succ_ne_zero (β e)
  exact (mul_eq_zero.mp hc).resolve_right hn

private theorem pivot_projection_eq_of_pderiv_zero (e : Fin n) (F : R)
    (hD : MvPowerSeries.pderiv ℂ e F=0) : pivotZeroProjection e F=F := by
  apply MvPowerSeries.ext
  intro α
  rw [pivotZeroProjection_coefficient]
  split_ifs with hα
  · rfl
  · exact (pivot_coefficient_zero_of_pderiv_zero e F hD α hα).symm

private theorem zero_dehom_polynomial_of_pivot_free (e : Fin n) (p : MvPolynomial (Fin n) ℂ)
    (hp : ∀ α∈p.support,α e=0) : actualPointDehomogenization e (fun _ => 0) p=p := by
  conv_lhs => rw [←p.support_sum_monomial_coeff,map_sum]
  conv_rhs => rw [←p.support_sum_monomial_coeff]
  apply Finset.sum_congr rfl
  intro α hα
  rw [actualPointDehomogenization,MvPolynomial.aeval_monomial,MvPolynomial.monomial_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hie : i≠e := by
    intro he
    subst i
    exact (Finsupp.mem_support_iff.mp hi) (hp α hα)
  simp [hie]

private theorem weight_point (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) α=normalExponentDegree α := by
  simp [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree]

private theorem canonical_source_normalized_shadow (K : Ideal R) (e : Fin n)
    (hD : ∀ F∈actualHomogeneousInitialIdeal K,MvPowerSeries.pderiv ℂ e F∈actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    pivotZeroProjection e (actualNormalizedFormalMember univ e (mem_univ e) (fun _ => 0)
      (normalExponentDegree a.val) (actualReducedVertexSeries MonomialOrder.degLex K a) (canonical_point_power K a))=
      MvPowerSeries.homogeneousComponent (normalExponentDegree a.val) (actualReducedVertexSeries MonomialOrder.degLex K a) := by
  let d := normalExponentDegree a.val
  let G := actualReducedVertexSeries MonomialOrder.degLex K a
  let P := actualPointHomogeneousPolynomial d G
  have hP : (P : R)=MvPowerSeries.homogeneousComponent d G := actualPointHomogeneousPolynomial_coe d G
  have hDZ : MvPowerSeries.pderiv ℂ e (MvPowerSeries.homogeneousComponent d G)=0 := canonical_source_form_pderiv_zero K e hD a
  have hFree (α : Fin n →₀ ℕ) (hα : α∈P.support) : α e=0 := by
    by_contra he
    have hc : MvPowerSeries.coeff α (MvPowerSeries.homogeneousComponent d G)≠0 := by
      rw [←hP,MvPolynomial.coeff_coe]
      exact MvPolynomial.mem_support_iff.mp hα
    exact hc (pivot_coefficient_zero_of_pderiv_zero e _ hDZ α he)
  have hCon := actual_point_normalized_member_congr_dehomogenization e (fun _ => 0) d G (canonical_point_power K a)
  rw [zero_dehom_polynomial_of_pivot_free e P hFree] at hCon
  have hKer : pivotZeroProjection e (actualNormalizedFormalMember univ e (mem_univ e) (fun _ => 0) d G
      (canonical_point_power K a)-(P : R))=0 :=
    (pivotZeroProjection_eq_zero_iff e _).mpr (Ideal.mem_span_singleton.mp hCon)
  rw [map_sub,hP,pivot_projection_eq_of_pderiv_zero e _ hDZ,sub_eq_zero] at hKer
  exact hKer

open HironakaActualFormalStrictGenerators

/-- The entire independent actual strict ideal has precisely the whole source
initial shadow under genuine SOURCE tangent stability, with no chosen family. -/
theorem pivot_projection_strict_eq_source_initial (K : Ideal R) (e : Fin n)
    (hD : ∀ F∈actualHomogeneousInitialIdeal K,MvPowerSeries.pderiv ℂ e F∈actualHomogeneousInitialIdeal K) :
    Ideal.map (pivotZeroProjection e).toRingHom (actualFormalStrictTransform K univ e (mem_univ e) (fun _ => 0))=
      actualHomogeneousInitialIdeal K := by
  let B := actualReducedVertexFamily MonomialOrder.degLex K
  have hv (a : actualInitialVertices MonomialOrder.degLex K) : familyVertexSeries MonomialOrder.degLex K B a∈
      𝔪^Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) a.val :=
    actualReducedVertexSeries_mem_point_power n K a
  rw [actualFormalStrictTransform_eq_family_span MonomialOrder.degLex K B univ e (mem_univ e) (fun _ => 0) hv,
    Ideal.map_span,←range_comp,actualHomogeneousInitialIdeal_eq_reduced_component_span]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  change pivotZeroProjection e (familyNormalizedFormalVertex MonomialOrder.degLex K B univ e (mem_univ e) (fun _ => 0) hv a)=_
  have hSpec := actualNormalizedFormalMember_spec univ e (mem_univ e) (fun _ => 0) _
    (familyVertexSeries MonomialOrder.degLex K B a) (hv a)
  change (MvPowerSeries.X e)^Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) a.val*
    familyNormalizedFormalVertex MonomialOrder.degLex K B univ e (mem_univ e) (fun _ => 0) hv a=
      actualFormalBlowup univ e (fun _ => 0) (actualReducedVertexSeries MonomialOrder.degLex K a) at hSpec
  rw [weight_point] at hSpec
  have hNorm := actualNormalizedFormalMember_unique univ e (mem_univ e) (fun _ => 0) _
    (actualReducedVertexSeries MonomialOrder.degLex K a) (canonical_point_power K a)
    (familyNormalizedFormalVertex MonomialOrder.degLex K B univ e (mem_univ e) (fun _ => 0) hv a) hSpec
  rw [hNorm]
  exact canonical_source_normalized_shadow K e hD a

open HironakaActualZeroPointReducedTail

private theorem canonical_zero_quotient_power_of_colons (K : Ideal R) (e : Fin n)
    (hD : ∀ F∈actualHomogeneousInitialIdeal K,MvPowerSeries.pderiv ℂ e F∈actualHomogeneousInitialIdeal K)
    (hCol : ∀ q,((actualFormalStrictTransform K univ e (mem_univ e) (fun _ => 0)) ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=
      actualFormalStrictTransform K univ e (mem_univ e) (fun _ => 0) ⊔ 𝔪^q)
    (a : actualInitialVertices MonomialOrder.degLex K) (H : R)
    (hH : (MvPowerSeries.X e)^(normalExponentDegree a.val)*H=
      actualFormalBlowup univ e (fun _ => 0) (actualReducedVertexSeries MonomialOrder.degLex K a)) :
    H∈𝔪^(normalExponentDegree a.val) := by
  by_contra hp
  have hne : H≠0 := by intro hz;apply hp;rw [hz];exact Ideal.zero_mem _
  let r := actualHomogeneousInitialDegree H hne
  have hHr : H∈𝔪^r := by
    rw [pointIdeal_eq_genuineVariables]
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n r H).mpr
    intro β hβ
    apply MvPowerSeries.coeff_of_lt_order
    rw [←actualHomogeneousInitialDegree_eq_order H hne]
    exact_mod_cast (show β.degree<r from by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hβ)
  have hr : r<normalExponentDegree a.val := by
    by_contra h
    exact hp (Ideal.pow_le_pow_right (by omega) hHr)
  let J := actualFormalStrictTransform K univ e (mem_univ e) (fun _ => 0)
  have hHJ : H∈J := by
    change H∈actualFormalStrictTransform K univ e (mem_univ e) (fun _ => 0)
    rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
    exact Ideal.subset_span ⟨normalExponentDegree a.val,actualReducedVertexSeries MonomialOrder.degLex K a,
      actualReducedVertexSeries_mem MonomialOrder.degLex K a,canonical_point_power K a,
      actualNormalizedFormalMember_unique univ e (mem_univ e) (fun _ => 0) _ _ (canonical_point_power K a) H hH⟩
  have hFJ : MvPowerSeries.homogeneousComponent r H∈actualHomogeneousInitialIdeal J :=
    component_member_initial J r H hHJ hHr
  have hNormal (β : Fin n →₀ ℕ) (hβ : β∈actualInitialDiagram MonomialOrder.degLex K) :
      MvPowerSeries.coeff β (MvPowerSeries.homogeneousComponent r H)=0 := by
    rw [MvPowerSeries.coeff_homogeneousComponent]
    split_ifs with hd
    · apply canonical_zero_point_low_coefficient_zero_on_source_diagram K a e H hH β _ hβ
      have hb : normalExponentDegree β=r := by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hd
      omega
    · rfl
  have hz := homogeneous_source_normal_current_member_eq_zero J K e hCol
    (le_of_eq (pivot_projection_strict_eq_source_initial K e hD)) r
    (MvPowerSeries.homogeneousComponent r H) hFJ (MvPowerSeries.isHomogeneous_homogeneousComponent H r) hNormal
  change actualHomogeneousInitialForm H hne=0 at hz
  exact actualHomogeneousInitialForm_ne_zero H hne hz

open HolGerm HironakaHolomorphicPointJets HironakaActualAnalyticStrictGenerators
  HironakaActualCoefficientPresentationCentrePower HironakaActualAxisTaylorRigidity

/-- ONLY original analytic point data, genuine source tangent stability and
actual source/current entire HS persistence imply EVERY actual canonical
normalized member's original vertex order. No current normality/regularity,
family, shadow profile or source/current diagram inclusion is an input. -/
theorem original_zero_point_persistent_hs_orders_of_source_tangent_stable
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n)
    (hD : ∀ F∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I),
      MvPowerSeries.pderiv ℂ e F∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (hPersist : ∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I univ e (fun _ => 0)) ℓ=hilbertSamuelValue I ℓ) :
    ∀ (a : actualInitialVertices MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)) (H : R),
      (MvPowerSeries.X e)^(normalExponentDegree a.val)*H=actualFormalBlowup univ e (fun _ => 0)
        (actualReducedVertexSeries MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a) →
      H∈𝔪^(normalExponentDegree a.val) := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  obtain ⟨_H,_hN,hStrict⟩ := exists_actual_point_normalized_member_generators n I e (fun _ => 0)
  have hCurrent := original_point_persistent_hs_initial_colons I e (fun _ => 0) hPersist
  dsimp only at hCurrent
  have hCol : ∀ q,((actualFormalStrictTransform K univ e (mem_univ e) (fun _ => 0)) ⊔ 𝔪^(q+1)).colon {MvPowerSeries.X e}=
      actualFormalStrictTransform K univ e (mem_univ e) (fun _ => 0) ⊔ 𝔪^q := by
    intro q
    have hc := (hCurrent q).2
    rw [hStrict] at hc
    exact hc
  intro a H hH
  exact canonical_zero_quotient_power_of_colons K e hD hCol a H hH

end
end Hironaka.HironakaActualInitialPivotNormality
