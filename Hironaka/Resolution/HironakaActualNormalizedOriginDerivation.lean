import Hironaka.Resolution.HironakaActualEulerContactPowerRecovery
import Hironaka.Analytic.HolomorphicGermCoordinateDerivation
import Hironaka.Resolution.HironakaRelativeNormalDeformationInitialRelations

/-! Genuine normalization of an actual source directional germ derivation,
with ENTIRE original derivative-ideal and Euler-stability memberships.
Blueprint: hironaka-actual-normalized-origin-derivation-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalizedOriginDerivation
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaActualEulerContactPowerRecovery HironakaActualPrincipalPartsCompatibility
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalTaylorCoefficients
  HolomorphicTaylorTail HironakaHolomorphicJetChartInvariance
  GermIdealOrder IdealOrderArithmetic DerivativeIdeal RelativePrincipalizationSpan

variable {n : ℕ}

private theorem origin_zero_mono {I J : GermIdeal n (ComplexModel n)}
    (hIJ : ∀f,I.mem 0 f→J.mem 0 f) :
    originalCoherentOriginIdeal I≤originalCoherentOriginIdeal J:=by
  apply Ideal.span_le.mpr
  rintro _ ⟨f,hf,hIf,rfl⟩
  exact Ideal.subset_span ⟨f,hf,hIJ f hIf,rfl⟩

private theorem origin_mono {I J : GermIdeal n (ComplexModel n)} (hIJ : I.Le J) :
    originalCoherentOriginIdeal I≤originalCoherentOriginIdeal J:=by
  apply Ideal.span_le.mpr
  rintro _ ⟨f,hf,hIf,rfl⟩
  exact Ideal.subset_span ⟨f,hf,hIJ 0 f hIf,rfl⟩

/-- Entire original origin members multiply into the ACTUAL functional
product origin, without a global coordinate-model coherence premise. -/
theorem origin_product_member (I J : GermIdeal n (ComplexModel n))
    {a b : HolGerm (ComplexModel n)} (ha : a∈originalCoherentOriginIdeal I)
    (hb : b∈originalCoherentOriginIdeal J) : a*b∈originalCoherentOriginIdeal (I.mul J):=by
  have hMul : (originalCoherentOriginIdeal I)*(originalCoherentOriginIdeal J)≤
      originalCoherentOriginIdeal (I.mul J):=by
    rw [originalCoherentOriginIdeal,originalCoherentOriginIdeal,Ideal.span_mul_span']
    apply Ideal.span_le.mpr
    rintro _ ⟨a,⟨f,hf,hIf,rfl⟩,b,⟨g,hg,hJg,rfl⟩,rfl⟩
    apply Ideal.subset_span
    refine ⟨(fun z=>f z*g z),hf.mul hg,?_,?_⟩
    · exact IdealOrderArithmetic.mul_mem_mul hIf hJg
        ((hf.mul hg).mono (fun _ h=>h.mdifferentiableAt))
    · rw [HolGerm.mk_mul]
  exact hMul (Ideal.mul_mem_mul ha hb)

private theorem directional_mk (v : ComplexModel n) (f : ComplexModel n→ℂ)
    (hf : HolAt f 0) :
    actualDirectionalDerivation v (HolGerm.mk f hf)=
      HolGerm.mk (fun z=>fderiv ℂ f z v) (eventually_holomorphic_iterDeriv hf [v]):=rfl

/-- Genuine whole-ring directional differentiation sends EVERY original
origin member into the ACTUAL ambient derivative origin ideal. -/
theorem directional_derivative_origin_member (I : GermIdeal n (ComplexModel n))
    (hHol : ∀x f,I.mem x f → HolomorphicAt n f x) (v : ComplexModel n)
    {g : HolGerm (ComplexModel n)} (hg : g∈originalCoherentOriginIdeal I) :
    actualDirectionalDerivation v g∈originalCoherentOriginIdeal (derivIdeal I):=by
  have hOrigin:=origin_mono (le_derivIdeal hHol)
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨f,hf,hIf,rfl⟩
    rw [directional_mk]
    apply Ideal.subset_span
    refine ⟨(fun z=>fderiv ℂ f z v),eventually_holomorphic_iterDeriv hf [v],?_,rfl⟩
    have hD : (derivIdeal I).mem (0 : ComplexModel n)
        (chartDeriv (complexChartAt (n:=n) (0 : ComplexModel n)) v f):=
      chartDeriv_mem_derivIdeal hHol (mem_complexChartAt_source (0 : ComplexModel n)) hIf
    change (derivIdeal I).mem 0 (fun z=>fderiv ℂ f z v) at hD
    exact hD
  · simpa only [map_zero] using (originalCoherentOriginIdeal (derivIdeal I)).zero_mem
  · intro a b _ha _hb hDa hDb
    rw [map_add]
    exact (originalCoherentOriginIdeal (derivIdeal I)).add_mem hDa hDb
  · intro a b hb hDb
    change actualDirectionalDerivation v (a*b)∈originalCoherentOriginIdeal (derivIdeal I)
    rw [(actualDirectionalDerivation v).leibniz]
    simp only [smul_eq_mul]
    exact (originalCoherentOriginIdeal (derivIdeal I)).add_mem
      ((originalCoherentOriginIdeal (derivIdeal I)).mul_mem_left a hDb)
      ((originalCoherentOriginIdeal (derivIdeal I)).mul_mem_right (actualDirectionalDerivation v a)
        (hOrigin hb))

/-- A TRUE original direction with nonzero derivative value internally produces
the SAME normalized derivation, ALL derivative-origin iterates, and actual Euler
stability from source functional stability at the SAME actual origin only. -/
theorem exists_actual_normalized_origin_derivation (u : HolGerm (ComplexModel n))
    (v : ComplexModel n) (hEval : HolGerm.eval (actualDirectionalDerivation v u)≠0) :
    ∃δ : Derivation ℂ (HolGerm (ComplexModel n)) (HolGerm (ComplexModel n)),
      δ u=1 ∧
      (∀ (A : GermIdeal n (ComplexModel n))
        (_hA : ∀x f,A.mem x f→HolomorphicAt n f x) k g,
        g∈originalCoherentOriginIdeal A→
        iteratedDerivation δ k g∈originalCoherentOriginIdeal (iterDerivIdeal A k)) ∧
      (∀ (A T : GermIdeal n (ComplexModel n))
        (_hA : ∀x f,A.mem x f→HolomorphicAt n f x)
        (_hStable : ∀f,((derivIdeal A).mul T).mem 0 f→A.mem 0 f),
        u∈originalCoherentOriginIdeal T→∀g∈originalCoherentOriginIdeal A,
          u*δ g∈originalCoherentOriginIdeal A):=by
  obtain ⟨w,hw⟩:=(HolGerm.isUnit_iff_eval_ne_zero _).mpr hEval
  let δ : Derivation ℂ (HolGerm (ComplexModel n)) (HolGerm (ComplexModel n)):=
    (↑(w⁻¹) : HolGerm (ComplexModel n)) • actualDirectionalDerivation v
  have hOne : δ u=1:=by
    change (↑(w⁻¹) : HolGerm (ComplexModel n))*actualDirectionalDerivation v u=1
    rw [←hw]
    simp
  have hFirst (A : GermIdeal n (ComplexModel n))
      (hA : ∀x f,A.mem x f→HolomorphicAt n f x)
      (g : HolGerm (ComplexModel n)) (hg : g∈originalCoherentOriginIdeal A) :
      δ g∈originalCoherentOriginIdeal (derivIdeal A):=by
    exact (originalCoherentOriginIdeal (derivIdeal A)).mul_mem_left _
      (directional_derivative_origin_member A hA v hg)
  refine ⟨δ,hOne,?_,?_⟩
  · intro A hA k g hg
    induction k with
    | zero=>exact hg
    | succ k ih=>
      exact hFirst (iterDerivIdeal A k) (holomorphicAt_of_mem_iterDerivIdeal hA k)
        (iteratedDerivation δ k g) ih
  · intro A T hA hStable hu g hg
    have hMul:=origin_product_member (derivIdeal A) T (hFirst A hA g hg) hu
    have hResult:=origin_zero_mono hStable hMul
    simpa only [mul_comm] using hResult

end
end Hironaka.HironakaActualNormalizedOriginDerivation
