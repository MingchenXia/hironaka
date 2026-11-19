import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.MarkedIdeal.HomogenizedIdeal

/-! Actual dense strict representatives have no Cartier divisor factor. The
critical-support inclusion, current coherence and nonzero stalk are explicit;
this module does not assume or claim a complete born-boundary history.
Blueprint: hironaka-actual-strict-divisor-zero-exponent-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualStrictDivisorZeroExponent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealOrder IdealWeightPowers
  DivisorExponent DivisorExponentAlong BlowupDerivativeIdeal OrderTaylor

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Genuine density off the local zero set permits cancellation inside the
SAME actual vanishing ideal, without any supplied saturation certificate. -/
theorem vanishingIdeal_cancel_dense {W H : Set M} {x : M} {t g : M → ℂ}
    (hDense : W ⊆ closure (W \ H))
    (hZero : ∀ᶠ y in 𝓝 x,t y=0 ↔ y∈H) (hg : HolomorphicAt n g x)
    (hprod : (vanishingIdeal (n := n) W).mem x (fun y => t y*g y)) :
    (vanishingIdeal (n := n) W).mem x g := by
  obtain ⟨U,hU,hUo,hxU⟩ := eventually_nhds_iff.mp (hg.and (hprod.2.and hZero))
  refine ⟨hg,?_⟩
  filter_upwards [hUo.mem_nhds hxU] with z hz hzW
  have hfreq : ∃ᶠ y in 𝓝 z,g y=0 := by
    refine (mem_closure_iff_frequently.mp (hDense hzW)).mp ?_
    filter_upwards [hUo.mem_nhds hz] with y hy hyOff
    have ht : t y≠0 := fun ht => hyOff.2 ((hU y hy).2.2.mp ht)
    exact (mul_eq_zero.mp ((hU y hy).2.1 hyOff.1)).resolve_left ht
  have hcl := isClosed_singleton.mem_of_frequently_of_tendsto
    (hfreq.mono fun y hy => (show g y∈({0} : Set ℂ) from hy)) (hU z hz).1.continuousAt.tendsto
  exact hcl

/-- An actual coherent vanishing ideal, nonzero at the current point and with
a dense off-divisor representative, has zero native whole-carrier exponent. -/
theorem vanishingIdeal_divExpAlong_eq_zero {W H : Set M}
    (hI : (vanishingIdeal (n := n) W).IsCoherent) (hH : IsClosedSubmanifold n H)
    (hInv : (vanishingIdeal (n := n) H).IsInvertible)
    (hDense : W ⊆ closure (W \ H)) (x : M)
    (hNZ : IsNonzeroAlongAt (univ : Set M) (vanishingIdeal (n := n) W) x) :
    divExpAlong n univ (vanishingIdeal (n := n) W) H x=0 := by
  rw [divExpAlong_univ]
  have hhol : ∀ y g,(vanishingIdeal (n := n) W).mem y g → HolomorphicAt n g y :=
    fun _ _ h => h.1
  by_cases hxH : x∈H
  · obtain ⟨k,hReg⟩ := hH.2 x hxH
    obtain ⟨U,hU,hxU,t,ht,_htNZ,hGen⟩ := hInv x
    have htHol : ∀ y∈U,HolomorphicAt n t y :=
      fun y hy => holomorphicAt_of_mdifferentiableOn_open hU ht hy
    have hZero : ∀ᶠ y in 𝓝 x,t y=0 ↔ y∈H := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      constructor
      · intro hty
        by_contra hyH
        have hOne : (vanishingIdeal (n := n) H).mem y (fun _ => (1 : ℂ)) :=
          ⟨holomorphicAt_const 1,(show ∀ᶠ z in 𝓝 y,z∉H from hH.1.isOpen_compl.mem_nhds hyH).mono
            (fun z hz hzH => False.elim (hz hzH))⟩
        obtain ⟨_hone,c,_hc,hc⟩ := isInSpanAt_eq_iff.mp ((hGen y hy _).mp hOne)
        exact one_ne_zero (by simpa only [hty,mul_zero] using hc.self_of_nhds)
      · intro hyH
        have htMem : (vanishingIdeal (n := n) H).mem y t :=
          (hGen y hy t).mpr (isInSpanAt_self rfl (htHol y hy))
        exact htMem.2.self_of_nhds hyH
    let e := divExp n (vanishingIdeal (n := n) W) H x
    change e=0
    by_contra he
    have hePos : 0<e := Nat.pos_of_ne_zero he
    have hOld : IsDivNear n (vanishingIdeal (n := n) W) H e x := isDivNear_divExp hhol x
    have hStalk := (isDivNear_iff hI hReg).mp hOld
    have hGenPow := idealPow_mem_iff_of_generator htHol hGen e x hxU
    have hDouble : IsDivNear n (vanishingIdeal (n := n) W) H (e+e) x := by
      apply (isDivNear_iff hI hReg).mpr
      intro f hf
      obtain ⟨_hfhol,a,ha,hfa⟩ := isInSpanAt_eq_iff.mp ((hGenPow f).mp (hStalk f hf))
      have hfa' : f=ᶠ[𝓝 x] (fun y => t y^e*a y) :=
        hfa.mono fun y hy => hy.trans (mul_comm _ _)
      have hprod : (vanishingIdeal (n := n) W).mem x (fun y => t y^e*a y) :=
        HomogenizedIdeal.mem_congr hI hf hfa'
      have hZeroPow : ∀ᶠ y in 𝓝 x,t y^e=0 ↔ y∈H :=
        hZero.mono fun y hy => (pow_eq_zero_iff he).trans hy
      have haMem : (vanishingIdeal (n := n) W).mem x a :=
        vanishingIdeal_cancel_dense hDense hZeroPow ha hprod
      have htPow : (idealPow (vanishingIdeal (n := n) H) e).mem x (fun y => t y^e) :=
        (hGenPow _).mpr (isInSpanAt_self rfl (holomorphicAt_pow (htHol x hxU) e))
      exact mem_idealPow_congr
        (mul_mem_idealPow_add (𝔞 := vanishingIdeal (n := n) H) (fun _ _ h => h.1) htPow (hStalk a haMem)) hfa'.symm
    exact not_isDivNear_divExp_succ hhol hxH (isNonzeroAlongAt_univ_iff.mp hNZ)
      (hDouble.mono (by change e+1≤e+e;omega))
  · have hnone : ¬ ∃ e,¬ IsDivNear n (vanishingIdeal (n := n) W) H (e+1) x := by
      rintro ⟨e,he⟩
      exact he (isDivNear_of_notMem hH.1 hxH (e+1))
    simp only [divExp,dif_neg hnone]

omit [IsComplexManifold n M] in
/-- The actual differential strict transform has a dense representative off
EVERY actual subset of the SAME differential exceptional locus. -/
theorem strictTransform_dense_off_critical_subset
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (f : M → X) (W : Set X) {H : Set M}
    (hH : H ⊆ exceptionalLocus n f) :
    strictTransform n f W ⊆ closure (strictTransform n f W \ H) := by
  apply closure_mono
  intro y hy
  exact ⟨subset_closure hy,fun hyH => hy.2 (hH hyH)⟩

/-- Genuine critical Cartier divisors have zero exponent in the SAME current
strict ideal. Actual born-to-critical and current NZ/coherence are kept explicit. -/
theorem strictTransform_divExpAlong_eq_zero
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (f : M → X) (W : Set X) {H : Set M}
    (hCritical : H ⊆ exceptionalLocus n f)
    (hI : (vanishingIdeal (n := n) (strictTransform n f W)).IsCoherent)
    (hH : IsClosedSubmanifold n H) (hInv : (vanishingIdeal (n := n) H).IsInvertible)
    (x : M) (hNZ : IsNonzeroAlongAt univ (vanishingIdeal (n := n) (strictTransform n f W)) x) :
    divExpAlong n univ (vanishingIdeal (n := n) (strictTransform n f W)) H x=0 :=
  vanishingIdeal_divExpAlong_eq_zero hI hH hInv (strictTransform_dense_off_critical_subset f W hCritical) x hNZ

end
end Hironaka.HironakaActualStrictDivisorZeroExponent
