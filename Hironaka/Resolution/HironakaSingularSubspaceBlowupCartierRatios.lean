import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartier
import Hironaka.Resolution.HironakaSingularBlowupDenominator

/-!
# Genuine ambient holomorphic ratios from actual singular Cartier stalks

The principal ideal and regular generator live in the EXISTING quotient
structure-sheaf stalk. Ambient cofactors and their common relative identities
are derived from those actual stalk data. No ambient factorization, nonzero
denominator, smoothness or integral-domain assumption is input.

Blueprint: `hironaka-singular-subspace-blowup-cartier-ratios.tex`.
This module does not yet glue morphisms through blowup monomial charts.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierRatios

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue
  HironakaActualAnalyticSubspaceLocalFunctions
  HironakaSingularSubspaceBlowupCartier HironakaSingularBlowupDenominator

noncomputable section

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem holomorphic_sub {f g : M → ℂ} {x : M}
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    HolomorphicAt n (fun z => f z - g z) x :=
  (hf.and hg).mono fun _ h => h.1.sub h.2

private theorem originalGerm_sub (x : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    actualOriginalFunctionGerm x (fun z => f z - g z) (holomorphic_sub hf hg) =
      actualOriginalFunctionGerm x f hf - actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [map_sub, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

private theorem originalGerm_mul (x : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    actualOriginalFunctionGerm x (fun z => f z * g z) (hf.mul hg) =
      actualOriginalFunctionGerm x f hf * actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [map_mul, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

/-- Equality in the actual singular quotient stalk is equality of original
holomorphic germs along the original carrier on a genuine neighbourhood. -/
theorem actual_quotient_germ_eq_iff (C : Set M) (x : C) (f g : M → ℂ)
    (hf : HolomorphicAt n f x.val) (hg : HolomorphicAt n g x.val) :
    ((actualSubspaceInclusion (n := n) C).stalkMap x) (actualOriginalFunctionGerm x.val f hf) =
      ((actualSubspaceInclusion (n := n) C).stalkMap x) (actualOriginalFunctionGerm x.val g hg) ↔
        ∀ᶠ z in 𝓝 x.val, z ∈ C → f z = g z := by
  let q := ((actualSubspaceInclusion (n := n) C).stalkMap x).hom
  have hsub := originalGerm_sub x.val f g hf hg
  constructor
  · intro heq
    have hz : q (actualOriginalFunctionGerm x.val (fun z => f z - g z)
        (holomorphic_sub hf hg)) = 0 := by
      rw [hsub, map_sub, heq, sub_self]
    have hmem : actualOriginalFunctionGerm x.val (fun z => f z - g z)
        (holomorphic_sub hf hg) ∈ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val := by
      rw [← actualSubspaceInclusion_stalk_kernel C x]
      exact hz
    have hvan := (actualOriginalGerm_mem_vanishingIdeal_iff C x.val _
      (holomorphic_sub hf hg)).mp hmem
    exact hvan.2.mono fun z hz hzC => sub_eq_zero.mp (hz hzC)
  · intro heq
    have hmem := (actualOriginalGerm_mem_vanishingIdeal_iff C x.val _
      (holomorphic_sub hf hg)).mpr ⟨holomorphic_sub hf hg,
        heq.mono fun z hz hzC => sub_eq_zero.mpr (hz hzC)⟩
    have hz : q (actualOriginalFunctionGerm x.val (fun z => f z - g z)
        (holomorphic_sub hf hg)) = 0 := by
      rw [← actualSubspaceInclusion_stalk_kernel C x] at hmem
      exact hmem
    rw [hsub, map_sub] at hz
    exact sub_eq_zero.mp hz

private theorem exists_original_quotient_representative (C : Set M) (x : C)
    (r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f x.val),
      ((actualSubspaceInclusion (n := n) C).stalkMap x)
        (actualOriginalFunctionGerm x.val f hf) = r := by
  obtain ⟨a, ha⟩ := actualSubspaceInclusionRingedHom_stalk_surjective (n := n) C x r
  obtain ⟨U, hxU, s, hs⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq a
  let f := sectionExtension U s
  have hf : HolomorphicAt n f x.val := sectionExtension_holomorphicAt U s x.val hxU
  have hg : actualOriginalFunctionGerm x.val f hf = a :=
    (actualOriginalFunctionGerm_eq_section U x.val hxU s f hf Filter.EventuallyEq.rfl).trans hs
  exact ⟨f, hf, (congrArg ((actualSubspaceInclusion (n := n) C).stalkMap x) hg).trans ha⟩

private theorem eval_original_quotient_germ (C : Set M) (x : C) (f : M → ℂ)
    (hf : HolomorphicAt n f x.val) :
    actualSubspaceStalkEval (n := n) C x
      (((actualSubspaceInclusion (n := n) C).stalkMap x)
        (actualOriginalFunctionGerm x.val f hf)) = f x.val := by
  obtain ⟨U, hxU, s, hs⟩ := exists_actual_section_of_original_holomorphicAt x.val f hf
  rw [actualOriginalFunctionGerm_eq_section U x.val hxU s f hf hs,
    actualSubspaceStalkEval_inclusion_germ]
  exact (sectionExtension_apply U s x.val hxU).symm.trans hs.self_of_nhds

/-- A finite principal ideal in the actual singular stalk internally supplies
original holomorphic cofactors, one nonzero denominator and all relative
factorizations on ONE genuine neighbourhood. -/
theorem exists_local_actual_cartier_cofactors {ι : Type*} [Fintype ι]
    (C : Set M) (x : C) (f : ι → M → ℂ)
    (hf : ∀ i, HolomorphicAt n (f i) x.val)
    {alpha : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier}
    (halpha : IsRegular alpha)
    (hspan : Ideal.span (Set.range fun i =>
      ((actualSubspaceInclusion (n := n) C).stalkMap x)
        (actualOriginalFunctionGerm x.val (f i) (hf i))) = Ideal.span {alpha}) :
    ∃ (a : M → ℂ) (ha : HolomorphicAt n a x.val) (q : ι → M → ℂ),
      (∀ i, HolomorphicAt n (q i) x.val) ∧
      ((actualSubspaceInclusion (n := n) C).stalkMap x)
        (actualOriginalFunctionGerm x.val a ha) = alpha ∧
      ∃ j : ι, q j x.val ≠ 0 ∧
        ∀ᶠ z in 𝓝 x.val, z ∈ C → ∀ i, f i z = a z * q i z := by
  classical
  let g := fun i => ((actualSubspaceInclusion (n := n) C).stalkMap x)
    (actualOriginalFunctionGerm x.val (f i) (hf i))
  obtain ⟨b, hb, j, hj⟩ := exists_actual_stalk_quotients_of_principal_span C x halpha g hspan
  obtain ⟨a, ha, haq⟩ := exists_original_quotient_representative C x alpha
  choose q hq hqq using fun i => exists_original_quotient_representative C x (b i)
  have hrel : ∀ i, ∀ᶠ z in 𝓝 x.val, z ∈ C → f i z = a z * q i z := by
    intro i
    apply (actual_quotient_germ_eq_iff C x (f i) (fun z => a z * q i z)
      (hf i) (ha.mul (hq i))).mp
    rw [originalGerm_mul x.val a (q i) ha (hq i), map_mul, haq, hqq]
    exact hb i
  have hjq : q j x.val ≠ 0 := by
    rw [← eval_original_quotient_germ C x (q j) (hq j), hqq]
    exact hj
  refine ⟨a, ha, q, hq, haq, j, hjq, ?_⟩
  exact (Filter.eventually_all.mpr hrel).mono fun z hz hzC i => hz i hzC

/-- The same actual Cartier condition yields holomorphic coordinate ratios on
one ambient open, with the pivot identically one and every original finite
coordinate factored along the singular carrier. -/
theorem exists_local_actual_cartier_ratios {ι : Type*} [Fintype ι]
    (C : Set M) (x : C) (f : ι → M → ℂ)
    (hf : ∀ i, HolomorphicAt n (f i) x.val)
    {alpha : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier}
    (halpha : IsRegular alpha)
    (hspan : Ideal.span (Set.range fun i =>
      ((actualSubspaceInclusion (n := n) C).stalkMap x)
        (actualOriginalFunctionGerm x.val (f i) (hf i))) = Ideal.span {alpha}) :
    ∃ (U : Opens M) (_hxU : x.val ∈ U) (j : ι) (r : ι → M → ℂ),
      (∀ i, ∀ z ∈ U, HolomorphicAt n (r i) z) ∧
      (∀ z ∈ U, r j z = 1) ∧
      ∀ z ∈ U, z ∈ C → ∀ i, f i z = f j z * r i z := by
  obtain ⟨a, ha, q, hq, haq, j, hj, heq⟩ :=
    exists_local_actual_cartier_cofactors C x f hf halpha hspan
  have hqev : ∀ᶠ z in 𝓝 x.val, ∀ i, HolomorphicAt n (q i) z :=
    Filter.eventually_all.mpr (fun i => (hq i).eventually)
  have hnev : ∀ᶠ z in 𝓝 x.val, q j z ≠ 0 :=
    (hq j).continuousAt.eventually (isOpen_ne.mem_nhds hj)
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (hqev.and (hnev.and heq))
  let U : Opens M := ⟨V, hVo⟩
  let r := fun i z => q i z / q j z
  refine ⟨U, hxV, j, r, ?_, ?_, ?_⟩
  · intro i z hz
    exact (hV hz).1 i |>.mul (BlowupFlatCoordinates.HolomorphicAt.inv ((hV hz).1 j) (hV hz).2.1)
  · intro z hz
    exact div_self (hV hz).2.1
  · intro z hz hzC i
    change f i z = f j z * (q i z / q j z)
    rw [(hV hz).2.2 hzC i, (hV hz).2.2 hzC j]
    field_simp [(hV hz).2.1]

end

end Hironaka.HironakaSingularSubspaceBlowupCartierRatios
