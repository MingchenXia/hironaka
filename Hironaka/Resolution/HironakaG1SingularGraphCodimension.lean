import Hironaka.Resolution.HironakaG1CodimensionTwoChartTransport
import Hironaka.Resolution.HironakaActualWholeHSSingularity
import Hironaka.Resolution.HironakaG1NativeFiniteProductHSValues
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels

/-! The actual singular native cut lowers the dimension in a smooth graph envelope. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1SingularGraphCodimension

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaG11PresLineState HironakaEmbeddedAnalytic HironakaActualWholeHSSingularity
  AnalyticDimensionBasics HironakaG1CodimensionTwoChartTransport
  HironakaBaseChange HironakaG1CommonGraphRestrictionMaps HironakaActualLocalCommonGraphModel
  HironakaG1NormalGraphFlags HironakaHolomorphicJetChartInvariance
  HironakaActualReferenceHSSingularCentre AnalyticSubsetOpens
  HironakaOneDimensionalCanonicalSuperlevels

/-- A native cut point is singular, even if the original records use
different ambient dimensions. -/
theorem native_cut_singular {n : ℕ} {X : CMfd.{0} n}
    {A : Set X} {H : ℕ → ℕ} {P : MarkedIdeal n X} (hP : NativeHSState P A H)
    {x : X} (hx : x ∈ P.cosupp) :
    x ∈ singularSet (n := n) A := by
  have hxProfile : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) A) x ℓ = H ℓ :=
    by rw [hP.cosupp_eq] at hx; exact hx
  apply mem_singularSet_iff.mpr
  refine ⟨?_, fun d hReg => ?_⟩
  · have h0 := (HironakaG1NativeFiniteProductHSValues.singularHS_zero_one hP.1).1
    have hx0 : 1 ≤ hilbertSamuelAt (vanishingIdeal (n := n) A) x 0 := by rw [hxProfile 0, h0]
    have hCo := CartanIrreducible.cartanCoherence _ hP.2.1
    exact (BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (n := n) hP.2.1.isClosed) ▸
      (one_le_hilbertSamuelAt_zero_iff _ hCo x).mp hx0
  obtain ⟨m, Y, B, y, hB, hy, hHS⟩ := hP.1
  have hProfile := (regularAtDim_iff_intrinsic_hs_binomial hP.2.1 x d).mp hReg
  have hyReg := (regularAtDim_iff_intrinsic_hs_binomial hB y d).mpr
    (fun ℓ => (congrFun hHS ℓ).trans ((hxProfile ℓ).symm.trans (hProfile ℓ)))
  exact (mem_singularSet_iff.mp hy).2 d hyReg

/-- At a singular cut in a smooth envelope of dimension a, the actual
analytic germ has local dimension at most a minus one. -/
theorem native_cut_locDimLE_of_smooth_envelope {n a : ℕ} {X : CMfd.{0} n}
    {A B : Set X} {H : ℕ → ℕ} {P : MarkedIdeal n X} (hP : NativeHSState P A H)
    {x : X} (hx : x ∈ P.cosupp)
    (hB : RegularAtDim (n := n) B x a) (hAB : ∀ᶠ y in 𝓝 x, y ∈ A → y ∈ B) :
    LocDimLE (n := n) A x (a - 1) := by
  classical
  have hNo : ¬ LocDimGE (n := n) A x a := by
    intro hGE
    have heq := CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE hP.2.1 hB hAB hGE
    exact (mem_singularSet_iff.mp (native_cut_singular hP hx)).2 a
      (CodimOneSupport.regularAtDim_of_eventually_mem_iff (heq.mono fun _ h => h.symm) hB)
  unfold LocDimGE at hNo
  push Not at hNo
  obtain ⟨O, hO, hBound⟩ := hNo
  refine ⟨O, hO, fun y hy j hj => ?_⟩
  by_contra! h
  have ha : a ≤ j := by omega
  exact hBound y hy j ha hj

/-- The literal native singular cut is empty in an original ambient of
dimension at most one. -/
theorem native_cut_empty_of_ambient_dim_le_one {n : ℕ} {X : CMfd.{0} n}
    (hn : n ≤ 1) {A : Set X} {H : ℕ → ℕ} {P : MarkedIdeal n X} (hP : NativeHSState P A H) :
    P.cosupp = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hSing := mem_singularSet_iff.mp (native_cut_singular hP hx)
  have h0 := native_cut_locDimLE_of_smooth_envelope hP hx
    (AnalyticIrreducibleComponents.regularAtDim_univ x)
    (Eventually.of_forall fun _ _ => trivial)
  rw [show n - 1 = 0 by omega] at h0
  obtain ⟨O, hO, hDim⟩ := h0
  obtain ⟨W, hWO, hOpen, hxW⟩ := mem_nhds_iff.mp hO
  let U : Opens X := ⟨W, hOpen⟩
  let y : U := ⟨x, hxW⟩
  have hdim : AnalyticDimensionBasics.DimLE (n := n) ((Subtype.val : U → X) ⁻¹' A) 0 :=
    fun z d hz => hDim z.val (hWO z.property) d (regularAtDim_preimage_val_iff.mp hz)
  exact hSing.2 0 (regularAtDim_preimage_val_iff.mp
    (regularAtDim_zero_of_analytic_dimLE_zero (isComplexAnalyticSubset_preimage_val hP.2.1 U)
      hdim (x := y) hSing.1))

private theorem coordinate_graph_holomorphic {a b : ℕ} {A : Opens (ComplexModel a)}
    {F : ComplexModel a → ComplexModel b} (hF : ContDiffOn ℂ ∞ F A) :
    ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel b) ∞ (fun x : A => F x.val) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr ((hF.contDiffAt (A.isOpen.mem_nhds x.property)).contMDiffAt)

/-- On the literal common graph at a genuine native cut point, one
positive block coordinate already suffices for ambient codimension two. -/
theorem actual_common_graph_codim_two_of_positive_right {a b : ℕ} (hb : 0 < b)
    (A : Opens (ComplexModel a)) (B : Opens (ComplexModel b)) (F : ComplexModel a → ComplexModel b)
    (D : Set (ComplexModel a)) (hF : ContDiffOn ℂ ∞ F A)
    {P : MarkedIdeal (a + b) (CMfd.of (n := a + b) (commonDomain A B))} {H : ℕ → ℕ}
    (hP : NativeHSState P (commonGraphSubset A B F D) H) :
    ∀ x ∈ P.cosupp, ∃ k, k + 2 ≤ a + b ∧
      LocDimLE (n := a + b) (commonGraphSubset A B F D) x k := by
  intro x hx
  let X := CMfd.of (n := a + b) (commonDomain A B)
  let Y := CMfd.of (n := a + b) (blockOpen A b)
  let i : X → Y := commonGraphFirstRestriction (B := B) (le_refl A)
  let f : A → ComplexModel b := fun z => F z.val
  let G : Set Y := blockGraph f univ
  have hi := commonGraphFirstRestriction_isOpenHoloEmbedding (B := B) (le_refl A)
  have hf := coordinate_graph_holomorphic hF
  have hSub : commonGraphSubset A B F D ⊆ i ⁻¹' G := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hSing := mem_singularSet_iff.mp (native_cut_singular hP hx)
  have hReg : RegularAtDim (n := a + b) G (i x) a :=
    regularAtDim_blockGraph_of hf (hSub hSing.1) (AnalyticIrreducibleComponents.regularAtDim_univ _)
  have hB : RegularAtDim (n := a + b) (i ⁻¹' G) x a := hi.regularAtDim_preimage hReg
  by_cases ha : 0 < a
  · exact ⟨a - 1, by omega, native_cut_locDimLE_of_smooth_envelope hP hx hB (Eventually.of_forall hSub)⟩
  · have ha0 : a = 0 := by omega
    have hGE : LocDimGE (n := a + b) (commonGraphSubset A B F D) x a := by
      intro O hO
      obtain ⟨z, hz, k, _, hReg⟩ := locDimGE_zero hP.2.1 hSing.1 O hO
      exact ⟨z, hz, k, by omega, hReg⟩
    have heq := CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE hP.2.1 hB
      (Eventually.of_forall hSub) hGE
    exact (hSing.2 a
      (CodimOneSupport.regularAtDim_of_eventually_mem_iff (heq.mono fun _ h => h.symm) hB)).elim

end Hironaka.HironakaG1SingularGraphCodimension
