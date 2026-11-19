import Hironaka.Resolution.HironakaActualProjectionCarrierQuotientDictionary
import Hironaka.Resolution.HironakaNonreducedQuotientNeighborhoodLifting
/-! ONE-STEP existing native log operator under genuine projection.
BP FIRST: hironaka-actual-projection-native-log-ideal.tex.
No copied operator, independent chart or C01/C02/full-C04 closure claim. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualProjectionNativeLogIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm BlowupTowers
  HironakaActualIntrinsicLogDerivativeFrame HironakaActualExceptionalLogDerivativeIdeal
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceOpenRestriction HironakaActualWholeStalkHolomorphicPullback
  HironakaActualOpenIntrinsicHS HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaSmoothSubmersionContactParameterCharts HironakaSmoothSubmersionContactParameterCoefficientIdeals
  HironakaContactParameterIntrinsicOrder HironakaIntrinsicCarrierBoundaryCharts
  NormalCrossings BlowupFlatCoordinates GiraudAlong DerivativeIdealAlongCoherent
  DerivativeIdealAlong RelativePrincipalizationSpan HolomorphicGermCoordinateDerivation
  Hironaka.RegularLocusDense DerivativeIdealAlongEtale

open DerivativeIdeal HironakaActualIntrinsicLogQuotientDictionary
  HironakaActualProjectionCarrierQuotientDictionary HironakaActualProjectionTestRecord
  HironakaNonreducedQuotientNeighborhoodLifting
open scoped ProductComplexManifold
-- Held actual540 field/division/chain-rule proofs lines37–295, recompiled
-- privately from GIVEN geometry, zero duplicate credit. PUBLIC actual operator,
-- IsLogTangentField and boundaryWeight definitions are reused, NOT copied.
section GivenFieldEngines
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
omit [IsComplexManifold n M] in
private theorem fieldDeriv_smul (e : ComplexChart n M) (ξ : Fin n → M → ℂ)
    (a f : M → ℂ) :
    fieldDeriv e (fun j p => a p * ξ j p) f = fun p => a p * fieldDeriv e ξ f p := by
  funext p
  simp only [fieldDeriv,Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

omit [IsComplexManifold n M] in
private theorem tangent_smul {N : Set M} {e : ComplexChart n M}
    {ξ : Fin n → M → ℂ} {y : M} (hξ : IsTangentField N e ξ y)
    {a : M → ℂ} (ha : HolomorphicAt n a y) :
    IsTangentField N e (fun j p => a p * ξ j p) y := by
  refine ⟨hξ.mem_source,fun j => ha.mul (hξ.holomorphicAt j),?_⟩
  intro g hg
  have h := hξ.preserves g hg
  rw [fieldDeriv_smul]
  refine ⟨ha.mul h.1,?_⟩
  filter_upwards [h.2] with p hp hpN
  rw [hp hpN,mul_zero]

section Flat
variable {x : M} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
  (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)

include hΦsrc in
/-- Whole one-coordinate division on the original manifold, including points off the divisor. -/
private theorem exists_eq_flatCoord_mul {H : Set M} {j : Fin n}
    (hH : ∀ z ∈ flatDomain Φ, z ∈ H ↔ flatCoord Φ j z = 0)
    {y : M} (hy : y ∈ flatDomain Φ) {g : M → ℂ}
    (hg : (vanishingIdeal (n := n) H).mem y g) :
    ∃ b : M → ℂ, HolomorphicAt n b y ∧
      g =ᶠ[𝓝 y] fun p => flatCoord Φ j p * b p := by
  by_cases hz : flatCoord Φ j y = 0
  · let G : ComplexModel n → ℂ := g ∘ flatInv Φ
    have hq : flatMap Φ y ∈ Φ.target := flatMap_mem_target hy
    have hG : ∀ᶠ w in 𝓝 (flatMap Φ y), DifferentiableAt ℂ G w := by
      filter_upwards [Φ.isOpen_target.mem_nhds hq,
        (tendsto_flatInverse Φ hy).eventually hg.1.eventually_nhds] with w hw hgw
      exact differentiableAt_comp_flatInv hw hΦsrc hgw
    have hvan : ∀ᶠ w in 𝓝 (flatMap Φ y), w j = 0 → G w = 0 := by
      filter_upwards [Φ.isOpen_target.mem_nhds hq,
        (tendsto_flatInverse Φ hy).eventually hg.2] with w hw hgw hwj
      apply hgw
      apply (hH _ (flatInv_mem_flatDomain hw hΦsrc)).mpr
      have hround := congrArg (fun v : ComplexModel n => v j) (flatMap_flatInv hw hΦsrc)
      exact hround.trans hwj
    obtain ⟨B,hB,hEq⟩ := CoordinatePlaneDivision.exists_eq_coord_mul hG hz hvan
    refine ⟨fun p => B (flatMap Φ p),holomorphicAt_comp_flat Φ hy hB,?_⟩
    have ht : Tendsto (flatMap Φ) (𝓝 y) (𝓝 (flatMap Φ y)) :=
      ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).continuousAt.comp
        ((chartAt (ComplexModel n) x).continuousAt hy.1)).tendsto
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy,ht.eventually hEq] with p hp he
    change g (flatInv Φ (flatMap Φ p)) = flatCoord Φ j p * B (flatMap Φ p) at he
    rwa [flatInv_flatMap hp] at he
  · refine ⟨fun p => g p * (flatCoord Φ j p)⁻¹,
      hg.1.mul (BlowupFlatCoordinates.HolomorphicAt.inv (holomorphicAt_flatCoord Φ j hy) hz),?_⟩
    have hn : ∀ᶠ p in 𝓝 y, flatCoord Φ j p ≠ 0 :=
      (holomorphicAt_flatCoord Φ j hy).continuousAt.eventually (isOpen_ne.mem_nhds hz)
    filter_upwards [hn] with p hp
    field_simp

private theorem flatCoord_mem_boundary {H : Set M} {j : Fin n}
    (hH : ∀ z ∈ flatDomain Φ, z ∈ H ↔ flatCoord Φ j z = 0)
    {y : M} (hy : y ∈ flatDomain Φ) :
    (vanishingIdeal (n := n) H).mem y (flatCoord Φ j) := by
  refine ⟨holomorphicAt_flatCoord Φ j hy,?_⟩
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy] with p hp hpH
  exact (hH p hp).mp hpH

include hΦsrc in
/-- The true chart inverse gives the coordinate Kronecker derivative, not an incoming Jacobian. -/
private theorem flatPartial_flatCoord (i j : Fin n) {y : M} (hy : y ∈ flatDomain Φ) :
    flatPartial Φ i (flatCoord Φ j) y = if i = j then 1 else 0 := by
  rw [flatPartial_eq hy (holomorphicAt_flatCoord Φ j hy)]
  have he : flatCoord Φ j ∘ flatInv Φ =ᶠ[𝓝 (flatMap Φ y)] fun w => w j := by
    filter_upwards [Φ.isOpen_target.mem_nhds (flatMap_mem_target hy)] with w hw
    exact congrArg (fun v : ComplexModel n => v j) (flatMap_flatInv hw hΦsrc)
  rw [he.fderiv_eq]
  change (fderiv ℂ (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ) (flatMap Φ y))
    (EuclideanSpace.single i 1) = _
  rw [(EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).fderiv]
  change (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ)
    (EuclideanSpace.single i 1) = _
  by_cases h : i = j
  · subst j
    simp
  · simp [h,Ne.symm h]

private theorem boundaryWeight_holomorphic {l : ℕ} (κ : Fin l → Option (Fin n))
    (j : Fin n) {y : M} (hy : y ∈ flatDomain Φ) :
    HolomorphicAt n (boundaryWeight Φ κ j) y := by
  classical
  unfold boundaryWeight
  split
  · exact holomorphicAt_flatCoord Φ j hy
  · exact holomorphicAt_const 1

private theorem flatPartial_eventuallyEq_product {a b g : M → ℂ} {y : M}
    (hy : y ∈ flatDomain Φ) (ha : HolomorphicAt n a y) (hb : HolomorphicAt n b y)
    (he : g =ᶠ[𝓝 y] fun p => a p * b p) (j : Fin n) :
    flatPartial Φ j g =ᶠ[𝓝 y] fun p =>
      flatPartial Φ j a p * b p + a p * flatPartial Φ j b p := by
  have he' : g =ᶠ[𝓝 y] fun p => ∑ _i : Fin 1, a p * b p := by
    simpa only [Fin.sum_univ_one] using he
  simpa only [Fin.sum_univ_one,flatPartial] using
    (fieldDeriv_eventuallyEq_sum_mul (e := complexChartAt (n := n) x)
      (ξ := flatField Φ (EuclideanSpace.single j 1)) hy.1
      (fun _i : Fin 1 => ha) (fun _i : Fin 1 => hb) he')

include hΦsrc in
private theorem weighted_flatField_boundary {l : ℕ} (κ : Fin l → Option (Fin n))
    {H : Set M} {i : Fin l} {a j : Fin n} (hi : κ i = some a)
    (hH : ∀ z ∈ flatDomain Φ, z ∈ H ↔ flatCoord Φ a z = 0)
    {y : M} (hy : y ∈ flatDomain Φ) :
    IsTangentField H (complexChartAt (n := n) x)
      (fun m p => boundaryWeight Φ κ j p * flatField Φ (EuclideanSpace.single j 1) m p) y := by
  classical
  have hw := boundaryWeight_holomorphic Φ κ j hy
  have hξ := fun m => hw.mul (holomorphicAt_flatField (EuclideanSpace.single j 1) m hy)
  refine ⟨hy.1,hξ,?_⟩
  intro g hg
  obtain ⟨b,hb,he⟩ := exists_eq_flatCoord_mul Φ hΦsrc hH hy hg
  have hprod := flatPartial_eventuallyEq_product Φ hy
    (holomorphicAt_flatCoord Φ a hy) hb he j
  refine ⟨holomorphicAt_fieldDeriv hy.1 hξ hg.1,?_⟩
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy,hprod] with p hp hprodP hpH
  have ha0 : flatCoord Φ a p = 0 := (hH p hp).mp hpH
  rw [fieldDeriv_smul]
  change boundaryWeight Φ κ j p * flatPartial Φ j g p = 0
  rw [hprodP,flatPartial_flatCoord Φ hΦsrc j a hp,ha0,zero_mul,add_zero]
  by_cases hja : j = a
  · subst a
    have hactive : ∃ k, κ k = some j := ⟨i,hi⟩
    simp [boundaryWeight,hactive,ha0]
  · simp [hja]

include hΦsrc in
private theorem weighted_flatField_log {N : Set M} {E : List (Set M)} {k : ℕ}
    (κ : Fin E.length → Option (Fin n))
    (hN : ∀ z ∈ flatDomain Φ, z ∈ N ↔ flatMap Φ z ∈ complexCoordinatePlane n k)
    (hE : ∀ z ∈ flatDomain Φ, ∀ i, z ∈ E.get i ↔
      ∃ a, κ i = some a ∧ flatCoord Φ a z = 0)
    {j : Fin n} (hj : j.val < k) {y : M} (hy : y ∈ flatDomain Φ) :
    IsLogTangentField N E (complexChartAt (n := n) x)
      (fun m p => boundaryWeight Φ κ j p * flatField Φ (EuclideanSpace.single j 1) m p) y := by
  have hflat : ∀ {z : M}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
      (z ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ complexCoordinatePlane n k) :=
    fun hz hz' => hN _ ⟨hz,hz'⟩
  refine ⟨tangent_smul (isTangentField_flatField hΦsrc hflat
    (single_mem_complexCoordinatePlane hj) hy) (boundaryWeight_holomorphic Φ κ j hy),?_⟩
  intro H hH
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH
  subst H
  cases hslot : κ i with
  | none =>
    have hξ := fun m => (boundaryWeight_holomorphic Φ κ j hy).mul
      (holomorphicAt_flatField (EuclideanSpace.single j 1) m hy)
    refine ⟨hy.1,hξ,?_⟩
    intro g hg
    refine ⟨holomorphicAt_fieldDeriv hy.1 hξ hg.1,?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy] with p hp hpH
    obtain ⟨a,ha,_⟩ := (hE p hp i).mp hpH
    rw [hslot] at ha
    cases ha
  | some a =>
    exact weighted_flatField_boundary Φ hΦsrc κ hslot
      (fun z hz => by simpa [hslot] using hE z hz i) hy

include hΦsrc in
private theorem exists_log_coefficients {N : Set M} {E : List (Set M)}
    (κ : Fin E.length → Option (Fin n))
    (hE : ∀ z ∈ flatDomain Φ, ∀ i, z ∈ E.get i ↔
      ∃ a, κ i = some a ∧ flatCoord Φ a z = 0)
    {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {y : M}
    (hy : y ∈ flatDomain Φ) (hξ : IsLogTangentField N E e ξ y) :
    ∃ c : Fin n → M → ℂ, (∀ j, HolomorphicAt n (c j) y) ∧
      ∀ j, fieldDeriv e ξ (flatCoord Φ j) =ᶠ[𝓝 y]
        fun p => boundaryWeight Φ κ j p * c j p := by
  classical
  have hEach (j : Fin n) : ∃ c : M → ℂ, HolomorphicAt n c y ∧
      fieldDeriv e ξ (flatCoord Φ j) =ᶠ[𝓝 y]
        fun p => boundaryWeight Φ κ j p * c p := by
    by_cases ha : ∃ i, κ i = some j
    · obtain ⟨i,hi⟩ := ha
      have hH : ∀ z ∈ flatDomain Φ, z ∈ E.get i ↔ flatCoord Φ j z = 0 := by
        intro z hz
        simpa [hi] using hE z hz i
      have hv := (hξ.2 (E.get i) (List.get_mem E i)).preserves
        (flatCoord Φ j) (flatCoord_mem_boundary Φ hH hy)
      obtain ⟨c,hc,he⟩ := exists_eq_flatCoord_mul Φ hΦsrc hH hy hv
      have hactive : ∃ i, κ i = some j := ⟨i,hi⟩
      refine ⟨c,hc,?_⟩
      simpa only [boundaryWeight,if_pos hactive] using he
    · refine ⟨fieldDeriv e ξ (flatCoord Φ j),
        holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt
          (holomorphicAt_flatCoord Φ j hy),?_⟩
      exact Eventually.of_forall fun p => by simp [boundaryWeight,ha]
  choose c hc he using hEach
  exact ⟨c,hc,he⟩

include hΦsrc in
private theorem all_fields_mod_carrier {N : Set M} {E : List (Set M)} {k : ℕ}
    (κ : Fin E.length → Option (Fin n))
    (hN : ∀ z ∈ flatDomain Φ, z ∈ N ↔ flatMap Φ z ∈ complexCoordinatePlane n k)
    (hE : ∀ z ∈ flatDomain Φ, ∀ i, z ∈ E.get i ↔
      ∃ a, κ i = some a ∧ flatCoord Φ a z = 0)
    {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {y : M}
    (hy : y ∈ flatDomain Φ) (hξ : IsLogTangentField N E e ξ y) :
    ∃ c : Fin n → M → ℂ, (∀ j, HolomorphicAt n (c j) y) ∧
      ∀ (f : M → ℂ), HolomorphicAt n f y →
        (vanishingIdeal (n := n) N).mem y
          (fun p => fieldDeriv e ξ f p -
            ∑ j : Fin n, if j.val < k then
              c j p * (boundaryWeight Φ κ j p * flatPartial Φ j f p) else 0) := by
  classical
  obtain ⟨c,hc,he⟩ := exists_log_coefficients Φ hΦsrc κ hE hy hξ
  have hflat : ∀ {z : M}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
      (z ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ complexCoordinatePlane n k) :=
    fun hz hz' => hN _ ⟨hz,hz'⟩
  have hn (j : Fin n) : ∀ᶠ p in 𝓝 y, k ≤ j.val → p ∈ N →
      fieldDeriv e ξ (flatCoord Φ j) p = 0 := by
    by_cases hj : k ≤ j.val
    · exact ((hξ.1.preserves _ (flatCoord_mem_vanishingIdeal Φ hflat hj hy)).2).mono
        fun p hp _ hpN => hp hpN
    · exact Eventually.of_forall fun _ h => False.elim (hj h)
  refine ⟨c,hc,?_⟩
  intro f hf
  have hSum : HolomorphicAt n
      (fun p => ∑ j : Fin n, if j.val < k then
        c j p * (boundaryWeight Φ κ j p * flatPartial Φ j f p) else 0) y := by
    apply HolomorphicAt.sum
    intro j _
    by_cases hj : j.val < k
    · simpa only [if_pos hj] using
        (hc j).mul ((boundaryWeight_holomorphic Φ κ j hy).mul
          (holomorphicAt_flatPartial j hy hf))
    · simpa only [if_neg hj] using holomorphicAt_const (n := n) (x := y) (0 : ℂ)
  have hDiff := holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt hf
  refine ⟨?_,?_⟩
  · filter_upwards [hDiff,hSum] with p hp hpSum
    exact hp.sub hpSum
  have hchain := fieldDeriv_eventuallyEq_sum_flatPartial hΦsrc e ξ hξ.1.mem_source hy hf
  filter_upwards [hchain,eventually_all.mpr he,eventually_all.mpr hn] with p hp heP hnP hpN
  apply sub_eq_zero.mpr
  rw [hp]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · rw [if_pos hj,heP j]
    ring
  · rw [if_neg hj,hnP j (Nat.le_of_not_lt hj) hpN,zero_mul]


end Flat
end GivenFieldEngines

-- Held original824 native/function/span/log-image proof engines lines26–661;
-- its three PUBLIC parameter factories are imported unchanged. sourceLogGen
-- is only the proof-generator relation for the EXISTING operation, not a new
-- native operator definition. Zero duplicate engine credit.
section NativeStalks
variable {n m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) P] [IsComplexManifold m P]

private theorem exists_original_stalk_function (p : M)
    (r : actualComplexStructureStalk (n := n) p) :
    ∃ (g : M → ℂ) (hg : HolomorphicAt n g p), actualOriginalFunctionGerm p g hg = r := by
  obtain ⟨U,hp,s,rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  refine ⟨sectionExtension U s,sectionExtension_holomorphicAt U s p hp,?_⟩
  exact actualOriginalFunctionGerm_eq_section U p hp s _ _ (Eventually.of_forall fun _ => rfl)

private theorem original_stalk_function_congr (p : M) {g h : M → ℂ}
    (hg : HolomorphicAt n g p) (hh : HolomorphicAt n h p) (he : g =ᶠ[𝓝 p] h) :
    actualOriginalFunctionGerm p g hg = actualOriginalFunctionGerm p h hh := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original p g h hg hh he

private theorem original_stalk_zero (p : M) :
    actualOriginalFunctionGerm p (fun _ => (0 : ℂ)) (holomorphicAt_const (n := n) 0) = 0 := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [actualOriginalFunctionGerm_chart,map_zero]
  rfl

private theorem original_stalk_zero_iff (p : M) {g : M → ℂ} (hg : HolomorphicAt n g p) :
    actualOriginalFunctionGerm p g hg = 0 ↔ g =ᶠ[𝓝 p] fun _ => 0 := by
  constructor
  · intro hz
    have h := congrArg (actualStalkChartEquiv (n := n) p)
      (hz.trans (original_stalk_zero p).symm)
    rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart] at h
    apply original_eventuallyEq_of_preferred_chart_eventuallyEq (n := n) p g (fun _ => 0)
    apply (HolGerm.mk_eq_mk_iff
      (hf := translated_holomorphic (chartAt (ComplexModel n) p p)
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source (ComplexModel n) p) hg))
      (hg := translated_holomorphic (chartAt (ComplexModel n) p p)
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source (ComplexModel n) p)
          (holomorphicAt_const (n := n) 0)))).mp
    exact h
  · intro he
    exact (original_stalk_function_congr p hg (holomorphicAt_const 0) he).trans (original_stalk_zero p)

private theorem native_stalk_original_function {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ) (z : P)
    (g : M → ℂ) (hg : HolomorphicAt n g (σ z)) :
    (ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z (actualOriginalFunctionGerm (σ z) g hg) =
      actualOriginalFunctionGerm z (g ∘ σ)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hσ.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := m) z).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

private theorem original_stalk_mul (p : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f p) (hg : HolomorphicAt n g p) :
    actualOriginalFunctionGerm p (fun q => f q * g q) (hf.mul hg) =
      actualOriginalFunctionGerm p f hf * actualOriginalFunctionGerm p g hg := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [map_mul,actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_mul _ _ _ _

private theorem original_stalk_sub (p : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f p) (hg : HolomorphicAt n g p)
    (hsub : HolomorphicAt n (fun q => f q - g q) p) :
    actualOriginalFunctionGerm p (fun q => f q - g q) hsub =
      actualOriginalFunctionGerm p f hf - actualOriginalFunctionGerm p g hg := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [map_sub,actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_sub _ _ _ _

private theorem original_stalk_sum (p : M) {r : ℕ} (s : Fin r → M → ℂ)
    (hs : ∀ i, HolomorphicAt n (s i) p) :
    actualOriginalFunctionGerm p (fun q => ∑ i, s i q)
      (HolomorphicAt.sum Finset.univ fun i _ => hs i) =
      ∑ i, actualOriginalFunctionGerm p (s i) (hs i) := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [map_sum]
  simp only [actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_sum _ _ _

private theorem span_image_mem {R : Type*} [CommRing R] (p : M)
    (φ : actualComplexStructureStalk (n := n) p →+* R) (L : Ideal R)
    (S : (M → ℂ) → Prop) (hS : ∀ g, S g → HolomorphicAt n g p)
    (hG : ∀ g hg, S g → φ (actualOriginalFunctionGerm p g hg) ∈ L)
    {f : M → ℂ} (hspan : IsInSpanAt (n := n) S p f) :
    φ (actualOriginalFunctionGerm p f hspan.1) ∈ L := by
  obtain ⟨hf,r,s,a,hs,ha,he⟩ := hspan
  have hsa (i) := (ha i).mul (hS (s i) (hs i))
  have hsum := HolomorphicAt.sum Finset.univ fun i _ => hsa i
  rw [original_stalk_function_congr p hf hsum he,
    original_stalk_sum p (fun i q => a i q * s i q) hsa,map_sum]
  apply L.sum_mem
  intro i _
  rw [original_stalk_mul _ _ _ (ha i) (hS (s i) (hs i)),map_mul]
  exact L.mul_mem_left _ (hG (s i) (hS (s i) (hs i)) (hs i))

private theorem native_whole_mono {A B : GermIdeal n M} (hAB : A.Le B) (p : M) :
    actualWholeSheafStalkIdeal A p ≤ actualWholeSheafStalkIdeal B p := by
  apply Ideal.span_le.mpr
  rintro _ ⟨g,hg,hm,rfl⟩
  exact Ideal.subset_span ⟨g,hg,hAB p g hm,rfl⟩

private theorem native_whole_finite_span (A : GermIdeal n M) (p : M)
    {r : ℕ} (s : Fin r → M → ℂ) (hs : ∀ i, HolomorphicAt n (s i) p)
    (hgen : ∀ g, A.mem p g ↔ IsInSpanAt (n := n) (· ∈ Set.range s) p g) :
    actualWholeSheafStalkIdeal A p = Ideal.span (Set.range fun i => actualOriginalFunctionGerm p (s i) (hs i)) := by
  rw [actualWholeSheafStalkIdeal_eq_map_chart,
    wholeChartStalkIdeal_eq_actual_generator_span A p s hs hgen,Ideal.map_span,←Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  apply (actualStalkChartEquiv (n := n) p).injective
  change actualStalkChartEquiv (n := n) p
      ((actualStalkChartEquiv (n := n) p).symm (chartTranslatedGerm p p (mem_chart_source _ p) (s i) (hs i))) = _
  rw [RingEquiv.apply_symm_apply,actualOriginalFunctionGerm_chart]

private def sourceLogGen (N : Set M) (E : List (Set M)) (A : GermIdeal n M)
    (p : M) (s : M → ℂ) : Prop :=
  A.mem p s ∨ (vanishingIdeal (n := n) N).mem p s ∨
    ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (f : M → ℂ),
      IsLogTangentField N E e ξ p ∧ A.mem p f ∧ s = fieldDeriv e ξ f

private theorem sourceLogGen_holomorphic {N : Set M} {E : List (Set M)}
    {A : GermIdeal n M} (hA : A.IsCoherent) (p : M) :
    ∀ g, sourceLogGen N E A p g → HolomorphicAt n g p := by
  rintro g (hg | hg | ⟨e,ξ,f,hξ,hf,rfl⟩)
  · exact GermIdeal.IsCoherent.holomorphicAt_mem hA hg
  · exact hg.1
  · exact holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt
      (GermIdeal.IsCoherent.holomorphicAt_mem hA hf)

omit [IsComplexManifold n M] in
private theorem base_le_log {N : Set M} {E : List (Set M)} {A : GermIdeal n M}
    (hA : A.IsCoherent) : A.Le (logDerivIdealAlong N E A) := by
  intro p g hg
  change IsInSpanAt (sourceLogGen N E A p) p g
  exact isInSpanAt_of_eq_mul (Or.inl hg) (GermIdeal.IsCoherent.holomorphicAt_mem hA hg)
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm)

omit [IsComplexManifold n M] in
private theorem carrier_le_log {N : Set M} {E : List (Set M)} {A : GermIdeal n M} :
    (vanishingIdeal (n := n) N).Le (logDerivIdealAlong N E A) := by
  intro p g hg
  change IsInSpanAt (sourceLogGen N E A p) p g
  exact isInSpanAt_of_eq_mul (Or.inr (Or.inl hg)) hg.1
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm)

omit [IsComplexManifold n M] [IsComplexManifold m P] in
private theorem holomorphic_comp_local {r : M → P} {p : M}
    (hr : ∀ᶠ q in 𝓝 p, MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) r q)
    {g : P → ℂ} (hg : HolomorphicAt m g (r p)) : HolomorphicAt n (g ∘ r) p := by
  filter_upwards [hr,hr.self_of_nhds.continuousAt.eventually hg] with q hq hgq
  exact hgq.comp q hq

/-- A true local geometric section lifts EVERY original native target stalk numerator. -/
private theorem native_stalk_surjective_of_local_retraction {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ)
    (r : M → P) (z : P)
    (hr : ∀ᶠ p in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) r p)
    (hrz : r (σ z) = z) (hsect : ∀ᶠ w in 𝓝 z, r (σ w) = w) :
    Function.Surjective ((ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z) := by
  intro q
  obtain ⟨g,hg,rfl⟩ := exists_original_stalk_function z q
  have hgr : HolomorphicAt n (g ∘ r) (σ z) :=
    holomorphic_comp_local hr (hrz.symm ▸ hg)
  refine ⟨actualOriginalFunctionGerm (σ z) (g ∘ r) hgr,?_⟩
  rw [native_stalk_original_function]
  apply original_stalk_function_congr
  exact hsect.mono fun w hw => congrArg g hw

/-- Native kernel is the SAME whole vanishing ideal, derived by the actual on-carrier roundtrip. -/
private theorem native_stalk_kernel_of_local_retraction {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ)
    (r : M → P) (N : Set M) (z : P)
    (hr : ∀ᶠ p in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) r p)
    (hrz : r (σ z) = z) (hσN : ∀ w, σ w ∈ N)
    (hround : ∀ᶠ p in 𝓝 (σ z), p ∈ N → σ (r p) = p) :
    RingHom.ker ((ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z).hom =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (σ z) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨g,hg,rfl⟩ := exists_original_stalk_function (σ z) q
    have hz : actualOriginalFunctionGerm z (g ∘ σ)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hσ.contMDiffAt)) = 0 := by
      rw [←native_stalk_original_function hσ z g hg]
      exact hq
    have hzero := (original_stalk_zero_iff z _).mp hz
    have hrt : Tendsto r (𝓝 (σ z)) (𝓝 z) := by
      simpa only [hrz] using hr.self_of_nhds.continuousAt.tendsto
    have hN : (vanishingIdeal (n := n) N).mem (σ z) g := by
      refine ⟨hg,?_⟩
      filter_upwards [hround,hrt.eventually hzero] with p hp hz hpN
      exact (congrArg g (hp hpN)).symm.trans hz
    exact Ideal.subset_span ⟨g,hg,hN,rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨g,hg,hmem,rfl⟩
    change (ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z
      (actualOriginalFunctionGerm (σ z) g hg) = 0
    rw [native_stalk_original_function]
    apply (original_stalk_zero_iff z _).mpr
    filter_upwards [hσ.continuous.continuousAt.eventually hmem.2] with w hw
    exact hw (hσN w)

end NativeStalks

section Parameter
variable {n : ℕ} {X : CMfd.{0} n} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (k : ℕ) (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)

include hΦsrc in
private theorem parameter_function_holomorphic (v : parameterOpen Φ k) (g : X → ℂ)
    (hg : HolomorphicAt n g (parameterMapOn Φ k v)) :
    ∀ᶠ w in 𝓝 v.val, DifferentiableAt ℂ (g ∘ parameterMap Φ k) w := by
  have hs := (parameterMap_contMDiffOn Φ k hΦsrc).contMDiffAt
    ((parameterOpen Φ k).isOpen.mem_nhds v.property)
  filter_upwards [(parameterOpen Φ k).isOpen.mem_nhds v.property,
    hs.continuousAt.eventually hg.eventually_nhds] with w hw hgw
  apply mdifferentiableAt_iff_differentiableAt.mp
  exact hgw.self_of_nhds.comp w
    (((parameterMap_contMDiffOn Φ k hΦsrc).contMDiffAt
      ((parameterOpen Φ k).isOpen.mem_nhds hw)).mdifferentiableAt (by simp))

private theorem parameter_function_germ (v : parameterOpen Φ k) (g : X → ℂ)
    (hg : HolomorphicAt n g (parameterMapOn Φ k v)) :
    parameterGermPullback Φ k hΦsrc v (actualOriginalFunctionGerm (parameterMapOn Φ k v) g hg) =
      translatedGerm v.val (g ∘ parameterMap Φ k) (parameter_function_holomorphic Φ k hΦsrc v g hg) := by
  change actualStalkChartEquiv (n := k) v
    ((ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hΦsrc)).stalkMap v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v) g hg)) = _
  rw [native_stalk_original_function (parameterMapOn_contMDiff Φ k hΦsrc) v g hg,
    actualOriginalFunctionGerm_chart]
  have hF : HolomorphicAt k (g ∘ parameterMap Φ k) v.val := by
    filter_upwards [parameter_function_holomorphic Φ k hΦsrc v g hg] with w hw
    exact mdifferentiableAt_iff_differentiableAt.mpr hw
  have he := actualHolomorphicGermPullback_original_function
    (f := (Subtype.val : parameterOpen Φ k → ComplexModel k)) contMDiff_subtype_val v
    (g ∘ parameterMap Φ k) hF
  rw [actualHolomorphicGermPullback_val] at he
  exact he.symm

private theorem coordinateInclusion_single (hk : k ≤ n) (j : Fin k) :
    coordinateInclusion n k (EuclideanSpace.single j 1) =
      EuclideanSpace.single (j.castLE hk) (1 : ℂ) := by
  ext i
  by_cases hij : i = j.castLE hk
  · subst i
    simp [coordinateInclusion_apply,j.isLt]
  · by_cases hi : i.val < k
    · have hne : (⟨i.val,hi⟩ : Fin k) ≠ j := by
        intro h
        apply hij
        exact Fin.ext (congrArg (fun a : Fin k => a.val) h)
      simp [coordinateInclusion_apply,hi,hij,hne]
    · simp [coordinateInclusion_apply,hi,hij]

include hΦsrc in
private theorem parameter_function_derivative (hk : k ≤ n) (j : Fin k)
    (w : ComplexModel k) (hw : w ∈ parameterOpen Φ k) (g : X → ℂ)
    (hg : HolomorphicAt n g (parameterMap Φ k w)) :
    fderiv ℂ (g ∘ parameterMap Φ k) w (EuclideanSpace.single j 1) =
      flatPartial Φ (j.castLE hk) g (parameterMap Φ k w) := by
  have hd := differentiableAt_comp_flatInv hw hΦsrc hg
  change fderiv ℂ ((g ∘ flatInv Φ) ∘ coordinateInclusion n k) w _ = _
  rw [fderiv_comp w hd (coordinateInclusion n k).differentiableAt,
    ContinuousLinearMap.comp_apply,(coordinateInclusion n k).fderiv,
    coordinateInclusion_single k hk j]
  rw [flatPartial_eq (parameterMap_flat_dictionary Φ k hΦsrc w hw).1 hg,
    (parameterMap_flat_dictionary Φ k hΦsrc w hw).2]

private theorem parameter_partial_germ (hk : k ≤ n) (v : parameterOpen Φ k)
    (g : X → ℂ) (hg : HolomorphicAt n g (parameterMapOn Φ k v)) (j : Fin k) :
    parameterGermPullback Φ k hΦsrc v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v) (flatPartial Φ (j.castLE hk) g)
        (holomorphicAt_flatPartial _ (parameterMap_flat_dictionary Φ k hΦsrc v.val v.property).1 hg)) =
      coordinatePartial j (parameterGermPullback Φ k hΦsrc v
        (actualOriginalFunctionGerm (parameterMapOn Φ k v) g hg)) := by
  rw [parameter_function_germ,parameter_function_germ]
  unfold translatedGerm
  rw [coordinatePartial_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  have ht : Tendsto (fun z : ComplexModel k => z + v.val) (𝓝 0) (𝓝 v.val) := by
    have hc : ContinuousAt (fun z : ComplexModel k => z + v.val) 0 := continuousAt_id.add_const v.val
    simpa only [zero_add] using hc.tendsto
  have hs := (parameterMap_contMDiffOn Φ k hΦsrc).contMDiffAt
    ((parameterOpen Φ k).isOpen.mem_nhds v.property)
  filter_upwards [ht.eventually ((parameterOpen Φ k).isOpen.mem_nhds v.property),
    ht.eventually (parameter_function_holomorphic Φ k hΦsrc v g hg),
    ht.eventually (hs.continuousAt.eventually hg.eventually_nhds)] with z hz hF hgz
  have he : fderiv ℂ (fun w => (g ∘ parameterMap Φ k) (w + v.val)) z =
      fderiv ℂ (g ∘ parameterMap Φ k) (z + v.val) := by
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using
      (hF.hasFDerivAt.comp z ((hasFDerivAt_id z).add_const v.val)).fderiv
  rw [he,parameter_function_derivative Φ k hΦsrc hk j (z + v.val) hz g hgz]
  rfl

include hΦsrc in
private theorem weight_holomorphic {l : ℕ} (κ : Fin l → Option (Fin n)) (i : Fin n)
    (v : parameterOpen Φ k) :
    HolomorphicAt n (boundaryWeight Φ κ i) (parameterMapOn Φ k v) := by
  classical
  unfold boundaryWeight
  split
  · exact holomorphicAt_flatCoord Φ i (parameterMap_flat_dictionary Φ k hΦsrc v.val v.property).1
  · exact holomorphicAt_const 1

private theorem parameter_weight_germ {l : ℕ} (κ : Fin l → Option (Fin n)) (hk : k ≤ n)
    (v : parameterOpen Φ k) (j : Fin k) :
    parameterGermPullback Φ k hΦsrc v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v) (boundaryWeight Φ κ (j.castLE hk))
        (weight_holomorphic Φ k hΦsrc κ (j.castLE hk) v)) = parameterWeight Φ k κ hk v j := by
  classical
  rw [parameter_function_germ]
  by_cases ha : ∃ i, κ i = some (j.castLE hk)
  · simp only [parameterWeight,if_pos ha,boundaryWeight]
    change HolGerm.mk (fun z => flatCoord Φ (j.castLE hk) (parameterMap Φ k (z + v.val))) _ =
      HolGerm.constHom (v.val j) + coordinateGerm j
    rw [coordinateGerm,HolGerm.constHom_apply,←HolGerm.mk_add]
    apply HolGerm.mk_eq_mk_iff.mpr
    have ht : Tendsto (fun z : ComplexModel k => z + v.val) (𝓝 0) (𝓝 v.val) := by
      have hc : ContinuousAt (fun z : ComplexModel k => z + v.val) 0 := continuousAt_id.add_const v.val
      simpa only [zero_add] using hc.tendsto
    filter_upwards [ht.eventually ((parameterOpen Φ k).isOpen.mem_nhds v.property)] with z hz
    have h := congrArg (fun w : ComplexModel n => w (j.castLE hk))
      (parameterMap_flat_dictionary Φ k hΦsrc (z + v.val) hz).2
    calc
      _ = coordinateInclusion n k (z + v.val) (j.castLE hk) := h
      _ = (z + v.val) j := by simp [coordinateInclusion_apply,j.isLt]
      _ = v.val j + z j := by simp [add_comm]
  · simp [parameterWeight,ha,boundaryWeight,translatedGerm,HolGerm.mk_const]

include hΦsrc in
private theorem parameter_retraction_section (hk : k ≤ n) (v w : parameterOpen Φ k) :
    actualParameterRetraction Φ k v (parameterMapOn Φ k w) = w := by
  change openInv (parameterOpen Φ k) v
    (coordinateProjection n k (flatMap Φ (parameterMap Φ k w.val))) = w
  rw [(parameterMap_roundtrip Φ k hk hΦsrc).1 w.val w.property]
  simp [openInv,w.property]

private theorem parameter_whole_kernel {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) :
    Function.Surjective (parameterStalkMap Φ k hΦsrc v) ∧
      RingHom.ker (parameterStalkMap Φ k hΦsrc v) =
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v) := by
  have hg := actual_parameter_retraction_geometry Φ hk hΦsrc N hN v
  constructor
  · exact native_stalk_surjective_of_local_retraction (parameterMapOn_contMDiff Φ k hΦsrc)
      (actualParameterRetraction Φ k v) v hg.2.1 hg.2.2.1
      (Eventually.of_forall fun w => parameter_retraction_section Φ k hΦsrc hk v w)
  · exact native_stalk_kernel_of_local_retraction (parameterMapOn_contMDiff Φ k hΦsrc)
      (actualParameterRetraction Φ k v) N v hg.2.1 hg.2.2.1 hg.1 hg.2.2.2

private theorem parameter_germ_kernel {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) :
    RingHom.ker (parameterGermPullback Φ k hΦsrc v) =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v) := by
  rw [←(parameter_whole_kernel Φ k hΦsrc hk hN v).2]
  ext r
  change actualStalkChartEquiv (n := k) v (parameterStalkMap Φ k hΦsrc v r) = 0 ↔
    parameterStalkMap Φ k hΦsrc v r = 0
  constructor
  · intro h
    apply (actualStalkChartEquiv (n := k) v).injective
    simpa only [map_zero] using h
  · intro h
    simp only [h,map_zero]

private theorem parameter_germ_surjective {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) : Function.Surjective (parameterGermPullback Φ k hΦsrc v) :=
  (actualStalkChartEquiv (n := k) v).surjective.comp (parameter_whole_kernel Φ k hΦsrc hk hN v).1

private def carrierQuotientEquiv {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) :
    (actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v)) ≃+*
      actualComplexStructureStalk (n := k) v :=
  (Ideal.quotEquivOfEq (parameter_whole_kernel Φ k hΦsrc hk hN v).2.symm).trans
    (RingHom.quotientKerEquivOfSurjective (parameter_whole_kernel Φ k hΦsrc hk hN v).1)

private theorem carrierQuotientEquiv_mk {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k)
    (r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v)) :
    carrierQuotientEquiv Φ k hΦsrc hk hN v (Ideal.Quotient.mk _ r) =
      parameterStalkMap Φ k hΦsrc v r := by
  rfl

private theorem parameter_complex_square :
    ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hΦsrc) ≫
        ambientPointMap n X = ambientPointMap k (parameterOpen Φ k) := by
  exact (ChartedSpace.locallyRingedSpace_comp 𝓘(ℂ,ComplexModel 0) (parameterMapOn_contMDiff Φ k hΦsrc)
    (contMDiff_const : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel 0) ∞
      (fun _ : X => (0 : ComplexModel 0)))).symm

end Parameter

section WholeLogarithmicImage
variable {k : ℕ}

/-- Held Leibniz/span engine specialized to ALL analytic coefficients of a whole finite ideal.
This generic plumbing receives no repeated independent engine credit. -/
private theorem derivative_of_span_mem
    (D : Derivation ℂ (HolGerm (ComplexModel k)) (HolGerm (ComplexModel k)))
    {r : ℕ} (G : Fin r → HolGerm (ComplexModel k))
    (J L : Ideal (HolGerm (ComplexModel k))) (hJ : J = Ideal.span (Set.range G))
    (hJL : J ≤ L) (hD : ∀ i, D (G i) ∈ L) : ∀ f ∈ J, D f ∈ L := by
  let K : Ideal (HolGerm (ComplexModel k)) :=
    { carrier := {f | f ∈ J ∧ D f ∈ L}
      zero_mem' := ⟨J.zero_mem,by rw [map_zero];exact L.zero_mem⟩
      add_mem' := by
        intro f g hf hg
        exact ⟨J.add_mem hf.1 hg.1,by rw [map_add];exact L.add_mem hf.2 hg.2⟩
      smul_mem' := by
        intro c f hf
        refine ⟨J.mul_mem_left c hf.1,?_⟩
        rw [smul_eq_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul]
        exact L.add_mem (L.mul_mem_left c hf.2) (hJL (J.mul_mem_right _ hf.1)) }
  have hJK : J ≤ K := by
    rw [hJ]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨hJ.symm ▸ Ideal.subset_span ⟨i,rfl⟩,hD i⟩
  intro f hf
  exact (hJK hf).2

/-- Whole ideal equality covers EVERY member and coefficient, not selected generator values. -/
private theorem logIdeal_eq_finite_span (a : Fin k → HolGerm (ComplexModel k))
    {r : ℕ} (G : Fin r → HolGerm (ComplexModel k))
    (J : Ideal (HolGerm (ComplexModel k))) (hJ : J = Ideal.span (Set.range G)) :
    logIdeal a J = J ⊔ Ideal.span {h | ∃ (j : Fin k) (i : Fin r), h = logDirection a j (G i)} := by
  let L := J ⊔ Ideal.span {h | ∃ (j : Fin k) (i : Fin r), h = logDirection a j (G i)}
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    apply Ideal.span_le.mpr
    rintro _ ⟨j,f,hf,rfl⟩
    exact derivative_of_span_mem (logDirection a j) G J L hJ le_sup_left
      (fun i => (show Ideal.span _ ≤ L from le_sup_right) (Ideal.subset_span ⟨j,i,rfl⟩)) f hf
  · refine sup_le le_sup_left ?_
    apply Ideal.span_le.mpr
    rintro _ ⟨j,i,rfl⟩
    exact (show Ideal.span _ ≤ logIdeal a J from le_sup_right)
      (Ideal.subset_span ⟨j,G i,hJ.symm ▸ Ideal.subset_span ⟨i,rfl⟩,rfl⟩)

end WholeLogarithmicImage

section LogImage
variable {n : ℕ} {X : CMfd.{0} n} {x : X}
  (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
  (k : ℕ) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)

private theorem frame_derivative_image_mem {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (κ : Fin E.length → Option (Fin n)) (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) (e : ComplexChart n X) (ξ : Fin n → X → ℂ)
    (hξ : IsLogTangentField N E e ξ (parameterMapOn Φ k v)) (f : X → ℂ)
    (hf : A.mem (parameterMapOn Φ k v) f) (c : Fin n → X → ℂ)
    (hc : ∀ j, HolomorphicAt n (c j) (parameterMapOn Φ k v))
    (hr : (vanishingIdeal (n := n) N).mem (parameterMapOn Φ k v)
      (fun p => fieldDeriv e ξ f p - ∑ j : Fin n, if j.val < k then
        c j p * (boundaryWeight Φ κ j p * flatPartial Φ j f p) else 0)) :
    parameterGermPullback Φ k hsrc v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v) (fieldDeriv e ξ f)
        (holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt
          (GermIdeal.IsCoherent.holomorphicAt_mem hA hf))) ∈
      logIdeal (parameterWeight Φ k κ hk v)
        (Ideal.map (parameterGermPullback Φ k hsrc v)
          (actualWholeSheafStalkIdeal A (parameterMapOn Φ k v))) := by
  classical
  let p := parameterMapOn Φ k v
  let φ := parameterGermPullback Φ k hsrc v
  let a := parameterWeight Φ k κ hk v
  let J := Ideal.map φ (actualWholeSheafStalkIdeal A p)
  let L := logIdeal a J
  have hpΦ : p ∈ flatDomain Φ := (parameterMap_flat_dictionary Φ k hsrc v.val v.property).1
  have hfhol := GermIdeal.IsCoherent.holomorphicAt_mem hA hf
  have hD := holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt hfhol
  let B : Fin n → X → ℂ := fun j q => if j.val < k then
    c j q * (boundaryWeight Φ κ j q * flatPartial Φ j f q) else 0
  have hB (j) : HolomorphicAt n (B j) p := by
    by_cases hj : j.val < k
    · simpa only [B,if_pos hj] using (hc j).mul
        ((weight_holomorphic Φ k hsrc κ j v).mul (holomorphicAt_flatPartial j hpΦ hfhol))
    · simpa only [B,if_neg hj] using holomorphicAt_const (n := n) (x := p) (0 : ℂ)
  have hsum := HolomorphicAt.sum Finset.univ fun j _ => hB j
  have hR0 : φ (actualOriginalFunctionGerm p
      (fun q => fieldDeriv e ξ f q - ∑ j, B j q) hr.1) = 0 := by
    change actualOriginalFunctionGerm p _ _ ∈ RingHom.ker (parameterGermPullback Φ k hsrc v)
    rw [parameter_germ_kernel Φ k hsrc hk hN v]
    exact Ideal.subset_span ⟨_,hr.1,hr,rfl⟩
  rw [original_stalk_sub _ _ _ hD hsum hr.1,map_sub,original_stalk_sum p B hB,map_sum] at hR0
  rw [sub_eq_zero.mp hR0]
  apply L.sum_mem
  intro j _
  by_cases hj : j.val < k
  · simp only [B,if_pos hj]
    have hw := weight_holomorphic Φ k hsrc κ j v
    have hP := holomorphicAt_flatPartial j hpΦ hfhol
    rw [original_stalk_mul _ _ _ (hc j) (hw.mul hP),map_mul]
    apply L.mul_mem_left
    let jj : Fin k := ⟨j.val,hj⟩
    have hcast : jj.castLE hk = j := Fin.ext rfl
    have he := actual_weighted_field_pullback_germ Φ k hsrc κ hk v f hfhol jj
    rw [hcast] at he
    rw [he]
    exact (show Ideal.span _ ≤ L from le_sup_right)
      (Ideal.subset_span ⟨jj,φ (actualOriginalFunctionGerm p f hfhol),
        Ideal.mem_map_of_mem φ (Ideal.subset_span ⟨f,hfhol,hf,rfl⟩),rfl⟩)
  · simp only [B,if_neg hj,original_stalk_zero (n := n) p,map_zero]
    exact L.zero_mem

private theorem whole_log_image_eq {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (κ : Fin E.length → Option (Fin n)) (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k)
    (hfields : ∀ j : Fin k, IsLogTangentField N E (complexChartAt (n := n) x)
      (fun m p => boundaryWeight Φ κ (j.castLE hk) p *
        flatField Φ (EuclideanSpace.single (j.castLE hk) 1) m p) (parameterMapOn Φ k v))
    (hcoeff : ∀ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsLogTangentField N E e ξ (parameterMapOn Φ k v) →
      ∃ c : Fin n → X → ℂ, (∀ j, HolomorphicAt n (c j) (parameterMapOn Φ k v)) ∧
        ∀ f, HolomorphicAt n f (parameterMapOn Φ k v) →
          (vanishingIdeal (n := n) N).mem (parameterMapOn Φ k v)
            (fun p => fieldDeriv e ξ f p - ∑ j : Fin n, if j.val < k then
              c j p * (boundaryWeight Φ κ j p * flatPartial Φ j f p) else 0)) :
    Ideal.map (parameterGermPullback Φ k hsrc v)
      (actualWholeSheafStalkIdeal (logDerivIdealAlong N E A) (parameterMapOn Φ k v)) =
      logIdeal (parameterWeight Φ k κ hk v)
        (Ideal.map (parameterGermPullback Φ k hsrc v)
          (actualWholeSheafStalkIdeal A (parameterMapOn Φ k v))) := by
  classical
  let p := parameterMapOn Φ k v
  let φ := parameterGermPullback Φ k hsrc v
  let a := parameterWeight Φ k κ hk v
  let J := Ideal.map φ (actualWholeSheafStalkIdeal A p)
  let K := Ideal.map φ (actualWholeSheafStalkIdeal (logDerivIdealAlong N E A) p)
  have hpΦ : p ∈ flatDomain Φ := (parameterMap_flat_dictionary Φ k hsrc v.val v.property).1
  have hbase : J ≤ K := Ideal.map_mono (native_whole_mono (base_le_log (N := N) (E := E) hA) p)
  apply le_antisymm
  · rw [actualWholeSheafStalkIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨r,⟨f,hf,hm,rfl⟩,rfl⟩
    change IsInSpanAt (sourceLogGen N E A p) p f at hm
    apply span_image_mem p φ (logIdeal a J) (sourceLogGen N E A p)
      (sourceLogGen_holomorphic hA p) ?_ hm
    rintro g hg (hmem | hmem | ⟨e,ξ,f,hξ,hf,rfl⟩)
    · exact (show J ≤ logIdeal a J from le_sup_left)
        (Ideal.mem_map_of_mem φ (Ideal.subset_span ⟨g,hg,hmem,rfl⟩))
    · have hz : φ (actualOriginalFunctionGerm p g hg) = 0 := by
        change actualOriginalFunctionGerm p g hg ∈ RingHom.ker (parameterGermPullback Φ k hsrc v)
        rw [parameter_germ_kernel Φ k hsrc hk hN v]
        exact Ideal.subset_span ⟨g,hg,hmem,rfl⟩
      rw [hz]
      exact Ideal.zero_mem _
    · obtain ⟨c,hc,hr⟩ := hcoeff e ξ hξ
      exact frame_derivative_image_mem Φ k hsrc A hA κ hk hN v e ξ hξ f hf c hc
        (hr f (GermIdeal.IsCoherent.holomorphicAt_mem hA hf))
  · obtain ⟨U,hU,hp,r,s,hs,hgen⟩ := hA p
    have hhol (i : Fin r) : HolomorphicAt n (s i) p :=
      eventually_of_mem (hU.mem_nhds hp) fun q hq =>
        (hs i q hq).mdifferentiableAt (hU.mem_nhds hq)
    let G : Fin r → HolGerm (ComplexModel k) := fun i => φ (actualOriginalFunctionGerm p (s i) (hhol i))
    have hJ : J = Ideal.span (Set.range G) := by
      change Ideal.map φ (actualWholeSheafStalkIdeal A p) = _
      rw [native_whole_finite_span A p s hhol (hgen p hp),Ideal.map_span,←Set.range_comp]
      rfl
    rw [logIdeal_eq_finite_span a G J hJ]
    refine sup_le hbase ?_
    apply Ideal.span_le.mpr
    rintro _ ⟨j,i,rfl⟩
    have hsi : A.mem p (s i) := (hgen p hp _).mpr
      (isInSpanAt_of_eq_mul ⟨i,rfl⟩ (hhol i) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm))
    let jj := j.castLE hk
    let w : X → ℂ := fun q => boundaryWeight Φ κ jj q * flatPartial Φ jj (s i) q
    have hw : HolomorphicAt n w p := (weight_holomorphic Φ k hsrc κ jj v).mul
      (holomorphicAt_flatPartial jj hpΦ (hhol i))
    have he : w = fieldDeriv (complexChartAt (n := n) x)
        (fun m q => boundaryWeight Φ κ jj q * flatField Φ (EuclideanSpace.single jj 1) m q) (s i) := by
      funext q
      simp only [w,flatPartial,fieldDeriv,Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hGen : sourceLogGen N E A p w :=
      Or.inr (Or.inr ⟨_,_,s i,hfields j,hsi,he⟩)
    have hLog : (logDerivIdealAlong N E A).mem p w := by
      change IsInSpanAt (sourceLogGen N E A p) p w
      exact isInSpanAt_of_eq_mul hGen hw (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    have himage : φ (actualOriginalFunctionGerm p w hw) ∈ K :=
      Ideal.mem_map_of_mem φ (Ideal.subset_span ⟨w,hw,hLog,rfl⟩)
    exact (actual_weighted_field_pullback_germ Φ k hsrc κ hk v (s i) (hhol i) j) ▸ himage

end LogImage


theorem fixed_chart_actual_log_dictionary
    {n : ℕ} {X : CMfd.{0} n} {x : X} {N : Set X} {E : List (Set X)}
    (Phi : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (k : ℕ) (hk : k≤n)
    (hsrc : Phi.source⊆(chartAt (ComplexModel n) x).target)
    (kappa : Fin E.length→Option (Fin n))
    (hcharts : ∀ p∈flatDomain Phi,
      (p∈N ↔ flatMap Phi p∈complexCoordinatePlane n k) ∧
      ∀ i,p∈E.get i ↔ ∃ j,kappa i=some j ∧ flatCoord Phi j p=0)
    (B : GermIdeal n X) (hB : B.IsCoherent) :
    ∀ v : parameterOpen Phi k,
      let phi:=parameterGermPullback Phi k hsrc v
      let a:=parameterWeight Phi k kappa hk v
      let J:=Ideal.map phi (actualWholeSheafStalkIdeal B (parameterMapOn Phi k v))
      let D:=actualWholeSheafStalkIdeal (logDerivIdealAlong N E B) (parameterMapOn Phi k v)
      Function.Surjective phi ∧
      RingHom.ker phi=actualWholeSheafStalkIdeal (vanishingIdeal (n:=n) N) (parameterMapOn Phi k v) ∧
      Ideal.map phi D=logIdeal a J ∧ Ideal.comap phi (logIdeal a J)=D ∧
      ∀ r : actualComplexStructureStalk (n:=n) (M:=X) (parameterMapOn Phi k v),
        r∈D ↔ phi r∈logIdeal a J := by
  intro v
  dsimp only
  have hn := fun p hp => (hcharts p hp).1
  have he := fun p hp => (hcharts p hp).2
  have hv := (parameterMap_flat_dictionary Phi k hsrc v.val v.property).1
  have hmap := whole_log_image_eq Phi k hsrc B hB kappa hk hn v
    (fun j => weighted_flatField_log Phi hsrc kappa hn he j.isLt hv)
    (fun e ξ hξ => all_fields_mod_carrier Phi hsrc kappa hn he hv hξ)
  have hs := parameter_germ_surjective Phi k hsrc hk hn v
  have hkern := parameter_germ_kernel Phi k hsrc hk hn v
  have hkd : RingHom.ker (parameterGermPullback Phi k hsrc v)≤
      actualWholeSheafStalkIdeal (logDerivIdealAlong N E B) (parameterMapOn Phi k v) := by
    rw [hkern]
    exact native_whole_mono (carrier_le_log (E:=E) (A:=B)) _
  have hinv : Ideal.comap (parameterGermPullback Phi k hsrc v)
      (logIdeal (parameterWeight Phi k kappa hk v)
        (Ideal.map (parameterGermPullback Phi k hsrc v)
          (actualWholeSheafStalkIdeal B (parameterMapOn Phi k v)))) =
      actualWholeSheafStalkIdeal (logDerivIdealAlong N E B) (parameterMapOn Phi k v) := by
    rw [←hmap,Ideal.comap_map_of_surjective _ hs,←RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hkd
  refine ⟨hs,hkern,hmap,hinv,?_⟩
  intro r
  exact (Iff.of_eq (congrArg (fun I => r∈I) hinv)).symm

private def nativeStalkTransport {d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M] {p q : M} (h : p=q) :
    actualComplexStructureStalk (n:=d) p ≃+* actualComplexStructureStalk (n:=d) q :=
  h ▸ RingEquiv.refl _

section FixedNativeLogOutput
variable {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
  {A : GermIdeal n X} {x : X} (F : OriginalLogFrame A N E x)
  (G : ProjectionCarrierQuotientOutput F)

private abbrev piX (_F : OriginalLogFrame A N E x) : projectionAmbient X→X := Prod.fst
private abbrev sigma (v : parameterOpen F.Φ F.k) := parameterMapOn F.Φ F.k v
private abbrev Sigma : parameterProduct F→projectionAmbient X := productParameterMap F
private abbrev Nplus : Set (projectionAmbient X) := (piX F) ⁻¹' N
private abbrev Eplus : List (Set (projectionAmbient X)) := projectedBoundary F
private abbrev pulled (B : GermIdeal n X) := GermIdeal.pullback (m:=n+1) (piX F) B
private abbrev Dold (_F : OriginalLogFrame A N E x) (B : GermIdeal n X) := logDerivIdealAlong N E B
private abbrev Dnew (B : GermIdeal n X) := logDerivIdealAlong (Nplus F) (Eplus F) (pulled F B)
private abbrev R (t : parameterProduct F) := actualComplexStructureStalk (n:=n) (M:=X) (sigma F t.1)
private abbrev Rplus (t : parameterProduct F) :=
  actualComplexStructureStalk (n:=n+1) (M:=projectionAmbient X) (Sigma F t)
private abbrev K (B : GermIdeal n X) (t : parameterProduct F) := actualWholeSheafStalkIdeal B (sigma F t.1)
private abbrev Kplus (B : GermIdeal (n+1) (projectionAmbient X)) (t : parameterProduct F) :=
  actualWholeSheafStalkIdeal B (Sigma F t)
private abbrev phi (t : parameterProduct F) := parameterGermPullback F.Φ F.k F.hsrc t.1
private abbrev phiPlus (t : parameterProduct F) : Rplus F t →+* HolGerm (ComplexModel (F.k+1)) :=
  (actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t).toRingHom.comp
    ((ChartedSpace.locallyRingedSpaceMap (Sigma F) G.geometry.sigma_holo).stalkMap t).hom
private abbrev piNative (t : parameterProduct F) : R F t →+* Rplus F t :=
  ((ChartedSpace.locallyRingedSpaceMap (piX F)
    (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1))).stalkMap (Sigma F t)).hom
private abbrev T := HironakaRelativeNormalIdeal.tangentPullback F.k 1
private abbrev L (B : GermIdeal n X) (t : parameterProduct F) :=
  logIdeal (parameterWeight F.Φ F.k F.κ F.hk t.1) (Ideal.map (phi F t) (K F B t))
private abbrev Lplus (B : GermIdeal n X) (t : parameterProduct F) := Ideal.map (T F).toRingHom (L F B t)
private abbrev coordinateQuotient (B : GermIdeal n X) (t : parameterProduct F) :=
  Ideal.quotientMap (Lplus F B t) (T F).toRingHom Ideal.le_comap_map

-- All four maps fixed before the quotient; source/product native operator ideals literal.
abbrev NewNativeLogProjectionDiagram (B : GermIdeal n X) (t : parameterProduct F) :=
  NativeQuotientDiagram
    ((Ideal.Quotient.mk (L F B t)).comp (phi F t))
    ((Ideal.Quotient.mk (Lplus F B t)).comp (phiPlus F G t))
    (piNative F t) (coordinateQuotient F B t)
    (K F (Dold F B) t) (Kplus F (Dnew F B) t)

structure SameRingNativeLogEqualityQuotient (B : GermIdeal n X) (t : parameterProduct F) where
  ideal_eq : Kplus F (pulled F (Dold F B)) t=Kplus F (Dnew F B) t
  e : (Rplus F t ⧸ Kplus F (pulled F (Dold F B)) t) ≃+*
    (Rplus F t ⧸ Kplus F (Dnew F B) t)
  e_mk : ∀ r,e (Ideal.Quotient.mk _ r)=Ideal.Quotient.mk _ r
  e_inv_mk : ∀ r,e.symm (Ideal.Quotient.mk _ r)=Ideal.Quotient.mk _ r
  e_action : ∀ r q,e (Ideal.Quotient.mk _ r*q)=Ideal.Quotient.mk _ r*e q

private abbrev Wplus := parameterOpen (X:=projectionAmbient X) G.geometry.Ψ (F.k+1)
private abbrev sigmaPlus := parameterMapOn (X:=projectionAmbient X) G.geometry.Ψ (F.k+1)
private abbrev factoryPhi (w : Wplus F G) :=
  parameterGermPullback (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) G.geometry.hsrc w
private abbrev factoryL (B : GermIdeal n X) (w : Wplus F G) :=
  logIdeal (parameterWeight (X:=projectionAmbient X) G.geometry.Ψ (F.k+1)
    (projectedAmbientSlot F) (Nat.succ_le_succ F.hk) w)
    (Ideal.map (factoryPhi F G w) (actualWholeSheafStalkIdeal (pulled F B) (sigmaPlus F G w)))

structure FactoryNewNativeLogQuotient (B : GermIdeal n X) (w : Wplus F G) where
  image : Ideal.map (factoryPhi F G w) (actualWholeSheafStalkIdeal (Dnew F B) (sigmaPlus F G w))=
    factoryL F G B w
  comap : Ideal.comap (factoryPhi F G w) (factoryL F G B w)=
    actualWholeSheafStalkIdeal (Dnew F B) (sigmaPlus F G w)
  all_numerators : ∀ r,r∈actualWholeSheafStalkIdeal (Dnew F B) (sigmaPlus F G w) ↔
    factoryPhi F G w r∈factoryL F G B w
  e : (actualComplexStructureStalk (n:=n+1) (M:=projectionAmbient X) (sigmaPlus F G w) ⧸
    actualWholeSheafStalkIdeal (Dnew F B) (sigmaPlus F G w)) ≃+*
    (HolGerm (ComplexModel (F.k+1)) ⧸ factoryL F G B w)
  e_mk : ∀ r,e (Ideal.Quotient.mk _ r)=Ideal.Quotient.mk _ (factoryPhi F G w r)
  e_action : ∀ r q,e (Ideal.Quotient.mk _ r*q)=Ideal.Quotient.mk _ (factoryPhi F G w r)*e q

structure NativeProjectionLogOutput where
  coherent_old : ∀ B : GermIdeal n X,B.IsCoherent→(Dold F B).IsCoherent
  coherent_pull : ∀ B : GermIdeal n X,B.IsCoherent→(pulled F (Dold F B)).IsCoherent
  coherent_new : ∀ B : GermIdeal n X,B.IsCoherent→(Dnew F B).IsCoherent
  global_operator_eq : ∀ B : GermIdeal n X,B.IsCoherent→pulled F (Dold F B)=Dnew F B
  every_native_ideal : ∀ (B : GermIdeal n X),B.IsCoherent→∀ t,
    Kplus F (pulled F (Dold F B)) t=Kplus F (Dnew F B) t
  every_original_function : ∀ (B : GermIdeal n X),B.IsCoherent→∀ (y : projectionAmbient X)
    (g : projectionAmbient X→ℂ) (_hg : HolomorphicAt (n+1) g y),
    (pulled F (Dold F B)).mem y g ↔ (Dnew F B).mem y g
  every_product_image_comap : ∀ (B : GermIdeal n X),B.IsCoherent→∀ t,
    Ideal.map (phiPlus F G t) (Kplus F (Dnew F B) t)=Lplus F B t ∧
    Ideal.comap (phiPlus F G t) (Lplus F B t)=Kplus F (Dnew F B) t ∧
    ∀ r,r∈Kplus F (Dnew F B) t ↔ phiPlus F G t r∈Lplus F B t
  equality_quotient : ∀ (B : GermIdeal n X),B.IsCoherent→∀ t,
    SameRingNativeLogEqualityQuotient F B t
  any_old_choice : ∀ (B : GermIdeal n X),B.IsCoherent→∀ t,
    ∀ eOld : (R F t ⧸ K F (Dold F B) t) ≃+* (HolGerm (ComplexModel F.k) ⧸ L F B t),
    (∀ r,eOld (Ideal.Quotient.mk _ r)=Ideal.Quotient.mk _ (phi F t r))→
    ∃ Q : NewNativeLogProjectionDiagram F G B t,Q.e=eOld
  factory_new : ∀ (B : GermIdeal n X),B.IsCoherent→∀ w,FactoryNewNativeLogQuotient F G B w
  -- Every dependent point is transported via the ACTUAL G.geometry.sigma w.
  factory_every_native_germ : ∀ w (r : Rplus F (G.geometry.rho w)),
    factoryPhi F G w (nativeStalkTransport (G.geometry.sigma w).symm r)=phiPlus F G (G.geometry.rho w) r
  -- The complete inherited G stays an index/output, including its FULL native
  -- triangles, ALL complex-point stalk scalars, actual constants, every ordered
  -- old/empty/horizontal label, c+zlast, native maps, and separate domain s+1.
  -- NativeQuotientDiagram includes surjectivity, EXACT kernels/ideal_map,
  -- e/e' ALL-mk/actions, independently induced fbar, ALL-class square.
  -- FactoryNewNativeLogQuotient contains corresponding EVERY-r/EVERY-class laws.
end FixedNativeLogOutput

-- Held actual projection-record global product-chart/full-boundary geometry.
-- Explicit private recompilation with zero duplicate credit; no imported
-- private calls or global purity assumption, including empty N.
section GlobalProductGeometry
open ProductComplexManifold
variable {n : ℕ} {X : CMfd.{0} n}
private def boundary (E : List (Set X)) : List (Set (projectionAmbient X)) :=
  E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]

private def liftAxes (S : Finset (Fin n)) : Finset (Fin (n+1)) :=
  S.map (Fin.castAddEmb 1)

private theorem last_not_lift (S : Finset (Fin n)) : Fin.last n ∉ liftAxes S := by
  intro h
  obtain ⟨i,_hi,he⟩:=Finset.mem_map.mp h
  have hv:=congrArg Fin.val he
  change i.val=n at hv
  exact (Nat.ne_of_lt i.isLt) hv

private theorem split_old (w : ComplexModel (n+1)) (i : Fin n) :
    ((prodModelEquiv n 1).symm w).1 i=w (i.castAdd 1) := by
  rfl

private theorem split_normal (w : ComplexModel (n+1)) (i : Fin 1) :
    ((prodModelEquiv n 1).symm w).2 i=w (i.natAdd n) := by
  rfl

private theorem product_old (a : ComplexModel n) (b : ComplexModel 1) (i : Fin n) :
    prodModelEquiv n 1 (a,b) (i.castAdd 1)=a i := by
  have h:=congrArg (fun z : ComplexModel n × ComplexModel 1 => z.1 i)
    ((prodModelEquiv n 1).symm_apply_apply (a,b))
  rw [split_old] at h
  exact h

private theorem product_last (a : ComplexModel n) (b : ComplexModel 1) :
    prodModelEquiv n 1 (a,b) (Fin.last n)=b 0 := by
  have he : Fin.last n=(0 : Fin 1).natAdd n:=Fin.ext (by simp)
  rw [he]
  have h:=congrArg (fun z : ComplexModel n × ComplexModel 1 => z.2 0)
    ((prodModelEquiv n 1).symm_apply_apply (a,b))
  rw [split_normal] at h
  exact h

private theorem product_mask (a : ComplexModel n) (b : ComplexModel 1) (S : Finset (Fin n)) :
    prodModelEquiv n 1 (a,b)∈coordSubspace (liftAxes S) ↔ a∈coordSubspace S := by
  constructor
  · intro h i hi
    exact (product_old a b i) ▸ h (i.castAdd 1) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  · intro h j hj
    obtain ⟨i,hi,rfl⟩:=Finset.mem_map.mp hj
    change prodModelEquiv n 1 (a,b) (i.castAdd 1)=0
    rw [product_old]
    exact h i hi

private theorem product_normal (a : ComplexModel n) (b : ComplexModel 1) :
    prodModelEquiv n 1 (a,b)∈coordSubspace {Fin.last n} ↔ b=0 := by
  constructor
  · intro h
    ext i
    obtain rfl : i=0:=Subsingleton.elim _ _
    simpa only [product_last,PiLp.zero_apply] using h (Fin.last n) (Finset.mem_singleton_self _)
  · intro hb j hj
    rw [Finset.mem_singleton.mp hj,product_last,hb]
    rfl

private def productCoordinates (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1)) :
    LocalHolomorphicEquivAt (n := n+1) (chartAt (ComplexModel (n+1)) p p) where
  source := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.source
  target := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  isOpen_target := Φ.isOpen_target.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  center_mem_source := by
    simpa only [mem_preimage,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply]
      using Φ.center_mem_source
  toFun w := prodModelEquiv n 1
    (Φ.toFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2-p.2)
  invFun w := prodModelEquiv n 1
    (Φ.invFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2+p.2)
  toFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.toFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.sub_const p.2).differentiableOn)
  invFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.invFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.add_const p.2).differentiableOn)
  mapsTo_toFun := by intro w hw; simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_toFun hw
  mapsTo_invFun := by intro w hw; simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_invFun hw
  left_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.left_inv _ hw,sub_add_cancel,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w
  right_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.right_inv _ hw,add_sub_cancel_right,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w

private theorem lift_family {ι : Type*} (A : ι → Set X) (S : ι → Finset (Fin n))
    (p : projectionAmbient X) (h : IsCoordinateFamilyAt n A S p.1) :
    IsCoordinateFamilyAt (n+1)
      (Sum.elim (fun i => (Prod.fst : projectionAmbient X → X) ⁻¹' A i) (fun _ : Unit => horizontal X))
      (Sum.elim (fun i => liftAxes (S i)) (fun _ : Unit => {Fin.last n})) p := by
  obtain ⟨Φ,hsrc,h0,hflat⟩:=h
  refine ⟨productCoordinates p Φ,?_,?_,?_⟩
  · intro w hw
    change w∈(prodChart (chartAt (ComplexModel n) p.1) (chartAt (ComplexModel 1) p.2)).target
    rw [prodChart_target]
    exact ⟨hsrc hw,Set.mem_univ _⟩
  · change prodModelEquiv n 1
      (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).1,
        ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).2-p.2)=0
    have hzero : Φ.toFun (chartAt (ComplexModel n) p.1 p.1)=0:=h0
    simp only [chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
      chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,hzero,sub_self]
    exact (prodModelEquiv n 1).map_zero
  · rintro (i | u) hp q hq hqΦ
    · have hpair : q∈(chartAt (ComplexModel n) p.1).source ×ˢ
          (chartAt (ComplexModel 1) p.2).source:=by
        simpa only [complexChartAt,chartAt_prod,prodChart_source] using hq
      have hbase : q.1∈(chartAt (ComplexModel n) p.1).source:=hpair.1
      have hΦ : chartAt (ComplexModel n) p.1 q.1∈Φ.source:=by
        simpa only [productCoordinates,complexChartAt,chartAt_prod,prodChart_apply,
          ContinuousLinearEquiv.symm_apply_apply,mem_preimage] using hqΦ
      change q.1∈A i ↔ _
      rw [hflat i hp hbase hΦ]
      change _ ↔ prodModelEquiv n 1
        (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).1,
          ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).2-p.2)∈coordSubspace _
      simpa only [complexChartAt,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,Sum.elim_inl]
        using (product_mask (Φ.toFun (chartAt (ComplexModel n) p.1 q.1))
          ((chartAt (ComplexModel 1) p.2) q.2-p.2) (S i)).symm
    · change q.2=0 ↔ _
      change p.2=0 at hp
      change _ ↔ prodModelEquiv n 1
        (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).1,
          ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p q)).2-p.2)∈coordSubspace _
      simpa only [complexChartAt,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply,
        chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq,Sum.elim_inr,hp,sub_zero]
        using (product_normal (Φ.toFun (chartAt (ComplexModel n) p.1 q.1)) q.2).symm

private def boundaryIndex (E : List (Set X)) (i : Fin (boundary E).length) : Fin E.length ⊕ Unit :=
  if hi : i.val<E.length then Sum.inl ⟨i.val,hi⟩ else Sum.inr ()

private theorem boundary_get (E : List (Set X)) (i : Fin (boundary E).length) :
    (boundary E).get i=(boundaryIndex E i).elim
      (fun j => (Prod.fst : projectionAmbient X → X) ⁻¹' E.get j) (fun _ => horizontal X) := by
  by_cases hi : i.val<E.length
  · simp only [boundaryIndex,dif_pos hi,Sum.elim_inl]
    change (E.map _ ++ [horizontal X])[i.val]=_
    rw [List.getElem_append_left (by simpa using hi),List.getElem_map]
    rfl
  · have he : i.val=E.length:=by have := i.isLt; simp only [boundary,List.length_append,List.length_map,List.length_singleton] at this; omega
    simp only [boundaryIndex,dif_neg hi,Sum.elim_inr]
    change (E.map _ ++ [horizontal X])[i.val]=_
    rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi)]
    simp [he]

private theorem boundary_index_value (E : List (Set X)) (i : Fin (boundary E).length) :
    (boundaryIndex E i).elim Fin.val (fun _ => E.length)=i.val := by
  unfold boundaryIndex
  split
  · rfl
  · have := i.isLt
    simp only [boundary,List.length_append,List.length_map,List.length_singleton] at this
    dsimp
    omega

private theorem boundary_index_injective (E : List (Set X)) : Function.Injective (boundaryIndex E) := by
  intro i j hij
  apply Fin.ext
  rw [←boundary_index_value E i,←boundary_index_value E j,hij]

private theorem boundary_snc (E : List (Set X)) (hE : IsSNCDivisor n E) :
    IsSNCDivisor (n+1) (boundary E) := by
  classical
  refine ⟨?_,?_⟩
  · intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨K,hK,rfl⟩:=List.mem_map.mp hH
      exact (hE.1 K hK).preimage continuous_fst
    · rw [List.mem_singleton.mp hH]
      exact isClosed_singleton.preimage continuous_snd
  · intro p
    obtain ⟨S,hFamily,hCard,hInj⟩:=hE.2 p.1
    let F := Sum.elim (fun j => liftAxes (S j)) (fun _ : Unit => {Fin.last n})
    have hLift:=lift_family (fun j => E.get j) S p hFamily
    refine ⟨F ∘ boundaryIndex E,
      NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hLift (boundaryIndex E) (boundary_get E) (fun _ => rfl),?_,?_⟩
    · intro i hi
      rw [boundary_get] at hi
      cases hidx : boundaryIndex E i with
      | inl j =>
        have hj : p.1∈E.get j:=by simpa only [hidx,Sum.elim_inl,mem_preimage] using hi
        simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,liftAxes,Finset.card_map] using hCard j hj
      | inr u => simp only [Function.comp_apply,F,hidx,Sum.elim_inr,Finset.card_singleton]
    · intro i hi j hj heq
      apply boundary_index_injective E
      change p∈(boundary E).get i at hi
      change p∈(boundary E).get j at hj
      rw [boundary_get] at hi hj
      cases hiidx : boundaryIndex E i with
      | inl a =>
        cases hjidx : boundaryIndex E j with
        | inl b =>
          have ha : p.1∈E.get a:=by simpa only [hiidx,Sum.elim_inl,mem_preimage] using hi
          have hb : p.1∈E.get b:=by simpa only [hjidx,Sum.elim_inl,mem_preimage] using hj
          have hh : liftAxes (S a)=liftAxes (S b):=by simpa only [Function.comp_apply,F,hiidx,hjidx,Sum.elim_inl] using heq
          have hS : S a=S b:=Finset.map_injective (Fin.castAddEmb 1) hh
          exact congrArg Sum.inl (hInj ha hb hS)
        | inr v =>
          have hh : liftAxes (S a)={Fin.last n}:=by simpa only [Function.comp_apply,F,hiidx,hjidx,Sum.elim_inl,Sum.elim_inr] using heq
          exact False.elim (last_not_lift (S a) (hh.symm ▸ Finset.mem_singleton_self _))
      | inr v =>
        cases hjidx : boundaryIndex E j with
        | inl b =>
          have hh : {Fin.last n}=liftAxes (S b):=by simpa only [Function.comp_apply,F,hiidx,hjidx,Sum.elim_inl,Sum.elim_inr] using heq
          exact False.elim (last_not_lift (S b) (hh ▸ Finset.mem_singleton_self _))
        | inr w => cases v; cases w; rfl

private theorem boundary_transverse {N : Set X} {E : List (Set X)} (hT : IsTransverse n N E) :
    IsTransverse (n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' N) (boundary E) := by
  classical
  intro p hp
  obtain ⟨S₀,S,hFamily,hCard⟩:=hT p.1 hp
  let F := Sum.elim (fun j => liftAxes (S j)) (fun _ : Unit => {Fin.last n})
  have hLift:=lift_family (fun o : Option (Fin E.length) => o.elim N (fun j => E.get j))
    (fun o => o.elim S₀ S) p hFamily
  let ix : Option (Fin (boundary E).length) → Option (Fin E.length) ⊕ Unit :=
    fun o => o.elim (Sum.inl none) (fun j => (boundaryIndex E j).map some id)
  refine ⟨liftAxes S₀,F ∘ boundaryIndex E,?_,?_⟩
  · apply NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hLift ix
    · rintro (_ | i)
      · rfl
      · cases hidx : boundaryIndex E i <;> simpa [ix,hidx] using boundary_get E i
    · rintro (_ | i)
      · rfl
      · cases hidx : boundaryIndex E i <;> simp [ix,F,hidx]
  · intro i hi
    rw [boundary_get] at hi
    cases hidx : boundaryIndex E i with
    | inl j =>
      have hj : p.1∈E.get j:=by simpa only [hidx,Sum.elim_inl,mem_preimage] using hi
      obtain ⟨hc,hd⟩:=hCard j hj
      refine ⟨?_,?_⟩
      · simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,liftAxes,Finset.card_map] using hc
      · simpa only [Function.comp_apply,F,hidx,Sum.elim_inl,liftAxes,Finset.disjoint_map] using hd
    | inr u =>
      refine ⟨by simp [F,hidx],?_⟩
      apply Finset.disjoint_left.mpr
      intro j hj hjs
      have hjlast : j=Fin.last n:=by simpa [F,hidx] using hj
      exact last_not_lift S₀ (hjlast ▸ hjs)


end GlobalProductGeometry

-- Held C03 elementary quotient assembly, privately reproved; zero duplicate credit.
private def nativeQuotientDiagram {R R' S S' : Type*}
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    (alpha : R→+*S) (alpha' : R'→+*S') (f : R→+*R') (g : S→+*S')
    (K : Ideal R) (K' : Ideal R')
    (hs : Function.Surjective alpha) (hs' : Function.Surjective alpha')
    (hk : RingHom.ker alpha=K) (hk' : RingHom.ker alpha'=K')
    (hi : Ideal.map f K=K') (hq : alpha'.comp f=g.comp alpha) :
    NativeQuotientDiagram alpha alpha' f g K K' := by
  let e : (R⧸K)≃+*S := (Ideal.quotEquivOfEq hk.symm).trans
    (RingHom.quotientKerEquivOfSurjective hs)
  let e' : (R'⧸K')≃+*S' := (Ideal.quotEquivOfEq hk'.symm).trans
    (RingHom.quotientKerEquivOfSurjective hs')
  have he (r : R) : e (Ideal.Quotient.mk K r)=alpha r := rfl
  have he' (r : R') : e' (Ideal.Quotient.mk K' r)=alpha' r := rfl
  let fbar : (R⧸K)→+*(R'⧸K') := Ideal.quotientMap K' f (hi ▸ Ideal.le_comap_map)
  have hfbar (r : R) : fbar (Ideal.Quotient.mk K r)=Ideal.Quotient.mk K' (f r) := rfl
  refine ⟨hs,hs',hk,hk',hi,hq,e,e',he,he',?_,?_,fbar,hfbar,?_⟩
  · intro r q
    rw [map_mul,he]
  · intro r q
    rw [map_mul,he']
  · intro q
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hfbar,he,he']
    exact RingHom.congr_fun hq r


section GivenProjection
variable {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
  {A : GermIdeal n X} {x : X} (F : OriginalLogFrame A N E x)
  (G : ProjectionCarrierQuotientOutput F)

private def projectedFactorySlot : Fin (Eplus F).length→Option (Fin (n+1)) :=
  fun i => projectedAmbientSlot F (Fin.cast (by simp [Eplus,projectedBoundary]) i)

private theorem projectedFactoryWeight (w : Wplus F G) :
    parameterWeight (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) (projectedFactorySlot F)
      (Nat.succ_le_succ F.hk) w=
    parameterWeight (X:=projectionAmbient X) G.geometry.Ψ (F.k+1) (projectedAmbientSlot F)
      (Nat.succ_le_succ F.hk) w := by
  funext j
  have he : (∃ i,projectedFactorySlot F i=some (j.castLE (Nat.succ_le_succ F.hk))) ↔
      ∃ i,projectedAmbientSlot F i=some (j.castLE (Nat.succ_le_succ F.hk)) := by
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨Fin.cast (by simp [Eplus,projectedBoundary]) i,hi⟩
    · rintro ⟨i,hi⟩
      refine ⟨Fin.cast (by simp [Eplus,projectedBoundary]) i,?_⟩
      simpa [projectedFactorySlot] using hi
  simp only [parameterWeight,he]

private theorem projectedFactoryCharts : ∀ p∈flatDomain G.geometry.Ψ,
    (p∈Nplus F ↔ flatMap G.geometry.Ψ p∈complexCoordinatePlane (n+1) (F.k+1)) ∧
    ∀ i,p∈(Eplus F).get i ↔ ∃ j,projectedFactorySlot F i=some j ∧ flatCoord G.geometry.Ψ j p=0 := by
  intro p hp
  refine ⟨G.geometry.carrier_chart p hp,?_⟩
  intro i
  have h := G.geometry.boundary_chart p hp (Fin.cast (by simp [Eplus,projectedBoundary]) i)
  simpa [projectedFactorySlot,Eplus] using h

/-- The newly computed EXISTING native log operation on the SAME C03 Psi. -/
theorem same_frame_new_native_log_image (B : GermIdeal n X) (hB : B.IsCoherent) :
    ∀ w : Wplus F G,
      Ideal.map (factoryPhi F G w)
        (actualWholeSheafStalkIdeal (Dnew F B) (sigmaPlus F G w))=factoryL F G B w ∧
      Ideal.comap (factoryPhi F G w) (factoryL F G B w)=
        actualWholeSheafStalkIdeal (Dnew F B) (sigmaPlus F G w) := by
  intro w
  have hb := GermIdealPullbackCalculus.isCoherent_pullback
    (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)) hB
  have h := fixed_chart_actual_log_dictionary (X:=projectionAmbient X) G.geometry.Ψ (F.k+1)
    (Nat.succ_le_succ F.hk) G.geometry.hsrc (projectedFactorySlot F)
    (projectedFactoryCharts F G) (pulled F B) hb w
  have hm := h.2.2.1
  have hi := h.2.2.2.1
  rw [projectedFactoryWeight F G w] at hm hi
  exact ⟨hm,hi⟩

private theorem nativeWhole_transport {d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M]
    (C : GermIdeal d M) {p q : M} (h : p=q) :
    Ideal.map (nativeStalkTransport h).toRingHom (actualWholeSheafStalkIdeal C p)=
      actualWholeSheafStalkIdeal C q := by
  cases h
  exact Ideal.map_id _

private theorem factory_native_germ_square (w : Wplus F G) :
    (factoryPhi F G w).comp (nativeStalkTransport (G.geometry.sigma w).symm).toRingHom=
      phiPlus F G (G.geometry.rho w) := by
  apply RingHom.ext
  intro r
  exact G.factory_all_germs w r

private theorem factory_whole_ideal_image (C : GermIdeal (n+1) (projectionAmbient X))
    (w : Wplus F G) :
    Ideal.map (factoryPhi F G w) (actualWholeSheafStalkIdeal C (sigmaPlus F G w))=
      Ideal.map (phiPlus F G (G.geometry.rho w)) (Kplus F C (G.geometry.rho w)) := by
  rw [←nativeWhole_transport C (G.geometry.sigma w).symm,Ideal.map_map,factory_native_germ_square]

private theorem factory_input_image (B : GermIdeal n X) (hB : B.IsCoherent) (w : Wplus F G) :
    Ideal.map (factoryPhi F G w) (actualWholeSheafStalkIdeal (pulled F B) (sigmaPlus F G w))=
      Ideal.map (T F).toRingHom (Ideal.map (phi F (G.geometry.rho w)) (K F B (G.geometry.rho w))) := by
  rw [factory_whole_ideal_image]
  exact (G.every_coherent_ideal B hB (G.geometry.rho w)).2.1

private theorem factory_log_target (B : GermIdeal n X) (hB : B.IsCoherent) (w : Wplus F G) :
    factoryL F G B w=Lplus F B (G.geometry.rho w) := by
  unfold factoryL
  rw [factory_input_image F G B hB w,G.geometry.all_weights]
  exact (HironakaActualProjectionLogDerivativeIdeal.projection_log_derivative_ideal_eq
    (parameterWeight F.Φ F.k F.κ F.hk (G.geometry.rho w).1) ((G.geometry.rho w).2 0)
    (Ideal.map (phi F (G.geometry.rho w)) (K F B (G.geometry.rho w)))).symm

private theorem old_log_image (B : GermIdeal n X) (hB : B.IsCoherent) (t : parameterProduct F) :
    Ideal.map (phi F t) (K F (Dold F B) t)=L F B t :=
  (fixed_chart_actual_log_dictionary F.Φ F.k F.hk F.hsrc F.κ
    F.output.2.2.2.2.2.1 B hB t.1).2.2.1

private theorem old_log_coherent (B : GermIdeal n X) (hB : B.IsCoherent) :
    (Dold F B).IsCoherent := isCoherent_logDerivIdealAlong hB F.smooth F.snc F.transverse

private theorem factory_pulled_log_image (B : GermIdeal n X) (hB : B.IsCoherent) (w : Wplus F G) :
    Ideal.map (factoryPhi F G w)
      (actualWholeSheafStalkIdeal (pulled F (Dold F B)) (sigmaPlus F G w))=factoryL F G B w := by
  rw [factory_whole_ideal_image,factory_log_target F G B hB w]
  have h := (G.every_coherent_ideal (Dold F B) (old_log_coherent F B hB) (G.geometry.rho w)).2.1
  change Ideal.map (phiPlus F G (G.geometry.rho w)) (Kplus F (pulled F (Dold F B)) (G.geometry.rho w))=
    Ideal.map (T F).toRingHom (Ideal.map (phi F (G.geometry.rho w)) (K F (Dold F B) (G.geometry.rho w))) at h
  rw [old_log_image F B hB] at h
  exact h

private theorem factory_carrier_facts (w : Wplus F G) :
    Function.Surjective (factoryPhi F G w) ∧ RingHom.ker (factoryPhi F G w)=
      actualWholeSheafStalkIdeal (vanishingIdeal (n:=n+1) (Nplus F)) (sigmaPlus F G w) := by
  have hb := GermIdealPullbackCalculus.isCoherent_pullback
    (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)) F.coherent
  have h := fixed_chart_actual_log_dictionary (X:=projectionAmbient X) G.geometry.Ψ (F.k+1)
    (Nat.succ_le_succ F.hk) G.geometry.hsrc (projectedFactorySlot F)
    (projectedFactoryCharts F G) (pulled F A) hb w
  exact ⟨h.1,h.2.1⟩

include G in
private theorem product_carrier_le_pulled_log (B : GermIdeal n X) (hB : B.IsCoherent)
    (t : parameterProduct F) :
    Kplus F (vanishingIdeal (n:=n+1) (Nplus F)) t≤Kplus F (pulled F (Dold F B)) t := by
  have hi := (G.carrier t).ideal_map
  change Ideal.map (piNative F t) (K F (vanishingIdeal (n:=n) N) t)=
    Kplus F (vanishingIdeal (n:=n+1) (Nplus F)) t at hi
  have hd := (G.every_coherent_ideal (Dold F B) (old_log_coherent F B hB) t).1
  change Ideal.map (piNative F t) (K F (Dold F B) t)=Kplus F (pulled F (Dold F B)) t at hd
  have hm : Ideal.map (piNative F t) (K F (vanishingIdeal (n:=n) N) t)≤
      Ideal.map (piNative F t) (K F (Dold F B) t) :=
    Ideal.map_mono (native_whole_mono (carrier_le_log (E:=E) (A:=B)) _)
  rw [hi,hd] at hm
  exact hm

private theorem factory_carrier_le_pulled_log (B : GermIdeal n X) (hB : B.IsCoherent)
    (w : Wplus F G) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n:=n+1) (Nplus F)) (sigmaPlus F G w)≤
      actualWholeSheafStalkIdeal (pulled F (Dold F B)) (sigmaPlus F G w) := by
  have hm := Ideal.map_mono (f:=(nativeStalkTransport (G.geometry.sigma w).symm).toRingHom)
    (product_carrier_le_pulled_log F G B hB (G.geometry.rho w))
  simpa only [Kplus,nativeWhole_transport] using hm

private theorem factory_native_log_ideal_eq (B : GermIdeal n X) (hB : B.IsCoherent)
    (w : Wplus F G) :
    actualWholeSheafStalkIdeal (pulled F (Dold F B)) (sigmaPlus F G w)=
      actualWholeSheafStalkIdeal (Dnew F B) (sigmaPlus F G w) := by
  have hinv : Ideal.comap (factoryPhi F G w) (factoryL F G B w)=
      actualWholeSheafStalkIdeal (pulled F (Dold F B)) (sigmaPlus F G w) := by
    rw [←factory_pulled_log_image F G B hB w,
      Ideal.comap_map_of_surjective _ (factory_carrier_facts F G w).1,←RingHom.ker_eq_comap_bot,
      (factory_carrier_facts F G w).2]
    exact sup_eq_left.mpr (factory_carrier_le_pulled_log F G B hB w)
  exact hinv.symm.trans (same_frame_new_native_log_image F G B hB w).2

include G in
private theorem product_native_log_ideal_eq (B : GermIdeal n X) (hB : B.IsCoherent)
    (t : parameterProduct F) : Kplus F (pulled F (Dold F B)) t=Kplus F (Dnew F B) t := by
  have h := factory_native_log_ideal_eq F G B hB (G.geometry.rho.symm t)
  have hp : sigmaPlus F G (G.geometry.rho.symm t)=Sigma F t :=
    (G.geometry.sigma _).trans (congrArg (Sigma F) (G.geometry.rho.apply_symm_apply t))
  rw [hp] at h
  exact h

private theorem product_germ_facts (t : parameterProduct F) :
    Function.Surjective (phiPlus F G t) ∧ RingHom.ker (phiPlus F G t)=
      Kplus F (vanishingIdeal (n:=n+1) (Nplus F)) t := by
  constructor
  · exact (actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t).surjective.comp
      (G.carrier t).surjective'
  · have hk : RingHom.ker ((ChartedSpace.locallyRingedSpaceMap (Sigma F)
        G.geometry.sigma_holo).stalkMap t).hom=Kplus F (vanishingIdeal (n:=n+1) (Nplus F)) t :=
      (G.carrier t).kernel'
    apply Ideal.ext
    intro r
    have hh := congrArg (fun I => r∈I) hk
    have hz : phiPlus F G t r=0 ↔
        (ChartedSpace.locallyRingedSpaceMap (Sigma F) G.geometry.sigma_holo).stalkMap t r=0 := by
      constructor
      · intro h
        exact (actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t).injective
          (h.trans (map_zero _).symm)
      · intro h
        change actualStalkChartEquiv (n:=F.k+1) (M:=parameterProduct F) t
          ((ChartedSpace.locallyRingedSpaceMap (Sigma F) G.geometry.sigma_holo).stalkMap t r)=0
        rw [h,map_zero]
    exact hz.trans (Iff.of_eq hh)

private theorem product_new_log_image (B : GermIdeal n X) (hB : B.IsCoherent)
    (t : parameterProduct F) : Ideal.map (phiPlus F G t) (Kplus F (Dnew F B) t)=Lplus F B t := by
  have h := (same_frame_new_native_log_image F G B hB (G.geometry.rho.symm t)).1
  rw [factory_whole_ideal_image,factory_log_target F G B hB] at h
  erw [G.geometry.rho.apply_symm_apply] at h
  exact h

private theorem product_new_log_comap (B : GermIdeal n X) (hB : B.IsCoherent)
    (t : parameterProduct F) : Ideal.comap (phiPlus F G t) (Lplus F B t)=Kplus F (Dnew F B) t := by
  rw [←product_new_log_image F G B hB t,
    Ideal.comap_map_of_surjective _ (product_germ_facts F G t).1,←RingHom.ker_eq_comap_bot,
    (product_germ_facts F G t).2]
  exact sup_eq_left.mpr (native_whole_mono (carrier_le_log (N:=Nplus F) (E:=Eplus F) (A:=pulled F B)) _)

private theorem quotient_kernel_of_comap {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (I : Ideal R) (J : Ideal S) (h : Ideal.comap f J=I) :
    RingHom.ker ((Ideal.Quotient.mk J).comp f)=I := by
  ext r
  change Ideal.Quotient.mk J (f r)=0 ↔ r∈I
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Iff.of_eq (congrArg (fun K => r∈K) h)

private def newLogProjectionDiagram (B : GermIdeal n X) (hB : B.IsCoherent)
    (t : parameterProduct F) : NewNativeLogProjectionDiagram F G B t := by
  have hOld := fixed_chart_actual_log_dictionary F.Φ F.k F.hk F.hsrc F.κ
    F.output.2.2.2.2.2.1 B hB t.1
  refine nativeQuotientDiagram _ _ _ _ _ _
    (Ideal.Quotient.mk_surjective.comp hOld.1)
    (Ideal.Quotient.mk_surjective.comp (product_germ_facts F G t).1)
    (quotient_kernel_of_comap _ _ _ hOld.2.2.2.1)
    (quotient_kernel_of_comap _ _ _ (product_new_log_comap F G B hB t)) ?_ ?_
  · exact ((G.every_coherent_ideal (Dold F B) (old_log_coherent F B hB) t).1).trans
      (product_native_log_ideal_eq F G B hB t)
  · apply RingHom.ext
    intro r
    change Ideal.Quotient.mk _ (phiPlus F G t (piNative F t r))=
      Ideal.Quotient.mk _ (T F (phi F t r))
    exact congrArg (Ideal.Quotient.mk _) (G.all_germs t r)

private def sameRingLogQuotient (B : GermIdeal n X) (hB : B.IsCoherent)
    (t : parameterProduct F) : SameRingNativeLogEqualityQuotient F B t where
  ideal_eq := product_native_log_ideal_eq F G B hB t
  e := Ideal.quotEquivOfEq (product_native_log_ideal_eq F G B hB t)
  e_mk := fun _ => rfl
  e_inv_mk := fun _ => rfl
  e_action := by intro r q; rw [map_mul]; rfl

private theorem any_old_log_choice (B : GermIdeal n X) (hB : B.IsCoherent)
    (t : parameterProduct F)
    (eOld : (R F t ⧸ K F (Dold F B) t) ≃+* (HolGerm (ComplexModel F.k) ⧸ L F B t))
    (hOld : ∀ r,eOld (Ideal.Quotient.mk _ r)=Ideal.Quotient.mk _ (phi F t r)) :
    ∃ Q : NewNativeLogProjectionDiagram F G B t,Q.e=eOld := by
  refine ⟨newLogProjectionDiagram F G B hB t,?_⟩
  apply RingEquiv.ext
  intro q
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ((newLogProjectionDiagram F G B hB t).e_mk r).trans (hOld r).symm

private def factoryNewLogQuotient (B : GermIdeal n X) (hB : B.IsCoherent)
    (w : Wplus F G) : FactoryNewNativeLogQuotient F G B w := by
  have h := same_frame_new_native_log_image F G B hB w
  have hk := quotient_kernel_of_comap (factoryPhi F G w)
    (actualWholeSheafStalkIdeal (Dnew F B) (sigmaPlus F G w)) (factoryL F G B w) h.2
  have hs : Function.Surjective ((Ideal.Quotient.mk (factoryL F G B w)).comp (factoryPhi F G w)) :=
    Ideal.Quotient.mk_surjective.comp (factory_carrier_facts F G w).1
  let e := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs)
  refine ⟨h.1,h.2,?_,e,?_,?_⟩
  · intro r
    exact (Iff.of_eq (congrArg (fun I => r∈I) h.2)).symm
  · intro r
    rfl
  · intro r q
    rw [map_mul]
    rfl

end GivenProjection

private theorem original_stalk_one {d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M] (p : M) :
    actualOriginalFunctionGerm (n:=d) p (fun _ => (1 : ℂ)) (holomorphicAt_const (n:=d) 1)=1 := by
  apply (actualStalkChartEquiv (n:=d) p).injective
  rw [actualOriginalFunctionGerm_chart,map_one]
  rfl

private theorem native_log_top_off {d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M]
    (C : Set M) (E : List (Set M)) (B : GermIdeal d M) (hC : IsClosed C)
    (p : M) (hp : p∉C) : actualWholeSheafStalkIdeal (logDerivIdealAlong C E B) p=⊤ := by
  have hone : (1 : actualComplexStructureStalk (n:=d) p)∈
      actualWholeSheafStalkIdeal (logDerivIdealAlong C E B) p := by
    rw [←original_stalk_one p]
    have hv : (vanishingIdeal (n:=d) C).mem p (fun _ => (1 : ℂ)) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      filter_upwards [hC.isOpen_compl.mem_nhds hp] with q hq hqC
      exact (hq hqC).elim
    exact Ideal.subset_span ⟨_,holomorphicAt_const 1,carrier_le_log p _ hv,rfl⟩
  apply top_unique
  intro r _
  simpa only [mul_one] using
    (actualWholeSheafStalkIdeal (logDerivIdealAlong C E B) p).mul_mem_left r hone

private theorem projected_log_coherent {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (B : GermIdeal n X) (hB : B.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) :
    (logDerivIdealAlong ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
      (E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X])
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) B)).IsCoherent := by
  have hf := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)
  exact isCoherent_logDerivIdealAlong (GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hB)
    (HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hN)
    (boundary_snc E hE) (boundary_transverse hTr)

private theorem global_native_log_ideal_eq {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (B : GermIdeal n X) (hB : B.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (q : projectionAmbient X) :
    actualWholeSheafStalkIdeal
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) (logDerivIdealAlong N E B)) q=
    actualWholeSheafStalkIdeal
      (logDerivIdealAlong ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
        (E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X])
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) B)) q := by
  by_cases hq : q.1∈N
  · obtain ⟨F,⟨G⟩⟩ := exists_actual_projection_carrier_quotient_dictionary B hB hN hE hTr q.1 hq
    obtain ⟨hz,hzero⟩ := parameterMap_zero F.Φ F.k F.output.1
    let v : parameterOpen F.Φ F.k := ⟨0,hz⟩
    let t : parameterProduct F := (v,q.2)
    have hp : Sigma F t=q := by
      apply Prod.ext
      · exact hzero
      · rfl
    have h := product_native_log_ideal_eq F G B hB t
    change actualWholeSheafStalkIdeal
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) (logDerivIdealAlong N E B)) (Sigma F t)=
      actualWholeSheafStalkIdeal
        (logDerivIdealAlong ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
          (E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X])
          (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) B)) (Sigma F t) at h
    rw [hp] at h
    exact h
  · have hd := isCoherent_logDerivIdealAlong hB hN hE hTr
    have hf := ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)
    rw [←HironakaSingularSubspaceBlowupCartier.map_actualWholeSheafStalkIdeal_native_pullback hf _ hd q,
      native_log_top_off N E B hN.1 q.1 hq]
    erw [Ideal.map_top]
    exact (native_log_top_off _ _ _ (hN.1.preimage continuous_fst) q hq).symm

/-- Genuine GLOBAL equality of the EXISTING original operators, not only their quotients. -/
theorem projection_native_logIdeal_eq
    {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (B : GermIdeal n X) (hB : B.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) :
    GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X)
        (logDerivIdealAlong N E B)=
      logDerivIdealAlong ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
        (E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X])
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) B) := by
  have hd := isCoherent_logDerivIdealAlong hB hN hE hTr
  have hf := ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)
  have hpull := GermIdealPullbackCalculus.isCoherent_pullback hf hd
  have hnew := projected_log_coherent B hB hN hE hTr
  apply GermIdeal.ext
  funext q g
  apply propext
  by_cases hg : HolomorphicAt (n+1) g q
  · rw [coherent_mem_iff_actual_whole _ hpull q g hg,
      coherent_mem_iff_actual_whole _ hnew q g hg,global_native_log_ideal_eq B hB hN hE hTr q]
  · exact iff_of_false (fun h => hg (GermIdeal.IsCoherent.holomorphicAt_mem hpull h))
      (fun h => hg (GermIdeal.IsCoherent.holomorphicAt_mem hnew h))

section FinalOutput
variable {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
  {A : GermIdeal n X} {x : X} (F : OriginalLogFrame A N E x)
  (G : ProjectionCarrierQuotientOutput F)

private def nativeProjectionLogOutput : NativeProjectionLogOutput F G where
  coherent_old := old_log_coherent F
  coherent_pull := by
    intro B hB
    exact GermIdealPullbackCalculus.isCoherent_pullback
      (ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1))
      (old_log_coherent F B hB)
  coherent_new := fun B hB => projected_log_coherent B hB F.smooth F.snc F.transverse
  global_operator_eq := fun B hB => projection_native_logIdeal_eq B hB F.smooth F.snc F.transverse
  every_native_ideal := product_native_log_ideal_eq F G
  every_original_function := by
    intro B hB y g _hg
    rw [show pulled F (Dold F B)=Dnew F B from
      projection_native_logIdeal_eq B hB F.smooth F.snc F.transverse]
  every_product_image_comap := by
    intro B hB t
    have hi := product_new_log_comap F G B hB t
    exact ⟨product_new_log_image F G B hB t,hi,
      fun r => (Iff.of_eq (congrArg (fun I => r∈I) hi)).symm⟩
  equality_quotient := sameRingLogQuotient F G
  any_old_choice := any_old_log_choice F G
  factory_new := factoryNewLogQuotient F G
  factory_every_native_germ := fun w r => G.factory_all_germs w r

end FinalOutput

/-- One C03 choice precedes every B/numerator/scalar. ONLY the existing
one-step native operator is compared; C01/C02/full C04 credit is not asserted. -/
theorem exists_actual_projection_native_log_dictionary
    {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (x : X) (hx : x∈N) :
    ∃ F : OriginalLogFrame A N E x,
      ∃ G : ProjectionCarrierQuotientOutput F,Nonempty (NativeProjectionLogOutput F G) := by
  obtain ⟨F,⟨G⟩⟩ := exists_actual_projection_carrier_quotient_dictionary A hA hN hE hTr x hx
  exact ⟨F,G,⟨nativeProjectionLogOutput F G⟩⟩

private theorem iterate_log_coherent {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (r : ℕ) :
    (((logDerivIdealAlong N E)^[r]) A).IsCoherent := by
  induction r with
  | zero => exact hA
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact isCoherent_logDerivIdealAlong ih hN hE hTr

/-- Consequence for Function.iterate of the EXISTING actual540 operator.
No finite marked sum/common-mark interpretation or C02 completion is asserted. -/
theorem projection_native_logIdeal_iterate_eq
    {n : ℕ} {X : CMfd.{0} n} {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (r : ℕ) :
    GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X)
        (((logDerivIdealAlong N E)^[r]) A)=
      ((logDerivIdealAlong ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
        (E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·) ++ [horizontal X]))^[r])
        (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) A) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [Function.iterate_succ_apply']
    rw [projection_native_logIdeal_eq _ (iterate_log_coherent A hA hN hE hTr r) hN hE hTr,ih]

end
end Hironaka.HironakaActualProjectionNativeLogIdeal
