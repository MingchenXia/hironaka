import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.Resolution.HironakaIntrinsicCarrierBoundaryCharts

/-! Whole logarithmic field differentiation on the original proper carrier
and full ordered boundary. BP FIRST: hironaka-actual-intrinsic-log-derivative-frame.tex.
This auxiliary ambient representative reuses the original native field calculus.
It does not redefine the ordinary derivative ideal or any marked ideal. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualIntrinsicLogDerivativeFrame
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  DerivativeIdeal DerivativeIdealAlong DerivativeIdealAlongCoherent
  GiraudAlong BlowupFlatCoordinates RelativePrincipalizationSpan
  HironakaIntrinsicCarrierBoundaryCharts NormalCrossings BlowupTowers

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The original native field preserves the carrier and EVERY original boundary member. -/
def IsLogTangentField (N : Set M) (E : List (Set M)) (e : ComplexChart n M)
    (ξ : Fin n → M → ℂ) (x : M) : Prop :=
  IsTangentField N e ξ x ∧ ∀ H ∈ E, IsTangentField H e ξ x

private def LogDerivGen (N : Set M) (E : List (Set M)) (A : GermIdeal n M)
    (x : M) (s : M → ℂ) : Prop :=
  A.mem x s ∨ (vanishingIdeal (n := n) N).mem x s ∨
    ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (f : M → ℂ),
      IsLogTangentField N E e ξ x ∧ A.mem x f ∧ s = fieldDeriv e ξ f

/-- Whole original ideal plus carrier ideal and all original native logarithmic derivatives. -/
def logDerivIdealAlong (N : Set M) (E : List (Set M)) (A : GermIdeal n M) : GermIdeal n M where
  mem x := IsInSpanAt (n := n) (LogDerivGen N E A x) x

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

/-- Actual coordinate weight of the COMPLETE original optional slot list. -/
def boundaryWeight {l : ℕ} (κ : Fin l → Option (Fin n)) (j : Fin n) : M → ℂ :=
  if ∃ i, κ i = some j then flatCoord Φ j else fun _ => 1

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

/-- The finite original family, retaining the proper carrier equations and actual weights. -/
def logFamily {l r : ℕ} (κ : Fin l → Option (Fin n)) (k : ℕ)
    (s : Fin r → M → ℂ) : Fin r ⊕ Fin n ⊕ (Fin r × Fin n) → M → ℂ
  | .inl i => s i
  | .inr (.inl j) => if k ≤ j.val then flatCoord Φ j else fun _ => 0
  | .inr (.inr ij) => if ij.2.val < k then
      fun p => boundaryWeight Φ κ ij.2 p * flatPartial Φ ij.2 (s ij.1) p else fun _ => 0

omit [IsComplexManifold n M] in
private theorem span_zero (S : (M → ℂ) → Prop) (y : M) :
    IsInSpanAt (n := n) S y (fun _ => 0) := by
  refine ⟨holomorphicAt_const 0,0,Fin.elim0,Fin.elim0,?_,?_,?_⟩
  · intro i;exact i.elim0
  · intro i;exact i.elim0
  · exact Eventually.of_forall fun _ => by simp

include hΦsrc in
private theorem carrier_span_logFamily {N : Set M} {k l r : ℕ}
    (κ : Fin l → Option (Fin n)) (s : Fin r → M → ℂ)
    (hN : ∀ z ∈ flatDomain Φ, z ∈ N ↔ flatMap Φ z ∈ complexCoordinatePlane n k)
    {y : M} (hy : y ∈ flatDomain Φ) {g : M → ℂ}
    (hg : (vanishingIdeal (n := n) N).mem y g) :
    IsInSpanAt (n := n) (· ∈ range (logFamily Φ κ k s)) y g := by
  have hflat : ∀ {z : M}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
      (z ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ complexCoordinatePlane n k) :=
    fun hz hz' => hN _ ⟨hz,hz'⟩
  obtain ⟨b,hb0,hb,he⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflat hy hg
  refine ⟨hg.1,n,fun j => logFamily Φ κ k s (.inr (.inl j)),b,
    fun j => ⟨_,rfl⟩,hb,?_⟩
  filter_upwards [he] with p hp
  rw [hp]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : k ≤ j.val
  · simp [logFamily,hj]
  · rw [hb0 j (Nat.lt_of_not_le hj)]
    simp

include hΦsrc in
private theorem log_mem_iff_family {N : Set M} {E : List (Set M)} {k : ℕ}
    (κ : Fin E.length → Option (Fin n))
    (hN : ∀ z ∈ flatDomain Φ, z ∈ N ↔ flatMap Φ z ∈ complexCoordinatePlane n k)
    (hE : ∀ z ∈ flatDomain Φ, ∀ i, z ∈ E.get i ↔
      ∃ a, κ i = some a ∧ flatCoord Φ a z = 0)
    {A : GermIdeal n M} {U : Set M} (hU : IsOpen U) (hUΦ : U ⊆ flatDomain Φ)
    {r : ℕ} (s : Fin r → M → ℂ)
    (hs : ∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (s i) U)
    (hgen : ∀ y ∈ U, ∀ g, A.mem y g ↔ IsInSpanAt (n := n) (· ∈ range s) y g)
    {y : M} (hy : y ∈ U) (g : M → ℂ) :
    (logDerivIdealAlong N E A).mem y g ↔
      IsInSpanAt (n := n) (· ∈ range (logFamily Φ κ k s)) y g := by
  classical
  have hhol : ∀ i, ∀ z ∈ U, HolomorphicAt n (s i) z := fun i z hz =>
    eventually_of_mem (hU.mem_nhds hz) fun w hw =>
      (hs i w hw).mdifferentiableAt (hU.mem_nhds hw)
  have hyΦ := hUΦ hy
  have hfam : ∀ c, HolomorphicAt n (logFamily Φ κ k s c) y := by
    rintro (i | j | ij)
    · exact hhol i y hy
    · by_cases hj : k ≤ j.val
      · simpa [logFamily,hj] using holomorphicAt_flatCoord Φ j hyΦ
      · simpa [logFamily,hj] using holomorphicAt_const (n := n) (x := y) (0 : ℂ)
    · by_cases hj : ij.2.val < k
      · simpa [logFamily,hj] using (boundaryWeight_holomorphic Φ κ ij.2 hyΦ).mul
          (holomorphicAt_flatPartial ij.2 hyΦ (hhol ij.1 y hy))
      · simpa [logFamily,hj] using holomorphicAt_const (n := n) (x := y) (0 : ℂ)
  have hFamMem (c) : IsInSpanAt (n := n) (· ∈ range (logFamily Φ κ k s)) y
      (logFamily Φ κ k s c) :=
    isInSpanAt_of_eq_mul ⟨c,rfl⟩ (hfam c) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm)
  have hsmem (i) : A.mem y (s i) := (hgen y hy _).mpr
    (isInSpanAt_of_eq_mul ⟨i,rfl⟩ (hhol i y hy) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm))
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ hg
    rintro t (ht | ht | ⟨e,ξ,f,hξ,hf,rfl⟩)
    · exact ((hgen y hy t).mp ht).mono fun v ⟨i,hi⟩ => ⟨.inl i,hi⟩
    · exact carrier_span_logFamily Φ hΦsrc κ s hN hyΦ ht
    · obtain ⟨c,hc,hrem⟩ := all_fields_mod_carrier Φ hΦsrc κ hN hE hyΦ hξ
      have hξs (i) : IsInSpanAt (n := n) (· ∈ range (logFamily Φ κ k s)) y
          (fieldDeriv e ξ (s i)) := by
        have hR := carrier_span_logFamily Φ hΦsrc κ s hN hyΦ (hrem (s i) (hhol i y hy))
        have hSum : IsInSpanAt (n := n) (· ∈ range (logFamily Φ κ k s)) y
            (fun p => ∑ j : Fin n, if j.val < k then
              c j p * (boundaryWeight Φ κ j p * flatPartial Φ j (s i) p) else 0) := by
          apply IsInSpanAt.sum Finset.univ
          intro j _
          by_cases hj : j.val < k
          · have h := IsInSpanAt.mul_left (hc j) (hFamMem (.inr (.inr (i,j))))
            simpa only [logFamily,if_pos hj] using h
          · simpa only [if_neg hj] using span_zero (n := n)
              (· ∈ range (logFamily Φ κ k s)) y
        exact isInSpanAt_congr (IsInSpanAt.add hR hSum) (Eventually.of_forall fun p => by
          dsimp only
          ring)
      obtain ⟨_,K,t,a,ht,ha,hsum⟩ := (hgen y hy f).mp hf
      choose σ hσ using ht
      have hthol (l) : HolomorphicAt n (t l) y := hσ l ▸ hhol (σ l) y hy
      refine isInSpanAt_congr ?_
        (fieldDeriv_eventuallyEq_sum_mul hξ.1.mem_source ha hthol hsum).symm
      apply IsInSpanAt.sum Finset.univ
      intro l _
      apply IsInSpanAt.add
      · rw [←hσ l]
        exact IsInSpanAt.mul_left
          (holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt (ha l))
          (hFamMem (.inl (σ l)))
      · rw [←hσ l]
        exact IsInSpanAt.mul_left (ha l) (hξs (σ l))
  · intro hg
    refine IsInSpanAt.trans ?_ hg
    rintro t ⟨c,rfl⟩
    have hgen1 : ∀ {u : M → ℂ}, LogDerivGen N E A y u → HolomorphicAt n u y →
        IsInSpanAt (n := n) (LogDerivGen N E A y) y u := fun hu hhu =>
      isInSpanAt_of_eq_mul hu hhu (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    rcases c with i | j | ij
    · exact hgen1 (Or.inl (hsmem i)) (hfam _)
    · by_cases hj : k ≤ j.val
      · have hflat : ∀ {z : M}, z ∈ (chartAt (ComplexModel n) x).source →
          chartAt (ComplexModel n) x z ∈ Φ.source →
          (z ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ complexCoordinatePlane n k) :=
          fun hz hz' => hN _ ⟨hz,hz'⟩
        have h := flatCoord_mem_vanishingIdeal Φ hflat hj hyΦ
        simpa [logFamily,hj] using hgen1 (Or.inr (Or.inl h)) h.1
      · simpa [logFamily,hj] using span_zero (n := n) (LogDerivGen N E A y) y
    · by_cases hj : ij.2.val < k
      · have hξ := weighted_flatField_log Φ hΦsrc κ hN hE hj hyΦ
        have he : (fun p => boundaryWeight Φ κ ij.2 p * flatPartial Φ ij.2 (s ij.1) p) =
            fieldDeriv (complexChartAt (n := n) x)
              (fun m p => boundaryWeight Φ κ ij.2 p * flatField Φ (EuclideanSpace.single ij.2 1) m p)
              (s ij.1) := (fieldDeriv_smul _ _ _ _).symm
        have h : LogDerivGen N E A y
            (fun p => boundaryWeight Φ κ ij.2 p * flatPartial Φ ij.2 (s ij.1) p) :=
          Or.inr (Or.inr ⟨_,_,s ij.1,hξ,hsmem ij.1,he⟩)
        simpa [logFamily,hj] using hgen1 h (by simpa [logFamily,hj] using hfam (.inr (.inr ij)))
      · simpa [logFamily,hj] using span_zero (n := n) (LogDerivGen N E A y) y

end Flat

/-- Original SNC/transverse geometry internally supplies the full native log frame,
and ALL fields have coefficients chosen before EVERY function being differentiated. -/
theorem exists_actual_full_boundary_log_frame {N : Set M} {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) (x : M) (hx : x ∈ N) :
    ∃ k ≤ n, ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (κ : Fin E.length → Option (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ i j, κ i = some j → j.val < k) ∧ Set.InjOn κ {i | x ∈ E.get i} ∧
      (∀ y ∈ flatDomain Φ,
        (y ∈ N ↔ flatMap Φ y ∈ complexCoordinatePlane n k) ∧
        ∀ i, y ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j y = 0) ∧
      (∀ y ∈ flatDomain Φ, ∀ j : Fin n, j.val < k →
        IsLogTangentField N E (complexChartAt (n := n) x)
          (fun m p => boundaryWeight Φ κ j p * flatField Φ (EuclideanSpace.single j 1) m p) y) ∧
      ∀ y ∈ flatDomain Φ, ∀ (e : ComplexChart n M) (ξ : Fin n → M → ℂ),
        IsLogTangentField N E e ξ y →
        ∃ c : Fin n → M → ℂ, (∀ j, HolomorphicAt n (c j) y) ∧
          ∀ (f : M → ℂ), HolomorphicAt n f y →
            (vanishingIdeal (n := n) N).mem y
              (fun p => fieldDeriv e ξ f p -
                ∑ j : Fin n, if j.val < k then
                  c j p * (boundaryWeight Φ κ j p * flatPartial Φ j f p) else 0) := by
  obtain ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts⟩ :=
    exists_actual_indexed_carrier_boundary_chart (X := CMfd.of (n := n) M) hE hT x hx
  refine ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts,?_,?_⟩
  · intro y hy j hj
    exact weighted_flatField_log Φ hsrc κ (fun z hz => (hcharts z hz).1)
      (fun z hz => (hcharts z hz).2) hj hy
  · intro y hy e ξ hξ
    exact all_fields_mod_carrier Φ hsrc κ (fun z hz => (hcharts z hz).1)
      (fun z hz => (hcharts z hz).2) hy hξ

omit [IsComplexManifold n M] in
private theorem log_mem_of_notMem {N : Set M} {E : List (Set M)} {A : GermIdeal n M}
    (hN : IsClosed N) {y : M} (hy : y ∉ N) {g : M → ℂ} (hg : HolomorphicAt n g y) :
    (logDerivIdealAlong N E A).mem y g := by
  have hvan : (vanishingIdeal (n := n) N).mem y g :=
    ⟨hg,by filter_upwards [hN.isOpen_compl.mem_nhds hy] with p hp hpN using absurd hpN hp⟩
  exact isInSpanAt_of_eq_mul (Or.inr (Or.inl hvan)) hg (holomorphicAt_const 1)
    (Eventually.of_forall fun _ => (one_mul _).symm)

/-- Coherence is produced from ordinary original whole coherence and actual full-boundary geometry. -/
theorem isCoherent_logDerivIdealAlong {N : Set M} {E : List (Set M)} {A : GermIdeal n M}
    (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) :
    (logDerivIdealAlong N E A).IsCoherent := by
  classical
  intro x
  by_cases hx : x ∈ N
  · obtain ⟨k,_hk,Φ,κ,hsrc,_h0,_hκ,_hinj,hcharts⟩ :=
      exists_actual_indexed_carrier_boundary_chart (X := CMfd.of (n := n) M) hE hT x hx
    obtain ⟨U,hU,hxU,r,s,hs,hgen⟩ := hA x
    have hU' : IsOpen (U ∩ flatDomain Φ) := hU.inter (isOpen_flatDomain Φ)
    have hhol : ∀ i, ∀ z ∈ U, HolomorphicAt n (s i) z := fun i z hz =>
      eventually_of_mem (hU.mem_nhds hz) fun w hw =>
        (hs i w hw).mdifferentiableAt (hU.mem_nhds hw)
    have hfam : ∀ c z, z ∈ U ∩ flatDomain Φ →
        HolomorphicAt n (logFamily Φ κ k s c) z := by
      rintro (i | j | ij) z hz
      · exact hhol i z hz.1
      · by_cases hj : k ≤ j.val
        · simpa [logFamily,hj] using holomorphicAt_flatCoord Φ j hz.2
        · simpa [logFamily,hj] using holomorphicAt_const (n := n) (x := z) (0 : ℂ)
      · by_cases hj : ij.2.val < k
        · simpa [logFamily,hj] using (boundaryWeight_holomorphic Φ κ ij.2 hz.2).mul
            (holomorphicAt_flatPartial ij.2 hz.2 (hhol ij.1 z hz.1))
        · simpa [logFamily,hj] using holomorphicAt_const (n := n) (x := z) (0 : ℂ)
    let eqv := Fintype.equivFin (Fin r ⊕ Fin n ⊕ (Fin r × Fin n))
    refine ⟨U ∩ flatDomain Φ,hU',⟨hxU,mem_flatDomain_self Φ⟩,
      Fintype.card (Fin r ⊕ Fin n ⊕ (Fin r × Fin n)),
      fun c => logFamily Φ κ k s (eqv.symm c),?_,?_⟩
    · intro c z hz
      exact (hfam _ z hz).self_of_nhds.mdifferentiableWithinAt
    · intro z hz g
      have hrange : range (fun c => logFamily Φ κ k s (eqv.symm c)) =
          range (logFamily Φ κ k s) := by
        ext t
        constructor
        · rintro ⟨c,rfl⟩;exact ⟨_,rfl⟩
        · rintro ⟨c,rfl⟩;exact ⟨eqv c,by simp⟩
      rw [hrange]
      exact log_mem_iff_family Φ hsrc κ (fun w hw => (hcharts w hw).1)
        (fun w hw => (hcharts w hw).2) hU' inter_subset_right s
        (fun i => (hs i).mono inter_subset_left) (fun w hw => hgen w hw.1) hz g
  · refine ⟨Nᶜ,hN.1.isOpen_compl,hx,1,fun _ _ => (1 : ℂ),
      fun _ => mdifferentiableOn_const,fun y hy g => ⟨fun hg => ?_,fun hg =>
        log_mem_of_notMem hN.1 hy hg.1⟩⟩
    exact isInSpanAt_of_eq_mul ⟨0,rfl⟩ hg.1 hg.1
      (Eventually.of_forall fun _ => (mul_one _).symm)

/-- One actual finite original family is chosen before ALL nearby points and ALL ideal members. -/
theorem exists_original_finite_log_generators {N : Set M} {E : List (Set M)}
    (A : GermIdeal n M) (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) (x : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hxU : x ∈ U) (r : ℕ) (s : Fin r → M → ℂ),
      (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (s i) U) ∧
      ∀ y ∈ U, ∀ g : M → ℂ, (logDerivIdealAlong N E A).mem y g ↔
        IsInSpanAt (n := n) (· ∈ range s) y g := by
  obtain ⟨U,hU,hxU,r,s,hs,hgen⟩ := isCoherent_logDerivIdealAlong hA hN hE hT x
  exact ⟨U,hU,hxU,r,s,hs,hgen⟩

end
end Hironaka.HironakaActualIntrinsicLogDerivativeFrame
