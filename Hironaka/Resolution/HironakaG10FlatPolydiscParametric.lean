import Hironaka.Resolution.HironakaG10FlatPolydiscAlgebra
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Holomorphic dependence of `B(K)`-restrictions on a parameter

Let `F(s,z)` be holomorphic on an open set `O ⊆ X × E` (finite-dimensional complex spaces)
containing `{s₀} × K`, `K ⊆ E` compact. Then `s ↦ F(s,·)|_K ∈ B(K)` (`restrictParam`, defined
as `0` where `{s} × K ⊄ O`) is complex differentiable at `s₀` as a map into the Banach algebra
`B(K)` (`differentiableAt_restrictParam`), with derivative
`v ↦ (z ↦ ∂F(s₀,z)(v,0))|_K`. Consequently a holomorphic matrix `f(s,z)` gives a holomorphic
family of bounded operators `s ↦ B(K, f(s)) : B(K)^p → B(K)^q`
(`differentiableAt_matrixOperator_restrictParam`): the operator family of Frisch's Lemme 2
depends analytically on the parameter (FLAT03-FRISCH-CONTRACT.md, item 1).
The proof is a uniform second-order Taylor bound on a compact tube.
BP: hironaka-g10-flat-polydisc-parametric.tex. -/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace Hironaka.HironakaG10FlatPolydiscParametric
noncomputable section
open Classical HironakaG10FlatPolydiscAlgebra

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The slice `z ↦ F(s,z)` is holomorphic on `{z | (s,z) ∈ O}`. -/
theorem differentiableOn_slice {F : X × E → ℂ} {O : Set (X × E)} (hF : DifferentiableOn ℂ F O)
    (s : X) : DifferentiableOn ℂ (fun z => F (s, z)) {z | (s, z) ∈ O} :=
  hF.comp ((differentiableOn_const s).prodMk differentiableOn_id) fun _ hz => hz

/-- `s ↦ F(s,·)|_K` as a `B(K)`-valued map (`0` where `{s} × K ⊄ O`). -/
def restrictParam (K : Set E) {F : X × E → ℂ} {O : Set (X × E)} (hF : DifferentiableOn ℂ F O)
    (s : X) : holSubalgebra K :=
  if h : ∀ z ∈ K, (s, z) ∈ O then restrict K h (fun z => F (s, z)) (differentiableOn_slice hF s)
  else 0

theorem restrictParam_apply (K : Set E) {F : X × E → ℂ} {O : Set (X × E)}
    (hF : DifferentiableOn ℂ F O) {s : X} (hs : ∀ z ∈ K, (s, z) ∈ O) (z : K) :
    ((restrictParam K hF s : holSubalgebra K) : C(K, ℂ)) z = F (s, z) := by
  rw [restrictParam, dif_pos hs]
  rfl

variable [FiniteDimensional ℂ X] [FiniteDimensional ℂ E]

/-- A compact tube around `{s₀} × K` inside `O`, with a uniform bound for `‖DF‖`. -/
theorem exists_tube_bound (K : Set E) [CompactSpace K] {F : X × E → ℂ} {O : Set (X × E)}
    (hO : IsOpen O) (hF : DifferentiableOn ℂ F O) {s₀ : X} (hK : ∀ z ∈ K, (s₀, z) ∈ O) :
    ∃ δ > 0, ∃ L, 0 ≤ L ∧ (∀ z ∈ K, ball (s₀, z) δ ⊆ O) ∧
      ∀ z ∈ K, ∀ p ∈ ball (s₀, z) δ, ‖fderiv ℂ F p‖ ≤ L := by
  have : ProperSpace X := FiniteDimensional.proper ℂ X
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hKc : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  have hK₀ : IsCompact (({s₀} : Set X) ×ˢ K) := isCompact_singleton.prod hKc
  obtain ⟨δ, hδ, hδO⟩ := hK₀.exists_cthickening_subset_open hO (by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    rw [mem_singleton_iff] at hs
    subst hs
    exact hK z hz)
  have hcomp : IsCompact (cthickening δ (({s₀} : Set X) ×ˢ K)) := hK₀.cthickening
  have hcd : ContinuousOn (fderiv ℂ F) O :=
    (Hironaka.contDiffOn_of_differentiableOn_complex hF hO).continuousOn_fderiv_of_isOpen hO
      (by simp)
  obtain ⟨L, hL⟩ := hcomp.exists_bound_of_continuousOn (hcd.mono hδO)
  have hball : ∀ z ∈ K, ball (s₀, z) δ ⊆ cthickening δ (({s₀} : Set X) ×ˢ K) := fun z hz p hp =>
    Metric.mem_cthickening_of_dist_le p (s₀, z) δ _ ⟨rfl, hz⟩ (mem_ball.mp hp).le
  refine ⟨δ, hδ, max L 0, le_max_right _ _, fun z hz => (hball z hz).trans hδO,
    fun z hz p hp => (hL p (hball z hz hp)).trans (le_max_left _ _)⟩

/-- The derivative candidate `v ↦ (z ↦ ∂F(s₀,z)(v,0))|_K`. -/
def derivRestrict (K : Set E) {F : X × E → ℂ} {O : Set (X × E)} (hO : IsOpen O)
    (hF : DifferentiableOn ℂ F O) {s₀ : X} (hK : ∀ z ∈ K, (s₀, z) ∈ O) (v : X) :
    holSubalgebra K :=
  restrict K hK (fun z => fderiv ℂ F (s₀, z) (v, 0))
    ((Hironaka.differentiableOn_fderiv_apply_of_isOpen hF hO (v, 0)).comp
      ((differentiableOn_const s₀).prodMk differentiableOn_id) fun _ hz => hz)

theorem derivRestrict_isBoundedLinearMap (K : Set E) [CompactSpace K] {F : X × E → ℂ}
    {O : Set (X × E)} (hO : IsOpen O) (hF : DifferentiableOn ℂ F O) {s₀ : X}
    (hK : ∀ z ∈ K, (s₀, z) ∈ O) :
    IsBoundedLinearMap ℂ (derivRestrict K hO hF hK) := by
  obtain ⟨δ, hδ, L, hL0, -, hL⟩ := exists_tube_bound K hO hF hK
  refine IsLinearMap.with_bound ⟨fun v w => ?_, fun c v => ?_⟩ L fun v => ?_
  · apply Subtype.ext
    ext z
    change fderiv ℂ F (s₀, z.1) (v + w, 0) = fderiv ℂ F (s₀, z.1) (v, 0) + fderiv ℂ F (s₀, z.1) (w, 0)
    rw [← map_add, Prod.mk_add_mk, add_zero]
  · apply Subtype.ext
    ext z
    change fderiv ℂ F (s₀, z.1) (c • v, 0) = c • fderiv ℂ F (s₀, z.1) (v, 0)
    rw [← map_smul, Prod.smul_mk, smul_zero]
  · rw [norm_holSubalgebra, ContinuousMap.norm_le _ (by positivity)]
    intro z
    change ‖fderiv ℂ F (s₀, z.1) (v, 0)‖ ≤ L * ‖v‖
    refine ((fderiv ℂ F (s₀, z.1)).le_opNorm _).trans ?_
    have hn : ‖((v, 0) : X × E)‖ = ‖v‖ := by simp [Prod.norm_def]
    rw [hn]
    exact mul_le_mul_of_nonneg_right (hL z.1 z.2 _ (mem_ball_self hδ)) (norm_nonneg _)

/-- The derivative candidate as a continuous linear map. -/
def derivRestrictCLM (K : Set E) [CompactSpace K] {F : X × E → ℂ} {O : Set (X × E)}
    (hO : IsOpen O) (hF : DifferentiableOn ℂ F O) {s₀ : X} (hK : ∀ z ∈ K, (s₀, z) ∈ O) :
    X →L[ℂ] holSubalgebra K :=
  IsBoundedLinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := X) (F := holSubalgebra K)
    (derivRestrict K hO hF hK) (derivRestrict_isBoundedLinearMap K hO hF hK)

theorem derivRestrictCLM_apply (K : Set E) [CompactSpace K] {F : X × E → ℂ} {O : Set (X × E)}
    (hO : IsOpen O) (hF : DifferentiableOn ℂ F O) {s₀ : X} (hK : ∀ z ∈ K, (s₀, z) ∈ O) (v : X) :
    derivRestrictCLM K hO hF hK v = derivRestrict K hO hF hK v := rfl

/-- **Holomorphic dependence on the parameter.** -/
theorem hasFDerivAt_restrictParam (K : Set E) [CompactSpace K] {F : X × E → ℂ} {O : Set (X × E)}
    (hO : IsOpen O) (hF : DifferentiableOn ℂ F O) {s₀ : X} (hK : ∀ z ∈ K, (s₀, z) ∈ O) :
    HasFDerivAt (restrictParam K hF) (derivRestrictCLM K hO hF hK) s₀ := by
  obtain ⟨δ, hδ, L, hL0, hsub, hL⟩ := exists_tube_bound K hO hF hK
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hδ8 : 0 < δ / 8 := by positivity
  have hr : 0 < min (δ / 8) (c / (L / (δ / 4) + 1)) := lt_min hδ8 (by positivity)
  filter_upwards [ball_mem_nhds (0 : X) hr] with v hv
  rw [mem_ball_zero_iff, lt_min_iff] at hv
  have hs : ∀ z ∈ K, (s₀ + v, z) ∈ O := fun z hz => hsub z hz (by
    rw [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_eq_norm,
      add_sub_cancel_left]
    linarith [hv.1])
  rw [derivRestrictCLM_apply, norm_holSubalgebra, ContinuousMap.norm_le _ (by positivity)]
  intro z
  have key : ((restrictParam K hF (s₀ + v) - restrictParam K hF s₀ -
      derivRestrict K hO hF hK v : holSubalgebra K) :
        C(K, ℂ)) z = F (s₀ + v, z.1) - F (s₀, z.1) - fderiv ℂ F (s₀, z.1) (v, 0) := by
    rw [Subalgebra.coe_sub, Subalgebra.coe_sub, ContinuousMap.sub_apply, ContinuousMap.sub_apply,
      restrictParam_apply K hF hs, restrictParam_apply K hF hK]
    rfl
  rw [key]
  have hT := Hironaka.norm_sub_sub_fderiv_le (f := F) (z₀ := (s₀, z.1)) hδ
    (hF.mono (hsub z.1 z.2)) (hL z.1 z.2) (z := (s₀, z.1)) (u := (v, 0))
    (mem_ball_self hδ8) (by simpa [Prod.norm_def] using hv.1)
  have hn : ‖((v, 0) : X × E)‖ = ‖v‖ := by simp [Prod.norm_def]
  rw [Prod.mk_add_mk, add_zero, hn] at hT
  refine hT.trans ?_
  have hq : 0 ≤ L / (δ / 4) := by positivity
  have h1 : L / (δ / 4) * ‖v‖ ≤ c := by
    have h2 : ‖v‖ * (L / (δ / 4) + 1) < c := (lt_div_iff₀ (by positivity)).mp hv.2
    nlinarith [norm_nonneg v]
  calc L / (δ / 4) * ‖v‖ * ‖v‖ ≤ c * ‖v‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
    _ = c * ‖v‖ := rfl

theorem differentiableAt_restrictParam (K : Set E) [CompactSpace K] {F : X × E → ℂ}
    {O : Set (X × E)} (hO : IsOpen O) (hF : DifferentiableOn ℂ F O) {s₀ : X}
    (hK : ∀ z ∈ K, (s₀, z) ∈ O) : DifferentiableAt ℂ (restrictParam K hF) s₀ :=
  (hasFDerivAt_restrictParam K hO hF hK).differentiableAt

/-- **The operator family `s ↦ B(K, f(s))` is holomorphic.** A matrix of functions holomorphic
on `O ⊇ {s₀} × K` gives a holomorphic family of bounded operators `B(K)^p → B(K)^q`. -/
theorem differentiableAt_matrixOperator_restrictParam (K : Set E) [CompactSpace K]
    {p q : Type*} [Fintype p] [Fintype q] {F : q → p → X × E → ℂ} {O : Set (X × E)}
    (hO : IsOpen O) (hF : ∀ i j, DifferentiableOn ℂ (F i j) O) {s₀ : X}
    (hK : ∀ z ∈ K, (s₀, z) ∈ O) :
    DifferentiableAt ℂ (fun s => matrixOperator (fun i j => restrictParam K (hF i j) s)) s₀ :=
  differentiableAt_matrixOperator fun i j => differentiableAt_restrictParam K hO (hF i j) hK

end
end Hironaka.HironakaG10FlatPolydiscParametric
