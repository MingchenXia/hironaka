import Hironaka.Resolution.HironakaG10FlatResolutionStart

/-! # Douady §8 Lemme 1 (a₀): exactness over `B(K)` gives exactness of germs on `K̊`

Douady 1966, §8 n° 2, Lemme 1, proof of (a₀): "pour tout `h ∈ H⁰(K; Ker g)`, la restriction de `h`
à `K` est dans l'image de `f`, et `H⁰(K; Ker g)` engendre `Ker g_x` d'après le théorème A classique."
Free form: a matrix `F` holomorphic near the compact `K`, and a matrix `G` with entries in `B(K)`.

* **`RelationsTheoremA 𝒦`** (named classical input, Douady §7 (b) "les théorèmes A et B pour un
  polycylindre … classiques"; H. Cartan, Séminaire 1951/52, exposés XVIII–XIX): for every `K ∈ 𝒦` and
  every finite matrix holomorphic on an open `U ⊇ K`, finitely many holomorphic relations on an open
  `W`, `K ⊆ W ⊆ U`, generate its germ relations at EVERY point of `W`. TRUE for `X = ℂⁿ` and `𝒦` the
  compact polydiscs (Theorem A on an open polydisc `K ⊆ P ⊆ U`, Oka coherence of the relation sheaf,
  compactness of `K`); it is used, never proved, here.
* `bkFun K G`: the entries of a `B(K)`-matrix as functions on `X` (extension by zero), holomorphic on
  `K̊` (`holAt_bkFun`).
* **`isCombinationAt_of_bK_exact`** (Lemme 1 (a₀)): `σ` generates the relations of `F` on `W ⊇ K`,
  and every `v ∈ B(K)^{ι₁}` with `F v = 0` is `G t`; then at every `y ∈ K̊` every germ relation of `F`
  is a germ combination of the columns of `G`. `isCombinationAt_of_bK_exact'`: `G` holomorphic near `K`.
* `exactAt_of_theoremA`: the same with the generators supplied by `RelationsTheoremA`.
* Fibres: `fib F s` (the matrix `x ↦ F(s,x)`), `differentiableOn_fib`; `fibRestrict` (its
  restriction to `B(K)`, junk `0` off `V`) and **`continuousAt_fibRestrict`**: `s ↦ F(s,·)|_K` is
  continuous at `s₀ ∈ V` in `B(K)` (`S` locally compact; uniform continuity on `{s₀} × K`).
BP: hironaka-g10-loc-sheaf-exact.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10LocSheafExact
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

variable (X) in
/-- **Cartan's Theorem A on the compact sets of `𝒦`** (relation sheaves of holomorphic matrices,
named classical input): for `K ∈ 𝒦` and `F` holomorphic on an open `U ⊇ K`, finitely many holomorphic
relations of `F` on an open `W`, `K ⊆ W ⊆ U`, generate its relations at every point of `W`. -/
def RelationsTheoremA (𝒦 : Set (Set X)) : Prop :=
  ∀ K ∈ 𝒦, ∀ U : Set X, IsOpen U → K ⊆ U → ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
    (F : κ → ι → X → ℂ), (∀ i j, DifferentiableOn ℂ (F i j) U) →
      ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
        ∃ (μ : Type) (_ : Fintype μ) (σ : μ → ι → X → ℂ), GeneratesRelationsOn F W σ

/-- The entries of a `B(K)`-matrix as functions on `X` (extension by zero). -/
def bkFun (K : Set X) {κ ι : Type*} (G : κ → ι → holSubalgebra K) : κ → ι → X → ℂ :=
  fun j k => extendZero K ((G j k : holSubalgebra K) : C(K, ℂ))

theorem holAt_bkFun (K : Set X) {κ ι : Type*} (G : κ → ι → holSubalgebra K) (j : κ) (k : ι)
    {y : X} (hy : y ∈ interior K) : HolAt (bkFun K G j k) y :=
  holAt_of_differentiableOn isOpen_interior (G j k).2 hy

/-- Evaluating a `B(K)`-identity `∑ G_{jl} t_l = v_j` at a point of `K`. -/
theorem eval_matrixOperator {K : Set X} [CompactSpace K] {κ ι : Type*} [Fintype ι] (G : κ → ι → holSubalgebra K)
    (t : ι → holSubalgebra K) (j : κ) (z : K) :
    ((matrixOperator G t j : holSubalgebra K) : C(K, ℂ)) z =
      ∑ l, ((G j l : holSubalgebra K) : C(K, ℂ)) z * ((t l : holSubalgebra K) : C(K, ℂ)) z := by
  rw [matrixOperator_apply]
  simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, ContinuousMap.coe_sum,
    Finset.sum_apply, ContinuousMap.mul_apply]

variable {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

omit [Fintype ι₀] in
/-- **Douady §8 Lemme 1 (a₀), free form.** If `σ` generates the relations of `F` on `W ⊇ K` and the
`B(K)`-start `(G, F|_K)` is exact, then at every interior point of `K` every germ relation of `F` is a
germ combination of the columns of `G`. -/
theorem isCombinationAt_of_bK_exact {K W : Set X} [CompactSpace K] (hKW : K ⊆ W)
    {F : ι₀ → ι₁ → X → ℂ} (hF : ∀ i j, DifferentiableOn ℂ (F i j) W) {μ : Type*} [Fintype μ]
    {σ : μ → ι₁ → X → ℂ} (hσ : GeneratesRelationsOn F W σ) (G : ι₁ → ι₂ → holSubalgebra K)
    (hex : ∀ v : ι₁ → holSubalgebra K, matrixOperator (restrictMatrix K hKW F hF) v = 0 →
      ∃ t, matrixOperator G t = v)
    {y : X} (hy : y ∈ interior K) (a : ι₁ → X → ℂ) (ha : IsRelationAt F y a) :
    IsCombinationAt (columns (bkFun K G)) y a := by
  obtain ⟨c, hc, hca⟩ := hσ.2.2 y (hKW (interior_subset hy)) a ha
  -- each generator restricts to a `B(K)`-relation
  have hv : ∀ k, matrixOperator (restrictMatrix K hKW F hF)
      (fun j => restrict K hKW (σ k j) (hσ.1 k j)) = 0 := by
    intro k
    funext i
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    rw [eval_matrixOperator (ι := ι₁)]
    simp only [restrictMatrix, HironakaG10FlatPolydiscAlgebra.restrict_apply, Pi.zero_apply,
      ZeroMemClass.coe_zero, ContinuousMap.zero_apply]
    have h := hσ.2.1 k i z (hKW z.2)
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  choose t ht using fun k => hex _ (hv k)
  refine ⟨fun l x => ∑ k, c k x * bkFun K (fun k l => t k l) k l x,
    fun l => HolAt.fintype_sum fun k => (hc k).mul (holAt_bkFun K _ k l hy), fun j => ?_⟩
  filter_upwards [hca j, isOpen_interior.mem_nhds hy] with x hx hxK
  have hxK' : x ∈ K := interior_subset hxK
  rw [hx]
  have hσx : ∀ k, σ k j x = ∑ l, bkFun K G j l x * bkFun K (fun k l => t k l) k l x := by
    intro k
    have h := congrArg (fun v : holSubalgebra K => (v : C(K, ℂ)) ⟨x, hxK'⟩) (congrFun (ht k) j)
    simp only [HironakaG10FlatPolydiscAlgebra.restrict_apply] at h
    rw [eval_matrixOperator (ι := ι₂)] at h
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => by
      simp only [bkFun, extendZero_of_mem K _ hxK']
  simp only [hσx, columns, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

omit [Fintype ι₀] in
/-- **Lemme 1 (a₀) for a holomorphic second matrix.** -/
theorem isCombinationAt_of_bK_exact' {K W : Set X} [CompactSpace K] (hKW : K ⊆ W)
    {F : ι₀ → ι₁ → X → ℂ} (hF : ∀ i j, DifferentiableOn ℂ (F i j) W) {μ : Type*} [Fintype μ]
    {σ : μ → ι₁ → X → ℂ} (hσ : GeneratesRelationsOn F W σ) {G : ι₁ → ι₂ → X → ℂ}
    (hG : ∀ j k, DifferentiableOn ℂ (G j k) W)
    (hex : ∀ v : ι₁ → holSubalgebra K, matrixOperator (restrictMatrix K hKW F hF) v = 0 →
      ∃ t, matrixOperator (restrictMatrix K hKW G hG) t = v)
    {y : X} (hy : y ∈ interior K) (a : ι₁ → X → ℂ) (ha : IsRelationAt F y a) :
    IsCombinationAt (columns G) y a := by
  obtain ⟨c, hc, hca⟩ := isCombinationAt_of_bK_exact hKW hF hσ _ hex hy a ha
  refine ⟨c, hc, fun j => ?_⟩
  filter_upwards [hca j, isOpen_interior.mem_nhds hy] with x hx hxK
  rw [hx]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [columns, bkFun, restrictMatrix, extendZero_of_mem K _ (interior_subset hxK)]
  rfl

/-- **Exactness on `K̊` from exactness over `B(K)`, with Theorem A** (Douady §8 Lemme 1 (a₀)). -/
theorem exactAt_of_theoremA {𝒦 : Set (Set X)} (hA : RelationsTheoremA X 𝒦) {K U : Set X}
    (hK : K ∈ 𝒦) [CompactSpace K] (hU : IsOpen U) (hKU : K ⊆ U) {ι₂' ι₁' ι₀' : Type} [Fintype ι₂']
    [Fintype ι₁'] [Fintype ι₀'] {F : ι₀' → ι₁' → X → ℂ} (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    {G : ι₁' → ι₂' → X → ℂ} (hG : ∀ j k, DifferentiableOn ℂ (G j k) U)
    (hex : ∀ v : ι₁' → holSubalgebra K, matrixOperator (restrictMatrix K hKU F hF) v = 0 →
      ∃ t, matrixOperator (restrictMatrix K hKU G hG) t = v)
    {y : X} (hy : y ∈ interior K) (a : ι₁' → X → ℂ) (ha : IsRelationAt F y a) :
    IsCombinationAt (columns G) y a := by
  obtain ⟨W, -, hKW, hWU, μ, _, σ, hσ⟩ := hA K hK U hU hKU ι₀' ι₁' F hF
  exact isCombinationAt_of_bK_exact' hKW (fun i j => (hF i j).mono hWU) hσ
    (fun j k => (hG j k).mono hWU) hex hy a ha

/-! ## Fibres of matrices on a product and their restrictions -/

section Fibre
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]

/-- The fibre at `s` of a matrix on `S × X`. -/
def fib {κ ι : Type*} (F : κ → ι → S × X → ℂ) (s : S) : κ → ι → X → ℂ :=
  fun i j x => F i j (s, x)

theorem differentiableOn_fib {f : S × X → ℂ} {V : Set S} {U : Set X}
    (hf : DifferentiableOn ℂ f (V ×ˢ U)) {s : S} (hs : s ∈ V) :
    DifferentiableOn ℂ (fun x => f (s, x)) U :=
  hf.comp ((differentiableOn_const s).prodMk differentiableOn_id) fun _ hx => ⟨hs, hx⟩

open Classical in
/-- The `B(K)`-restriction of the fibre at `s` (junk `0` for `s ∉ V`). -/
def fibRestrict (K : Set X) {U : Set X} (hKU : K ⊆ U) {V : Set S} (f : S × X → ℂ)
    (hf : DifferentiableOn ℂ f (V ×ˢ U)) (s : S) : holSubalgebra K :=
  if hs : s ∈ V then restrict K hKU (fun x => f (s, x)) (differentiableOn_fib hf hs) else 0

theorem fibRestrict_of_mem (K : Set X) {U : Set X} (hKU : K ⊆ U) {V : Set S} (f : S × X → ℂ)
    (hf : DifferentiableOn ℂ f (V ×ˢ U)) {s : S} (hs : s ∈ V) :
    fibRestrict K hKU f hf s = restrict K hKU (fun x => f (s, x)) (differentiableOn_fib hf hs) :=
  dif_pos hs

/-- **Continuity of fibre restrictions**: `s ↦ f(s,·)|_K` is continuous at `s₀ ∈ V` in `B(K)`. -/
theorem continuousAt_fibRestrict [LocallyCompactSpace S] (K : Set X) [CompactSpace K] {U : Set X}
    (hKU : K ⊆ U) {V : Set S} (hV : IsOpen V) (f : S × X → ℂ) (hf : DifferentiableOn ℂ f (V ×ˢ U))
    {s₀ : S} (hs₀ : s₀ ∈ V) : ContinuousAt (fibRestrict K hKU f hf) s₀ := by
  set f' : S → K → ℂ := fun s z => f (s, z) with hf'
  have hcont : ContinuousOn ↿f' (V ×ˢ univ) := by
    have h1 : ContinuousOn f (V ×ˢ U) := hf.continuousOn
    refine h1.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      fun q hq => ⟨hq.1, hKU q.2.2⟩
  have hunif := ContinuousOn.tendstoUniformly (hV.mem_nhds hs₀) hcont
  rw [Metric.tendstoUniformly_iff] at hunif
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hunif (ε / 2) (half_pos hε), hV.mem_nhds hs₀] with s hs hsV
  rw [dist_eq_norm, fibRestrict_of_mem K hKU f hf hsV, fibRestrict_of_mem K hKU f hf hs₀,
    norm_holSubalgebra]
  refine lt_of_le_of_lt ((ContinuousMap.norm_le _ (half_pos hε).le).2 fun z => ?_) (half_lt_self hε)
  have h := hs z
  rw [dist_comm, dist_eq_norm] at h
  exact h.le

end Fibre

end
end Hironaka.HironakaG10LocSheafExact
