import Hironaka.Resolution.HironakaG10FlatResolutionStart

/-! # Privileged neighbourhoods: Douady's §7 Th. 1 in matrix form (statement and basic API)

Douady 1966, §7 n° 1 Déf. 1–2 and n° 4 Th. 1, for a coherent sheaf presented as `coker A` by a
finite holomorphic matrix `A`.

* `rankSeq a b s`: the ranks `a, b, s 0, s 1, …` of a resolution whose first matrix is `a × b`
  (so that `d 0 = A` type-checks without casts).
* `FiniteResolutionOn U m d`: `d_k : L_{k+1} → L_k` holomorphic on `U`, `(d_{k+1}, d_k)` an exact start
  on `U` (germ-exact at every point of `U`) for `k < m`, and `L_{m+1} = 0` (so `d_{m-1}` is injective
  on germs: `0 → L_m → ⋯ → L_0 → coker d_0 → 0` is a finite free resolution); `0 < m`.
* `PrivilegedOn K hKU m d hd`: the `B(K)`-complex `B(K)^{r m} → ⋯ → B(K)^{r 0}` is direct exact in
  every degree (Douady's Déf. 1: `K` is privileged for `coker d_0`).
* `HasPrivilegedNbhds 𝒦 A x` (a finite family `A_l`): finite free resolutions `d_l 0 = A_l` on an open
  `U ∋ x`, and inside every neighbourhood of `x` a compact neighbourhood `K ∈ 𝒦`, `K ⊆ U`, of `x` with
  `K ⊆ closure (interior K)`, privileged for every `d_l` (Déf. 2 (a), (b); the injectivity (c) of
  `B(K; 𝓕) → 𝓕_x` is not required). `PrivilegedNbhdsProperty X 𝒦`: this for every finite family of
  matrices holomorphic near every point — **Douady's §7 Th. 1** when `X = ℂⁿ` and `𝒦` = polydiscs.
  It is NOT proved here. `discProd 𝒦'`: the products `K' × D̄(c,ρ)`, `K' ∈ 𝒦'` (polydiscs of `P × ℂ`).
* `exactStartOn_comp_homeomorph`, `exactStartOn_comp_cle`: exact starts transport along
  biholomorphic homeomorphisms (e.g. the swap `P × ℂ ≃ ℂ × P`).
* `subset_closure_interior_prod`: `K' × D̄(0,ρ)` is regular closed if `K'` is.
BP: hironaka-g10-flat-privileged-nbhd.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatPrivilegedNbhd
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The ranks `a, b, s 0, s 1, …` of a resolution whose first matrix is `a × b`. -/
def rankSeq (a b : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | k + 2 => s k

/-- **A finite free resolution of length `m` on `U`**: `d_k : L_{k+1} → L_k` holomorphic on `U`,
consecutive pairs exact starts on `U` in degrees `k < m`, and `L_{m+1} = 0`. -/
structure FiniteResolutionOn (U : Set X) (m : ℕ) {r : ℕ → ℕ}
    (d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ) : Prop where
  pos : 0 < m
  top : r (m + 1) = 0
  hol : ∀ k i j, DifferentiableOn ℂ (d k i j) U
  exact : ∀ k < m, ExactStartOn U (d (k + 1)) (d k)

variable {U V : Set X} {m : ℕ} {r : ℕ → ℕ} {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ}

theorem FiniteResolutionOn.mono (h : FiniteResolutionOn U m d) (hVU : V ⊆ U) :
    FiniteResolutionOn V m d :=
  ⟨h.pos, h.top, fun k i j => (h.hol k i j).mono hVU, fun k hk => (h.exact k hk).mono hVU⟩

/-- The last differential of a finite resolution is zero (its source is `0`). -/
theorem FiniteResolutionOn.top_eq_zero (h : FiniteResolutionOn U m d) (i : Fin (r m))
    (j : Fin (r (m + 1))) (x : X) : d m i j x = 0 :=
  (Fin.cast h.top j).elim0

/-- **`K` is privileged for the finite resolution `d`** (Douady 1966, §7 Déf. 1): the
`B(K)`-complex is direct exact in every degree. -/
def PrivilegedOn (K : Set X) [CompactSpace K] (hKU : K ⊆ U) (m : ℕ)
    (d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ)
    (hd : ∀ k i j, DifferentiableOn ℂ (d k i j) U) : Prop :=
  ∀ k < m, DirectExact (restrictMatrix K hKU (d (k + 1)) (hd (k + 1)))
    (restrictMatrix K hKU (d k) (hd k))

/-- **`x` has a fundamental system of compact neighbourhoods in `𝒦` privileged for the sheaves
`coker A_l`** (Douady 1966, §7 Déf. 2 (a), (b) and Th. 1, finitely many sheaves at once): finite free
resolutions `d_l` with `d_l 0 = A_l` on a common open `U ∋ x`, and inside every neighbourhood `N` of
`x` a compact neighbourhood `K ∈ 𝒦`, `K ⊆ U`, of `x`, regular closed, privileged for every `d_l`. -/
def HasPrivilegedNbhds (𝒦 : Set (Set X)) {ι : Type*} {a b : ι → ℕ}
    (A : (l : ι) → Fin (a l) → Fin (b l) → X → ℂ) (x : X) : Prop :=
  ∃ (U : Set X) (m : ι → ℕ) (s : ι → ℕ → ℕ)
    (d : (l : ι) → (k : ℕ) → Fin (rankSeq (a l) (b l) (s l) k) →
      Fin (rankSeq (a l) (b l) (s l) (k + 1)) → X → ℂ)
    (hres : ∀ l, FiniteResolutionOn U (m l) (d l)), IsOpen U ∧ x ∈ U ∧ (∀ l, d l 0 = A l) ∧
    ∀ N ∈ 𝓝 x, ∃ K ∈ 𝒦, K ⊆ N ∧ ∃ hKU : K ⊆ U, IsCompact K ∧ K ∈ 𝓝 x ∧
      K ⊆ closure (interior K) ∧ ∀ [CompactSpace K], ∀ l, PrivilegedOn K hKU (m l) (d l) (hres l).hol

/-- Enlarging the class of admissible compact sets. -/
theorem HasPrivilegedNbhds.mono_class {𝒦 𝒦' : Set (Set X)} (h𝒦 : 𝒦 ⊆ 𝒦') {ι : Type*}
    {a b : ι → ℕ} {A : (l : ι) → Fin (a l) → Fin (b l) → X → ℂ} {x : X}
    (h : HasPrivilegedNbhds 𝒦 A x) : HasPrivilegedNbhds 𝒦' A x := by
  obtain ⟨U, m, s, d, hres, hU, hxU, hd0, hK⟩ := h
  refine ⟨U, m, s, d, hres, hU, hxU, hd0, fun N hN => ?_⟩
  obtain ⟨K, hK𝒦, hKN, hKU, hKc, hKx, hKr, hpriv⟩ := hK N hN
  exact ⟨K, h𝒦 hK𝒦, hKN, hKU, hKc, hKx, hKr, hpriv⟩

/-- Restricting (or reindexing) the family of sheaves along any map `f : ι' → ι`. -/
theorem HasPrivilegedNbhds.comp {𝒦 : Set (Set X)} {ι ι' : Type*} {a b : ι → ℕ}
    {A : (l : ι) → Fin (a l) → Fin (b l) → X → ℂ} {x : X} (h : HasPrivilegedNbhds 𝒦 A x)
    (f : ι' → ι) : HasPrivilegedNbhds 𝒦 (fun l => A (f l)) x := by
  obtain ⟨U, m, s, d, hres, hU, hxU, hd0, hK⟩ := h
  refine ⟨U, fun l => m (f l), fun l => s (f l), fun l => d (f l), fun l => hres (f l), hU, hxU,
    fun l => hd0 (f l), fun N hN => ?_⟩
  obtain ⟨K, hK𝒦, hKN, hKU, hKc, hKx, hKr, hpriv⟩ := hK N hN
  exact ⟨K, hK𝒦, hKN, hKU, hKc, hKx, hKr, fun l => hpriv (f l)⟩

variable (X) in
/-- **Douady's theorem of privileged neighbourhoods** (§7 Th. 1) for the space `X` and the class
`𝒦` of compact sets (polydiscs for `X = ℂⁿ`): every finite family of finite matrices holomorphic near
a point `x` has privileged neighbourhoods in `𝒦` at `x`. -/
def PrivilegedNbhdsProperty (𝒦 : Set (Set X)) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ι → ℕ) (A : (l : ι) → Fin (a l) → Fin (b l) → X → ℂ) (x : X),
    (∀ l i j, HolAt (A l i j) x) → HasPrivilegedNbhds 𝒦 A x

/-- Products `K' × D̄(c,ρ)` (`ρ > 0`) with `K' ∈ 𝒦'`: polydiscs of `P × ℂ` from polydiscs of `P`. -/
def discProd {P : Type*} (𝒦' : Set (Set P)) : Set (Set (P × ℂ)) :=
  {K | ∃ K' ∈ 𝒦', ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧ K = K' ×ˢ Metric.closedBall c ρ}

/-! ## Transport along biholomorphic homeomorphisms -/

section Transport
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **Exact starts transport along a biholomorphic homeomorphism.** -/
theorem exactStartOn_comp_homeomorph (φ : X ≃ₜ Y) (hφ : ∀ x, DifferentiableAt ℂ φ x)
    (hφs : ∀ y, DifferentiableAt ℂ φ.symm y) {U : Set Y} {G : ι₁ → ι₂ → Y → ℂ}
    {F : ι₀ → ι₁ → Y → ℂ} (h : ExactStartOn U G F) :
    ExactStartOn (φ ⁻¹' U) (fun j k => G j k ∘ φ) (fun i j => F i j ∘ φ) := by
  have hφd : DifferentiableOn ℂ φ (φ ⁻¹' U) := fun x _ => (hφ x).differentiableWithinAt
  refine ⟨fun i j => (h.holF i j).comp hφd fun _ hx => hx,
    fun j k => (h.holG j k).comp hφd fun _ hx => hx, fun i k x hx => h.comp i k (φ x) hx,
    fun y hy a ha => ?_⟩
  have hsy : φ.symm (φ y) = y := φ.symm_apply_apply y
  have hφs_t : Tendsto φ.symm (𝓝 (φ y)) (𝓝 y) := by
    have := φ.symm.continuous.tendsto (φ y)
    rwa [hsy] at this
  have hφ_t : Tendsto φ (𝓝 y) (𝓝 (φ y)) := φ.continuous.tendsto y
  have ha' : IsRelationAt F (φ y) fun j => a j ∘ φ.symm := by
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have h1 : HolAt (a j) (φ.symm (φ y)) := by rw [hsy]; exact ha.1 j
      exact h1.comp φ.symm.continuous hφs
    · filter_upwards [hφs_t.eventually (ha.2 i)] with z hz
      simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using hz
  obtain ⟨c, hc, hcσ⟩ := h.exact (φ y) hy _ ha'
  refine ⟨fun k => c k ∘ φ, fun k => (hc k).comp φ.continuous hφ, fun j => ?_⟩
  filter_upwards [hφ_t.eventually (hcσ j)] with x hx
  simpa only [Function.comp_apply, Homeomorph.symm_apply_apply, columns] using hx

/-- Exact starts transport along a continuous linear equivalence. -/
theorem exactStartOn_comp_cle (L : X ≃L[ℂ] Y) {U : Set Y} {G : ι₁ → ι₂ → Y → ℂ}
    {F : ι₀ → ι₁ → Y → ℂ} (h : ExactStartOn U G F) :
    ExactStartOn (L ⁻¹' U) (fun j k => G j k ∘ L) (fun i j => F i j ∘ L) :=
  exactStartOn_comp_homeomorph L.toHomeomorph (fun _ => (L : X →L[ℂ] Y).differentiableAt)
    (fun _ => (L.symm : Y →L[ℂ] X).differentiableAt) h

end Transport

/-! ## Regular closed products -/

omit [NormedSpace ℂ X] in
theorem subset_closure_interior_prod {K' : Set X} (hK' : K' ⊆ closure (interior K')) {ρ : ℝ}
    (hρ : 0 < ρ) :
    K' ×ˢ Metric.closedBall (0 : ℂ) ρ ⊆ closure (interior (K' ×ˢ Metric.closedBall (0 : ℂ) ρ)) := by
  rw [interior_prod_eq, closure_prod_eq, interior_closedBall (0 : ℂ) hρ.ne', closure_ball (0 : ℂ) hρ.ne']
  exact prod_mono hK' subset_rfl

end
end Hironaka.HironakaG10FlatPrivilegedNbhd
