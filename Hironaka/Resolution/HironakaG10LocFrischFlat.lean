import Hironaka.Resolution.HironakaG10LocProductExact

/-! # Frisch's Lemme 3 (i) at sheaf level: flatness over `T` on `T × K̊`

Frisch 1968, Lemme 3 (i) (p. 308–309): "il existe un voisinage ouvert `V` de `s` dans `T` tel que
`𝓕(V)` soit `V`-plat sur `V × K̊`". Frisch's proof: sections `σ(t)` of the kernel bundle of
`B(K, f(t))` over `T`, holomorphic in `t`, with `σ(s)` generating `ker B(K, f(s))` (privilege), give a
direct exact `B(K)`-linear sequence `B(K,L₂) → B(K,L₁) → B(K,L₀)` over `V`, hence a complex of sheaves
on `V × K̊` with exact fibres (Douady §8 Lemme 1 (b)), hence exact and `𝓕` flat (Prop. 2).

Here, for a presentation `f` holomorphic on `V × U` and ANY parameter set `T` along which the kernel of
`B(K, f(s₀))` extends holomorphically — a family `σ(s)` of `B(K)`-matrices, holomorphic near `s₀`,
with `f(s)|_K σ(s) = 0` for `s ∈ T` and `(σ(s₀), f(s₀)|_K)` direct exact —
**`relFibreFlatAt_of_kernelFamily`**: for `s ∈ T` near `s₀` and every `y ∈ K̊`, `coker f` is flat over
`T` at `(s, y)` in Tor₁ form (`RelFibreFlatAt`, with the start `(σ, f)` itself, exact over `T × X` on
the open set `V₁ × K̊`).

Auxiliary: `bkMat σ` (the matrix of functions `(s, x) ↦ σ(s)(x)` on `S × X`),
`fibreExactAt_of_bK_exact` (Lemme 1 (a₀) with Theorem A, for `B(K)`-entry second matrices).
Inputs: `hTh1` (Douady §7 Th. 1) and `hA` (Theorem A), explicit hypotheses.
BP: hironaka-g10-loc-frisch-flat.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10LocFrischFlat
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10LocDirectPersistence HironakaG10LocSheafExact
  HironakaG10LocFibreOpen HironakaG10LocRelative HironakaG10LocJointHol HironakaG10LocProductExact

variable {S X : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [NormedAddCommGroup X]
  [NormedSpace ℂ X]

/-- The matrix of functions `(s, x) ↦ σ(s)(x)` of a family of `B(K)`-matrices. -/
def bkMat (K : Set X) {κ ι : Type*} (σ : S → κ → ι → holSubalgebra K) : κ → ι → S × X → ℂ :=
  fun j k q => extendZero K ((σ q.1 j k : holSubalgebra K) : C(K, ℂ)) q.2

omit [NormedAddCommGroup S] [NormedSpace ℂ S] in
theorem fib_bkMat (K : Set X) {κ ι : Type*} (σ : S → κ → ι → holSubalgebra K) (s : S) :
    fib (bkMat K σ) s = bkFun K (σ s) := rfl

/-- **Lemme 1 (a₀) with Theorem A for a `B(K)`-entry second matrix**: if `(σ, f(s,·)|_K)` is exact
over `B(K)`, the fibre start `(σ, f(s,·))` is exact at every point of `K̊`. -/
theorem fibreExactAt_of_bK_exact {𝒦 : Set (Set X)} (hA : RelationsTheoremA X 𝒦) {K U : Set X}
    (hK : K ∈ 𝒦) [CompactSpace K] (hU : IsOpen U) (hKU : K ⊆ U) {V : Set S} {a b c : ℕ}
    (f : Fin a → Fin b → S × X → ℂ) (hf : ∀ i j, DifferentiableOn ℂ (f i j) (V ×ˢ U))
    (σ : S → Fin b → Fin c → holSubalgebra K) {s : S} (hs : s ∈ V)
    (hex : ∀ v : Fin b → holSubalgebra K,
      matrixOperator (fun i j => fibRestrict K hKU (f i j) (hf i j) s) v = 0 →
        ∃ t, matrixOperator (σ s) t = v)
    {y : X} (hy : y ∈ interior K) : FibreExactAt (bkMat K σ) f s y := by
  intro av hav
  obtain ⟨W, -, hKW, hWU, μ, _, τ, hτ⟩ :=
    hA K hK U hU hKU (Fin a) (Fin b) (fib f s) fun i j => differentiableOn_fib (hf i j) hs
  have hex' : ∀ v : Fin b → holSubalgebra K, matrixOperator (restrictMatrix K hKW (fib f s)
      fun i j => (differentiableOn_fib (hf i j) hs).mono hWU) v = 0 →
        ∃ t, matrixOperator (σ s) t = v := by
    intro v hv
    have hmat : (fun i j => fibRestrict K hKU (f i j) (hf i j) s) = restrictMatrix K hKW (fib f s)
        (fun i j => (differentiableOn_fib (hf i j) hs).mono hWU) := by
      funext i j
      rw [fibRestrict_of_mem K hKU (f i j) (hf i j) hs]
      rfl
    refine hex v ?_
    rw [hmat]
    exact hv
  rw [show columns (fib (bkMat K σ) s) = columns (bkFun K (σ s)) from rfl]
  exact isCombinationAt_of_bK_exact hKW _ hτ (σ s) hex' hy av hav

/-- **Frisch 1968 Lemme 3 (i), sheaf level**: if the kernel of `B(K, f(s₀))` extends holomorphically
along the parameter set `T` (a family `σ` of `B(K)`-matrices holomorphic near `s₀` with
`f(s)|_K σ(s) = 0` for `s ∈ T` and `(σ(s₀), f(s₀)|_K)` direct exact), then for `s ∈ T` near `s₀`,
`coker f` is flat over `T` at every point of `{s} × K̊`. -/
theorem relFibreFlatAt_of_kernelFamily [FiniteDimensional ℂ S] [FiniteDimensional ℂ X]
    {𝒦 : Set (Set X)} (hTh1 : PrivilegedNbhdsProperty X 𝒦) (hA : RelationsTheoremA X 𝒦)
    (T : Set S) {K U : Set X} (hK : K ∈ 𝒦) [CompactSpace K] (hU : IsOpen U) (hKU : K ⊆ U)
    {V : Set S} (hV : IsOpen V) {s₀ : S} (hs₀V : s₀ ∈ V) (hs₀T : s₀ ∈ T) {a b c : ℕ}
    (f : Fin a → Fin b → S × X → ℂ) (hf : ∀ i j, DifferentiableOn ℂ (f i j) (V ×ˢ U))
    (σ : S → Fin b → Fin c → holSubalgebra K) (hσ : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ σ s)
    (hcomp : ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ i k,
      ∑ j, fibRestrict K hKU (f i j) (hf i j) s * σ s j k = 0)
    (h₀ : DirectExact (σ s₀) (fun i j => fibRestrict K hKU (f i j) (hf i j) s₀)) :
    ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ y ∈ interior K, RelFibreFlatAt T f (s, y) := by
  have hFc : ContinuousAt (fun s i j => fibRestrict K hKU (f i j) (hf i j) s) s₀ :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
      continuousAt_fibRestrict K hKU hV (f i j) (hf i j) hs₀V
  have hpers := directExact_eventually_rel T hs₀T hσ.self_of_nhds.continuousAt hFc hcomp h₀
  -- an open neighbourhood `V₁` of `s₀` where everything holds
  obtain ⟨V₁, hV₁, hV₁o, hs₀V₁⟩ := eventually_nhds_iff.1
    ((show ∀ᶠ s in 𝓝 s₀, s ∈ V from hV.mem_nhds hs₀V).and (hσ.and (hcomp.and hpers)))
  -- the start `(σ, f)` on `W = V₁ × K̊`
  set W : Set (S × X) := V₁ ×ˢ interior K with hWdef
  have hWo : IsOpen W := hV₁o.prod isOpen_interior
  have hWsub : W ⊆ V ×ˢ U := fun q hq => ⟨(hV₁ q.1 hq.1).1, hKU (interior_subset hq.2)⟩
  have hGd : ∀ j k, DifferentiableOn ℂ (bkMat K σ j k) W := by
    intro j k q hq
    exact (differentiableAt_bkEval_comp (c := fun s => σ s j k)
      (differentiableAt_pi.1 (differentiableAt_pi.1 (hV₁ q.1 hq.1).2.1 j) k) hq.2).differentiableWithinAt
  have hcompW : ∀ i k, ∀ q ∈ W, q.1 ∈ T → ∑ j, f i j q * bkMat K σ j k q = 0 := by
    intro i k q hq hqT
    have hqK : q.2 ∈ K := interior_subset hq.2
    have h := congrArg (fun w : holSubalgebra K => (w : C(K, ℂ)) ⟨q.2, hqK⟩)
      ((hV₁ q.1 hq.1).2.2.1 hqT i k)
    simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, ContinuousMap.coe_sum,
      Finset.sum_apply, ContinuousMap.mul_apply, ZeroMemClass.coe_zero,
      ContinuousMap.zero_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fibRestrict_of_mem K hKU (f i j) (hf i j) (hV₁ q.1 hq.1).1]
    simp only [bkMat, extendZero_of_mem K _ hqK]
    rfl
  -- fibre exactness at every point of `W` over `T`
  have hfibW : ∀ q ∈ W, q.1 ∈ T → FibreExactAt (bkMat K σ) f q.1 q.2 := by
    intro q hq hqT
    exact fibreExactAt_of_bK_exact hA hK hU hKU f hf σ (hV₁ q.1 hq.1).1
      ((hV₁ q.1 hq.1).2.2.2 hqT).exact hq.2
  have hstart : RelExactStartOn T W (bkMat K σ) f := by
    refine ⟨fun i j => (hf i j).mono hWsub, hGd, hcompW, fun p hp hpT => ?_⟩
    obtain ⟨s, y⟩ := p
    exact relExactAt_of_fibreExactAt hTh1 T hpT
      (fun j k => holAt_of_differentiableOn hWo (hGd j k) hp)
      (fun i j => holAt_of_differentiableOn hWo ((hf i j).mono hWsub) hp)
      (fun i k => Filter.mem_of_superset (hWo.mem_nhds hp) fun q hq hqT => hcompW i k q hq hqT)
      (hfibW _ hp hpT)
  filter_upwards [hV₁o.mem_nhds hs₀V₁] with s hs hsT y hy
  exact ⟨c, bkMat K σ, W, hWo, ⟨hs, hy⟩, hstart, hfibW (s, y) ⟨hs, hy⟩ hsT⟩

end
end Hironaka.HironakaG10LocFrischFlat
