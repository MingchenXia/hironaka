import Hironaka.Resolution.HironakaG10FlatPrivilegedNbhd
import Hironaka.Resolution.HironakaG10FlatLiftResolution
import Hironaka.Resolution.HironakaG10FlatFlatFamilyResolution

/-! # The flat step of Douady's theorem of privileged neighbourhoods

Douady 1966, §7 n° 3 Prop. 6 (a) and the flat case of the induction of n° 4 Th. 1: let `𝓕 = coker A`
on `ℂ × P` with `w` (the first coordinate) regular on `𝓕` at `(0, z₀)`. Then privileged
neighbourhoods of `z₀` for the fibre `𝓕(0) = coker A(0,·)` give privileged neighbourhoods
`K' × D̄(0,ρ)` of `(z₀, 0)` for `𝓕` (coordinates `P × ℂ` on the `B(K)` side, `swapMat`).

* `exists_lift_resolution`: a finite free resolution of the fibre lifts to a finite free resolution of
  `𝓕` on an open neighbourhood of `(0, z₀)` with the same ranks (`exists_lift_chain`).
* `fibreOp_eq_matrixOperator`: on `K'` where the slices `d_k(0,·)` agree with `e_k`, the fibre
  operators of `d_k` at `w = 0` are the `B(K')`-operators of `e_k`.
* **`eventually_privilegedOn_prod`** (Prop. 6 (a)): if `K'` is privileged for the fibre resolution `e`
  and `d_k(0,·) = e_k` on `K'`, then `K' × D̄(0,ρ)` is privileged for `d` for all small `ρ > 0`.
* **`hasPrivilegedNbhds_of_regular`** (flat step of Th. 1, finitely many sheaves): if `w` is regular on
  every `coker A_l` at `(0, z₀)` and `z₀` has privileged neighbourhoods in `𝒦'` for the fibres
  `coker A_l(0,·)`, then `(z₀, 0)` has privileged neighbourhoods in `discProd 𝒦'` for the `coker A_l`.
BP: hironaka-g10-flat-privileged-flat-step.tex. -/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace Hironaka.HironakaG10FlatPrivilegedFlatStep
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatSliceResolution HironakaG10FlatLiftResolution
  HironakaG10FlatFlatFamilyPrivilege HironakaG10FlatFlatFamilyResolution
  HironakaG10FlatPolydiscParametric

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- **Lifting a finite resolution of the fibre** (in `FiniteResolutionOn` form). -/
theorem exists_lift_resolution (hX : OkaProperty (ℂ × P)) {U₀ : Set P} (hU₀ : IsOpen U₀) {z₀ : P}
    (hz₀ : z₀ ∈ U₀) {m : ℕ} {r : ℕ → ℕ} {e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ}
    (he : FiniteResolutionOn U₀ m e) {A : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ}
    (hA : ∀ i j, HolAt (A i j) ((0 : ℂ), z₀))
    (hAe : ∀ᶠ z in 𝓝 z₀, ∀ i j, A i j ((0 : ℂ), z) = e 0 i j z)
    (hreg : RegularAt A (fun x => x.1) ((0 : ℂ), z₀)) :
    ∃ V : Set (ℂ × P), IsOpen V ∧ ((0 : ℂ), z₀) ∈ V ∧
      ∃ d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → ℂ × P → ℂ, d 0 = A ∧ FiniteResolutionOn V m d ∧
        ∀ k ≤ m, ∀ᶠ z in 𝓝 z₀, ∀ i j, d k i j ((0 : ℂ), z) = e k i j z := by
  obtain ⟨V, hVo, hyV, d, hd0, hdhol, hdex, -, hdsl⟩ := exists_lift_chain hX he.pos hU₀ hz₀ he.exact
    (fun i j z _ => he.top_eq_zero i j z) hA hAe hreg
  exact ⟨V, hVo, hyV, d, hd0, ⟨he.pos, he.top, hdhol, hdex⟩, hdsl⟩

/-- On `K'` where the slices agree, the fibre operator at `w = 0` is the `B(K')`-operator. -/
theorem fibreOp_eq_matrixOperator {K' : Set P} [CompactSpace K'] {V : Set (ℂ × P)} {κ ι : Type*}
    [Fintype ι] {D : κ → ι → ℂ × P → ℂ} (hD : ∀ i j, DifferentiableOn ℂ (D i j) V) {U₀ : Set P}
    {E : κ → ι → P → ℂ} (hE : ∀ i j, DifferentiableOn ℂ (E i j) U₀) (hK'U₀ : K' ⊆ U₀)
    (hK'V : ∀ z ∈ K', ((0 : ℂ), z) ∈ V) (hDE : ∀ z ∈ K', ∀ i j, D i j ((0 : ℂ), z) = E i j z) :
    fibreOp K' hD 0 = matrixOperator (restrictMatrix K' hK'U₀ E hE) := by
  unfold fibreOp
  congr 1
  funext i j
  apply Subtype.ext; apply ContinuousMap.ext; intro z
  rw [restrictParam_apply K' (hD i j) hK'V z]
  exact hDE z z.2 i j

variable [FiniteDimensional ℂ P]

/-- **Douady 1966, §7 Prop. 6 (a), privileged form.** Let `d` be a finite free resolution on an open
`V ⊆ ℂ × P` containing `{w} × K'` for `w` near `0`, whose slices at `w = 0` agree on `K'` with a
finite resolution `e` (same ranks) holomorphic on `U₀ ⊇ K'`. If the compact regular closed `K'` is
privileged for `e`, then `K' × D̄(0,ρ)` is privileged for `d` (in coordinates `P × ℂ`) for all small
`ρ > 0`. -/
theorem eventually_privilegedOn_prod {K' : Set P} (hK'c : IsCompact K')
    (hK' : K' ⊆ closure (interior K')) {V : Set (ℂ × P)} (hVo : IsOpen V)
    (hKV : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ z ∈ K', (w, z) ∈ V) {m : ℕ} {r : ℕ → ℕ}
    {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → ℂ × P → ℂ} (hd : FiniteResolutionOn V m d)
    {U₀ : Set P} {e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ}
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (hK'U₀ : K' ⊆ U₀)
    (hde : ∀ k ≤ m, ∀ z ∈ K', ∀ i j, d k i j ((0 : ℂ), z) = e k i j z)
    (hpriv : ∀ [CompactSpace K'], PrivilegedOn K' hK'U₀ m e he) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ hKO : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Prod.swap ⁻¹' V,
      ∀ [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)],
        PrivilegedOn (K' ×ˢ closedBall (0 : ℂ) ρ) hKO m (fun k => swapMat (d k))
          (fun k => differentiableOn_swapMat (hd.hol k)) := by
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  have hK'V : ∀ z ∈ K', ((0 : ℂ), z) ∈ V := hKV.self_of_nhds
  have hfib : ∀ k ≤ m, fibreOp K' (hd.hol k) 0 = matrixOperator (restrictMatrix K' hK'U₀ (e k) (he k)) :=
    fun k hk => fibreOp_eq_matrixOperator (hd.hol k) (he k) hK'U₀ hK'V (hde k hk)
  obtain ⟨ρ₀, hρ₀, hρ₀'⟩ := eventually_directExact_chain hK' hVo hKV hd.hol
    (fun k hk => (hd.exact k hk).comp) (fun i j q _ => hd.top_eq_zero i j q)
    (fun k hk x hx => by
      rw [hfib k hk.le] at hx
      rw [hfib (k + 1) hk]
      exact (hpriv k hk).exact x hx)
    (fun k hk => by rw [hfib k hk.le]; exact (hpriv k hk).kerf)
    (fun k hk => by rw [hfib k hk.le]; exact (hpriv k hk).imf)
  filter_upwards [Ioo_mem_nhdsGT hρ₀] with ρ hρ
  obtain ⟨hKO, hKO'⟩ := hρ₀' ρ hρ.1 hρ.2
  exact ⟨hKO, fun {_} k hk => hKO' k hk⟩

omit [FiniteDimensional ℂ P] in
/-- Exact starts on `V ⊆ ℂ × P` give exact starts of the swapped matrices on `P × ℂ`. -/
theorem exactStartOn_swap {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
    {V : Set (ℂ × P)} {G : ι₁ → ι₂ → ℂ × P → ℂ} {F : ι₀ → ι₁ → ℂ × P → ℂ}
    (h : ExactStartOn V G F) : ExactStartOn (Prod.swap ⁻¹' V) (swapMat G) (swapMat F) :=
  exactStartOn_comp_cle (ContinuousLinearEquiv.prodComm ℂ P ℂ) h

omit [FiniteDimensional ℂ P] in
/-- A finite free resolution on `V ⊆ ℂ × P`, swapped to `P × ℂ`. -/
theorem finiteResolutionOn_swap {V : Set (ℂ × P)} {m : ℕ} {r : ℕ → ℕ}
    {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → ℂ × P → ℂ} (hd : FiniteResolutionOn V m d) :
    FiniteResolutionOn (Prod.swap ⁻¹' V) m (fun k => swapMat (d k)) :=
  ⟨hd.pos, hd.top, fun k => differentiableOn_swapMat (hd.hol k),
    fun k hk => exactStartOn_swap (hd.exact k hk)⟩

/-- **The flat step of Douady's §7 Th. 1** (finitely many sheaves). Let `ℂ × P` have Oka's
property and `A_l` (`l : ι`, finite) be matrices holomorphic near `(0, z₀)` such that `w` is regular on
every `coker A_l` at `(0, z₀)`. If `z₀` has privileged neighbourhoods in `𝒦'` for the fibres
`coker A_l(0,·)`, then `(z₀, 0)` has privileged neighbourhoods in `discProd 𝒦'` (polydiscs
`K' × D̄(0,ρ)`) for the sheaves `coker A_l` (in coordinates `P × ℂ`). -/
theorem hasPrivilegedNbhds_of_regular (hX : OkaProperty (ℂ × P)) {𝒦' : Set (Set P)} {ι : Type*}
    [Finite ι] {a b : ι → ℕ} {A : (l : ι) → Fin (a l) → Fin (b l) → ℂ × P → ℂ} {z₀ : P}
    (hA : ∀ l i j, HolAt (A l i j) ((0 : ℂ), z₀))
    (hreg : ∀ l, RegularAt (A l) (fun x => x.1) ((0 : ℂ), z₀))
    (hfib : HasPrivilegedNbhds 𝒦' (fun l => sliceZero (A l)) z₀) :
    HasPrivilegedNbhds (discProd 𝒦') (fun l => swapMat (A l)) (z₀, (0 : ℂ)) := by
  obtain ⟨U₀, m, s, e, hres₀, hU₀o, hz₀, he0, hK⟩ := hfib
  -- lift every fibre resolution
  have hlift : ∀ l, ∃ V : Set (ℂ × P), IsOpen V ∧ ((0 : ℂ), z₀) ∈ V ∧
      ∃ d : (k : ℕ) → Fin (rankSeq (a l) (b l) (s l) k) → Fin (rankSeq (a l) (b l) (s l) (k + 1)) →
        ℂ × P → ℂ, d 0 = A l ∧ FiniteResolutionOn V (m l) d ∧
        ∀ k ≤ m l, ∀ᶠ z in 𝓝 z₀, ∀ i j, d k i j ((0 : ℂ), z) = e l k i j z := by
    intro l
    refine exists_lift_resolution hX hU₀o hz₀ (hres₀ l) (hA l) (Eventually.of_forall fun z i j => ?_)
      (hreg l)
    rw [he0 l]
    rfl
  choose V hVo hyV d hd0 hdres hdsl using hlift
  set W : Set (ℂ × P) := ⋂ l, V l with hW
  have hWo : IsOpen W := isOpen_iInter_of_finite hVo
  have hyW : ((0 : ℂ), z₀) ∈ W := mem_iInter.2 hyV
  have hdW : ∀ l, FiniteResolutionOn W (m l) (d l) := fun l => (hdres l).mono (iInter_subset _ l)
  -- the neighbourhood of `z₀` on which all slices agree
  have hsl : ∀ᶠ z in 𝓝 z₀, ∀ l, ∀ k ∈ Finset.range (m l + 1), ∀ i j, d l k i j ((0 : ℂ), z) = e l k i j z :=
    eventually_all.2 fun l => (Finset.eventually_all _).2 fun k hk =>
      hdsl l k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  refine ⟨Prod.swap ⁻¹' W, m, s, fun l k => swapMat (d l k), fun l => finiteResolutionOn_swap (hdW l),
    hWo.preimage continuous_swap, hyW, fun l => by show swapMat (d l 0) = swapMat (A l); rw [hd0 l]; rfl,
    fun N hN => ?_⟩
  -- a product ball inside `N` and the open set
  have hN' : N ∩ Prod.swap ⁻¹' W ∈ 𝓝 (z₀, (0 : ℂ)) :=
    inter_mem hN ((hWo.preimage continuous_swap).mem_nhds hyW)
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.mp hN'
  rw [← ball_prod_same] at hδN
  obtain ⟨K', hK'𝒦, hK'N, hK'U₀, hK'c, hK'x, hK'r, hpriv⟩ :=
    hK (ball z₀ δ ∩ {z | ∀ l, ∀ k ∈ Finset.range (m l + 1), ∀ i j, d l k i j ((0 : ℂ), z) = e l k i j z})
      (inter_mem (ball_mem_nhds z₀ hδ) hsl)
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  have hKW : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ z ∈ K', (w, z) ∈ W := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with w hw z hz
    exact (hδN (show (z, w) ∈ ball z₀ δ ×ˢ ball (0 : ℂ) δ from ⟨(hK'N hz).1, hw⟩)).2
  have hρ : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ l, ∃ hKO : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Prod.swap ⁻¹' W,
      ∀ [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)],
        PrivilegedOn (K' ×ˢ closedBall (0 : ℂ) ρ) hKO (m l) (fun k => swapMat (d l k))
          (fun k => differentiableOn_swapMat ((hdW l).hol k)) :=
    eventually_all.2 fun l => eventually_privilegedOn_prod hK'c hK'r hWo hKW (hdW l)
      (hres₀ l).hol hK'U₀
      (fun k hk z hz i j => (hK'N hz).2 l k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) i j)
      (fun {_} => hpriv l)
  obtain ⟨ρ, hρl, hρpos, hρδ⟩ := (hρ.and (Ioo_mem_nhdsGT hδ)).exists
  have hKN : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ N ∩ Prod.swap ⁻¹' W := fun q hq =>
    hδN ⟨(hK'N hq.1).1, closedBall_subset_ball hρδ hq.2⟩
  refine ⟨K' ×ˢ closedBall (0 : ℂ) ρ, ⟨K', hK'𝒦, 0, ρ, hρpos, rfl⟩,
    fun q hq => (hKN hq).1, fun q hq => (hKN hq).2, hK'c.prod (isCompact_closedBall 0 ρ),
    prod_mem_nhds hK'x (closedBall_mem_nhds 0 hρpos), subset_closure_interior_prod hK'r hρpos,
    fun {_} l => ?_⟩
  obtain ⟨_, hpl⟩ := hρl l
  exact hpl

end
end Hironaka.HironakaG10FlatPrivilegedFlatStep
