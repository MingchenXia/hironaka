import Hironaka.Resolution.HironakaG10LocDirectPersistence
import Hironaka.Resolution.HironakaG10LocSheafExact
import Hironaka.Resolution.HironakaG10FlatPrivilegedNbhd

/-! # Douady §8 Prop. 2 (b) for free starts: fibre exactness is an open condition

Douady 1966, §8 n° 3, Prop. 2 (b), for free sheaves: let `G : L₂ → L₁`, `F : L₁ → L₀` be holomorphic
matrices near `(s₀, x₀)` in `S × X` with `F G = 0`. If the fibre start `(G(s₀,·), F(s₀,·))` is exact at
`x₀` (germs at `x₀`), then the fibre start `(G(s,·), F(s,·))` is exact at `y` for all `(s, y)` near
`(s₀, x₀)` (**`eventually_fibreExactAt`**).

Proof (Douady): Th. 1 (`hTh1`) gives a finite resolution `d` of `coker F(s₀,·)` (`d₀ = F(s₀,·)`) and
arbitrarily small privileged compact neighbourhoods `K` of `x₀`; fibre exactness at `x₀` writes
`d₁ = G(s₀,·) X` near `x₀`, so for `K` inside that neighbourhood the `B(K)`-start
`(G(s₀,·)|_K, F(s₀,·)|_K)` is direct exact (`directExact_of_factor`). The `B(K)`-restrictions of the
fibres are continuous in `s` (`continuousAt_fibRestrict`), so direct exactness persists near `s₀`
(`directExact_eventually`), and Lemme 1 (a₀) with Theorem A (`hA`, `exactAt_of_theoremA`) gives
germ exactness of the fibre at `s` at every point of `K̊`.

Inputs: `hTh1 : PrivilegedNbhdsProperty X 𝒦` (Douady §7 Th. 1, being proved by lane G10F) and
`hA : RelationsTheoremA X 𝒦` (Theorem A on the compact sets of `𝒦`); both are TRUE for `X = ℂⁿ` and
`𝒦` the compact polydiscs.
BP: hironaka-g10-loc-fibre-open.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10LocFibreOpen
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10LocDirectPersistence HironakaG10LocSheafExact

variable {S X : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [NormedAddCommGroup X]
  [NormedSpace ℂ X]

/-- **The fibre start `(G(s,·), F(s,·))` is exact at `y`** (germs at `y`). -/
def FibreExactAt {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
    (G : ι₁ → ι₂ → S × X → ℂ) (F : ι₀ → ι₁ → S × X → ℂ) (s : S) (y : X) : Prop :=
  ∀ a : ι₁ → X → ℂ, IsRelationAt (fib F s) y a → IsCombinationAt (columns (fib G s)) y a

/-- `B(K)`-restriction of a fibre equals `restrictMatrix` of the fibre. -/
theorem fibRestrict_eq_restrictMatrix {κ ι : Type*} (K : Set X) {U : Set X} (hKU : K ⊆ U)
    {V : Set S} (F : κ → ι → S × X → ℂ) (hF : ∀ i j, DifferentiableOn ℂ (F i j) (V ×ˢ U))
    {s : S} (hs : s ∈ V) :
    (fun i j => fibRestrict K hKU (F i j) (hF i j) s) =
      restrictMatrix K hKU (fib F s) (fun i j => differentiableOn_fib (hF i j) hs) := by
  funext i j
  exact fibRestrict_of_mem K hKU (F i j) (hF i j) hs

/-- **Douady §8 Prop. 2 (b) for free starts: fibre exactness is an open condition.** -/
theorem eventually_fibreExactAt [LocallyCompactSpace S] {𝒦 : Set (Set X)}
    (hTh1 : PrivilegedNbhdsProperty X 𝒦) (hA : RelationsTheoremA X 𝒦) {a b c : ℕ}
    {G : Fin b → Fin c → S × X → ℂ} {F : Fin a → Fin b → S × X → ℂ} {s₀ : S} {x₀ : X}
    (hG : ∀ j k, HolAt (G j k) (s₀, x₀)) (hF : ∀ i j, HolAt (F i j) (s₀, x₀))
    (hFG : ∀ i k, ∀ᶠ p in 𝓝 (s₀, x₀), ∑ j, F i j p * G j k p = 0)
    (hex : FibreExactAt G F s₀ x₀) :
    ∀ᶠ p in 𝓝 (s₀, x₀), FibreExactAt G F p.1 p.2 := by
  classical
  -- a product neighbourhood where everything is holomorphic and `F G = 0`
  have hev : ∀ᶠ p in 𝓝 (s₀, x₀), (∀ j k, DifferentiableAt ℂ (G j k) p) ∧
      (∀ i j, DifferentiableAt ℂ (F i j) p) ∧ ∀ i k, ∑ j, F i j p * G j k p = 0 :=
    (eventually_all.2 fun j => eventually_all.2 fun k => hG j k).and
      ((eventually_all.2 fun i => eventually_all.2 fun j => hF i j).and
        (eventually_all.2 fun i => eventually_all.2 fun k => hFG i k))
  obtain ⟨V₀, U₀, hV₀, hs₀V₀, hU₀, hx₀U₀, hVU⟩ := mem_nhds_prod_iff'.1 hev
  have hGd : ∀ j k, DifferentiableOn ℂ (G j k) (V₀ ×ˢ U₀) := fun j k p hp =>
    ((hVU hp).1 j k).differentiableWithinAt
  have hFd : ∀ i j, DifferentiableOn ℂ (F i j) (V₀ ×ˢ U₀) := fun i j p hp =>
    ((hVU hp).2.1 i j).differentiableWithinAt
  have hFGd : ∀ p ∈ V₀ ×ˢ U₀, ∀ i k, ∑ j, F i j p * G j k p = 0 := fun p hp => (hVU hp).2.2
  -- the fibre at `s₀` and Th. 1
  have hF₀ : ∀ i j, HolAt (fib F s₀ i j) x₀ := fun i j =>
    holAt_of_differentiableOn hU₀ (differentiableOn_fib (hFd i j) hs₀V₀) hx₀U₀
  obtain ⟨U, m, sq, d, hres, hU, hx₀U, hd0, hK⟩ :=
    hTh1 Unit (fun _ => a) (fun _ => b) (fun _ => fib F s₀) x₀ (fun _ i j => hF₀ i j)
  have hst := (hres ()).exact 0 (hres ()).pos
  -- the second matrix of the resolution, `d₁ : L_2 → L_1`
  set d₁ : Fin b → Fin (sq () 0) → X → ℂ := d () 1 with hd₁
  -- its columns are relations of the fibre at `x₀`, hence combinations of the columns of `G(s₀,·)`
  have hcol : ∀ k, IsCombinationAt (columns (fib G s₀)) x₀ (fun j => d₁ j k) := by
    intro k
    refine hex _ ⟨fun j => holAt_of_differentiableOn hU (hst.holG j k) hx₀U, fun i => ?_⟩
    filter_upwards [hU.mem_nhds hx₀U] with x hx
    have h := hst.comp i k x hx
    rw [hd0 ()] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  choose Xm hXm hXeq using hcol
  -- an open neighbourhood `W₁` of `x₀` where `d₁ = G(s₀,·) X`
  have hW : ∀ᶠ x in 𝓝 x₀, x ∈ U ∧ x ∈ U₀ ∧ (∀ k l, DifferentiableAt ℂ (Xm k l) x) ∧
      ∀ j k, d₁ j k x = ∑ l, fib G s₀ j l x * Xm k l x :=
    (show ∀ᶠ x in 𝓝 x₀, x ∈ U from hU.mem_nhds hx₀U).and
      ((show ∀ᶠ x in 𝓝 x₀, x ∈ U₀ from hU₀.mem_nhds hx₀U₀).and ((eventually_all.2 fun k =>
      eventually_all.2 fun l => hXm k l).and (eventually_all.2 fun j => eventually_all.2 fun k =>
        (hXeq k j).mono fun x hx => by
          refine hx.trans ?_
          exact Finset.sum_congr rfl fun l _ => mul_comm _ _)))
  obtain ⟨W₁, hW₁, hW₁o, hx₀W₁⟩ := eventually_nhds_iff.1 hW
  -- a privileged compact neighbourhood inside `W₁`
  obtain ⟨K, hK𝒦, hKW₁, hKU, hKc, hKx₀, -, hpriv⟩ := hK W₁ (hW₁o.mem_nhds hx₀W₁)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hKU₀ : K ⊆ U₀ := fun x hx => (hW₁ x (hKW₁ hx)).2.1
  have hXd : ∀ k l, DifferentiableOn ℂ (Xm k l) W₁ := fun k l x hx =>
    ((hW₁ x hx).2.2.1 k l).differentiableWithinAt
  have h₀ := hpriv () 0 (hres ()).pos
  -- the families of `B(K)`-restrictions of the fibres
  set Gs : S → Fin b → Fin c → holSubalgebra K := fun s j k => fibRestrict K hKU₀ (G j k) (hGd j k) s
    with hGs
  set Fs : S → Fin a → Fin b → holSubalgebra K := fun s i j => fibRestrict K hKU₀ (F i j) (hFd i j) s
    with hFs
  have hGc : ContinuousAt Gs s₀ := continuousAt_pi.2 fun j => continuousAt_pi.2 fun k =>
    continuousAt_fibRestrict K hKU₀ hV₀ (G j k) (hGd j k) hs₀V₀
  have hFc : ContinuousAt Fs s₀ := continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
    continuousAt_fibRestrict K hKU₀ hV₀ (F i j) (hFd i j) hs₀V₀
  have hcomp : ∀ᶠ s in 𝓝 s₀, ∀ i k, ∑ j, Fs s i j * Gs s j k = 0 := by
    filter_upwards [hV₀.mem_nhds hs₀V₀] with s hs i k
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    have h := hFGd (s, z) ⟨hs, hKU₀ z.2⟩ i k
    simp only [hGs, hFs, (fun f hf => fibRestrict_of_mem K hKU₀ f hf hs),
      AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.mul_apply, HironakaG10FlatPolydiscAlgebra.restrict_apply, ZeroMemClass.coe_zero,
      ContinuousMap.zero_apply]
    exact h
  -- direct exactness at `s₀`
  have hF0eq : Fs s₀ = restrictMatrix K hKU (d () 0) ((hres ()).hol 0) := by
    funext i j
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    have h := congrFun (congrFun (congrFun (hd0 ()) i) j) z
    simp only [hFs, fibRestrict_of_mem K hKU₀ _ _ hs₀V₀, restrictMatrix,
      HironakaG10FlatPolydiscAlgebra.restrict_apply]
    exact h.symm
  have h₀' : DirectExact (restrictMatrix K hKU d₁ ((hres ()).hol 1)) (Fs s₀) := by
    rw [hF0eq]
    exact h₀
  set XK : Fin c → Fin (sq () 0) → holSubalgebra K := fun l k =>
    restrict K hKW₁ (Xm k l) (hXd k l) with hXK
  have hX : ∀ j k, restrictMatrix K hKU d₁ ((hres ()).hol 1) j k = ∑ l, Gs s₀ j l * XK l k := by
    intro j k
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    have h := (hW₁ z (hKW₁ z.2)).2.2.2 j k
    simp only [hGs, hXK, (fun f hf => fibRestrict_of_mem K hKU₀ f hf hs₀V₀), restrictMatrix,
      AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.mul_apply, HironakaG10FlatPolydiscAlgebra.restrict_apply]
    exact h
  have h₀'' : DirectExact (Gs s₀) (Fs s₀) :=
    directExact_of_factor h₀' XK hX hcomp.self_of_nhds
  have hpers := directExact_eventually hGc hFc hcomp h₀''
  -- Lemme 1 (a₀) at every nearby parameter
  filter_upwards [(hpers.and (hV₀.mem_nhds hs₀V₀)).prod_nhds (interior_mem_nhds.2 hKx₀)] with p hp
  obtain ⟨⟨hDE, hsV⟩, hyK⟩ := hp
  intro a' ha'
  have hFeq := fibRestrict_eq_restrictMatrix K hKU₀ F hFd hsV
  have hGeq := fibRestrict_eq_restrictMatrix K hKU₀ G hGd hsV
  have hDE' : DirectExact (restrictMatrix K hKU₀ (fib G p.1)
      (fun j k => differentiableOn_fib (hGd j k) hsV))
      (restrictMatrix K hKU₀ (fib F p.1) (fun i j => differentiableOn_fib (hFd i j) hsV)) := by
    rw [← hFeq, ← hGeq]
    exact hDE
  exact exactAt_of_theoremA hA hK𝒦 hU₀ hKU₀ (fun i j => differentiableOn_fib (hFd i j) hsV)
    (fun j k => differentiableOn_fib (hGd j k) hsV) hDE'.exact hyK a' ha'

/-! ## Openness of the flat locus (Tor₁ form) -/

/-- **`coker A` is flat over the parameter space at `p = (s, y)`, in Tor₁ form** (Douady 1966 §8 n° 3,
Déf. and Remarques 1–2, for a presentation): some exact start `(G, A)` on an open neighbourhood of `p`
has its fibre start at `s` exact at `y`. By `fibreFlatAt_iff_forall` this does not depend on the
start; the equivalence with flatness of the stalk of `coker A` over `𝒪_{S,s}` is the local criterion
of flatness (`Tor₁^{𝒪_{S,s}}(ℂ, coker A) = 0`), NOT formalized here. -/
def FibreFlatAt {a b : ℕ} (A : Fin a → Fin b → S × X → ℂ) (p : S × X) : Prop :=
  ∃ (c : ℕ) (G : Fin b → Fin c → S × X → ℂ) (W : Set (S × X)), IsOpen W ∧ p ∈ W ∧
    ExactStartOn W G A ∧ FibreExactAt G A p.1 p.2

/-- Fibre exactness passes to a start whose second matrix generates at least as much:
if `G = G' Y` near `(s,y)`, fibre exactness for `G` gives it for `G'`. -/
theorem fibreExactAt_of_factor {ι₂ ι₂' ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₂'] [Fintype ι₁]
    [Fintype ι₀] {G : ι₁ → ι₂ → S × X → ℂ} {G' : ι₁ → ι₂' → S × X → ℂ} {F : ι₀ → ι₁ → S × X → ℂ}
    {s : S} {y : X} (Y : ι₂' → ι₂ → S × X → ℂ) (hY : ∀ l k, HolAt (Y l k) (s, y))
    (hGY : ∀ j k, ∀ᶠ p in 𝓝 (s, y), G j k p = ∑ l, G' j l p * Y l k p)
    (h : FibreExactAt G F s y) : FibreExactAt G' F s y := by
  have ht : Tendsto (fun x : X => (s, x)) (𝓝 y) (𝓝 (s, y)) :=
    (continuous_const.prodMk continuous_id).tendsto y
  have hYf : ∀ l k, HolAt (fib Y s l k) y := fun l k =>
    (hY l k).comp (f := Y l k) (continuous_const.prodMk continuous_id)
      fun x => (differentiableAt_const s).prodMk differentiableAt_id
  intro a ha
  obtain ⟨c, hc, hca⟩ := h a ha
  refine ⟨fun l x => ∑ k, c k x * fib Y s l k x,
    fun l => HolAt.fintype_sum fun k => (hc k).mul (hYf l k), fun j => ?_⟩
  filter_upwards [hca j, ht.eventually (eventually_all.2 fun k => hGY j k)] with x hx hGx
  rw [hx]
  simp only [columns, fib, hGx, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

/-- **Independence of the start**: if `coker A` is flat at `p` in Tor₁ form, the fibre of EVERY exact
start `(G', A)` on an open neighbourhood of `p` is exact. -/
theorem fibreFlatAt_iff_forall {a b : ℕ} {A : Fin a → Fin b → S × X → ℂ} {p : S × X} :
    FibreFlatAt A p ↔ (∃ (c : ℕ) (G : Fin b → Fin c → S × X → ℂ) (W : Set (S × X)), IsOpen W ∧
      p ∈ W ∧ ExactStartOn W G A) ∧ ∀ (c' : ℕ) (G' : Fin b → Fin c' → S × X → ℂ)
        (W' : Set (S × X)), IsOpen W' → p ∈ W' → ExactStartOn W' G' A → FibreExactAt G' A p.1 p.2 := by
  constructor
  · rintro ⟨c, G, W, hW, hpW, hGA, hfib⟩
    refine ⟨⟨c, G, W, hW, hpW, hGA⟩, fun c' G' W' hW' hpW' hG'A => ?_⟩
    -- the columns of `G` are relations of `A` at `p`, hence combinations of the columns of `G'`
    have hcol : ∀ k, IsCombinationAt (columns G') p (fun j => G j k) := by
      intro k
      refine hG'A.exact p hpW' _ ⟨fun j => holAt_of_differentiableOn hW (hGA.holG j k) hpW,
        fun i => ?_⟩
      filter_upwards [hW.mem_nhds hpW] with q hq
      rw [← hGA.comp i k q hq]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    choose Y hY hYeq using hcol
    refine fibreExactAt_of_factor (fun l k => Y k l) (fun l k => hY k l) (fun j k => ?_) hfib
    filter_upwards [hYeq k j] with q hq
    rw [hq]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  · rintro ⟨⟨c, G, W, hW, hpW, hGA⟩, h⟩
    exact ⟨c, G, W, hW, hpW, hGA, h c G W hW hpW hGA⟩

/-- **Openness of the flat locus** (Tor₁ form; Douady §8 Prop. 2 (b), Frisch 1967 Th. IV.9 for the
openness part): the set of points where `coker A` is flat over the parameter space is open. -/
theorem isOpen_fibreFlatAt [LocallyCompactSpace S] {𝒦 : Set (Set X)}
    (hTh1 : PrivilegedNbhdsProperty X 𝒦) (hA : RelationsTheoremA X 𝒦) {a b : ℕ}
    (A : Fin a → Fin b → S × X → ℂ) : IsOpen {p : S × X | FibreFlatAt A p} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨s₀, x₀⟩ ⟨c, G, W, hW, hpW, hGA, hfib⟩
  have hev := eventually_fibreExactAt hTh1 hA
    (fun j k => holAt_of_differentiableOn hW (hGA.holG j k) hpW)
    (fun i j => holAt_of_differentiableOn hW (hGA.holF i j) hpW)
    (fun i k => Filter.mem_of_superset (hW.mem_nhds hpW) fun q hq => hGA.comp i k q hq) hfib
  filter_upwards [hev, hW.mem_nhds hpW] with q hq hqW
  exact ⟨c, G, W, hW, hqW, hGA, hq⟩

end
end Hironaka.HironakaG10LocFibreOpen
