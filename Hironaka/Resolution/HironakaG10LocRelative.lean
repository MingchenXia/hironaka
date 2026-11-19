import Hironaka.Resolution.HironakaG10LocFibreOpen

/-! # Douady §8 over a parameter SET: Scholie, Prop. 2 (b), openness of the relative flat locus

Douady 1966, §8 n° 3 (Scholie, Prop. 2 (b)) and Frisch 1968 §2 (the parameter space `T` of Lemme 3 is
a closed analytic subset of an open `Ω`), for a parameter SUBSET `T ⊆ S` of a normed space `S`
(reduced singular bases): matrices are holomorphic on open sets of `S × X`, complex identities are
required only over `T`, and germs over `T × X` are germs of ambient holomorphic functions compared
on `T × X`.

* `directExact_eventually_rel`: persistence of direct exactness along `T` (on the subtype `T`).
* **`eventually_fibreExactAt_rel`** (Prop. 2 (b), free starts, over `T`): `F G = 0` on `T × X` near
  `(s₀, x₀)`, `s₀ ∈ T`, fibre start at `s₀` exact at `x₀` ⇒ fibre start at `s` exact at `y` for all
  `(s, y)` near `(s₀, x₀)` with `s ∈ T`. With `T = univ` this is `eventually_fibreExactAt`.
* `RelExactAt`, `RelExactStartOn` (exactness of germs over `T × X`), **`RelFibreFlatAt T A p`**
  (flatness of `coker A` over `T` at `p` in Tor₁ form: a relatively exact start on an open
  neighbourhood of `p` whose fibre start at `p.1` is exact at `p.2`), `fibreExactAt_of_factor_rel`,
  `relFibreFlatAt_iff_forall` (independent of the start), **`eventually_relFibreFlatAt`** (the
  relative flat locus is open in `T × X`).
* **`eventually_privileged_fibre`** (the Scholie, Banach part + resolution part): a finite complex
  `d` on `V × U` (`d_k d_{k+1} = 0` over `T`) whose fibre at `s₀ ∈ T` is direct exact over `B(K)` in
  degrees `< m` stays so for `s ∈ T` near `s₀`, and (Theorem A) its fibres are then exact at every
  point of `K̊` in those degrees: `K` stays privileged for the fibre.

Inputs: `hTh1 : PrivilegedNbhdsProperty X 𝒦` (Douady §7 Th. 1) and `hA : RelationsTheoremA X 𝒦`
(Theorem A), as explicit hypotheses only where used.
BP: hironaka-g10-loc-relative.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10LocRelative
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10LocDirectPersistence HironakaG10LocSheafExact
  HironakaG10LocFibreOpen

/-! ## Persistence along a parameter set -/

section Persistence
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **Direct exactness persists along `T`.** -/
theorem directExact_eventually_rel {Y : Type*} [TopologicalSpace Y] (T : Set Y)
    {g : Y → ι₁ → ι₂ → R} {f : Y → ι₀ → ι₁ → R} {s₀ : Y} (hs₀ : s₀ ∈ T) (hg : ContinuousAt g s₀)
    (hf : ContinuousAt f s₀) (hcomp : ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ i k, ∑ j, f s i j * g s j k = 0)
    (h₀ : DirectExact (g s₀) (f s₀)) : ∀ᶠ s in 𝓝 s₀, s ∈ T → DirectExact (g s) (f s) := by
  have hc : ∀ᶠ t : T in 𝓝 ⟨s₀, hs₀⟩, ∀ i k, ∑ j, f t i j * g t j k = 0 :=
    (eventually_nhds_subtype_iff T ⟨s₀, hs₀⟩ (fun s => ∀ i k, ∑ j, f s i j * g s j k = 0)).2
      (eventually_nhdsWithin_iff.2 hcomp)
  have h := directExact_eventually (X := T) (s₀ := ⟨s₀, hs₀⟩) (g := fun t => g t)
    (f := fun t => f t) (hg.comp continuous_subtype_val.continuousAt)
    (hf.comp continuous_subtype_val.continuousAt) hc h₀
  exact eventually_nhdsWithin_iff.1
    ((eventually_nhds_subtype_iff T ⟨s₀, hs₀⟩ (fun s => DirectExact (g s) (f s))).1 h)

end Persistence

variable {S X : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [NormedAddCommGroup X]
  [NormedSpace ℂ X]

/-! ## Prop. 2 (b) over a parameter set -/

/-- **Douady §8 Prop. 2 (b) for free starts, over a parameter set `T`.** -/
theorem eventually_fibreExactAt_rel [LocallyCompactSpace S] {𝒦 : Set (Set X)}
    (hTh1 : PrivilegedNbhdsProperty X 𝒦) (hA : RelationsTheoremA X 𝒦) (T : Set S) {a b c : ℕ}
    {G : Fin b → Fin c → S × X → ℂ} {F : Fin a → Fin b → S × X → ℂ} {s₀ : S} {x₀ : X}
    (hs₀T : s₀ ∈ T) (hG : ∀ j k, HolAt (G j k) (s₀, x₀)) (hF : ∀ i j, HolAt (F i j) (s₀, x₀))
    (hFG : ∀ i k, ∀ᶠ p in 𝓝 (s₀, x₀), p.1 ∈ T → ∑ j, F i j p * G j k p = 0)
    (hex : FibreExactAt G F s₀ x₀) :
    ∀ᶠ p in 𝓝 (s₀, x₀), p.1 ∈ T → FibreExactAt G F p.1 p.2 := by
  classical
  have hev : ∀ᶠ p in 𝓝 (s₀, x₀), (∀ j k, DifferentiableAt ℂ (G j k) p) ∧
      (∀ i j, DifferentiableAt ℂ (F i j) p) ∧ ∀ i k, p.1 ∈ T → ∑ j, F i j p * G j k p = 0 :=
    (eventually_all.2 fun j => eventually_all.2 fun k => hG j k).and
      ((eventually_all.2 fun i => eventually_all.2 fun j => hF i j).and
        (eventually_all.2 fun i => eventually_all.2 fun k => hFG i k))
  obtain ⟨V₀, U₀, hV₀, hs₀V₀, hU₀, hx₀U₀, hVU⟩ := mem_nhds_prod_iff'.1 hev
  have hGd : ∀ j k, DifferentiableOn ℂ (G j k) (V₀ ×ˢ U₀) := fun j k p hp =>
    ((hVU hp).1 j k).differentiableWithinAt
  have hFd : ∀ i j, DifferentiableOn ℂ (F i j) (V₀ ×ˢ U₀) := fun i j p hp =>
    ((hVU hp).2.1 i j).differentiableWithinAt
  have hFGd : ∀ p ∈ V₀ ×ˢ U₀, p.1 ∈ T → ∀ i k, ∑ j, F i j p * G j k p = 0 :=
    fun p hp hpT i k => (hVU hp).2.2 i k hpT
  have hF₀ : ∀ i j, HolAt (fib F s₀ i j) x₀ := fun i j =>
    holAt_of_differentiableOn hU₀ (differentiableOn_fib (hFd i j) hs₀V₀) hx₀U₀
  obtain ⟨U, m, sq, d, hres, hU, hx₀U, hd0, hK⟩ :=
    hTh1 Unit (fun _ => a) (fun _ => b) (fun _ => fib F s₀) x₀ (fun _ i j => hF₀ i j)
  have hst := (hres ()).exact 0 (hres ()).pos
  set d₁ : Fin b → Fin (sq () 0) → X → ℂ := d () 1 with hd₁
  have hcol : ∀ k, IsCombinationAt (columns (fib G s₀)) x₀ (fun j => d₁ j k) := by
    intro k
    refine hex _ ⟨fun j => holAt_of_differentiableOn hU (hst.holG j k) hx₀U, fun i => ?_⟩
    filter_upwards [hU.mem_nhds hx₀U] with x hx
    have h := hst.comp i k x hx
    rw [hd0 ()] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  choose Xm hXm hXeq using hcol
  have hW : ∀ᶠ x in 𝓝 x₀, x ∈ U ∧ x ∈ U₀ ∧ (∀ k l, DifferentiableAt ℂ (Xm k l) x) ∧
      ∀ j k, d₁ j k x = ∑ l, fib G s₀ j l x * Xm k l x :=
    (show ∀ᶠ x in 𝓝 x₀, x ∈ U from hU.mem_nhds hx₀U).and
      ((show ∀ᶠ x in 𝓝 x₀, x ∈ U₀ from hU₀.mem_nhds hx₀U₀).and ((eventually_all.2 fun k =>
      eventually_all.2 fun l => hXm k l).and (eventually_all.2 fun j => eventually_all.2 fun k =>
        (hXeq k j).mono fun x hx => by
          refine hx.trans ?_
          exact Finset.sum_congr rfl fun l _ => mul_comm _ _)))
  obtain ⟨W₁, hW₁, hW₁o, hx₀W₁⟩ := eventually_nhds_iff.1 hW
  obtain ⟨K, hK𝒦, hKW₁, hKU, hKc, hKx₀, -, hpriv⟩ := hK W₁ (hW₁o.mem_nhds hx₀W₁)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hKU₀ : K ⊆ U₀ := fun x hx => (hW₁ x (hKW₁ hx)).2.1
  have hXd : ∀ k l, DifferentiableOn ℂ (Xm k l) W₁ := fun k l x hx =>
    ((hW₁ x hx).2.2.1 k l).differentiableWithinAt
  have h₀ := hpriv () 0 (hres ()).pos
  set Gs : S → Fin b → Fin c → holSubalgebra K := fun s j k => fibRestrict K hKU₀ (G j k) (hGd j k) s
    with hGs
  set Fs : S → Fin a → Fin b → holSubalgebra K := fun s i j => fibRestrict K hKU₀ (F i j) (hFd i j) s
    with hFs
  have hGc : ContinuousAt Gs s₀ := continuousAt_pi.2 fun j => continuousAt_pi.2 fun k =>
    continuousAt_fibRestrict K hKU₀ hV₀ (G j k) (hGd j k) hs₀V₀
  have hFc : ContinuousAt Fs s₀ := continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
    continuousAt_fibRestrict K hKU₀ hV₀ (F i j) (hFd i j) hs₀V₀
  have hcomp : ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ i k, ∑ j, Fs s i j * Gs s j k = 0 := by
    filter_upwards [hV₀.mem_nhds hs₀V₀] with s hs hsT i k
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    have h := hFGd (s, z) ⟨hs, hKU₀ z.2⟩ hsT i k
    simp only [hGs, hFs, (fun f hf => fibRestrict_of_mem K hKU₀ f hf hs),
      AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.mul_apply, HironakaG10FlatPolydiscAlgebra.restrict_apply, ZeroMemClass.coe_zero,
      ContinuousMap.zero_apply]
    exact h
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
    directExact_of_factor h₀' XK hX (hcomp.self_of_nhds hs₀T)
  have hpers := directExact_eventually_rel T hs₀T hGc hFc hcomp h₀''
  filter_upwards [(hpers.and (hV₀.mem_nhds hs₀V₀)).prod_nhds (interior_mem_nhds.2 hKx₀)] with p hp
    hpT
  obtain ⟨⟨hDE, hsV⟩, hyK⟩ := hp
  intro a' ha'
  have hFeq := fibRestrict_eq_restrictMatrix K hKU₀ F hFd hsV
  have hGeq := fibRestrict_eq_restrictMatrix K hKU₀ G hGd hsV
  have hDE' : DirectExact (restrictMatrix K hKU₀ (fib G p.1)
      (fun j k => differentiableOn_fib (hGd j k) hsV))
      (restrictMatrix K hKU₀ (fib F p.1) (fun i j => differentiableOn_fib (hFd i j) hsV)) := by
    rw [← hFeq, ← hGeq]
    exact hDE hpT
  exact exactAt_of_theoremA hA hK𝒦 hU₀ hKU₀ (fun i j => differentiableOn_fib (hFd i j) hsV)
    (fun j k => differentiableOn_fib (hGd j k) hsV) hDE'.exact hyK a' ha'

/-! ## Relative exactness and the relative flat locus -/

section Relative
variable {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **Exactness of germs over `T × X` at `p`**: every germ `a` at `p` with `a A = 0` on `T × X` near
`p` is, on `T × X` near `p`, a germ combination of the columns of `G`. -/
def RelExactAt (T : Set S) (G : ι₁ → ι₂ → S × X → ℂ) (A : ι₀ → ι₁ → S × X → ℂ) (p : S × X) :
    Prop :=
  ∀ a : ι₁ → S × X → ℂ, (∀ j, HolAt (a j) p) →
    (∀ i, ∀ᶠ q in 𝓝 p, q.1 ∈ T → ∑ j, a j q * A i j q = 0) →
      ∃ c : ι₂ → S × X → ℂ, (∀ k, HolAt (c k) p) ∧
        ∀ j, ∀ᶠ q in 𝓝 p, q.1 ∈ T → a j q = ∑ k, c k q * G j k q

/-- **A relatively exact start on `W`** (over `T × X`). -/
structure RelExactStartOn (T : Set S) (W : Set (S × X)) (G : ι₁ → ι₂ → S × X → ℂ)
    (A : ι₀ → ι₁ → S × X → ℂ) : Prop where
  holA : ∀ i j, DifferentiableOn ℂ (A i j) W
  holG : ∀ j k, DifferentiableOn ℂ (G j k) W
  comp : ∀ i k, ∀ q ∈ W, q.1 ∈ T → ∑ j, A i j q * G j k q = 0
  exact : ∀ p ∈ W, p.1 ∈ T → RelExactAt T G A p

/-- Fibre exactness passes along `G = G' Y` over `T` (`s ∈ T`). -/
theorem fibreExactAt_of_factor_rel {ι₂' : Type*} [Fintype ι₂'] (T : Set S)
    {G : ι₁ → ι₂ → S × X → ℂ} {G' : ι₁ → ι₂' → S × X → ℂ} {F : ι₀ → ι₁ → S × X → ℂ}
    {s : S} {y : X} (hsT : s ∈ T) (Y : ι₂' → ι₂ → S × X → ℂ) (hY : ∀ l k, HolAt (Y l k) (s, y))
    (hGY : ∀ j k, ∀ᶠ p in 𝓝 (s, y), p.1 ∈ T → G j k p = ∑ l, G' j l p * Y l k p)
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
  simp only [columns, fib, fun k => hGx k hsT, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

/-- **`coker A` is flat over `T` at `p` (Tor₁ form)**: a relatively exact start on an open
neighbourhood of `p` has its fibre start at `p.1` exact at `p.2`. For `T` the underlying set of a
reduced analytic subspace this is `Tor₁^{𝒪_{T,s}}(ℂ, coker A) = 0` (local criterion of flatness, not
formalized here). -/
def RelFibreFlatAt (T : Set S) {a b : ℕ} (A : Fin a → Fin b → S × X → ℂ) (p : S × X) : Prop :=
  ∃ (c : ℕ) (G : Fin b → Fin c → S × X → ℂ) (W : Set (S × X)), IsOpen W ∧ p ∈ W ∧
    RelExactStartOn T W G A ∧ FibreExactAt G A p.1 p.2

/-- **Independence of the start** (over `T`). -/
theorem relFibreFlatAt_iff_forall (T : Set S) {a b : ℕ} {A : Fin a → Fin b → S × X → ℂ}
    {p : S × X} (hpT : p.1 ∈ T) :
    RelFibreFlatAt T A p ↔ (∃ (c : ℕ) (G : Fin b → Fin c → S × X → ℂ) (W : Set (S × X)),
      IsOpen W ∧ p ∈ W ∧ RelExactStartOn T W G A) ∧ ∀ (c' : ℕ) (G' : Fin b → Fin c' → S × X → ℂ)
        (W' : Set (S × X)), IsOpen W' → p ∈ W' → RelExactStartOn T W' G' A →
          FibreExactAt G' A p.1 p.2 := by
  constructor
  · rintro ⟨c, G, W, hW, hpW, hGA, hfib⟩
    refine ⟨⟨c, G, W, hW, hpW, hGA⟩, fun c' G' W' hW' hpW' hG'A => ?_⟩
    have hcol : ∀ k, ∃ Yk : Fin c' → S × X → ℂ, (∀ l, HolAt (Yk l) p) ∧
        ∀ j, ∀ᶠ q in 𝓝 p, q.1 ∈ T → G j k q = ∑ l, Yk l q * G' j l q := by
      intro k
      refine hG'A.exact p hpW' hpT (fun j => G j k)
        (fun j => holAt_of_differentiableOn hW (hGA.holG j k) hpW) fun i => ?_
      filter_upwards [hW.mem_nhds hpW] with q hq hqT
      rw [← hGA.comp i k q hq hqT]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    choose Y hY hYeq using hcol
    obtain ⟨s, y⟩ := p
    refine fibreExactAt_of_factor_rel T hpT (fun l k => Y k l) (fun l k => hY k l) ?_ hfib
    intro j k
    filter_upwards [hYeq k j] with q hq hqT
    rw [hq hqT]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  · rintro ⟨⟨c, G, W, hW, hpW, hGA⟩, h⟩
    exact ⟨c, G, W, hW, hpW, hGA, h c G W hW hpW hGA⟩

/-- **Openness of the relative flat locus**: the points of `T × X` at which `coker A` is flat over
`T` (Tor₁ form) form a relatively open subset of `T × X`. -/
theorem eventually_relFibreFlatAt [LocallyCompactSpace S] {𝒦 : Set (Set X)}
    (hTh1 : PrivilegedNbhdsProperty X 𝒦) (hA : RelationsTheoremA X 𝒦) (T : Set S) {a b : ℕ}
    (A : Fin a → Fin b → S × X → ℂ) {p₀ : S × X} (hp₀ : p₀.1 ∈ T) (h : RelFibreFlatAt T A p₀) :
    ∀ᶠ p in 𝓝 p₀, p.1 ∈ T → RelFibreFlatAt T A p := by
  obtain ⟨c, G, W, hW, hpW, hGA, hfib⟩ := h
  obtain ⟨s₀, x₀⟩ := p₀
  have hev := eventually_fibreExactAt_rel hTh1 hA T hp₀
    (fun j k => holAt_of_differentiableOn hW (hGA.holG j k) hpW)
    (fun i j => holAt_of_differentiableOn hW (hGA.holA i j) hpW)
    (fun i k => Filter.mem_of_superset (hW.mem_nhds hpW) fun q hq hqT => hGA.comp i k q hq hqT)
    hfib
  filter_upwards [hev, hW.mem_nhds hpW] with q hq hqW hqT
  exact ⟨c, G, W, hW, hqW, hGA, hq hqT⟩

end Relative

/-! ## The Scholie: privilege of `K` for the fibre is open along `T` -/

/-- **Douady §8 Scholie** (privilege of `K` for `𝓕(s)` is open in `s`), for a finite complex of free
modules on `V × U` (complex over `T`): if its fibre at `s₀ ∈ T` is direct exact over `B(K)` in degrees
`< m`, then for `s ∈ T` near `s₀` the fibre is direct exact over `B(K)` in degrees `< m` and (with
Theorem A) exact at every point of `K̊` in those degrees. -/
theorem eventually_privileged_fibre [LocallyCompactSpace S] {𝒦 : Set (Set X)}
    (hA : RelationsTheoremA X 𝒦) (T : Set S) {K U : Set X} (hK : K ∈ 𝒦) [CompactSpace K]
    (hU : IsOpen U) (hKU : K ⊆ U) {V : Set S} (hV : IsOpen V) {s₀ : S} (hs₀V : s₀ ∈ V)
    (hs₀T : s₀ ∈ T) {m : ℕ} {r : ℕ → ℕ} (d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → S × X → ℂ)
    (hd : ∀ k i j, DifferentiableOn ℂ (d k i j) (V ×ˢ U))
    (hcomp : ∀ k < m, ∀ q ∈ V ×ˢ U, q.1 ∈ T → ∀ i l, ∑ j, d k i j q * d (k + 1) j l q = 0)
    (h₀ : ∀ k < m, DirectExact (fun j l => fibRestrict K hKU (d (k + 1) j l) (hd (k + 1) j l) s₀)
      (fun i j => fibRestrict K hKU (d k i j) (hd k i j) s₀)) :
    ∀ᶠ s in 𝓝 s₀, s ∈ T → (∀ k < m, DirectExact
      (fun j l => fibRestrict K hKU (d (k + 1) j l) (hd (k + 1) j l) s)
      (fun i j => fibRestrict K hKU (d k i j) (hd k i j) s)) ∧
      ∀ k < m, ∀ y ∈ interior K, FibreExactAt (d (k + 1)) (d k) s y := by
  have hk : ∀ k < m, ∀ᶠ s in 𝓝 s₀, s ∈ T → s ∈ V ∧ DirectExact
      (fun j l => fibRestrict K hKU (d (k + 1) j l) (hd (k + 1) j l) s)
      (fun i j => fibRestrict K hKU (d k i j) (hd k i j) s) := by
    intro k hkm
    have hc : ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ i l, ∑ j, fibRestrict K hKU (d k i j) (hd k i j) s *
        fibRestrict K hKU (d (k + 1) j l) (hd (k + 1) j l) s = 0 := by
      filter_upwards [hV.mem_nhds hs₀V] with s hs hsT i l
      apply Subtype.ext
      apply ContinuousMap.ext
      intro z
      have h := hcomp k hkm (s, z) ⟨hs, hKU z.2⟩ hsT i l
      simp only [(fun f hf => fibRestrict_of_mem K hKU f hf hs),
        AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, ContinuousMap.coe_sum,
        Finset.sum_apply, ContinuousMap.mul_apply, HironakaG10FlatPolydiscAlgebra.restrict_apply,
        ZeroMemClass.coe_zero, ContinuousMap.zero_apply]
      exact h
    have hpers := directExact_eventually_rel T hs₀T
      (continuousAt_pi.2 fun j => continuousAt_pi.2 fun l =>
        continuousAt_fibRestrict K hKU hV (d (k + 1) j l) (hd (k + 1) j l) hs₀V)
      (continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
        continuousAt_fibRestrict K hKU hV (d k i j) (hd k i j) hs₀V) hc (h₀ k hkm)
    filter_upwards [hpers, hV.mem_nhds hs₀V] with s hs hsV hsT
    exact ⟨hsV, hs hsT⟩
  have hall : ∀ᶠ s in 𝓝 s₀, ∀ k ∈ Finset.range m, s ∈ T → s ∈ V ∧ DirectExact
      (fun j l => fibRestrict K hKU (d (k + 1) j l) (hd (k + 1) j l) s)
      (fun i j => fibRestrict K hKU (d k i j) (hd k i j) s) :=
    (Filter.eventually_all_finset _).2 fun k hk' => hk k (Finset.mem_range.1 hk')
  filter_upwards [hall, hV.mem_nhds hs₀V] with s hs hsV hsT
  refine ⟨fun k hkm => (hs k (Finset.mem_range.2 hkm) hsT).2, fun k hkm y hy a' ha' => ?_⟩
  have hDE := (hs k (Finset.mem_range.2 hkm) hsT).2
  have hFeq := fibRestrict_eq_restrictMatrix K hKU (d k) (hd k) hsV
  have hGeq := fibRestrict_eq_restrictMatrix K hKU (d (k + 1)) (hd (k + 1)) hsV
  have hDE' : DirectExact (restrictMatrix K hKU (fib (d (k + 1)) s)
      (fun j l => differentiableOn_fib (hd (k + 1) j l) hsV))
      (restrictMatrix K hKU (fib (d k) s) (fun i j => differentiableOn_fib (hd k i j) hsV)) := by
    rw [← hFeq, ← hGeq]
    exact hDE
  exact exactAt_of_theoremA hA hK hU hKU (fun i j => differentiableOn_fib (hd k i j) hsV)
    (fun j l => differentiableOn_fib (hd (k + 1) j l) hsV) hDE'.exact hy a' ha'

end
end Hironaka.HironakaG10LocRelative
