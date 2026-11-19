import Hironaka.Resolution.HironakaG10LocRelative
import Hironaka.Resolution.HironakaG10LocJointHol

/-! # Douady §8 Prop. 2 (a) for free starts: fibre exactness at a point gives exactness over `T × X`

Douady 1966, §8 n° 3, Prop. 2, part (a) ("exactitude au point `(s,x)`"), for free sheaves and over a
parameter SET `T ⊆ S` (`S`, `X` finite dimensional): if `F G = 0` on `T × X` near `(s₀, x₀)`,
`s₀ ∈ T`, and the fibre start `(G(s₀,·), F(s₀,·))` is exact at `x₀`, then `(G, F)` is exact over
`T × X` at `(s₀, x₀)` (`RelExactAt`): every germ `a` at `(s₀,x₀)` with `a F = 0` on `T × X` is, on
`T × X`, a germ combination of the columns of `G` (**`relExactAt_of_fibreExactAt`**).

Proof (Douady's "passage à la limite inductive", made explicit): Th. 1 gives a privileged `K` with
`(G(s₀,·)|_K, F(s₀,·)|_K)` direct exact; the right inverse `R(s) = R₀ P A(s)⁻¹ P` of the persistence
construction (`rinv`, `rinv_spec`, `HironakaG10LocDirectPersistence`) depends holomorphically on `s`
(`differentiableAt_rinv`); `c(s) = R(s) (a(s,·)|_K)` is a holomorphic `B(K)`-valued map
(`differentiableAt_fibRestrict`) with `G(s,·) c(s) = a(s,·)` on `K` for `s ∈ T`, and
`(s, x) ↦ c(s)(x)` is holomorphic on a neighbourhood of `(s₀, x₀)` (`differentiableAt_bkEval_comp`).
No Theorem A is used; only Th. 1 (`hTh1`).
BP: hironaka-g10-loc-product-exact.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10LocProductExact
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10LocDirectPersistence HironakaG10LocSheafExact
  HironakaG10LocFibreOpen HironakaG10LocRelative HironakaG10LocJointHol

/-! ## The explicit right inverse of the persistence construction -/

section Abstract
variable {E₂ E₁ E₀ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₁]
  [NormedSpace ℂ E₁] [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]

/-- The right inverse `R(g) = R₀ P A(g)⁻¹ P` of `g` on `ker f`. -/
def rinv (P : E₁ →L[ℂ] E₁) (R₀ : E₁ →L[ℂ] E₂) (g : E₂ →L[ℂ] E₁) : E₁ →L[ℂ] E₂ :=
  R₀.comp (P.comp ((opA P R₀ g).inverse.comp P))

variable {g₀ : E₂ →L[ℂ] E₁} {f₀ : E₁ →L[ℂ] E₀} {R₀ : E₁ →L[ℂ] E₂} {S₀ : E₀ →L[ℂ] E₁}

/-- **`R(g)` is a right inverse of `g` on `ker f`** wherever `A(g)`, `B(f)` are invertible and
`f g = 0`. -/
theorem rinv_spec (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e) {g : E₂ →L[ℂ] E₁} {f : E₁ →L[ℂ] E₀}
    (hc : ∀ e, f (g e) = 0) (hA : (opA (g₀.comp R₀) R₀ g).IsInvertible)
    (hB : (opB (g₀.comp R₀) S₀ f).IsInvertible) :
    ∀ x, f x = 0 → g (rinv (g₀.comp R₀) R₀ g x) = x := by
  set P : E₁ →L[ℂ] E₁ := g₀.comp R₀ with hPdef
  have hPP : ∀ x, P (P x) = P x := fun x => projP_idem hR₀ x
  have hinj : ∀ x, f x = 0 → P x = 0 → x = 0 := by
    intro x hfx hPx
    apply hB.injective
    rw [opB_apply, hfx, map_zero, map_zero, sub_zero, hPx, add_zero, map_zero]
  set A := opA P R₀ g with hAdef
  have hAP : ∀ x, A (P x) = P (A x) := by
    intro x
    simp only [hAdef, opA_apply, map_add, map_sub, hPP, sub_self, add_zero]
  have hAiP : ∀ y, A.inverse (P y) = P (A.inverse y) := by
    intro y
    apply hA.injective
    rw [hA.self_apply_inverse, hAP, hA.self_apply_inverse]
  have hPgR : ∀ x, P (g (rinv P R₀ g x)) = P x := by
    intro x
    set z := A.inverse (P x) with hz
    have hzP : P z = z := by rw [hz, ← hAiP, hPP]
    have hAz : A z = P x := hA.self_apply_inverse _
    have hRx : rinv P R₀ g x = R₀ (P z) := by
      show R₀ (P (A.inverse (P x))) = R₀ (P z)
      rw [← hz]
    rw [hRx, ← hAz, hAdef, opA_apply, hzP, sub_self, add_zero]
  intro x hx
  have h1 : f (g (rinv P R₀ g x) - x) = 0 := by rw [map_sub, hc, hx, sub_self]
  have h2 : P (g (rinv P R₀ g x) - x) = 0 := by rw [map_sub, hPgR, sub_self]
  exact sub_eq_zero.mp (hinj _ h1 h2)

/-- **The right inverse depends holomorphically on `g`.** -/
theorem differentiableAt_rinv [CompleteSpace E₁] {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] {g : Y → E₂ →L[ℂ] E₁} {s : Y} (P : E₁ →L[ℂ] E₁) (R₀ : E₁ →L[ℂ] E₂)
    (hg : DifferentiableAt ℂ g s) (hA : (opA P R₀ (g s)).IsInvertible) :
    DifferentiableAt ℂ (fun t => rinv P R₀ (g t)) s := by
  have hAd : DifferentiableAt ℂ (fun t => opA P R₀ (g t)) s :=
    ((differentiableAt_const _).clm_comp (hg.clm_comp (differentiableAt_const _))).add
      (differentiableAt_const _)
  have hI : DifferentiableAt ℂ (ContinuousLinearMap.inverse ∘ fun t => opA P R₀ (g t)) s :=
    DifferentiableAt.comp (g := ContinuousLinearMap.inverse) s
      ((hA.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero) hAd
  exact (differentiableAt_const _).clm_comp ((differentiableAt_const _).clm_comp
    (hI.clm_comp (differentiableAt_const _)))

end Abstract

/-! ## A holomorphic right inverse along a parameter set (matrix form) -/

section MatrixFamily
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **A holomorphic family of right inverses**: matrices `g(s)` holomorphic near `s₀`, `f(s)`
continuous at `s₀`, `f g = 0` over `T` near `s₀`, `(g(s₀), f(s₀))` direct exact. Then there is a
family `R(s)` of bounded operators, holomorphic near `s₀`, with `g(s) R(s) x = x` for every
`x ∈ ker f(s)`, `s ∈ T` near `s₀`. -/
theorem exists_rightInverse_hol {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] (T : Set Y)
    {g : Y → ι₁ → ι₂ → R} {f : Y → ι₀ → ι₁ → R} {s₀ : Y}
    (hg : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ g s) (hf : ContinuousAt f s₀)
    (hcomp : ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ i k, ∑ j, f s i j * g s j k = 0)
    (h₀ : DirectExact (g s₀) (f s₀)) :
    ∃ Rf : Y → (ι₁ → R) →L[ℂ] (ι₂ → R), (∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ Rf s) ∧
      ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ x, matrixOperator (f s) x = 0 → matrixOperator (g s) (Rf s x) = x := by
  obtain ⟨S₀, hS₀⟩ := h₀.exists_generalizedInverse_f
  obtain ⟨R₀, hR₀⟩ := h₀.exists_generalizedInverse_g
  set P := (matrixOperator (g s₀)).comp R₀ with hP
  have hgo : ∀ s, DifferentiableAt ℂ g s →
      DifferentiableAt ℂ (fun t => matrixOperator (g t)) s := fun s hs =>
    differentiableAt_matrixOperator fun i j => differentiableAt_pi.1 (differentiableAt_pi.1 hs i) j
  have hgc : ContinuousAt (fun s => matrixOperator (g s)) s₀ := (hgo s₀ hg.self_of_nhds).continuousAt
  have hfc : ContinuousAt (fun s => matrixOperator (f s)) s₀ :=
    (matrixOperatorCLM (R := R) (p := ι₁) (q := ι₀)).continuous.continuousAt.comp hf
  have hAc : ContinuousAt (fun s => opA P R₀ (matrixOperator (g s))) s₀ :=
    (continuousAt_const.clm_comp (hgc.clm_comp continuousAt_const)).add continuousAt_const
  have hBc : ContinuousAt (fun s => opB P S₀ (matrixOperator (f s))) s₀ :=
    (continuousAt_const.clm_comp (continuousAt_const.clm_comp hfc)).add continuousAt_const
  have hA : ∀ᶠ s in 𝓝 s₀, (opA P R₀ (matrixOperator (g s))).IsInvertible :=
    hAc (show {L : (ι₁ → R) →L[ℂ] (ι₁ → R) | L.IsInvertible} ∈
      𝓝 (opA P R₀ (matrixOperator (g s₀))) by
        rw [hP, opA_self hR₀]; exact isInvertible_mem_nhds_id)
  have hB : ∀ᶠ s in 𝓝 s₀, (opB P S₀ (matrixOperator (f s))).IsInvertible :=
    hBc (show {L : (ι₁ → R) →L[ℂ] (ι₁ → R) | L.IsInvertible} ∈
      𝓝 (opB P S₀ (matrixOperator (f s₀))) by
        rw [hP, opB_self hR₀ hS₀ h₀.exact]; exact isInvertible_mem_nhds_id)
  refine ⟨fun s => rinv P R₀ (matrixOperator (g s)), ?_, ?_⟩
  · filter_upwards [hg, hA] with s hs hsA
    exact differentiableAt_rinv P R₀ (hgo s hs) hsA
  · filter_upwards [hA, hB, hcomp] with s hsA hsB hsc hsT
    exact rinv_spec hR₀ (matrixOperator_comp_apply (g s) (f s) (hsc hsT)) hsA hsB

end MatrixFamily

/-! ## Prop. 2 (a) -/

variable {S X : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [NormedAddCommGroup X]
  [NormedSpace ℂ X]

/-- **Douady §8 Prop. 2 (a) for free starts, over a parameter set `T`**: fibre exactness at
`(s₀, x₀)` gives exactness over `T × X` at `(s₀, x₀)`. -/
theorem relExactAt_of_fibreExactAt [FiniteDimensional ℂ S] [FiniteDimensional ℂ X]
    {𝒦 : Set (Set X)} (hTh1 : PrivilegedNbhdsProperty X 𝒦) (T : Set S) {a b c : ℕ}
    {G : Fin b → Fin c → S × X → ℂ} {F : Fin a → Fin b → S × X → ℂ} {s₀ : S} {x₀ : X}
    (hs₀T : s₀ ∈ T) (hG : ∀ j k, HolAt (G j k) (s₀, x₀)) (hF : ∀ i j, HolAt (F i j) (s₀, x₀))
    (hFG : ∀ i k, ∀ᶠ p in 𝓝 (s₀, x₀), p.1 ∈ T → ∑ j, F i j p * G j k p = 0)
    (hex : FibreExactAt G F s₀ x₀) : RelExactAt T G F (s₀, x₀) := by
  classical
  intro av hav havF
  have hev : ∀ᶠ p in 𝓝 (s₀, x₀), (∀ j k, DifferentiableAt ℂ (G j k) p) ∧
      (∀ i j, DifferentiableAt ℂ (F i j) p) ∧ (∀ j, DifferentiableAt ℂ (av j) p) ∧
      (∀ i k, p.1 ∈ T → ∑ j, F i j p * G j k p = 0) ∧
      ∀ i, p.1 ∈ T → ∑ j, av j p * F i j p = 0 :=
    (eventually_all.2 fun j => eventually_all.2 fun k => hG j k).and
      ((eventually_all.2 fun i => eventually_all.2 fun j => hF i j).and
        ((eventually_all.2 fun j => hav j).and
          ((eventually_all.2 fun i => eventually_all.2 fun k => hFG i k).and
            (eventually_all.2 fun i => havF i))))
  obtain ⟨V₀, U₀, hV₀, hs₀V₀, hU₀, hx₀U₀, hVU⟩ := mem_nhds_prod_iff'.1 hev
  have hGd : ∀ j k, DifferentiableOn ℂ (G j k) (V₀ ×ˢ U₀) := fun j k p hp =>
    ((hVU hp).1 j k).differentiableWithinAt
  have hFd : ∀ i j, DifferentiableOn ℂ (F i j) (V₀ ×ˢ U₀) := fun i j p hp =>
    ((hVU hp).2.1 i j).differentiableWithinAt
  have had : ∀ j, DifferentiableOn ℂ (av j) (V₀ ×ˢ U₀) := fun j p hp =>
    ((hVU hp).2.2.1 j).differentiableWithinAt
  have hFGd : ∀ p ∈ V₀ ×ˢ U₀, p.1 ∈ T → ∀ i k, ∑ j, F i j p * G j k p = 0 :=
    fun p hp hpT i k => (hVU hp).2.2.2.1 i k hpT
  have haFd : ∀ p ∈ V₀ ×ˢ U₀, p.1 ∈ T → ∀ i, ∑ j, av j p * F i j p = 0 :=
    fun p hp hpT i => (hVU hp).2.2.2.2 i hpT
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
  have hcompAt : ∀ s ∈ V₀, s ∈ T → ∀ i k, ∑ j, Fs s i j * Gs s j k = 0 := by
    intro s hs hsT i k
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    have h := hFGd (s, z) ⟨hs, hKU₀ z.2⟩ hsT i k
    simp only [hGs, hFs, (fun f hf => fibRestrict_of_mem K hKU₀ f hf hs),
      AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.mul_apply, HironakaG10FlatPolydiscAlgebra.restrict_apply, ZeroMemClass.coe_zero,
      ContinuousMap.zero_apply]
    exact h
  have hcomp : ∀ᶠ s in 𝓝 s₀, s ∈ T → ∀ i k, ∑ j, Fs s i j * Gs s j k = 0 := by
    filter_upwards [hV₀.mem_nhds hs₀V₀] with s hs hsT
    exact hcompAt s hs hsT
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
  -- the explicit holomorphic right inverse
  have hGd' : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ Gs s := by
    filter_upwards [hV₀.mem_nhds hs₀V₀] with s hs
    exact differentiableAt_pi.2 fun j => differentiableAt_pi.2 fun k =>
      differentiableAt_fibRestrict K hU₀ hKU₀ hV₀ (G j k) (hGd j k) hs
  obtain ⟨Rf, hRfd, hRf⟩ := exists_rightInverse_hol T hGd' hFc hcomp h₀''
  obtain ⟨v, hv⟩ : ∃ v : S → Fin b → holSubalgebra K,
      v = fun s j => fibRestrict K hKU₀ (av j) (had j) s := ⟨_, rfl⟩
  have hvd : ∀ s ∈ V₀, DifferentiableAt ℂ v s := by
    intro s hs
    rw [hv]
    exact differentiableAt_pi.2 fun j =>
      differentiableAt_fibRestrict K hU₀ hKU₀ hV₀ (av j) (had j) hs
  have hfv : ∀ s ∈ V₀, s ∈ T → matrixOperator (Fs s) (v s) = 0 := by
    intro s hs hsT
    funext i
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    rw [eval_matrixOperator (ι := Fin b)]
    have h := haFd (s, z) ⟨hs, hKU₀ z.2⟩ hsT i
    rw [hv]
    simp only [hFs, (fun f hf => fibRestrict_of_mem K hKU₀ f hf hs),
      HironakaG10FlatPolydiscAlgebra.restrict_apply, Pi.zero_apply, ZeroMemClass.coe_zero,
      ContinuousMap.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hEv : ∀ᶠ s in 𝓝 s₀, s ∈ V₀ ∧ DifferentiableAt ℂ Rf s ∧
      (s ∈ T → ∀ x, matrixOperator (Fs s) x = 0 → matrixOperator (Gs s) (Rf s x) = x) :=
    (show ∀ᶠ s in 𝓝 s₀, s ∈ V₀ from hV₀.mem_nhds hs₀V₀).and (hRfd.and hRf)
  -- the coefficients
  refine ⟨fun k q => extendZero K ((Rf q.1 (v q.1) k : holSubalgebra K) : C(K, ℂ)) q.2,
    fun k => ?_, fun j => ?_⟩
  · filter_upwards [hEv.prod_nhds (interior_mem_nhds.2 hKx₀)] with q hq
    obtain ⟨⟨hq1, hqd, -⟩, hq2⟩ := hq
    exact differentiableAt_bkEval_comp (c := fun s => Rf s (v s) k)
      (differentiableAt_pi.1 (hqd.clm_apply (hvd q.1 hq1)) k) hq2
  · filter_upwards [hEv.prod_nhds (interior_mem_nhds.2 hKx₀)] with q hq hqT
    obtain ⟨⟨hq1, -, hqR⟩, hq2⟩ := hq
    have hqK : q.2 ∈ K := interior_subset hq2
    have h := congrArg (fun w : holSubalgebra K => (w : C(K, ℂ)) ⟨q.2, hqK⟩)
      (congrFun (hqR hqT (v q.1) (hfv q.1 hq1 hqT)) j)
    rw [eval_matrixOperator (ι := Fin c)] at h
    have hvq : ((v q.1 j : holSubalgebra K) : C(K, ℂ)) ⟨q.2, hqK⟩ = av j q := by
      rw [hv]
      show ((fibRestrict K hKU₀ (av j) (had j) q.1 : holSubalgebra K) : C(K, ℂ)) ⟨q.2, hqK⟩ = av j q
      rw [fibRestrict_of_mem K hKU₀ _ _ hq1]
      rfl
    have hGq : ∀ l, ((Gs q.1 j l : holSubalgebra K) : C(K, ℂ)) ⟨q.2, hqK⟩ = G j l q := by
      intro l
      show ((fibRestrict K hKU₀ (G j l) (hGd j l) q.1 : holSubalgebra K) : C(K, ℂ)) ⟨q.2, hqK⟩ =
        G j l q
      rw [fibRestrict_of_mem K hKU₀ _ _ hq1]
      rfl
    rw [hvq] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hGq k, extendZero_of_mem K _ hqK, mul_comm]

end
end Hironaka.HironakaG10LocProductExact
