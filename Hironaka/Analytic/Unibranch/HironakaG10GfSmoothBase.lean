import Hironaka.Analytic.Unibranch.HironakaG10GfVertical

/-!
# Generic flatness over a smooth base, II: the induction (lane G10GF, run 0081, plan item G10-03-05.c1)

Frisch 1967, Prop. (IV,14) (`references/frisch67-points-platitude`, p. 135), over a SMOOTH parameter space and
at chart level: for a finite holomorphic matrix `F` on an open `U ⊆ S × ℂⁿ` (`S` a finite-dimensional complex
normed space, the parameter space) and a compact `K ⊆ ℂⁿ`, every nonempty open `V ⊆ S` with `V × K ⊆ U` contains
a parameter `s` over which `coker F` is flat at every point of `{s} × K`
(**`exists_forall_fibreFlatAt`**, Tor₁ form `HironakaG10LocFibreOpen.FibreFlatAt`).

Proof by induction on `dim S`.  `dim S = 0`: an exact start (Oka) has exact fibres
(`fibreFlatAt_of_subsingleton`).  `dim S = k + 1`: write `S ≅ ℂ × ℂᵏ` and view `F` as a one-parameter family
`F'` on `ℂ × ℂ^{k+n}`; vertical avoidance (`HironakaG10GfVertical.eventually_forall_regularAt_sub`) gives a
parameter value `w` at which `t − w` is regular on `coker F'` along a compact neighbourhood of the relevant part
of the slice; the slice of an exact start is then an exact start of the slice family `F(σ(w,·),·)` over `ℂᵏ`
(`HironakaG10GfVertical.exactStartOn_slice_at`), the induction hypothesis gives `s'`, and the fibre of the
slice start at `s'` IS the fibre of the original start at `σ(w,s')` (start independence,
`HironakaG10LocFibreOpen.fibreFlatAt_iff_forall`).

No named input.  Blueprint: `hironaka-g10gf-smooth-base.tex`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GfSmoothBase

noncomputable section

open Hironaka OkaRelationSheaf HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10LocFibreOpen HironakaG10LocSheafExact

/-- **Over a point every exact start has exact fibres**: flatness over a zero-dimensional parameter space. -/
theorem fibreFlatAt_of_subsingleton {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
    [Subsingleton S] {n a b : ℕ} (F : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ) (s : S)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ∀ i j, HolAt (F i j) (s, z)) : FibreFlatAt F (s, z) := by
  have hF₀ : ∀ i j, HolAt (fib F s i j) z := fun i j =>
    (hF i j).comp (f := F i j) (φ := fun x => (s, x)) (continuous_const.prodMk continuous_id)
      (fun _ => (differentiableAt_const s).prodMk differentiableAt_id)
  obtain ⟨O, hO, hzO, c, G₀, hstart⟩ :=
    exists_exactStartOn (OkaCoherence.okaProperty_euclidean n) (fib F s) z hF₀
  let e : S × EuclideanSpace ℂ (Fin n) ≃ₜ EuclideanSpace ℂ (Fin n) :=
    { toFun := Prod.snd
      invFun := fun x => (s, x)
      left_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_snd
      continuous_invFun := continuous_const.prodMk continuous_id }
  have h1 := exactStartOn_comp_homeomorph e (fun _ => differentiableAt_snd)
    (fun _ => (differentiableAt_const s).prodMk differentiableAt_id) hstart
  have eF : (fun i j => fib F s i j ∘ e) = F := by
    funext i j p
    change F i j (s, p.2) = F i j p
    rw [show (s, p.2) = p from Prod.ext (Subsingleton.elim _ _) rfl]
  rw [eF] at h1
  exact ⟨c, fun j k => G₀ j k ∘ e, e ⁻¹' O, hO.preimage e.continuous, hzO, h1,
    fun a ha => hstart.exact z hzO a ha⟩

/-- The tube of a product: points of `ball p r` in a product of metric spaces. -/
theorem mem_ball_prod {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] {p : α × β} {r : ℝ}
    {x : α} {y : β} (hx : dist x p.1 < r) (hy : dist y p.2 < r) : (x, y) ∈ Metric.ball p r := by
  rw [Metric.mem_ball, Prod.dist_eq]
  exact max_lt hx hy

/-- **Generic flatness over a smooth parameter space (chart level, Tor₁ form).** -/
theorem exists_forall_fibreFlatAt (n : ℕ) : ∀ (k : ℕ) (S : Type) [NormedAddCommGroup S]
    [NormedSpace ℂ S] [FiniteDimensional ℂ S], Module.finrank ℂ S = k →
    ∀ {a b : ℕ} (F : Fin a → Fin b → S × EuclideanSpace ℂ (Fin n) → ℂ)
      {U : Set (S × EuclideanSpace ℂ (Fin n))}, IsOpen U → (∀ i j, DifferentiableOn ℂ (F i j) U) →
      ∀ {V : Set S} {K : Set (EuclideanSpace ℂ (Fin n))}, IsOpen V → V.Nonempty → IsCompact K →
        V ×ˢ K ⊆ U → ∃ s ∈ V, ∀ z ∈ K, FibreFlatAt F (s, z)
  | 0, S, _, _, _, hk, a, b, F, U, hU, hF, V, K, _, hVne, _, hVK => by
      have hS : Subsingleton S :=
        ⟨fun x y => ((finrank_zero_iff_forall_zero.1 hk x).trans
          (finrank_zero_iff_forall_zero.1 hk y).symm)⟩
      obtain ⟨s, hs⟩ := hVne
      exact ⟨s, hs, fun z hz => fibreFlatAt_of_subsingleton F s z fun i j =>
        holAt_of_differentiableOn hU (hF i j) (hVK ⟨hs, hz⟩)⟩
  | k + 1, S, _, _, _, hk, a, b, F, U, hU, hF, V, K, hV, hVne, hK, hVK => by
      -- coordinates `S ≅ ℂ × ℂᵏ` and `ℂ^{k+n} ≅ ℂᵏ × ℂⁿ`
      have hr1 : Module.finrank ℂ (ℂ × EuclideanSpace ℂ (Fin k)) = Module.finrank ℂ S := by
        rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hk, add_comm]
      let σ : (ℂ × EuclideanSpace ℂ (Fin k)) ≃L[ℂ] S := ContinuousLinearEquiv.ofFinrankEq hr1
      have hr2 : Module.finrank ℂ (EuclideanSpace ℂ (Fin (k + n))) =
          Module.finrank ℂ (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin n)) := by
        rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
          finrank_euclideanSpace_fin]
      let τ : EuclideanSpace ℂ (Fin (k + n)) ≃L[ℂ]
          EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin n) := ContinuousLinearEquiv.ofFinrankEq hr2
      let Θ : (ℂ × EuclideanSpace ℂ (Fin (k + n))) ≃L[ℂ] S × EuclideanSpace ℂ (Fin n) :=
        ((ContinuousLinearEquiv.refl ℂ ℂ).prodCongr τ).trans
          ((ContinuousLinearEquiv.prodAssoc ℂ ℂ (EuclideanSpace ℂ (Fin k))
            (EuclideanSpace ℂ (Fin n))).symm.trans
            (σ.prodCongr (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin n)))))
      have hΘ : ∀ p : ℂ × EuclideanSpace ℂ (Fin (k + n)), Θ p = (σ (p.1, (τ p.2).1), (τ p.2).2) := by
        intro p
        rfl
      have hΘsymm : ∀ (w : ℂ) (q : EuclideanSpace ℂ (Fin k)) (x : EuclideanSpace ℂ (Fin n)),
          Θ.symm (σ (w, q), x) = (w, τ.symm (q, x)) := by
        intro w q x
        rw [ContinuousLinearEquiv.symm_apply_eq, hΘ]
        simp
      -- a box around a point of `V`
      obtain ⟨s₀, hs₀⟩ := hVne
      have hσV : IsOpen (σ ⁻¹' V) := hV.preimage σ.continuous
      have hp₀ : σ.symm s₀ ∈ σ ⁻¹' V := by
        show σ (σ.symm s₀) ∈ V
        rw [ContinuousLinearEquiv.apply_symm_apply]
        exact hs₀
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hσV _ hp₀
      set w₀ : ℂ := (σ.symm s₀).1 with hw₀
      set s₀' : EuclideanSpace ℂ (Fin k) := (σ.symm s₀).2 with hs₀'
      have hbox : ∀ w x, dist w w₀ < r → dist x s₀' < r → σ (w, x) ∈ V := fun w x hw hx =>
        hball (mem_ball_prod hw hx)
      -- the one-parameter family
      let F' : Fin a → Fin b → ℂ × EuclideanSpace ℂ (Fin (k + n)) → ℂ := fun i j => F i j ∘ Θ
      have hU' : IsOpen (Θ ⁻¹' U) := hU.preimage Θ.continuous
      have hF' : ∀ i j, DifferentiableOn ℂ (F' i j) (Θ ⁻¹' U) := fun i j =>
        (hF i j).comp Θ.differentiableOn fun _ hx => hx
      -- the compact part of the slice that matters, and a compact neighbourhood of it
      let C : Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin n)) :=
        Metric.closedBall s₀' (r / 2) ×ˢ K
      have hC : IsCompact C := (isCompact_closedBall _ _).prod hK
      have hL₀ : IsCompact (τ ⁻¹' C) := τ.toHomeomorph.isCompact_preimage.2 hC
      have hO₀ : IsOpen {u : EuclideanSpace ℂ (Fin (k + n)) | (w₀, u) ∈ Θ ⁻¹' U} :=
        hU'.preimage (continuous_const.prodMk continuous_id)
      have hL₀U : τ ⁻¹' C ⊆ {u | (w₀, u) ∈ Θ ⁻¹' U} := by
        intro u hu
        obtain ⟨h1, h2⟩ := hu
        show Θ (w₀, u) ∈ U
        rw [hΘ]
        refine hVK ⟨hbox _ _ (by simp [hr]) ?_, h2⟩
        exact lt_of_le_of_lt (Metric.mem_closedBall.1 h1) (half_lt_self hr)
      obtain ⟨L, hL, hL₀L, hLU⟩ := exists_compact_between hL₀ hO₀ hL₀U
      have hholL : ∀ u ∈ L, ∀ i j, HolAt (F' i j) (w₀, u) := fun u hu i j =>
        holAt_of_differentiableOn hU' (hF' i j) (hLU hu)
      -- a good parameter value `w ≠ w₀` near `w₀`
      have hVA := HironakaG10GfVertical.eventually_forall_regularAt_sub F' hL hholL
      have htube : ∀ᶠ w in 𝓝 w₀, ∀ u ∈ L, (w, u) ∈ Θ ⁻¹' U :=
        HironakaG10LocEuclideanCartan.eventually_forall_mem_of_isOpen hL hU' fun u hu => hLU hu
      have hballw : ∀ᶠ w in 𝓝 w₀, dist w w₀ < r := Metric.ball_mem_nhds w₀ hr
      obtain ⟨w, ⟨hwVA, hwtube, hwball⟩, hwne⟩ :=
        (((hVA.and (htube.and hballw)).filter_mono nhdsWithin_le_nhds).and
          (self_mem_nhdsWithin : {w₀}ᶜ ∈ 𝓝[≠] w₀)).exists
      have hwne' : w ≠ w₀ := hwne
      -- the slice family over `ℂᵏ`
      let Fw : Fin a → Fin b → EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin n) → ℂ :=
        fun i j q => F i j (σ (w, q.1), q.2)
      let Ψ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin n) → S × EuclideanSpace ℂ (Fin n) :=
        fun q => (σ (w, q.1), q.2)
      have hΨc : Continuous Ψ :=
        (σ.continuous.comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd
      have hΨd : ∀ q, DifferentiableAt ℂ Ψ q := fun q =>
        (σ.differentiableAt.comp q ((differentiableAt_const w).prodMk differentiableAt_fst)).prodMk
          differentiableAt_snd
      have hUw : IsOpen (Ψ ⁻¹' U) := hU.preimage hΨc
      have hFw : ∀ i j, DifferentiableOn ℂ (Fw i j) (Ψ ⁻¹' U) := fun i j =>
        (hF i j).comp (fun q _ => (hΨd q).differentiableWithinAt) fun _ hq => hq
      have hV'K : Metric.ball s₀' (r / 2) ×ˢ K ⊆ Ψ ⁻¹' U := by
        rintro ⟨x, z⟩ ⟨hx, hz⟩
        exact hVK ⟨hbox _ _ hwball (lt_trans (Metric.mem_ball.1 hx) (half_lt_self hr)), hz⟩
      obtain ⟨s', hs', hflat⟩ := exists_forall_fibreFlatAt n k (EuclideanSpace ℂ (Fin k))
        finrank_euclideanSpace_fin Fw hUw hFw Metric.isOpen_ball
        ⟨s₀', Metric.mem_ball_self (half_pos hr)⟩ hK hV'K
      refine ⟨σ (w, s'), hbox _ _ hwball (lt_trans (Metric.mem_ball.1 hs') (half_lt_self hr)),
        fun z hz => ?_⟩
      -- the point of the one-parameter family over `(σ (w, s'), z)`
      have hτu : τ (τ.symm (s', z)) = (s', z) := τ.apply_symm_apply _
      have huL : τ.symm (s', z) ∈ interior L := by
        apply hL₀L
        show τ (τ.symm (s', z)) ∈ C
        rw [hτu]
        exact ⟨Metric.ball_subset_closedBall hs', hz⟩
      have hwu : (w, τ.symm (s', z)) ∈ Θ ⁻¹' U := hwtube _ (interior_subset huL)
      obtain ⟨U₁, hU₁, hwu₁, c, G', hstart⟩ :=
        exists_exactStartOn (HironakaG10FlatRelationLift.okaProperty_prod_euclidean (k + n)) F'
          (w, τ.symm (s', z)) fun i j => holAt_of_differentiableOn hU' (hF' i j) hwu
      have hU₂ : IsOpen (U₁ ∩ univ ×ˢ interior L) := hU₁.inter (isOpen_univ.prod isOpen_interior)
      have hstart₂ : ExactStartOn (U₁ ∩ univ ×ˢ interior L) G' F' := hstart.mono inter_subset_left
      -- slice at `w`, transported to `ℂᵏ × ℂⁿ`
      have hslice := HironakaG10GfVertical.exactStartOn_slice_at hstart₂ hU₂ w
        fun u hu => hwVA hwne' u (interior_subset hu.2.2)
      have h2 := exactStartOn_comp_homeomorph τ.symm.toHomeomorph
        (fun _ => τ.symm.differentiableAt) (fun _ => τ.symm.symm.differentiableAt) hslice
      have eFw : (fun i j => (fun u => F' i j (w, u)) ∘ τ.symm.toHomeomorph) = Fw := by
        funext i j q
        change F i j (Θ (w, τ.symm q)) = F i j (σ (w, q.1), q.2)
        rw [hΘ]
        simp
      rw [eFw] at h2
      have hO : IsOpen (τ.symm.toHomeomorph ⁻¹' {u | (w, u) ∈ U₁ ∩ univ ×ˢ interior L}) :=
        (hU₂.preimage (continuous_const.prodMk continuous_id)).preimage τ.symm.continuous
      have hq : (s', z) ∈ τ.symm.toHomeomorph ⁻¹' {u | (w, u) ∈ U₁ ∩ univ ×ˢ interior L} :=
        ⟨hwu₁, mem_univ _, huL⟩
      have hfib := (fibreFlatAt_iff_forall.1 (hflat z hz)).2 c _ _ hO hq h2
      -- the original start, pulled back to `S × ℂⁿ`
      have h3 := exactStartOn_comp_homeomorph Θ.symm.toHomeomorph
        (fun _ => Θ.symm.differentiableAt) (fun _ => Θ.symm.symm.differentiableAt) hstart
      have eF : (fun i j => F' i j ∘ Θ.symm.toHomeomorph) = F := by
        funext i j p
        change F i j (Θ (Θ.symm p)) = F i j p
        rw [ContinuousLinearEquiv.apply_symm_apply]
      rw [eF] at h3
      refine ⟨c, fun j k => G' j k ∘ Θ.symm.toHomeomorph, Θ.symm.toHomeomorph ⁻¹' U₁,
        hU₁.preimage Θ.symm.continuous, ?_, h3, ?_⟩
      · show Θ.symm (σ (w, s'), z) ∈ U₁
        rw [hΘsymm]
        exact hwu₁
      · have efib : fib (fun j k => G' j k ∘ Θ.symm.toHomeomorph) (σ (w, s')) =
            fib (fun j k => (fun u => G' j k (w, u)) ∘ τ.symm.toHomeomorph) s' := by
          funext j k x
          change G' j k (Θ.symm (σ (w, s'), x)) = G' j k (w, τ.symm (s', x))
          rw [hΘsymm]
        intro v hv
        have := hfib v hv
        rw [← efib] at this
        exact this

end

end Hironaka.Analytic.Unibranch.HironakaG10GfSmoothBase
