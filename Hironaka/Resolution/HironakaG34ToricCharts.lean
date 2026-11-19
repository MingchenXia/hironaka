import Hironaka.Resolution.HironakaG34EquivariantMonomialCharts
import Hironaka.Blowup.BlowupSNCTransform

/-!
# Toric charts: diagonal actions in flat coordinates, and their transfer through one blow-up (brick (d2))

Lane G34 (run 0080, round 11).  Blueprint: `hironaka-g34-resume-toric-charts.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §9.2 (d2), (d4).

`ActsDiagonallyNear F act μ Φ p`: the maps `act a` act near `p` diagonally in the flat coordinates `Φ ∘ e`, by the
scaling `μ a`, jointly for `a` eventually in the filter `F` and points near `p`.  This is the inductive invariant
of the toric induction along a lower tail (the maps being the lifts of the coordinate scalings of stage 0).

* `actsDiagonallyNear_scaleMap` (stage 0): the coordinate scalings of `HironakaG34CoordinateScaling` act diagonally
  near every point of the window, for `a` near `1`.
* **`exists_toric_chart_of_blowup`** (one blow-up): if the maps act diagonally near `π z` in a flattening of the
  centre, and lifted maps commute with `π` and are continuous near `z`, then there are a monomial index `j` and flat
  coordinates `Ψ` at `z` (the monomial local inverse `W`) with `σⱼ ∘ (Ψ ∘ e) = (Φ ∘ e) ∘ π` on the domain, in which the
  lifted maps act diagonally by `chartScale (μ a) k j` (scalings of `C` and of the pivot by `μ a`, of the other
  normal coordinates by ratios).  Proof: `HironakaG34EquivariantMonomialCharts.monomialLift_comm_of_diagonal` at
  `W(z')` for `(a, z')` near `(F, z)`, and `W ∘ ℓⱼ = id` near `W z` (inverse function theorem through
  `BlowupSNCTransform.exists_recentred_coords`).

## Main results

* `ActsDiagonallyNear`, `ActsDiagonallyNear.eventually`, `chartVec`, `tendsto_chartVec`;
* `actsDiagonallyNear_scaleMap`;
* **`exists_toric_chart_of_blowup`**.

New file; no existing statement changed; no sorry; no axiom.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34ToricCharts
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity
  HironakaNormalCrossingsDiagonalLiftOrbits HironakaG34CoordinateScaling HironakaG34EquivariantMonomialCharts

variable {n : ℕ}

/-! ### Filters -/

/-- A joint eventual property near `(F, z)` holds, eventually, near every nearby point. -/
theorem eventually_prod_nhds_eventually {A X : Type*} [TopologicalSpace X] {F : Filter A} {z : X}
    {P : A × X → Prop} (h : ∀ᶠ x in F ×ˢ 𝓝 z, P x) :
    ∀ᶠ x in F ×ˢ 𝓝 z, ∀ᶠ z' in 𝓝 x.2, P (x.1, z') := by
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_prod_iff.mp h
  obtain ⟨t₃, ht₃sub, ht₃o, hzt₃⟩ := mem_nhds_iff.mp ht₂
  refine mem_of_superset (prod_mem_prod ht₁ (ht₃o.mem_nhds hzt₃)) ?_
  rintro ⟨a, z'⟩ ⟨ha, hz'⟩
  exact mem_of_superset (ht₃o.mem_nhds hz') fun z'' hz'' => hsub ⟨ha, ht₃sub hz''⟩

/-! ### Scaling vectors -/

/-- The scaling vector of the `j`-th monomial chart: `a` on the coordinates `i < k` and on the pivot, `aᵢ / aⱼ` on
the other normal coordinates; `chartScale a k j = diagonal (chartVec a k j)`. -/
def chartVec (a : Fin n → ℂ) (k : ℕ) (j : Fin n) : Fin n → ℂ :=
  fun i => if k ≤ i.val ∧ i ≠ j then a i / a j else a i

theorem chartScale_eq (a : Fin n → ℂ) (k : ℕ) (j : Fin n) :
    chartScale a k j = diagonal (chartVec a k j) := rfl

theorem chartVec_one (k : ℕ) (j : Fin n) : chartVec (1 : Fin n → ℂ) k j = 1 := by
  funext i
  simp only [chartVec, Pi.one_apply, div_one, ite_self]

theorem tendsto_chartVec {A : Type*} {F : Filter A} {μ : A → Fin n → ℂ} (hμ : Tendsto μ F (𝓝 1))
    (k : ℕ) (j : Fin n) : Tendsto (fun a => chartVec (μ a) k j) F (𝓝 1) := by
  rw [← chartVec_one k j]
  refine tendsto_pi_nhds.2 fun i => ?_
  have hi : Tendsto (fun a => μ a i) F (𝓝 1) := (continuous_apply i).continuousAt.tendsto.comp hμ
  have hj : Tendsto (fun a => μ a j) F (𝓝 1) := (continuous_apply j).continuousAt.tendsto.comp hμ
  simp only [chartVec]
  by_cases h : k ≤ i.val ∧ i ≠ j
  · simp only [if_pos h, Pi.one_apply, div_one]
    have h2 := hi.div hj one_ne_zero
    rw [div_one] at h2
    exact h2
  · simp only [if_neg h, Pi.one_apply]
    exact hi

theorem continuous_diagonal_prod :
    Continuous fun p : (Fin n → ℂ) × ComplexModel n => diagonal p.1 p.2 := by
  have : (fun p : (Fin n → ℂ) × ComplexModel n => diagonal p.1 p.2) =
      fun p => WithLp.toLp 2 (fun i => p.1 i * p.2 i) := rfl
  rw [this]
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact ((continuous_apply i).comp continuous_fst).mul ((PiLp.continuous_apply 2 _ i).comp continuous_snd)

theorem diagonal_one (w : ComplexModel n) : diagonal (1 : Fin n → ℂ) w = w := by
  ext i
  simp

/-! ### Diagonal actions in flat coordinates -/

section Act

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The maps `act a` act near `p` diagonally in the flat coordinates of `Φ`, by `μ a`**, jointly for `a` eventually
in `F` and points near `p`. -/
def ActsDiagonallyNear {A : Type*} (F : Filter A) (act : A → M → M) (μ : A → Fin n → ℂ) {y₀ : M}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)) (p : M) : Prop :=
  ∀ᶠ x in F ×ˢ 𝓝 p, x.2 ∈ flatDomain Φ ∧ act x.1 x.2 ∈ flatDomain Φ ∧
    flatMap Φ (act x.1 x.2) = diagonal (μ x.1) (flatMap Φ x.2)

omit [IsComplexManifold n M] in
/-- A diagonal action near `p` is a diagonal action near every point near `p`. -/
theorem ActsDiagonallyNear.eventually {A : Type*} {F : Filter A} {act : A → M → M} {μ : A → Fin n → ℂ} {y₀ : M}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {p : M}
    (h : ActsDiagonallyNear F act μ Φ p) : ∀ᶠ p' in 𝓝 p, ActsDiagonallyNear F act μ Φ p' := by
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_prod_iff.mp h
  obtain ⟨t₃, ht₃sub, ht₃o, hpt₃⟩ := mem_nhds_iff.mp ht₂
  filter_upwards [ht₃o.mem_nhds hpt₃] with p' hp'
  exact mem_of_superset (prod_mem_prod ht₁ (ht₃o.mem_nhds hp')) fun x hx => hsub ⟨hx.1, ht₃sub hx.2⟩

/-- **Stage 0**: the coordinate scalings act diagonally (by `a`, for `a` near `1`) near every point of the window. -/
theorem actsDiagonallyNear_scaleMap {x₀ : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target) {O : Opens (ComplexModel n)}
    (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target) {p : M} (hp : p ∈ flatDomain Φ) (hpO : flatMap Φ p ∈ O) :
    ActsDiagonallyNear (𝓝 (1 : Fin n → ℂ)) (fun a => scaleMap (Φ := Φ) a) id Φ p := by
  have hflat : ∀ᶠ q in 𝓝 p, q ∈ flatDomain Φ := (isOpen_flatDomain Φ).mem_nhds hp
  have hcont : ContinuousAt (flatMap Φ) p :=
    (continuousOn_flatMap Φ).continuousAt ((isOpen_flatDomain Φ).mem_nhds hp)
  have h1 : ∀ᶠ x in 𝓝 (1 : Fin n → ℂ) ×ˢ 𝓝 p, x.2 ∈ flatDomain Φ :=
    tendsto_snd.eventually hflat
  have h2 : ∀ᶠ x in 𝓝 (1 : Fin n → ℂ) ×ˢ 𝓝 p, flatMap Φ x.2 ∈ O :=
    tendsto_snd.eventually (hcont.preimage_mem_nhds (O.isOpen.mem_nhds hpO))
  have ht : Tendsto (fun x : (Fin n → ℂ) × M => diagonal x.1 (flatMap Φ x.2)) (𝓝 1 ×ˢ 𝓝 p)
      (𝓝 (diagonal 1 (flatMap Φ p))) :=
    (continuous_diagonal_prod.tendsto (1, flatMap Φ p)).comp
      (tendsto_fst.prodMk_nhds ((hcont.tendsto).comp tendsto_snd))
  rw [diagonal_one] at ht
  have h3 : ∀ᶠ x in 𝓝 (1 : Fin n → ℂ) ×ˢ 𝓝 p, diagonal x.1 (flatMap Φ x.2) ∈ O :=
    ht.eventually (O.isOpen.mem_nhds hpO)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have hdom : x.2 ∈ scaleDomain Φ O x.1 := ⟨hx1, hx2, hx3⟩
  obtain ⟨hA, hB⟩ := scaleMap_spec hΦsrc hOt hdom
  exact ⟨hx1, hA, hB⟩

end Act

/-! ### One blow-up -/

section Blowup

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M} {y₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}

/-- **Toric charts through one blow-up.**  If the maps `act a` act diagonally near `π z` in a flattening `Φ` of the
centre, and the maps `act' a` lift them (`π ∘ act' a = act a ∘ π`) and are continuous near `z`, then flat coordinates
`Ψ` at `z` given by a monomial local inverse (`σⱼ ∘ (Ψ ∘ e) = (Φ ∘ e) ∘ π` on their domain) make the lifted maps act
diagonally near `z`, by `chartScale (μ a) k j`. -/
theorem exists_toric_chart_of_blowup (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {z : Z} (hz : π z ∈ flatDomain Φ) {A : Type*} {F : Filter A} {act : A → M → M} {act' : A → Z → Z}
    {μ : A → Fin n → ℂ} (hμ : Tendsto μ F (𝓝 1)) (hdiag : ActsDiagonallyNear F act μ Φ (π z))
    (hcomm : ∀ᶠ x in F ×ˢ 𝓝 z, π (act' x.1 x.2) = act x.1 (π x.2))
    (hcont : ∀ᶠ x in F ×ˢ 𝓝 z, ContinuousAt (act' x.1) x.2) :
    ∃ j : Fin n, k ≤ j.1 ∧ ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
      Ψ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      (∀ u ∈ flatDomain Ψ, π u ∈ flatDomain Φ ∧ monomial k j (flatMap Ψ u) = flatMap Φ (π u)) ∧
      ActsDiagonallyNear F act' (fun a => chartVec (μ a) k j) Ψ z := by
  classical
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hW, hℓW, -⟩ := exists_monomialLocalInverse hπ hΦsrc hflat hz
  obtain ⟨⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj |>.exists.choose_spec |>
    fun h => (⟨h, trivial⟩ : _ ∧ True)
  set ℓ := (existsUnique_monomialLift hπ hΦsrc hflat hj).exists.choose with hℓdef
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ k j := by
    intro z' hz'
    show monomial k j (W z') ∈ Φ.target
    rw [(hW z' hz').2]
    exact Φ.mapsTo_toFun (hW z' hz').1.2
  have hℓW' : ∀ z' (hz' : z' ∈ O), ℓ (LiftedOpen.mk _ (W z') (hWmem z' hz')) = z' :=
    fun z' hz' => hℓW ℓ hℓs hℓπ z' hz' (hWmem z' hz')
  have hFinj := BlowupSNCTransform.injective_fderiv_of_monomialInverse hO hWs hWmem hℓs
    (fun z' hz' hw => hℓW ℓ hℓs hℓπ z' hz' hw) hzO
  obtain ⟨Θ, hΘsrc, hΘ0, hΘ⟩ := BlowupSNCTransform.exists_recentred_coords hO hWs hzO hFinj
  let Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z) :=
    RegularPatchPullback.subConst Θ (-(W z))
  have hΨflat : ∀ u ∈ flatDomain Ψ, u ∈ O ∧ flatMap Ψ u = W u := by
    intro u hu
    obtain ⟨huO, hΘu⟩ := hΘ hu.1 hu.2
    refine ⟨huO, ?_⟩
    change Θ.toFun ((complexChartAt (n := n) z).val u) - -(W z) = W u
    rw [hΘu, sub_neg_eq_add, sub_add_cancel]
  have hzΨ : z ∈ flatDomain Ψ := ⟨mem_chart_source _ z, Θ.center_mem_source⟩
  refine ⟨j, hj, Ψ, hΘsrc, fun u hu => ?_, ?_⟩
  · obtain ⟨huO, hΨu⟩ := hΨflat u hu
    rw [hΨu]
    exact ⟨(hW u huO).1, (hW u huO).2⟩
  -- the transferred diagonal action
  have hWz : flatMap Ψ z = W z := (hΨflat z hzΨ).2
  have hWcont : ContinuousAt W z := (hWs z hzO).continuousAt
  -- `W ∘ ℓ = id` near `W z`
  have hinv : ∀ v ∈ Ψ.target, ∃ hv : v ∈ monomialDomain Φ k j,
      ℓ (LiftedOpen.mk _ v hv) ∈ flatDomain Ψ ∧ W (ℓ (LiftedOpen.mk _ v hv)) = v := by
    intro v hv
    obtain ⟨hu, hfu⟩ := flatInverse_mem Ψ hv hΘsrc
    set u := (chartAt (ComplexModel n) z).symm (Ψ.invFun v) with hudef
    obtain ⟨huO, hΨu⟩ := hΨflat u hu
    have hWu : W u = v := by rw [← hΨu]; exact hfu
    have hvD : v ∈ monomialDomain Φ k j := hWu ▸ hWmem u huO
    refine ⟨hvD, ?_⟩
    have hℓu : ℓ (LiftedOpen.mk _ v hvD) = u := by
      have := hℓW' u huO
      have hmk : LiftedOpen.mk (monomialDomain Φ k j) (W u) (hWmem u huO) =
          LiftedOpen.mk (monomialDomain Φ k j) v hvD := by
        apply Subtype.ext; apply ULift.ext; exact hWu
      rw [← hmk]; exact this
    rw [hℓu]
    exact ⟨hu, hWu⟩
  have hzt : W z ∈ Ψ.target := by
    rw [← hWz]; exact Ψ.mapsTo_toFun hzΨ.2
  -- eventual facts
  have hμj : ∀ᶠ x in F ×ˢ 𝓝 z, μ x.1 j ≠ 0 :=
    tendsto_fst.eventually (((continuous_apply j).continuousAt.tendsto.comp hμ).eventually_ne
      (by simp))
  have hscale : Tendsto (fun x : A × Z => chartScale (μ x.1) k j (W x.2)) (F ×ˢ 𝓝 z) (𝓝 (W z)) := by
    have h := (continuous_diagonal_prod.tendsto (1, W z)).comp
      (((tendsto_chartVec hμ k j).comp tendsto_fst).prodMk_nhds (hWcont.tendsto.comp tendsto_snd))
    rw [diagonal_one] at h
    exact h
  have hT : ∀ᶠ x in F ×ˢ 𝓝 z, chartScale (μ x.1) k j (W x.2) ∈ Ψ.target :=
    hscale.eventually (Ψ.isOpen_target.mem_nhds hzt)
  have hOev : ∀ᶠ x in F ×ˢ 𝓝 z, x.2 ∈ O ∩ flatDomain Ψ :=
    tendsto_snd.eventually ((hO.inter (isOpen_flatDomain Ψ)).mem_nhds ⟨hzO, hzΨ⟩)
  have hcomm' := eventually_prod_nhds_eventually hcomm
  have hπcont : Continuous π := hπ.contMDiff.continuous
  have hdiag' : ∀ᶠ x in F ×ˢ 𝓝 z, ∀ᶠ p in 𝓝 (π x.2),
      act x.1 p ∈ flatDomain Φ ∧ flatMap Φ (act x.1 p) = diagonal (μ x.1) (flatMap Φ p) := by
    have h := eventually_prod_nhds_eventually hdiag
    have ht : Tendsto (fun x : A × Z => (x.1, π x.2)) (F ×ˢ 𝓝 z) (F ×ˢ 𝓝 (π z)) :=
      tendsto_fst.prodMk ((hπcont.tendsto z).comp tendsto_snd)
    filter_upwards [ht.eventually h] with x hx
    filter_upwards [hx] with p hp
    exact ⟨hp.2.1, hp.2.2⟩
  filter_upwards [hμj, hT, hOev, hcomm', hdiag', hcont] with x hxj hxT hxO hxc hxd hxcont
  obtain ⟨a, z'⟩ := x
  simp only at hxj hxT hxO hxc hxd hxcont ⊢
  have hw₀ := hWmem z' hxO.1
  set w₀ := LiftedOpen.mk (monomialDomain Φ k j) (W z') hw₀ with hw₀def
  have hℓw₀ : ℓ w₀ = z' := hℓW' z' hxO.1
  have hγw₀ : monomialChart Φ k j w₀ = π z' := by
    rw [← hℓw₀]; exact (congrFun hℓπ w₀).symm
  obtain ⟨hvD, hvΨ, hWv⟩ := hinv _ hxT
  have hcomm₁ : ∀ᶠ z'' in 𝓝 (ℓ w₀), π (act' a z'') = act a (π z'') := by
    rw [hℓw₀]; exact hxc
  have hdiag₁ : ∀ᶠ p in 𝓝 (monomialChart Φ k j w₀),
      act a p ∈ flatDomain Φ ∧ flatMap Φ (act a p) = diagonal (μ a) (flatMap Φ p) := by
    rw [hγw₀]; exact hxd
  have hcont₁ : ContinuousAt (act' a) (ℓ w₀) := by rw [hℓw₀]; exact hxcont
  have key := monomialLift_comm_of_diagonal hπ hΦsrc hflat hj hℓs.continuous hℓπ hxj w₀ hcont₁
    hcomm₁ hdiag₁ hvD
  rw [hℓw₀] at key
  rw [key]
  refine ⟨hxO.2, hvΨ, ?_⟩
  change flatMap Ψ (ℓ (LiftedOpen.mk _ (chartScale (μ a) k j (W z')) hvD)) = _
  rw [(hΨflat _ hvΨ).2, hWv, (hΨflat z' hxO.2).2]
  rfl

end Blowup

end
end Hironaka.HironakaG34ToricCharts
