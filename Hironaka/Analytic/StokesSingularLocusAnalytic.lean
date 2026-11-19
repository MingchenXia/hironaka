import Hironaka.Analytic.StokesSingularLocus
import Hironaka.Analytic.AnalyticJacobianCriterion
import Hironaka.Analytic.RegularAtDimChart
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Analytic.StokesPolePotential

set_option autoImplicit false

/-!
# The singular locus of an irreducible analytic subvariety is analytic (TN.4 #4)

Blueprint `ana:stokes-singular-locus-analytic` (Demailly, `demailly-cadg:II.4.31`, for a
pure-dimensional set) and `ana:stokes-cutoffs` on `V_sing`.

Let `V` be a closed irreducible analytic subvariety of dimension `k` of a complex manifold of
dimension `n`.  Near a point `x`, let `sᵢ` be Cartan generators of the ideal of `V`
(`StokesSingularLocus.exists_cartanGenerators`), read in the preferred chart at `x`.

* `le_finrank_span_fderiv_of_regularAtDim` — at a regular point of dimension `k`, the
  differentials of the `sᵢ` span a space of dimension `≥ n - k` (the normal coordinates of a
  flattening lie in the ideal, so their independent differentials are combinations of the
  `dsᵢ`); hence some `(n - k)`-minor of the Jacobian is nonzero
  (`exists_minor_ne_zero_of_le_finrank`).
* `regularAtDim_of_minor_ne_zero` — conversely, a nonzero `(n - k)`-minor at a point of `V`
  forces regularity of dimension `k`: the selected equations cut out a `k`-manifold `Z ⊇ V`
  (implicit function theorem); `V ∩ Z`, read on a ball of `Z`, is an analytic subset; a regular
  point of it of dimension `j` gives (through `extendLHE`, `Φ₁ × id`) a regular point of `V` of
  dimension `j`, so `j = k` by pure dimensionality (`PureDimension.eq_dim_of_regularAtDim`);
  hence `V ∩ Z` has interior and is the whole ball (identity theorem).
* `singularLocus V = V \ V_reg`; `isClosed_singularLocus`, `isComplexAnalyticSubset_singularLocus`
  (cut out by the `sᵢ` and all `(n - k)`-minors of their Jacobian).
* `exists_stokesCutoffs_singularLocus` — the cutoffs of the one-sided probe for `A = V_sing`.
-/

open Set Filter Module
open scoped Topology Manifold

namespace Hironaka.StokesSingularLocusAnalytic

open AnalyticJacobianSingularCore

noncomputable section

variable {n : ℕ}

/-! ### Maximal minors -/

/-- Evaluation of a functional on the standard basis vectors. -/
def evalBasis : (ComplexModel n →L[ℂ] ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun L b := L (coordinateDirection b)
  map_add' L K := by ext b; simp
  map_smul' c L := by ext b; simp

theorem evalBasis_injective : Function.Injective (evalBasis (n := n)) := by
  intro L K h
  have hb : ∀ b, L (coordinateDirection b) = K (coordinateDirection b) := fun b =>
    congrFun h b
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = ∑ b, v b • coordinateDirection b := by
    ext i
    simp [coordinateDirection, Pi.single_apply]
  rw [hv, map_sum, map_sum]
  simp only [map_smul, hb]

/-- **A nonzero maximal minor of independent rows.**  If `r` functionals on `ℂⁿ` are linearly
independent, the `r × n` matrix of their values on the standard basis has a nonzero `r × r`
minor. -/
theorem exists_cols_det_ne_zero {r : ℕ} {L : Fin r → (ComplexModel n →L[ℂ] ℂ)}
    (hL : LinearIndependent ℂ L) :
    ∃ cols : Fin r → Fin n,
      (Matrix.of fun a b => L a (coordinateDirection (cols b))).det ≠ 0 := by
  classical
  set A : Matrix (Fin r) (Fin n) ℂ := Matrix.of fun a b => L a (coordinateDirection b) with hA
  have hrow : LinearIndependent ℂ A.row := by
    have : A.row = evalBasis ∘ L := by
      funext a; rfl
    rw [this]
    exact hL.map' evalBasis (LinearMap.ker_eq_bot.mpr evalBasis_injective)
  have hrank : A.rank = r := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hrow, Fintype.card_fin]
  have hspan : Submodule.span ℂ (Set.range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, hrank, finrank_fin_fun]
  obtain ⟨κ, a, ha, hspa, hlia⟩ := exists_linearIndependent' ℂ A.col
  have : Finite κ := Finite.of_injective a ha
  cases nonempty_fintype κ
  have hcard : Fintype.card κ = r := by
    have h1 := finrank_span_eq_card hlia
    rw [hspa, hspan, finrank_top, finrank_fin_fun] at h1
    exact h1.symm
  set σ : κ ≃ Fin r := Fintype.equivFinOfCardEq hcard
  refine ⟨a ∘ σ.symm, ?_⟩
  set B : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.of fun a' b => L a' (coordinateDirection ((a ∘ σ.symm) b))
  have hcol : B.col = (A.col ∘ a) ∘ σ.symm := by
    funext b; rfl
  have hli : LinearIndependent ℂ B.col := by
    rw [hcol]
    exact hlia.comp σ.symm σ.symm.injective
  exact (Matrix.isUnit_iff_isUnit_det B).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hli)
    |>.ne_zero

/-- **A nonzero `r × r` minor of a family of rank at least `r`.** -/
theorem exists_minor_ne_zero_of_le_finrank {N r : ℕ} (L : Fin N → (ComplexModel n →L[ℂ] ℂ))
    (hr : r ≤ finrank ℂ (Submodule.span ℂ (Set.range L))) :
    ∃ (rows : Fin r → Fin N) (cols : Fin r → Fin n),
      (Matrix.of fun a b => L (rows a) (coordinateDirection (cols b))).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspa, hlia⟩ := exists_linearIndependent' ℂ L
  have : Finite κ := Finite.of_injective a ha
  cases nonempty_fintype κ
  have hcard : r ≤ Fintype.card κ := by
    have h1 := finrank_span_eq_card hlia
    rw [hspa] at h1
    omega
  set ρ : Fin r → κ := (Fintype.equivFin κ).symm ∘ Fin.castLE hcard
  have hρ : Function.Injective ρ :=
    (Fintype.equivFin κ).symm.injective.comp (Fin.castLE_injective hcard)
  obtain ⟨cols, hcols⟩ := exists_cols_det_ne_zero (hlia.comp ρ hρ)
  exact ⟨a ∘ ρ, cols, hcols⟩

/-! ### Local biholomorphisms -/

/-- The derivative of a local holomorphic equivalence is injective on its source. -/
theorem injective_fderiv_toFun {p : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p)
    {z : ComplexModel n} (hz : z ∈ Ψ.source) : Function.Injective (fderiv ℂ Ψ.toFun z) := by
  have hzt : Ψ.toFun z ∈ Ψ.target := Ψ.mapsTo_toFun hz
  have hd : DifferentiableAt ℂ Ψ.toFun z :=
    Ψ.toFun_holomorphic.differentiableAt (Ψ.isOpen_source.mem_nhds hz)
  have hdi : DifferentiableAt ℂ Ψ.invFun (Ψ.toFun z) :=
    Ψ.invFun_holomorphic.differentiableAt (Ψ.isOpen_target.mem_nhds hzt)
  have hev : (Ψ.invFun ∘ Ψ.toFun) =ᶠ[𝓝 z] id := by
    filter_upwards [Ψ.isOpen_source.mem_nhds hz] with w hw
    exact Ψ.left_inv w hw
  have hcomp : (fderiv ℂ Ψ.invFun (Ψ.toFun z)).comp (fderiv ℂ Ψ.toFun z) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
    rw [← fderiv_comp z hdi hd, hev.fderiv_eq, fderiv_id]
  intro u v huv
  have := congrArg (fderiv ℂ Ψ.invFun (Ψ.toFun z)) huv
  have h1 := congrArg (fun L => L u) hcomp
  have h2 := congrArg (fun L => L v) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
  rw [← h1, ← h2, this]

/-- The normal coordinates of a surjective linear map are independent functionals. -/
theorem linearIndependent_normal_comp {k : ℕ} (hk : k ≤ n)
    {D : ComplexModel n →L[ℂ] ComplexModel n} (hD : Function.Surjective D) :
    LinearIndependent ℂ (fun a : Fin (n - k) =>
      (EuclideanSpace.proj (𝕜 := ℂ) (⟨k + a, by omega⟩ : Fin n)).comp D) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc a₀
  obtain ⟨v, hv⟩ := hD (EuclideanSpace.single (⟨k + a₀, by omega⟩ : Fin n) 1)
  have h := congrArg (fun L => L v) hc
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, hv, zero_apply, smul_eq_mul] at h
  rw [Finset.sum_eq_single a₀] at h
  · simpa using h
  · intro b _ hb
    have hne : (⟨k + b, by omega⟩ : Fin n) ≠ ⟨k + a₀, by omega⟩ := by
      intro heq
      apply hb
      ext
      have := congrArg Fin.val heq
      simp only at this
      omega
    simp [hne]
  · intro h'; exact absurd (Finset.mem_univ a₀) h'

/-! ### Applying a map to the first `k` coordinates -/

section Extend

open RegularLocusDense

variable {k : ℕ}

/-- Apply `f : ℂ^k → ℂ^k` to the first `k` coordinates of `v ∈ ℂ^n`, keeping the others. -/
def extendFirst (k : ℕ) (f : ComplexModel k → ComplexModel k) (v : ComplexModel n) :
    ComplexModel n :=
  coordinateInclusion n k (f (coordinateProjection n k v)) +
    (v - coordinateInclusion n k (coordinateProjection n k v))

theorem proj_extendFirst (hk : k ≤ n) (f : ComplexModel k → ComplexModel k)
    (v : ComplexModel n) :
    coordinateProjection n k (extendFirst k f v) = f (coordinateProjection n k v) := by
  simp only [extendFirst, map_add, map_sub, coordinateProjection_coordinateInclusion hk]
  abel

theorem extendFirst_extendFirst (hk : k ≤ n) (f g : ComplexModel k → ComplexModel k)
    (v : ComplexModel n) :
    extendFirst k g (extendFirst k f v) = extendFirst k (g ∘ f) v := by
  rw [extendFirst, proj_extendFirst hk]
  simp only [extendFirst, Function.comp_apply]
  abel

theorem extendFirst_of_eq {f : ComplexModel k → ComplexModel k} {v : ComplexModel n}
    (h : f (coordinateProjection n k v) = coordinateProjection n k v) : extendFirst k f v = v := by
  rw [extendFirst, h]
  abel

theorem extendFirst_apply_of_lt (f : ComplexModel k → ComplexModel k)
    (v : ComplexModel n) (i : Fin n) (hi : i.1 < k) :
    extendFirst k f v i = f (coordinateProjection n k v) ⟨i.1, hi⟩ := by
  simp [extendFirst, coordinateInclusion_apply, coordinateProjection_apply, hi, i.2]

theorem extendFirst_apply_of_le (f : ComplexModel k → ComplexModel k)
    (v : ComplexModel n) (i : Fin n) (hi : k ≤ i.1) : extendFirst k f v i = v i := by
  have : ¬ i.1 < k := not_lt.mpr hi
  simp [extendFirst, coordinateInclusion_apply, this]

theorem extendFirst_mem_plane_iff (hk : k ≤ n) {j : ℕ} (hj : j ≤ k)
    (f : ComplexModel k → ComplexModel k) (v : ComplexModel n) :
    extendFirst k f v ∈ complexCoordinatePlane n j ↔
      f (coordinateProjection n k v) ∈ complexCoordinatePlane k j ∧
        v ∈ complexCoordinatePlane n k := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hin : i.1 < n := lt_of_lt_of_le i.2 hk
      have := h ⟨i.1, hin⟩ hi
      rwa [extendFirst_apply_of_lt f v ⟨i.1, hin⟩ i.2] at this
    · have := h i (le_trans hj hi)
      rwa [extendFirst_apply_of_le f v i hi] at this
  · rintro ⟨h1, h2⟩ i hi
    by_cases hik : i.1 < k
    · rw [extendFirst_apply_of_lt f v i hik]
      exact h1 ⟨i.1, hik⟩ hi
    · rw [extendFirst_apply_of_le f v i (not_lt.mp hik)]
      exact h2 i (not_lt.mp hik)

theorem differentiableOn_extendFirst {f : ComplexModel k → ComplexModel k}
    {s : Set (ComplexModel k)} (hf : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (extendFirst (n := n) k f) (coordinateProjection n k ⁻¹' s) := by
  have h1 : DifferentiableOn ℂ (fun v : ComplexModel n => f (coordinateProjection n k v))
      (coordinateProjection n k ⁻¹' s) :=
    hf.comp (coordinateProjection n k).differentiableOn fun _ hv => hv
  have h2 := (coordinateInclusion n k).differentiable.comp_differentiableOn h1
  have h3 : DifferentiableOn ℂ (fun v : ComplexModel n =>
      v - coordinateInclusion n k (coordinateProjection n k v)) univ :=
    (differentiable_id.sub ((coordinateInclusion n k).differentiable.comp
      (coordinateProjection n k).differentiable)).differentiableOn
  exact h2.add (h3.mono (subset_univ _))

/-- The local holomorphic equivalence `Φ₁ × id` of `ℂ^n = ℂ^k × ℂ^{n-k}`. -/
def extendLHE (hk : k ≤ n) {w : ComplexModel k} (Φ₁ : LocalHolomorphicEquivAt (n := k) w) :
    LocalHolomorphicEquivAt (n := n) (coordinateInclusion n k w) where
  source := coordinateProjection n k ⁻¹' Φ₁.source
  target := coordinateProjection n k ⁻¹' Φ₁.target
  isOpen_source := Φ₁.isOpen_source.preimage (coordinateProjection n k).continuous
  isOpen_target := Φ₁.isOpen_target.preimage (coordinateProjection n k).continuous
  center_mem_source := by
    show coordinateProjection n k (coordinateInclusion n k w) ∈ Φ₁.source
    rw [coordinateProjection_coordinateInclusion hk]
    exact Φ₁.center_mem_source
  toFun := extendFirst k Φ₁.toFun
  invFun := extendFirst k Φ₁.invFun
  toFun_holomorphic := differentiableOn_extendFirst Φ₁.toFun_holomorphic
  invFun_holomorphic := differentiableOn_extendFirst Φ₁.invFun_holomorphic
  mapsTo_toFun := fun v hv => by
    show coordinateProjection n k (extendFirst k Φ₁.toFun v) ∈ Φ₁.target
    rw [proj_extendFirst hk]
    exact Φ₁.mapsTo_toFun hv
  mapsTo_invFun := fun v hv => by
    show coordinateProjection n k (extendFirst k Φ₁.invFun v) ∈ Φ₁.source
    rw [proj_extendFirst hk]
    exact Φ₁.mapsTo_invFun hv
  left_inv := fun v hv => by
    rw [extendFirst_extendFirst hk]
    exact extendFirst_of_eq (Φ₁.left_inv _ hv)
  right_inv := fun v hv => by
    rw [extendFirst_extendFirst hk]
    exact extendFirst_of_eq (Φ₁.right_inv _ hv)

end Extend

/-! ### Charts, germs and differentials -/

section Manifold

open RegularPatchNeighborhood RegularLocusDense HolomorphicIdealSheaves

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A regular point read in an arbitrary chart**: a flattening of `A` in the coordinates of
any chart `e` around the point. -/
theorem exists_chartFlattening {A : Set M} {y : M} {k : ℕ} (hy : RegularAtDim (n := n) A y k)
    (e : ComplexChart n M) (hye : y ∈ e.val.source) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (e.val y), Ψ.source ⊆ e.val.target ∧
      Ψ.toFun (e.val y) = 0 ∧
      ∀ z ∈ Ψ.source, (e.val.symm z ∈ A ↔ Ψ.toFun z ∈ complexCoordinatePlane n k) := by
  set f := complexChartAt (n := n) y with hf
  obtain ⟨-, -, Φ, -, hΦ0, hflat⟩ := hy
  set T := chartTransition e f with hT
  have hTsrc : T.source = e.val.target ∩ e.val.symm ⁻¹' f.val.source := by
    simp [hT, chartTransition]
  have hTapp : ∀ z, T z = f.val (e.val.symm z) := fun z => rfl
  have hyf : y ∈ f.val.source := mem_complexChartAt_source y
  have hc : e.val y ∈ T.source := by
    rw [hTsrc]
    exact ⟨e.val.map_source hye, by simpa [e.val.left_inv hye] using hyf⟩
  have hTc : T (e.val y) = f.val y := by rw [hTapp, e.val.left_inv hye]
  refine ⟨RegularAtDimChart.precomp T (differentiableOn_chartTransition e f)
    (differentiableOn_chartTransition_symm e f) hc hTc Φ, ?_, ?_, ?_⟩
  · intro z hz
    have := hz.1
    rw [hTsrc] at this
    exact this.1
  · change Φ.toFun (T (e.val y)) = 0
    rw [hTc]
    exact hΦ0
  · intro z hz
    change z ∈ T.source ∩ T ⁻¹' Φ.source at hz
    change _ ↔ Φ.toFun (T z) ∈ _
    have hzsrc := hz.1
    rw [hTsrc] at hzsrc
    have hz2 : f.val (e.val.symm z) ∈ Φ.source := by
      have := hz.2
      rwa [mem_preimage, hTapp] at this
    rw [hTapp]
    exact hflat hzsrc.2 hz2

/-- A function holomorphic at a point of `M`, read in a chart. -/
theorem differentiableAt_chart {f : M → ℂ} (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target)
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f (e.val.symm z)) :
    DifferentiableAt ℂ (fun w => f (e.val.symm w)) z :=
  mdifferentiableAt_iff_differentiableAt.mp
    (hf.comp z (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hz))

/-- **Differentials of an ideal combination.**  If `f = ∑ aₗ tₗ` near `y` with every `tₗ` one of
the `sᵢ`, all vanishing at `y`, then the differential of `f` at `y` (in a chart) lies in the span
of the differentials of the `sᵢ`. -/
theorem fderiv_mem_span_of_isInSpanAt {N : ℕ} {s : Fin N → M → ℂ} (e : ComplexChart n M)
    {y : M} (hye : y ∈ e.val.source) (hs0 : ∀ i, s i y = 0)
    (hsd : ∀ i, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) y)
    {f : M → ℂ} (hf : IsInSpanAt (n := n) (· ∈ range s) y f) :
    fderiv ℂ (fun w => f (e.val.symm w)) (e.val y) ∈
      Submodule.span ℂ (range fun i => fderiv ℂ (fun w => s i (e.val.symm w)) (e.val y)) := by
  classical
  obtain ⟨-, K, t, a, ht, ha, hfeq⟩ := hf
  have hq : e.val y ∈ e.val.target := e.val.map_source hye
  have hsq : e.val.symm (e.val y) = y := e.val.left_inv hye
  have hcont : Tendsto e.val.symm (𝓝 (e.val y)) (𝓝 y) := by
    have := e.val.continuousAt_symm hq
    rwa [ContinuousAt, hsq] at this
  have hev : (fun w => f (e.val.symm w)) =ᶠ[𝓝 (e.val y)]
      fun w => ∑ l, a l (e.val.symm w) * t l (e.val.symm w) := hfeq.comp_tendsto hcont
  rw [hev.fderiv_eq]
  have hda : ∀ l, DifferentiableAt ℂ (fun w => a l (e.val.symm w)) (e.val y) := fun l =>
    differentiableAt_chart e hq (by rw [hsq]; exact (ha l).self_of_nhds)
  choose idx hidx using ht
  have hdt : ∀ l, DifferentiableAt ℂ (fun w => t l (e.val.symm w)) (e.val y) := fun l => by
    rw [← hidx l]
    exact differentiableAt_chart e hq (by rw [hsq]; exact hsd _)
  have hprod : ∀ l, DifferentiableAt ℂ (fun w => a l (e.val.symm w) * t l (e.val.symm w))
      (e.val y) := fun l => (hda l).mul (hdt l)
  rw [fderiv_fun_sum (fun l _ => hprod l)]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [fderiv_fun_mul (hda l) (hdt l)]
  have ht0 : t l (e.val.symm (e.val y)) = 0 := by rw [hsq, ← hidx l]; exact hs0 _
  rw [ht0]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨idx l, ?_⟩)) ?_
  · simp only [hidx l]
  · have h0 : (0 : ℂ) • fderiv ℂ (fun w => a l (e.val.symm w)) (e.val y) = 0 := by
      ext v; simp
    rw [h0]
    exact Submodule.zero_mem _

/-- The coordinate functions of a flattening, read on `M`, are holomorphic. -/
theorem holomorphicAt_coord_chart {p₀ : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p₀)
    (e : ComplexChart n M) {y : M} (hye : y ∈ e.val.source) (hyΨ : e.val y ∈ Ψ.source)
    (j : Fin n) : HolomorphicAt n (fun p => Ψ.toFun (e.val p) j) y := by
  have hO : IsOpen (e.val.source ∩ e.val ⁻¹' Ψ.source) :=
    e.val.isOpen_inter_preimage Ψ.isOpen_source
  filter_upwards [hO.mem_nhds ⟨hye, hyΨ⟩] with p hp
  have hd : DifferentiableAt ℂ (fun v => Ψ.toFun v j) (e.val p) :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt.comp _
      (Ψ.toFun_holomorphic.differentiableAt (Ψ.isOpen_source.mem_nhds hp.2))
  exact hd.comp_mdifferentiableAt (mdifferentiableAt_atlas e.property hp.1)

/-- **Regular points have a Jacobian of rank at least the codimension**: at a point `y` where
`A` is regular of dimension `k`, the differentials (in any chart) of local generators of the
ideal of `A` span a space of dimension at least `n - k`. -/
theorem le_finrank_span_fderiv_of_regularAtDim {A U : Set M} (hU : IsOpen U) {N : ℕ}
    {s : Fin N → M → ℂ} (hs : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U)
    (hspan : ∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) A).mem y g ↔
      IsInSpanAt (n := n) (· ∈ range s) y g)
    (hzero : ∀ y ∈ U, (y ∈ A ↔ ∀ i, s i y = 0))
    (e : ComplexChart n M) {y : M} (hyU : y ∈ U) (hye : y ∈ e.val.source) {k : ℕ}
    (hy : RegularAtDim (n := n) A y k) :
    n - k ≤ finrank ℂ (Submodule.span ℂ
      (range fun i => fderiv ℂ (fun w => s i (e.val.symm w)) (e.val y))) := by
  have hk : k ≤ n := hy.1
  have hyA : y ∈ A := hy.2.1
  obtain ⟨Ψ, hΨt, -, hflat⟩ := exists_chartFlattening hy e hye
  have hqΨ : e.val y ∈ Ψ.source := Ψ.center_mem_source
  have hΨd : DifferentiableAt ℂ Ψ.toFun (e.val y) :=
    Ψ.toFun_holomorphic.differentiableAt (Ψ.isOpen_source.mem_nhds hqΨ)
  set D := fderiv ℂ Ψ.toFun (e.val y) with hD
  have hDinj : Function.Injective D := injective_fderiv_toFun Ψ hqΨ
  have hDsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective (f := (D : ComplexModel n →ₗ[ℂ] ComplexModel n))).mp
      hDinj
  have hli := linearIndependent_normal_comp hk hDsurj
  have hs0 : ∀ i, s i y = 0 := (hzero y hyU).mp hyA
  have hsd : ∀ i, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) y := fun i =>
    (hs i).mdifferentiableAt (hU.mem_nhds hyU)
  have hmem : ∀ a : Fin (n - k), (EuclideanSpace.proj (𝕜 := ℂ)
      (⟨k + a, by omega⟩ : Fin n)).comp D ∈ Submodule.span ℂ
        (range fun i => fderiv ℂ (fun w => s i (e.val.symm w)) (e.val y)) := by
    intro a
    set j : Fin n := ⟨k + a, by omega⟩ with hj
    -- the normal coordinate `Ψ_j`, read on `M`, lies in the ideal of `A`
    have hIdeal : (vanishingIdeal (n := n) A).mem y (fun p => Ψ.toFun (e.val p) j) := by
      refine ⟨holomorphicAt_coord_chart Ψ e hye hqΨ j, ?_⟩
      have hO : IsOpen (e.val.source ∩ e.val ⁻¹' Ψ.source) :=
        e.val.isOpen_inter_preimage Ψ.isOpen_source
      filter_upwards [hO.mem_nhds ⟨hye, hqΨ⟩] with p hp hpA
      have h := (hflat (e.val p) hp.2).mp (by rw [e.val.left_inv hp.1]; exact hpA)
      exact h j (by simp [hj])
    have hspanj := fderiv_mem_span_of_isInSpanAt e hye hs0 hsd ((hspan y hyU _).mp hIdeal)
    have hloc : (fun w => Ψ.toFun (e.val (e.val.symm w)) j) =ᶠ[𝓝 (e.val y)]
        fun w => Ψ.toFun w j := by
      filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hye)] with w hw
      rw [e.val.right_inv hw]
    rw [hloc.fderiv_eq, fderiv_coordinate_eq hΨd j] at hspanj
    exact hspanj
  have hle : Submodule.span ℂ (range fun a : Fin (n - k) =>
      (EuclideanSpace.proj (𝕜 := ℂ) (⟨k + a, by omega⟩ : Fin n)).comp D) ≤
      Submodule.span ℂ (range fun i => fderiv ℂ (fun w => s i (e.val.symm w)) (e.val y)) :=
    Submodule.span_le.mpr (range_subset_iff.mpr hmem)
  have := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card hli, Fintype.card_fin] at this

/-- **A nonzero maximal Jacobian minor at a point of `V` forces regularity**
(`demailly-cadg:II.4.31`, the direction that uses pure dimensionality).  In the preferred chart at
`x`, let `sᵢ` cut out the irreducible `V` on an open set `U`.  If an `(n - dim V)`-minor of the
Jacobian of the `sᵢ` is nonzero at a point `y ∈ V ∩ U`, then `V` is regular of dimension `dim V`
at `y`: the selected equations cut out a manifold `Z ⊇ V` of dimension `dim V`, and `V ∩ Z`,
read on `Z`, is an analytic subset of a ball which, being of pure dimension `dim V`, has
interior, hence is the whole ball by the identity theorem. -/
theorem regularAtDim_of_minor_ne_zero (V : ClosedIrreducibleAnalyticSubvariety n M) (x : M)
    {U : Set M} (hU : IsOpen U) {N : ℕ} {s : Fin N → M → ℂ}
    (hs : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U)
    (hzero : ∀ y ∈ U, (y ∈ V.carrier ↔ ∀ i, s i y = 0))
    {y : M} (hyU : y ∈ U) (hye : y ∈ (complexChartAt (n := n) x).val.source)
    (hyV : y ∈ V.carrier) (rows : Fin (n - V.dim) → Fin N) (cols : Fin (n - V.dim) → Fin n)
    (hminor : jacobianMinor (fun i w => s i ((complexChartAt (n := n) x).val.symm w)) rows cols
      ((complexChartAt (n := n) x).val y) ≠ 0) :
    RegularAtDim (n := n) V.carrier y V.dim := by
  classical
  set e := (complexChartAt (n := n) x).val with he
  have hk : V.dim ≤ n := V.dim_le
  set g : Fin N → ComplexModel n → ℂ := fun i w => s i (e.symm w) with hg
  set W : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' U with hW
  have hWo : IsOpen W := e.isOpen_inter_preimage_symm hU
  have hqt : e y ∈ e.target := e.map_source hye
  have hsq : e.symm (e y) = y := e.left_inv hye
  have hqW : e y ∈ W := ⟨hqt, by rw [mem_preimage, hsq]; exact hyU⟩
  have hgd : ∀ i, DifferentiableOn ℂ (g i) W := fun i z hz =>
    (differentiableAt_chart (complexChartAt (n := n) x) hz.1
      ((hs i).mdifferentiableAt (hU.mem_nhds hz.2))).differentiableWithinAt
  have hWV : ∀ z ∈ W, (e.symm z ∈ V.carrier ↔ ∀ i, g i z = 0) := fun z hz => hzero _ hz.2
  have hyg : ∀ i, g i (e y) = 0 := (hWV _ hqW).mp (by rw [hsq]; exact hyV)
  -- the selected equations have independent differentials and cut out a manifold `Z ⊇ V`
  have hli : LinearIndependent ℂ (fun a => fderiv ℂ (g (rows a)) (e y)) :=
    AnalyticJacobianCriterion.linearIndependent_of_fullJacobianMinor_ne_zero
      (g := fun a => g (rows a)) cols hminor
  obtain ⟨Φ, hΦW, hΦ0, hΦflat⟩ :=
    AnalyticJacobianCriterion.exists_flattening_of_localCompleteIntersection
      (S := {z | ∀ a, g (rows a) z = 0}) hWo hqW (fun a => hyg (rows a))
      (fun a => hgd (rows a)) (fun z _ => Iff.rfl) hli
  have hnk : n - (n - V.dim) = V.dim := by omega
  rw [hnk] at hΦflat
  -- a ball `D` of the plane on which `V ∩ Z` is read
  have h0t : coordinateInclusion n V.dim 0 ∈ Φ.target := by
    rw [map_zero, ← hΦ0]; exact Φ.mapsTo_toFun Φ.center_mem_source
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp
    (Φ.isOpen_target.preimage (coordinateInclusion n V.dim).continuous) 0 h0t
  set D : Set (ComplexModel V.dim) := Metric.ball 0 ρ with hD
  have hinvS : ∀ w ∈ D, Φ.invFun (coordinateInclusion n V.dim w) ∈ Φ.source := fun w hw =>
    Φ.mapsTo_invFun (hball hw)
  set G : Fin N → ComplexModel V.dim → ℂ := fun i w => g i (Φ.invFun (coordinateInclusion n V.dim w))
    with hG
  have hGd : ∀ i, DifferentiableOn ℂ (G i) D := fun i =>
    (hgd i).comp (Φ.invFun_holomorphic.comp (coordinateInclusion n V.dim).differentiableOn
      fun w hw => hball hw) fun w hw => hΦW (hinvS w hw)
  have h0D : (0 : ComplexModel V.dim) ∈ D := Metric.mem_ball_self hρ
  have hinv0 : Φ.invFun (coordinateInclusion n V.dim 0) = e y := by
    rw [map_zero, ← hΦ0, Φ.left_inv _ Φ.center_mem_source]
  have h0DV : (0 : ComplexModel V.dim) ∈ {w | ∀ i, G i w = 0} := fun i => by
    simp only [hG, hinv0]; exact hyg i
  -- a regular point of `V ∩ Z` read on the ball, of some dimension `j ≤ V.dim`
  obtain ⟨w₁, ⟨⟨hw₁DV, hw₁D⟩, -⟩, j, hjk, Φ₁, hΦ₁D, -, hΦ₁flat⟩ :=
    exists_flattening_of_isZeroLocus (n := V.dim) Metric.isOpen_ball Metric.isOpen_ball hGd
      (fun w _ => Iff.rfl) h0DV h0D h0D
  set p := Φ.invFun (coordinateInclusion n V.dim w₁) with hp
  have hpΦ : p ∈ Φ.source := hinvS w₁ hw₁D
  have hΦp : Φ.toFun p = coordinateInclusion n V.dim w₁ := Φ.right_inv _ (hball hw₁D)
  set Θ := RegularAtDimTransport.LocalHolomorphicEquivAt.comp
    (Φ.restrict univ isOpen_univ p ⟨hpΦ, trivial⟩) (extendLHE hk Φ₁) hΦp with hΘ
  have hΘflat : ∀ z ∈ Θ.source,
      (e.symm z ∈ V.carrier ↔ Θ.toFun z ∈ complexCoordinatePlane n j) := by
    intro z hz
    have hzΦ : z ∈ Φ.source := hz.1.1
    have hzW : z ∈ W := hΦW hzΦ
    have hz1 : coordinateProjection n V.dim (Φ.toFun z) ∈ Φ₁.source := hz.2
    change _ ↔ extendFirst V.dim Φ₁.toFun (Φ.toFun z) ∈ _
    rw [extendFirst_mem_plane_iff hk hjk, hWV z hzW]
    constructor
    · intro hz0
      have hZ : Φ.toFun z ∈ complexCoordinatePlane n V.dim :=
        (hΦflat z hzΦ).mp fun a => hz0 (rows a)
      refine ⟨(hΦ₁flat _ hz1).mp fun i => ?_, hZ⟩
      simp only [hG]
      rw [coordinateInclusion_coordinateProjection hZ, Φ.left_inv z hzΦ]
      exact hz0 i
    · rintro ⟨h1, hZ⟩ i
      have h2 := (hΦ₁flat _ hz1).mpr h1 i
      simp only [hG] at h2
      rwa [coordinateInclusion_coordinateProjection hZ, Φ.left_inv z hzΦ] at h2
  -- that point is a regular point of `V` of dimension `j`, so `j = dim V`
  have hpe : p ∈ e.target := (hΦW hpΦ).1
  have hy₁ : RegularAtDim (n := n) V.carrier (e.symm p) j := by
    refine regularAtDim_of_flattening_of_mem (x := x) (le_trans hjk hk) Θ ?_
      ((hWV p (hΦW hpΦ)).mpr fun i => hw₁DV i) (e.map_target hpe) ?_
    · intro y' hy' hy'Θ
      have h := hΘflat (e y') hy'Θ
      rwa [e.left_inv hy'] at h
    · rw [e.right_inv hpe]; exact Θ.center_mem_source
  have hjk' : j = V.dim := PureDimension.eq_dim_of_regularAtDim V hy₁
  -- so `V ∩ Z` has interior in the ball, and by the identity theorem it is the whole ball
  have hsub : ∀ w ∈ Φ₁.source, ∀ i, G i w = 0 := fun w hw =>
    (hΦ₁flat w hw).mpr (by
      rw [hjk']; intro i hi; exact absurd i.2 (not_lt.mpr hi))
  have hDall : ∀ w ∈ D, ∀ i, G i w = 0 := fun w hw i =>
    eqOn_zero_of_isOpen_convex Metric.isOpen_ball (convex_ball 0 ρ) (hGd i) Φ₁.isOpen_source
      (fun w' hw' => (hΦ₁D hw').1) ⟨w₁, Φ₁.center_mem_source⟩ (fun w' hw' => hsub w' hw' i) hw
  -- near `e y`, `V` is exactly `Z`
  set O : Set (ComplexModel n) := Φ.source ∩ Φ.toFun ⁻¹' (coordinateProjection n V.dim ⁻¹' D)
    with hO
  have hOo : IsOpen O := Φ.toFun_holomorphic.continuousOn.isOpen_inter_preimage
    Φ.isOpen_source (Metric.isOpen_ball.preimage (coordinateProjection n V.dim).continuous)
  have hqO : e y ∈ O := ⟨Φ.center_mem_source, by simp [hΦ0, h0D]⟩
  have hOflat : ∀ z ∈ O, (e.symm z ∈ V.carrier ↔ Φ.toFun z ∈ complexCoordinatePlane n V.dim) := by
    intro z hz
    rw [hWV z (hΦW hz.1)]
    constructor
    · intro h0; exact (hΦflat z hz.1).mp fun a => h0 (rows a)
    · intro hZ i
      have h2 := hDall _ hz.2 i
      simp only [hG] at h2
      rwa [coordinateInclusion_coordinateProjection hZ, Φ.left_inv z hz.1] at h2
  refine regularAtDim_of_flattening_of_mem (x := x) hk
    (Φ.restrict O hOo (e y) ⟨Φ.center_mem_source, hqO⟩) ?_ hyV hye ⟨Φ.center_mem_source, hqO⟩
  intro y' hy' hy'O
  have h := hOflat (e y') hy'O.2
  rwa [e.left_inv hy'] at h

/-! ### The singular locus -/

/-- The **singular locus** of `V`: the points of `V` at which `V` is not regular of dimension
`dim V`. -/
def singularLocus (V : ClosedIrreducibleAnalyticSubvariety n M) : Set M :=
  V.carrier \ regularLocus (n := n) V.carrier V.dim

theorem mem_singularLocus {V : ClosedIrreducibleAnalyticSubvariety n M} {y : M} :
    y ∈ singularLocus V ↔ y ∈ V.carrier ∧ ¬ RegularAtDim (n := n) V.carrier y V.dim :=
  Iff.rfl

theorem singularLocus_subset (V : ClosedIrreducibleAnalyticSubvariety n M) :
    singularLocus V ⊆ V.carrier := sdiff_subset

theorem disjoint_singularLocus_regularLocus (V : ClosedIrreducibleAnalyticSubvariety n M) :
    Disjoint (singularLocus V) (regularLocus (n := n) V.carrier V.dim) :=
  disjoint_sdiff_left

/-- **The singular locus is closed** (regularity is relatively open). -/
theorem isClosed_singularLocus (V : ClosedIrreducibleAnalyticSubvariety n M) :
    IsClosed (singularLocus V) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  by_cases hyV : y ∈ V.carrier
  · have hreg : RegularAtDim (n := n) V.carrier y V.dim := by
      by_contra h; exact hy ⟨hyV, h⟩
    filter_upwards [RegularPatchNeighborhood.eventually_regularAtDim hreg] with z hz hzS
    exact hzS.2 (hz hzS.1)
  · filter_upwards [V.isClosed_carrier.isOpen_compl.mem_nhds hyV] with z hz hzS
    exact hz hzS.1

/-- **The singular locus is analytic, cut out by Jacobian minors** (`demailly-cadg:II.4.31`): in
the preferred chart at any point, by Cartan generators `sᵢ` of the ideal of `V` and all
`(n - dim V)`-minors of their Jacobian. -/
theorem isComplexAnalyticSubset_singularLocus (V : ClosedIrreducibleAnalyticSubvariety n M) :
    IsComplexAnalyticSubset (n := n) (singularLocus V) := by
  classical
  intro x
  obtain ⟨U, hU, hxU, N, s, hs, hspan, hzeroU⟩ :=
    StokesSingularLocus.exists_cartanGenerators V.analytic V.isClosed_carrier x
  set e := (complexChartAt (n := n) x).val with he
  set g : Fin N → ComplexModel n → ℂ := fun i w => s i (e.symm w) with hg
  set W : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' U with hW
  have hWo : IsOpen W := e.isOpen_inter_preimage_symm hU
  have hgd : ∀ i, DifferentiableOn ℂ (g i) W := fun i z hz =>
    (differentiableAt_chart (complexChartAt (n := n) x) hz.1
      ((hs i).mdifferentiableAt (hU.mem_nhds hz.2))).differentiableWithinAt
  have hxe : x ∈ e.source := mem_complexChartAt_source x
  refine ⟨{ generatorCount := N + Fintype.card (JacobianMinorIndex N n (n - V.dim))
            generator := Fin.addCases g (jacobianMinorGenerator (n := n) (r := n - V.dim) g)
            coordinateNeighborhood := W
            isOpen_coordinateNeighborhood := hWo
            center_mem_coordinateNeighborhood :=
              ⟨e.map_source hxe, by rw [mem_preimage, e.left_inv hxe]; exact hxU⟩
            coordinateNeighborhood_subset_target := inter_subset_left
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · intro a
    refine Fin.addCases ?_ ?_ a
    · intro j; simpa using hgd j
    · intro j
      simpa using differentiableOn_jacobianMinorGenerator (n := n) (r := n - V.dim) hWo hgd j
  · intro y hye hyW
    have hyU : y ∈ U := by
      have := hyW.2
      rwa [mem_preimage, e.left_inv hye] at this
    have hgy : ∀ i, g i ((complexChartAt (n := n) x).val y) = s i y := fun i => by
      simp only [hg]
      rw [he, (complexChartAt (n := n) x).val.left_inv hye]
    rw [Fin.forall_fin_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    constructor
    · rintro ⟨hyV, hyreg⟩
      refine ⟨fun i => by rw [hgy]; exact (hzeroU y hyU).mp hyV i, fun b => ?_⟩
      by_contra hb
      exact hyreg (regularAtDim_of_minor_ne_zero V x hU hs hzeroU hyU hye hyV _ _ hb)
    · rintro ⟨hs0, hminor⟩
      have hyV := (hzeroU y hyU).mpr fun i => by rw [← hgy]; exact hs0 i
      refine ⟨hyV, fun hreg => ?_⟩
      obtain ⟨rows, cols, hrc⟩ := exists_minor_ne_zero_of_le_finrank _
        (le_finrank_span_fderiv_of_regularAtDim hU hs hspan hzeroU (complexChartAt (n := n) x)
          hyU hye hreg)
      apply hrc
      have h := hminor ((Fintype.equivFin (JacobianMinorIndex N n (n - V.dim))) (rows, cols))
      simpa [jacobianMinorGenerator, jacobianMinor, hg] using h

/-- **The cutoffs of the one-sided probe along `V_sing`** (`ana:stokes-cutoffs` for
`A = V_sing`): on a compact complex manifold with a Kähler form `ω`, chart-smooth `χ_m` with
`0 ≤ χ_m ≤ 1`, vanishing on an open neighbourhood of `V_sing`, tending to `1` at every regular
point of `V`, and `ddᶜ χ_m + (C / (m + 1)) ω ≥ 0`. -/
theorem exists_stokesCutoffs_singularLocus [CompactSpace M]
    (omega : PositiveClasses.KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M) :
    ∃ (C : ℝ) (χ : ℕ → M → ℝ) (hχ : ∀ m, ChartSmooth (n := n) (χ m)), 0 < C ∧
      (∀ m y, 0 ≤ χ m y ∧ χ m y ≤ 1) ∧
      (∀ m, ∃ O : Set M, IsOpen O ∧ singularLocus V ⊆ O ∧ ∀ y ∈ O, χ m y = 0) ∧
      (∀ y ∈ regularLocus (n := n) V.carrier V.dim, Tendsto (fun m => χ m y) atTop (𝓝 1)) ∧
      ∀ m, (ManifoldTubePositivity.ddcClosedForm (χ m) (hχ m) +
        (C / ((m : ℝ) + 1)) • omega.form).val.IsSemipositive := by
  obtain ⟨C, χ, hχ, hC, h01, hzero, hlim, hsemi⟩ :=
    StokesPolePotential.exists_stokesCutoffs omega (isComplexAnalyticSubset_singularLocus V)
      (isClosed_singularLocus V)
  exact ⟨C, χ, hχ, hC, h01, hzero,
    fun y hy => hlim y fun hyS => hyS.2 hy, hsemi⟩

end Manifold

end

end Hironaka.StokesSingularLocusAnalytic
