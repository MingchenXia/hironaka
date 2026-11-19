import Hironaka.Analytic.Unibranch.HironakaG10NfStrictMembership
import Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Coherence.CoherentIdealColon

/-!
# H3 (`spread`): a torsion bound on the joint chart quotient spreads to nearby chart points

Lane G10N5, run 0081, round 3 (field `spread` of `HironakaG10NfFibreModel.FibreModel`, item H3 of
`G10N5/hfib-H3-route.md`).  On a real-open blowup chart with the joint ideal `raw ⊔ target` (the fibre product
`Y ×_X X'` in the chart) and an extra ideal family `𝔍` spanned by the germs of finitely many fixed functions (the
pull-back of the local flattener `Z₁` of the strict family):

* germ calculus (`germ_add`, `germ_mul`, `germ_zero`, `germ_congr`, `eventuallyEq_of_germ_eq`, `exists_germ_rep`);
* `eventually_germ_mem_sumFam` — membership of a germ in `R ⊔ T ⊔ 𝔍` (`R`, `T` coherent) spreads to nearby points;
* `eventually_strict_le` — a coherent ideal contained in `R ⊔ T ⊔ 𝔍` at one point is so nearby;
* **`eventually_pivotTorsion_le`** — if the joint pivot torsion lies in `𝔍` at a point of the local saturation domain,
  it does at every nearby point of it (uniform saturation `strict_mem_iff_joint_pivot_power`, coherence).

No named input.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NfTorsionSpread

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel HironakaG10JointStrictTorsion

noncomputable section

section Germs

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

abbrev germ (y : M) (f : M → ℂ) (hf : HolomorphicAt n f y) : actualComplexStructureStalk (n := n) y :=
  actualOriginalFunctionGerm y f hf

theorem germ_add (y : M) (f g : M → ℂ) (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y) :
    germ y (fun p => f p + g p) (hf.add hg) = germ y f hf + germ y g hg := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [map_add, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

theorem germ_mul (y : M) (f g : M → ℂ) (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y) :
    germ y (fun p => f p * g p) (hf.mul hg) = germ y f hf * germ y g hg := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [map_mul, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

theorem germ_zero (y : M) (h : HolomorphicAt n (fun _ : M => (0 : ℂ)) y) : germ y (fun _ => 0) h = 0 := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [map_zero, actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_zero

theorem germ_congr (y : M) (f g : M → ℂ) (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y)
    (h : f =ᶠ[𝓝 y] g) : germ y f hf = germ y g hg := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original y f g hf hg h

theorem eventuallyEq_of_germ_eq (y : M) (f g : M → ℂ) (hf : HolomorphicAt n f y)
    (hg : HolomorphicAt n g y) (h : germ y f hf = germ y g hg) : f =ᶠ[𝓝 y] g := by
  have h' := congrArg (actualStalkChartEquiv (n := n) y) h
  rw [actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart] at h'
  unfold chartTranslatedGerm translatedGerm at h'
  have hev := HolGerm.mk_eq_mk_iff.mp h'
  set e := chartAt (ComplexModel n) y
  have ht : Tendsto (fun z : M => e z - e y) (𝓝 y) (𝓝 0) := by
    have hc : ContinuousAt (fun z : M => e z - e y) y :=
      (e.continuousAt (mem_chart_source _ y)).sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  filter_upwards [ht.eventually hev, e.open_source.mem_nhds (mem_chart_source _ y)] with z hz hzs
  simpa only [sub_add_cancel, e.left_inv hzs] using hz

theorem exists_germ_rep (y : M) (a : actualComplexStructureStalk (n := n) y) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f y), germ y f hf = a := by
  obtain ⟨V, hy, s, rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq a
  refine ⟨sectionExtension V s, sectionExtension_holomorphicAt V s y hy, ?_⟩
  exact actualOriginalFunctionGerm_eq_section V y hy s _ _ Filter.EventuallyEq.rfl

theorem germ_sum (y : M) {K : ℕ} (f : Fin K → M → ℂ) (hf : ∀ k, HolomorphicAt n (f k) y)
    (h : HolomorphicAt n (fun p => ∑ k, f k p) y) :
    germ y (fun p => ∑ k, f k p) h = ∑ k, germ y (f k) (hf k) := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [map_sum, actualOriginalFunctionGerm_chart]
  simp only [actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  rw [← HolGerm.mk_sum]

/-! ### Sums of coherent ideals and of fixed germ families -/

variable (R T : GermIdeal n M) {k : ℕ} (J : Fin k → M → ℂ)

/-- The ideal spanned by the germs of the fixed functions `J`. -/
def jfam (y : M) : Ideal (actualComplexStructureStalk (n := n) y) :=
  Ideal.span {g | ∃ (l : Fin k) (h : HolomorphicAt n (J l) y), g = germ y (J l) h}

/-- `R ⊔ T ⊔ 𝔍` at `y`. -/
def sumFam (y : M) : Ideal (actualComplexStructureStalk (n := n) y) :=
  actualWholeSheafStalkIdeal R y ⊔ actualWholeSheafStalkIdeal T y ⊔ jfam J y

variable {R T J}

omit [IsComplexManifold n M] in
theorem eventually_holomorphicAt {f : M → ℂ} {y : M} (h : HolomorphicAt n f y) :
    ∀ᶠ z in 𝓝 y, HolomorphicAt n f z :=
  h.eventually_nhds

/-- The spreading invariant. -/
def Spreads (o : M) (a : actualComplexStructureStalk (n := n) o) : Prop :=
  ∃ (ψ : M → ℂ) (hψ : HolomorphicAt n ψ o), germ o ψ hψ = a ∧
    ∀ᶠ y in 𝓝 o, ∀ hy : HolomorphicAt n ψ y, germ y ψ hy ∈ sumFam R T J y

theorem spreads_add {o : M} {a b : actualComplexStructureStalk (n := n) o}
    (ha : Spreads (R := R) (T := T) (J := J) o a) (hb : Spreads (R := R) (T := T) (J := J) o b) :
    Spreads (R := R) (T := T) (J := J) o (a + b) := by
  obtain ⟨ψ, hψ, rfl, hev⟩ := ha
  obtain ⟨φ, hφ, rfl, hev'⟩ := hb
  refine ⟨fun p => ψ p + φ p, hψ.add hφ, germ_add o ψ φ hψ hφ, ?_⟩
  filter_upwards [hev, hev', eventually_holomorphicAt hψ, eventually_holomorphicAt hφ] with y h1 h2 h3 h4 hy
  rw [germ_add y ψ φ h3 h4]
  exact Ideal.add_mem _ (h1 h3) (h2 h4)

theorem spreads_smul {o : M} (c : actualComplexStructureStalk (n := n) o)
    {a : actualComplexStructureStalk (n := n) o} (ha : Spreads (R := R) (T := T) (J := J) o a) :
    Spreads (R := R) (T := T) (J := J) o (c • a) := by
  obtain ⟨γ, hγ, rfl⟩ := exists_germ_rep o c
  obtain ⟨ψ, hψ, rfl, hev⟩ := ha
  refine ⟨fun p => γ p * ψ p, hγ.mul hψ, germ_mul o γ ψ hγ hψ, ?_⟩
  filter_upwards [hev, eventually_holomorphicAt hγ, eventually_holomorphicAt hψ] with y h1 h2 h3 hy
  rw [germ_mul y γ ψ h2 h3]
  exact Ideal.mul_mem_left _ _ (h1 h3)

theorem spreads_zero (o : M) : Spreads (R := R) (T := T) (J := J) o 0 := by
  have h0 : HolomorphicAt n (fun _ : M => (0 : ℂ)) o := holomorphicAt_const 0
  refine ⟨fun _ => 0, h0, germ_zero o h0, Eventually.of_forall fun y hy => ?_⟩
  rw [germ_zero y hy]
  exact Ideal.zero_mem _

theorem spreads_of_mem (hR : R.IsCoherent) (hT : T.IsCoherent) (o : M)
    (_hJ : ∀ l, ∀ᶠ y in 𝓝 o, HolomorphicAt n (J l) y)
    {a : actualComplexStructureStalk (n := n) o} (ha : a ∈ sumFam R T J o) :
    Spreads (R := R) (T := T) (J := J) o a := by
  unfold sumFam actualWholeSheafStalkIdeal jfam at ha
  rw [← Ideal.span_union, ← Ideal.span_union] at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    rcases hx with (⟨f, hf, hmem, rfl⟩ | ⟨f, hf, hmem, rfl⟩) | ⟨l, hl, rfl⟩
    · refine ⟨f, hf, rfl, ?_⟩
      filter_upwards [HadamardBridge.eventually_mem_of_isCoherent hR hmem] with y hy hfy
      exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span ⟨f, hfy, hy, rfl⟩))
    · refine ⟨f, hf, rfl, ?_⟩
      filter_upwards [HadamardBridge.eventually_mem_of_isCoherent hT hmem] with y hy hfy
      exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨f, hfy, hy, rfl⟩))
    · refine ⟨J l, hl, rfl, Eventually.of_forall fun y hy => ?_⟩
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨l, hy, rfl⟩)
  | zero => exact spreads_zero o
  | add x y _ _ hx hy => exact spreads_add hx hy
  | smul c x _ hx => exact spreads_smul c hx

/-- **Membership of a germ in `R ⊔ T ⊔ 𝔍` spreads to nearby points.** -/
theorem eventually_germ_mem_sumFam (hR : R.IsCoherent) (hT : T.IsCoherent) (o : M)
    (hJ : ∀ l, ∀ᶠ y in 𝓝 o, HolomorphicAt n (J l) y) (φ : M → ℂ) (hφ : HolomorphicAt n φ o)
    (h : germ o φ hφ ∈ sumFam R T J o) :
    ∀ᶠ y in 𝓝 o, ∀ hy : HolomorphicAt n φ y, germ y φ hy ∈ sumFam R T J y := by
  obtain ⟨ψ, hψ, he, hev⟩ := spreads_of_mem hR hT o hJ h
  have hfe := eventuallyEq_of_germ_eq o ψ φ hψ hφ he
  filter_upwards [hev, hfe.eventually_nhds, eventually_holomorphicAt hψ] with y h1 h2 h3 hy
  rw [← germ_congr y ψ φ h3 hy h2]
  exact h1 h3

/-- **A coherent ideal contained in `R ⊔ T ⊔ 𝔍` at one point is so nearby.** -/
theorem eventually_strict_le (S : GermIdeal n M) (hS : S.IsCoherent) (hR : R.IsCoherent) (hT : T.IsCoherent)
    (o : M) (hJ : ∀ l, ∀ᶠ y in 𝓝 o, HolomorphicAt n (J l) y)
    (h : actualWholeSheafStalkIdeal S o ≤ sumFam R T J o) :
    ∀ᶠ y in 𝓝 o, actualWholeSheafStalkIdeal S y ≤ sumFam R T J y := by
  obtain ⟨U, hU, hoU, N, s, hs, hgen⟩ := hS o
  have hsh : ∀ i, ∀ y ∈ U, HolomorphicAt n (s i) y := fun i y hy =>
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hs i) hy
  have hgen_o : ∀ i, ∀ᶠ y in 𝓝 o, ∀ hy : HolomorphicAt n (s i) y, germ y (s i) hy ∈ sumFam R T J y := by
    intro i
    have hmem : S.mem o (s i) :=
      (hgen o hoU (s i)).mpr (CoherentIdealColon.isInSpanAt_range_self (fun i => hsh i o hoU) i)
    exact eventually_germ_mem_sumFam hR hT o hJ (s i) (hsh i o hoU)
      (h (Ideal.subset_span ⟨s i, hsh i o hoU, hmem, rfl⟩))
  filter_upwards [eventually_all.mpr hgen_o, hU.mem_nhds hoU] with y hy hyU
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨f, hf, hmem, rfl⟩
  obtain ⟨-, K, t, a, ht, ha, hsum⟩ := (hgen y hyU f).mp hmem
  have htk : ∀ m, HolomorphicAt n (t m) y := fun m => by
    obtain ⟨i, hi⟩ := ht m
    rw [← hi]
    exact hsh i y hyU
  have hterm : ∀ m, HolomorphicAt n (fun p => a m p * t m p) y := fun m => (ha m).mul (htk m)
  have hsumhol : HolomorphicAt n (fun p => ∑ m, a m p * t m p) y := by
    have := hf.congr hsum
    exact this
  change germ y f hf ∈ _
  rw [germ_congr y f _ hf hsumhol hsum, germ_sum y _ hterm hsumhol]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [germ_mul y (a m) (t m) (ha m) (htk m)]
  refine Ideal.mul_mem_left _ _ ?_
  obtain ⟨i, hi⟩ := ht m
  have hti : t m = s i := hi.symm
  have := hy i (hsh i y hyU)
  rw [germ_congr y (t m) (s i) (htk m) (hsh i y hyU) (Filter.EventuallyEq.of_eq hti)]
  exact this

end Germs

/-! ### The joint pivot torsion -/

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (U : Opens (ComplexModel (d+t))) (W : Set U)
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  (f : realOpenChartDomain d t j b U → Y) (V : Set Y)
  (h0 : (0 : ComplexModel (d+t)) ∈ U) (hW : IsComplexAnalyticSubset (n := d+t) W)
  (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f) (hV : IsComplexAnalyticSubset (n := n) V)
  (hland : realOpenStrictTransform d t j b U W ⊆ f ⁻¹' V)
  {k : ℕ} (J : Fin k → realOpenChartDomain d t j b U → ℂ)

omit [IsComplexManifold n Y] in
include hf hland in
/-- Torsion bound in the joint quotient ⟺ strict ideal bound in the ambient stalk. -/
theorem pivotTorsion_le_iff (y : realOpenChartDomain d t j b U) (hy : y ∈ localDomain d t j b U W h0 hW) :
    pivotTorsion (n := n) d t j b U W f V y ≤
        Ideal.map (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)) (jfam J y) ↔
      geometricStrictIdeal d t j b U W y ≤
        sumFam (realOpenTotalIdeal d t j b U W) (GermIdeal.pullback (m := d+t) f (vanishingIdeal (n := n) V))
          J y := by
  have hmap : ∀ g, Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g ∈
      Ideal.map (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)) (jfam J y) ↔
      g ∈ sumFam (realOpenTotalIdeal d t j b U W)
        (GermIdeal.pullback (m := d+t) f (vanishingIdeal (n := n) V)) J y := by
    intro g
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    unfold sumFam
    rw [sup_comm]
    rfl
  have htor : ∀ g, Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g ∈
      pivotTorsion (n := n) d t j b U W f V y ↔ g ∈ geometricStrictIdeal d t j b U W y := by
    intro g
    rw [strict_mem_iff_joint_pivot_power (n := n) d t j b U W f V h0 hW hf.continuous hland y hy]
    constructor
    · rintro ⟨⟨_, m, rfl⟩, hm⟩
      refine ⟨m, ?_⟩
      change pivotClass (n := n) d t j b U W f V y ^ m • Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g = 0 at hm
      rw [smul_eq_mul, pivotClass, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm
      exact hm
    · rintro ⟨m, hm⟩
      refine ⟨⟨_, m, rfl⟩, ?_⟩
      change pivotClass (n := n) d t j b U W f V y ^ m • Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g = 0
      rw [smul_eq_mul, pivotClass, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
  constructor
  · intro h g hg
    exact (hmap g).mp (h ((htor g).mpr hg))
  · intro h a ha
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (hmap g).mpr (h ((htor g).mp ha))

include hf hV hland in
/-- **The joint pivot torsion bound spreads** from a point of the local saturation domain to nearby points of it. -/
theorem eventually_pivotTorsion_le (o : realOpenChartDomain d t j b U)
    (ho : o ∈ localDomain d t j b U W h0 hW) (hJ : ∀ l, ∀ᶠ y in 𝓝 o, HolomorphicAt (d+t) (J l) y)
    (h : pivotTorsion (n := n) d t j b U W f V o ≤
      Ideal.map (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V o)) (jfam J o)) :
    ∀ᶠ y in 𝓝 o, y ∈ localDomain d t j b U W h0 hW →
      pivotTorsion (n := n) d t j b U W f V y ≤
        Ideal.map (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)) (jfam J y) := by
  have hS : (realOpenStrictIdeal d t j b U W).IsCoherent :=
    (mem_realOpen_geoStrict_iff_exists_pivot_power d t j b U h0 W hW).2.1
  have hR : (realOpenTotalIdeal d t j b U W).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback (HironakaG10NfRealOpenChartIdeal.realOpenProjection_contMDiff
      d t j b U) (CartanIrreducible.cartanCoherence W hW)
  have hT : (GermIdeal.pullback (m := d+t) f (vanishingIdeal (n := n) V)).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hf (CartanIrreducible.cartanCoherence V hV)
  have h' := (pivotTorsion_le_iff d t j b U W f V h0 hW hf hland J o ho).mp h
  filter_upwards [eventually_strict_le _ hS hR hT o hJ h'] with y hy hyD
  exact (pivotTorsion_le_iff d t j b U W f V h0 hW hf hland J y hyD).mpr hy

end

end Hironaka.Analytic.Unibranch.HironakaG10NfTorsionSpread
