import Hironaka.Resolution.HironakaG10PNKernelSquare
import Hironaka.Resolution.HironakaG10ChowRatioGeneration

/-! The ideal in the base of a fibre of a blown-up ideal family is coherent (lane G10P, run 0080 r5).
Blueprint: `hironaka-g10-pn-step-kernel.tex`.

Let `π : Z → M` be the blowup of a complex manifold along a closed submanifold `C`
(`IsBlowupAlong`) and `𝒜` a locally finitely generated ideal family of `𝒪_Z`.  Assume that near
`z₀` (over `C`) the points where `𝒜` is not the unit ideal are the only ones over a neighbourhood of
`π z₀` (properness and injectivity on the fibre, `hloc`), and that at `z₀` every germ is congruent
modulo `𝒜` to a germ pulled back from `M` (surjective fibre algebra).  Then the kernel family
`kerFamily π 𝒜` (the ideal of the image of `V(𝒜)`) is locally finitely generated at `π z₀`
(`isLocallyFinitelyGeneratedAt_kerFamily_blowup`).

Proof (no direct-image theorem): in the monomial chart `(o, v_j, w)` of `Z` at `z₀`, the fibre
algebra gives germs `A_l` on `M` with `w_l - A_l ∘ π ∈ 𝒜` at `z₀`, hence near `z₀` (germ extension).
The substitution `R(y) = (o(y), v_j(y), A(y))` is a holomorphic section of `π` over the submanifold
`L = Fix(π ∘ R)`, and every point of `V(𝒜)` near `z₀` is `R(π z)`.  The kernel family is generated
near `π z₀` by the substituted generators `α_i ∘ R` of `𝒜` and the equations `u_l - (π ∘ R)_l` of `L`
in flattening coordinates: Hadamard's lemma with substitution on `Z` (`H ≡ H ∘ R ∘ π` modulo
`w - A ∘ π`) and on `M` (`g ≡ g ∘ π ∘ R` modulo the equations of `L`, at the fixed points). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry IsLocalRing
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG10PNBlowupKernel

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaG10ChowGermIdealDictionary HironakaG10ChowRatioGeneration
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity
  HironakaG10ChowSubstitutionHadamard HironakaG10PNIdealFamily HironakaG10PNPointIdeal
  HironakaG10PNKernelFamily HironakaG10PNKernelSquare

noncomputable section

/-! ### Germs and sections of holomorphic functions -/

section Germs

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The section over an open of a function holomorphic at each of its points. -/
def holSection (U : Opens M) (f : M → ℂ) (hf : ∀ y ∈ U, HolomorphicAt n f y) :
    (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.obj (op U) :=
  (⟨fun z : U => f z, by
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (fun z : U => f z)
    intro z
    apply contMDiffAt_subtype_iff.mpr
    exact contMDiffAt_of_eventually_mdifferentiableAt (hf z z.2)⟩ :
      actualComplexSection (n := n) U)

theorem germ_holSection (U : Opens M) (f : M → ℂ) (hf : ∀ y ∈ U, HolomorphicAt n f y) (y : M)
    (hy : y ∈ U) :
    (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.germ U y hy
        (holSection U f hf) = actualOriginalFunctionGerm y f (hf y hy) := by
  refine (actualOriginalFunctionGerm_eq_section U y hy _ f (hf y hy) ?_).symm
  filter_upwards [U.isOpen.mem_nhds hy] with z hz
  rw [sectionExtension_apply U _ z hz]
  rfl

/-- The germ of a section is the germ of its extension. -/
theorem germ_eq_originalGerm (U : Opens M)
    (s : (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.obj (op U)) (y : M)
    (hy : y ∈ U) :
    (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.germ U y hy s =
      actualOriginalFunctionGerm y (sectionExtension U s) (sectionExtension_holomorphicAt U s y hy) :=
  (actualOriginalFunctionGerm_eq_section U y hy s _ _ EventuallyEq.rfl).symm

/-- **Germ extension for functions.** -/
theorem exists_nhds_originalGerm_mem
    {J : ∀ x : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M,
      Ideal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGenerated _ J) {f : M → ℂ} {p : M} (hf : HolomorphicAt n f p)
    (h : actualOriginalFunctionGerm p f hf ∈ J p) :
    ∀ᶠ q in 𝓝 p, ∃ hq : HolomorphicAt n f q, actualOriginalFunctionGerm q f hq ∈ J q := by
  obtain ⟨T, hTo, hpT, hT⟩ : ∃ T : Set M, IsOpen T ∧ p ∈ T ∧ ∀ y ∈ T, HolomorphicAt n f y := by
    obtain ⟨T, hT, hTo, hpT⟩ := mem_nhds_iff.mp hf.eventually_nhds
    exact ⟨T, hTo, hpT, hT⟩
  let V : Opens M := ⟨T, hTo⟩
  have h' := germ_holSection V f hT p hpT
  rw [← h'] at h
  obtain ⟨O, hpO, hOV, hO⟩ := exists_nhds_mem_of_isLocallyFinitelyGenerated hJ (holSection V f hT)
    p hpT h
  filter_upwards [O.isOpen.mem_nhds hpO] with q hq
  refine ⟨hT q (hOV hq), ?_⟩
  rw [← germ_holSection V f hT q (hOV hq)]
  exact hO q hq

/-- A germ in a proper ideal vanishes at the point. -/
theorem eq_zero_of_originalGerm_mem {y : M} {f : M → ℂ} (hf : HolomorphicAt n f y)
    {I : Ideal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.stalk y)}
    (hI : I ≠ ⊤) (h : actualOriginalFunctionGerm y f hf ∈ I) : f y = 0 := by
  by_contra hne
  exact hI (Ideal.eq_top_of_isUnit_mem _ h (isUnit_originalGerm y hf hne))

end Germs

/-! ### Chart expressions and substitution -/

section Chart

variable {n : ℕ} {M Z : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] {y₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ} {j : Fin n}

/-- The chart expression `w ↦ H (ℓ w)` of a function on `Z` along a monomial lift (zero off the
domain). -/
def chartExpr (ℓ : LiftedOpen.{0} (monomialDomain Φ k j) → Z) (H : Z → ℂ) (w : ComplexModel n) :
    ℂ := by
  classical
  exact if h : w ∈ monomialDomain Φ k j then H (ℓ (LiftedOpen.mk _ w h)) else 0

omit [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] in
theorem chartExpr_of_mem (ℓ : LiftedOpen.{0} (monomialDomain Φ k j) → Z) (H : Z → ℂ)
    {w : ComplexModel n} (hw : w ∈ monomialDomain Φ k j) :
    chartExpr ℓ H w = H (ℓ (LiftedOpen.mk _ w hw)) := by
  unfold chartExpr
  rw [dif_pos hw]

theorem chartExpr_sum_mul (ℓ : LiftedOpen.{0} (monomialDomain Φ k j) → Z) {N : ℕ}
    (c H : Fin N → Z → ℂ) (w : ComplexModel n) :
    chartExpr ℓ (fun z => ∑ i, c i z * H i z) w = ∑ i, chartExpr ℓ (c i) w * chartExpr ℓ (H i) w := by
  by_cases hw : w ∈ monomialDomain Φ k j
  · simp only [chartExpr_of_mem ℓ _ hw]
  · unfold chartExpr
    simp only [dif_neg hw, mul_zero, Finset.sum_const_zero]

theorem chartExpr_const (ℓ : LiftedOpen.{0} (monomialDomain Φ k j) → Z) (a : ℂ)
    {w : ComplexModel n} (hw : w ∈ monomialDomain Φ k j) :
    chartExpr ℓ (fun _ => a) w = a := chartExpr_of_mem ℓ _ hw

variable {ℓ : LiftedOpen.{0} (monomialDomain Φ k j) → Z}

/-- Chart expressions of holomorphic germs are holomorphic. -/
theorem chartExpr_differentiableAt
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ) {H : Z → ℂ}
    {w : ComplexModel n} (hw : w ∈ monomialDomain Φ k j)
    (hH : HolomorphicAt n H (ℓ (LiftedOpen.mk _ w hw))) :
    ∀ᶠ w' in 𝓝 w, DifferentiableAt ℂ (chartExpr ℓ H) w' := by
  have h1 : ℓ ⁻¹' {z' | MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) H z'} ∈
      𝓝 (LiftedOpen.mk _ w hw) :=
    hℓs.continuous.continuousAt.preimage_mem_nhds hH
  have h2 := (LiftedOpen.isOpenEmbedding_toModel (monomialDomain Φ k j)).isOpenMap.image_mem_nhds h1
  rw [LiftedOpen.toModel_mk] at h2
  filter_upwards [h2] with w' hw'
  obtain ⟨p, hp, rfl⟩ := hw'
  have hpD : LiftedOpen.toModel _ p ∈ monomialDomain Φ k j := LiftedOpen.toModel_mem _ p
  have hm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (H ∘ ℓ) p :=
    (show MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) H (ℓ p) from hp).comp p
      ((hℓs p).mdifferentiableAt (by simp))
  have h := hm.differentiableWithinAt_writtenInExtChartAt
  simp only [modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ,
    LiftedOpen.extChartAt_eq] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(monomialDomain Φ k j).isOpen.mem_nhds hpD] with w'' hw''
  rw [chartExpr_of_mem ℓ H hw'']
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.comp_apply, id, BlowupFibreDirection.liftedOpen_extChartAt_symm _ p hw'']

/-- Chart expressions respect equality of germs. -/
theorem chartExpr_eventuallyEq
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ) {H₁ H₂ : Z → ℂ}
    {w : ComplexModel n} (hw : w ∈ monomialDomain Φ k j)
    (h : H₁ =ᶠ[𝓝 (ℓ (LiftedOpen.mk _ w hw))] H₂) :
    chartExpr ℓ H₁ =ᶠ[𝓝 w] chartExpr ℓ H₂ := by
  have h1 : ℓ ⁻¹' {z' | H₁ z' = H₂ z'} ∈ 𝓝 (LiftedOpen.mk _ w hw) :=
    hℓs.continuous.continuousAt.preimage_mem_nhds h
  have h2 := (LiftedOpen.isOpenEmbedding_toModel (monomialDomain Φ k j)).isOpenMap.image_mem_nhds h1
  rw [LiftedOpen.toModel_mk] at h2
  filter_upwards [h2] with w' hw'
  obtain ⟨p, hp, rfl⟩ := hw'
  have hpD : LiftedOpen.toModel _ p ∈ monomialDomain Φ k j := LiftedOpen.toModel_mem _ p
  rw [chartExpr_of_mem ℓ H₁ hpD, chartExpr_of_mem ℓ H₂ hpD]
  have hp' : LiftedOpen.mk _ (LiftedOpen.toModel _ p) hpD = p := rfl
  rw [hp']
  exact hp

omit [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] in
/-- The blowup of a monomial lift is the monomial chart. -/
theorem blowup_monomialLift {π : Z → M} (hℓπ : π ∘ ℓ = monomialChart Φ k j)
    {w : ComplexModel n} (hw : w ∈ monomialDomain Φ k j) :
    π (ℓ (LiftedOpen.mk _ w hw)) =
      (chartAt (ComplexModel n) y₀).symm (Φ.invFun (monomial k j w)) := by
  have h := congrFun hℓπ (LiftedOpen.mk _ w hw)
  simp only [Function.comp_apply, monomialChart, LiftedOpen.toModel_mk] at h
  exact h

/-- The flattening inverse is holomorphic. -/
theorem flatInverse_holomorphic (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    {g : M → ℂ} {u : ComplexModel n} (hu : u ∈ Φ.target)
    (hg : HolomorphicAt n g ((chartAt (ComplexModel n) y₀).symm (Φ.invFun u))) :
    DifferentiableAt ℂ (fun u' => g ((chartAt (ComplexModel n) y₀).symm (Φ.invFun u'))) u := by
  have hinvT := hΦsrc (Φ.mapsTo_invFun hu)
  have h1 := hg.self_of_nhds.comp (Φ.invFun u) (mdifferentiableAt_chart_symm hinvT)
  exact (mdifferentiableAt_iff_differentiableAt.mp h1).comp u
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hu))

/-- **Hadamard's lemma with substitution on the base**, at a fixed point of the substitution in
flattening coordinates. -/
theorem exists_sub_comp_flat_eq_sum (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    {y : M} (hy : y ∈ flatDomain Φ) (ρ : ComplexModel n → ComplexModel n)
    (hρd : ∀ᶠ u in 𝓝 (Φ.toFun (chartAt (ComplexModel n) y₀ y)), DifferentiableAt ℂ ρ u)
    (hfix : ρ (Φ.toFun (chartAt (ComplexModel n) y₀ y)) = Φ.toFun (chartAt (ComplexModel n) y₀ y))
    {g : M → ℂ} (hg : HolomorphicAt n g y) :
    ∃ c : Fin n → M → ℂ, (∀ l, HolomorphicAt n (c l) y) ∧
      (fun y' => g y' - g ((chartAt (ComplexModel n) y₀).symm
          (Φ.invFun (ρ (Φ.toFun (chartAt (ComplexModel n) y₀ y')))))) =ᶠ[𝓝 y]
        fun y' => ∑ l, c l y' * (Φ.toFun (chartAt (ComplexModel n) y₀ y') l -
          ρ (Φ.toFun (chartAt (ComplexModel n) y₀ y')) l) := by
  set u₀ := Φ.toFun (chartAt (ComplexModel n) y₀ y) with hu₀
  have hu₀T : u₀ ∈ Φ.target := Φ.mapsTo_toFun hy.2
  have hGd : ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ
      (fun u' => g ((chartAt (ComplexModel n) y₀).symm (Φ.invFun u'))) u := by
    filter_upwards [Φ.isOpen_target.mem_nhds hu₀T,
      (tendsto_flatInverse Φ hy).eventually hg.eventually_nhds] with u hu hgu
    exact flatInverse_holomorphic hΦsrc hu hgu
  obtain ⟨Hl, hHl, hHeq⟩ := exists_sub_comp_eq_sum hGd hρd hfix
  have hcont : ContinuousAt (fun y' => Φ.toFun (chartAt (ComplexModel n) y₀ y')) y :=
    ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).continuousAt).comp
      ((chartAt (ComplexModel n) y₀).continuousAt hy.1)
  refine ⟨fun l y' => Hl l (Φ.toFun (chartAt (ComplexModel n) y₀ y')),
    fun l => holomorphicAt_comp_flat Φ hy (hHl l), ?_⟩
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy, hcont.eventually hHeq] with y' hy' hH'
  rw [flatInverse_flat Φ hy'] at hH'
  rw [hH']
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- Properties near a point of a monomial chart lift to the chart coordinates. -/
theorem eventually_lift
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ) {P : Z → Prop}
    {w : ComplexModel n} (hw : w ∈ monomialDomain Φ k j)
    (h : ∀ᶠ z in 𝓝 (ℓ (LiftedOpen.mk _ w hw)), P z) :
    ∀ᶠ w' in 𝓝 w, ∃ hw' : w' ∈ monomialDomain Φ k j, P (ℓ (LiftedOpen.mk _ w' hw')) := by
  have h1 : ℓ ⁻¹' {z' | P z'} ∈ 𝓝 (LiftedOpen.mk _ w hw) :=
    hℓs.continuous.continuousAt.preimage_mem_nhds h
  have h2 := (LiftedOpen.isOpenEmbedding_toModel (monomialDomain Φ k j)).isOpenMap.image_mem_nhds h1
  rw [LiftedOpen.toModel_mk] at h2
  filter_upwards [h2] with w' hw'
  obtain ⟨p, hp, rfl⟩ := hw'
  exact ⟨LiftedOpen.toModel_mem _ p, hp⟩

/-- **Hadamard's lemma with substitution on the blowup**: near a point `z` of a monomial chart at
which the substitution `Ψ` fixes the chart coordinates, `H ≡ H ∘ ℓ ∘ Ψ ∘ σⱼ ∘ W` modulo the
functions `W_l - (Ψ ∘ σⱼ ∘ W)_l`. -/
theorem exists_sub_chartExpr_eq_sum
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ) {O : Set Z} (hO : IsOpen O)
    {Wc : Z → ComplexModel n}
    (hWcs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Wc z')
    (hℓW : ∀ z' ∈ O, ∀ hw : Wc z' ∈ monomialDomain Φ k j, ℓ (LiftedOpen.mk _ (Wc z') hw) = z')
    (Ψ : ComplexModel n → ComplexModel n) {z : Z} (hzO : z ∈ O)
    (hzD : Wc z ∈ monomialDomain Φ k j)
    (hΨd : ∀ᶠ u in 𝓝 (monomial k j (Wc z)), DifferentiableAt ℂ Ψ u)
    (hfix : Ψ (monomial k j (Wc z)) = Wc z) {H : Z → ℂ} (hH : HolomorphicAt n H z) :
    ∃ c : Fin n → Z → ℂ, (∀ l, HolomorphicAt n (c l) z) ∧
      (fun z' => H z' - chartExpr ℓ H (Ψ (monomial k j (Wc z')))) =ᶠ[𝓝 z]
        fun z' => ∑ l, c l z' * (Wc z' l - Ψ (monomial k j (Wc z')) l) := by
  have hℓ₀ : ℓ (LiftedOpen.mk _ (Wc z) hzD) = z := hℓW z hzO hzD
  have hGd := chartExpr_differentiableAt hℓs hzD (H := H) (by rw [hℓ₀]; exact hH)
  have hvd : ∀ᶠ w in 𝓝 (Wc z), DifferentiableAt ℂ (fun w => Ψ (monomial k j w)) w := by
    have h1 : ∀ᶠ w in 𝓝 (Wc z), DifferentiableAt ℂ Ψ (monomial k j w) :=
      (contDiff_monomial k j).continuous.continuousAt.eventually hΨd
    filter_upwards [h1] with w hw
    exact hw.comp w ((contDiff_monomial k j).contDiffAt.differentiableAt (by simp))
  obtain ⟨Hl, hHl, hHeq⟩ := exists_sub_comp_eq_sum hGd hvd hfix
  have hWcc : ContinuousAt Wc z := (hWcs z hzO).continuousAt
  refine ⟨fun l z' => Hl l (Wc z'), fun l => ?_, ?_⟩
  · filter_upwards [hO.mem_nhds hzO, hWcc.eventually (hHl l)] with z' hz' hd
    exact hd.mdifferentiableAt.comp z' ((hWcs z' hz').mdifferentiableAt (by simp))
  · filter_upwards [hO.mem_nhds hzO, hWcc.eventually hHeq,
      hWcc.eventually ((monomialDomain Φ k j).isOpen.mem_nhds hzD)] with z' hz' hH' hD'
    have hG1 : chartExpr ℓ H (Wc z') = H z' := by rw [chartExpr_of_mem ℓ H hD', hℓW z' hz' hD']
    rw [hG1] at hH'
    rw [hH']
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end Chart

/-! ### The kernel family of a blown-up ideal family -/

section Germ2

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem originalGerm_add' (x : M) (f g : M → ℂ) (hf : HolomorphicAt n f x)
    (hg : HolomorphicAt n g x) :
    actualOriginalFunctionGerm x (fun z => f z + g z) (hf.add hg) =
      actualOriginalFunctionGerm x f hf + actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [map_add, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

/-- Membership of a germ in the span of finitely many germs, from an identity of functions. -/
theorem originalGerm_mem_span {x : M} {r : ℕ} {f : M → ℂ} (hf : HolomorphicAt n f x)
    (c g : Fin r → M → ℂ) (hc : ∀ i, HolomorphicAt n (c i) x) (hg : ∀ i, HolomorphicAt n (g i) x)
    (h : f =ᶠ[𝓝 x] fun y => ∑ i, c i y * g i y) :
    actualOriginalFunctionGerm x f hf ∈
      Ideal.span (Set.range fun i => actualOriginalFunctionGerm x (g i) (hg i)) := by
  have hs : HolomorphicAt n (fun y => ∑ i, c i y * g i y) x :=
    HolomorphicAt.sum _ fun i _ => (hc i).mul (hg i)
  rw [originalGerm_congr x hf hs h, originalGerm_sum_mul x c g hc hg]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- An element of the span of finitely many germs comes from an identity of functions. -/
theorem exists_eq_sum_of_mem_span {x : M} {r : ℕ} {f : M → ℂ} (hf : HolomorphicAt n f x)
    (g : Fin r → M → ℂ) (hg : ∀ i, HolomorphicAt n (g i) x)
    (h : actualOriginalFunctionGerm x f hf ∈
      Ideal.span (Set.range fun i => actualOriginalFunctionGerm x (g i) (hg i))) :
    ∃ c : Fin r → M → ℂ, (∀ i, HolomorphicAt n (c i) x) ∧
      f =ᶠ[𝓝 x] fun y => ∑ i, c i y * g i y := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h
  choose cf hcf hcfe using fun i => exists_originalGerm_eq x (c i)
  refine ⟨cf, hcf, ?_⟩
  have hs : HolomorphicAt n (fun y => ∑ i, cf i y * g i y) x :=
    HolomorphicAt.sum _ fun i _ => (hcf i).mul (hg i)
  apply eventuallyEq_of_originalGerm_eq x hf hs
  rw [originalGerm_sum_mul x cf g hcf hg, ← hc]
  simp only [hcfe, smul_eq_mul]

end Germ2

section Subst

variable {n : ℕ} {M Z : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] {y₀ : M}
  (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀))

/-- Flattening coordinates. -/
abbrev flatMap (y : M) : ComplexModel n := Φ.toFun (chartAt (ComplexModel n) y₀ y)

/-- The inverse of the flattening coordinates. -/
abbrev flatInvMap (u : ComplexModel n) : M := (chartAt (ComplexModel n) y₀).symm (Φ.invFun u)

theorem continuousAt_flatMap {y : M} (hy : y ∈ flatDomain Φ) : ContinuousAt (flatMap Φ) y :=
  ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).continuousAt).comp
    ((chartAt (ComplexModel n) y₀).continuousAt hy.1)

/-- The substitution of base germs `A_l` for the ratio coordinates `l ≥ k, l ≠ j`. -/
def substΨ (k : ℕ) (j : Fin n) (A : Fin n → M → ℂ) (u : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun l => if k ≤ l.1 ∧ l ≠ j then A l (flatInvMap Φ u) else u l

theorem substΨ_apply (k : ℕ) (j : Fin n) (A : Fin n → M → ℂ) (u : ComplexModel n) (l : Fin n) :
    substΨ Φ k j A u l = if k ≤ l.1 ∧ l ≠ j then A l (flatInvMap Φ u) else u l := rfl

theorem substΨ_eventually_differentiableAt
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target) (k : ℕ) (j : Fin n)
    (A : Fin n → M → ℂ) {y : M} (hy : y ∈ flatDomain Φ) (hA : ∀ l, HolomorphicAt n (A l) y) :
    ∀ᶠ u in 𝓝 (flatMap Φ y), DifferentiableAt ℂ (substΨ Φ k j A) u := by
  filter_upwards [Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun hy.2),
    (tendsto_flatInverse Φ hy).eventually
      (eventually_all.2 fun l => (hA l).eventually_nhds)] with u hu hau
  rw [differentiableAt_euclidean]
  intro l
  have hfun : (fun x => substΨ Φ k j A x l) = fun x =>
      if k ≤ l.1 ∧ l ≠ j then A l (flatInvMap Φ x) else x l := rfl
  rw [hfun]
  split_ifs
  · exact flatInverse_holomorphic hΦsrc hu (hau l)
  · exact (EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).differentiableAt

end Subst

section Verify

variable {n : ℕ} {M Z : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] {C : Set M} {π : Z → M} {y₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ} {j : Fin n}
  {ℓ : LiftedOpen.{0} (monomialDomain Φ k j) → Z}

/-- Substituted functions are holomorphic. -/
theorem subst_holomorphicAt (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (Ψ : ComplexModel n → ComplexModel n) {y : M} (hyF : y ∈ flatDomain Φ)
    (hyΨ : ∀ᶠ u in 𝓝 (flatMap Φ y), DifferentiableAt ℂ Ψ u)
    (hyD : Ψ (flatMap Φ y) ∈ monomialDomain Φ k j) {H : Z → ℂ}
    (hH : HolomorphicAt n H (ℓ (LiftedOpen.mk _ _ hyD))) :
    HolomorphicAt n (fun y' => chartExpr ℓ H (Ψ (flatMap Φ y'))) y :=
  holomorphicAt_comp_flat Φ hyF (G := fun u => chartExpr ℓ H (Ψ u)) (by
    filter_upwards [hyΨ, hyΨ.self_of_nhds.continuousAt.eventually
      (chartExpr_differentiableAt hℓs hyD hH)] with u hu hG
    exact hG.comp u hu)

/-- **Substitution of an identity of germs on `Z`** into the span of the substituted generators. -/
theorem subst_mem_span (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (Ψ : ComplexModel n → ComplexModel n) {y : M} (hyF : y ∈ flatDomain Φ)
    (hyΨ : ∀ᶠ u in 𝓝 (flatMap Φ y), DifferentiableAt ℂ Ψ u)
    (hyD : Ψ (flatMap Φ y) ∈ monomialDomain Φ k j) {r : ℕ} (αf : Fin r → Z → ℂ)
    (hgα : ∀ i, HolomorphicAt n (fun y' => chartExpr ℓ (αf i) (Ψ (flatMap Φ y'))) y)
    {H : Z → ℂ} (c : Fin r → Z → ℂ) (hc : ∀ i, HolomorphicAt n (c i) (ℓ (LiftedOpen.mk _ _ hyD)))
    (hH : H =ᶠ[𝓝 (ℓ (LiftedOpen.mk _ _ hyD))] fun z => ∑ i, c i z * αf i z)
    {Hm : M → ℂ} (hHm : HolomorphicAt n Hm y)
    (hHmeq : Hm =ᶠ[𝓝 y] fun y' => chartExpr ℓ H (Ψ (flatMap Φ y'))) :
    actualOriginalFunctionGerm y Hm hHm ∈ Ideal.span (Set.range fun i =>
      actualOriginalFunctionGerm y (fun y' => chartExpr ℓ (αf i) (Ψ (flatMap Φ y'))) (hgα i)) := by
  have h1 := chartExpr_eventuallyEq hℓs hyD hH
  have hcont : ContinuousAt (fun y' => Ψ (flatMap Φ y')) y :=
    hyΨ.self_of_nhds.continuousAt.comp (continuousAt_flatMap Φ hyF)
  apply originalGerm_mem_span hHm (fun i y' => chartExpr ℓ (c i) (Ψ (flatMap Φ y'))) _
    (fun i => subst_holomorphicAt hℓs Ψ hyF hyΨ hyD (hc i)) hgα
  filter_upwards [hHmeq, hcont.eventually h1] with y' h2 h3
  rw [h2]
  exact h3.trans (chartExpr_sum_mul ℓ c αf _)

end Verify


section Cases

variable {n : ℕ} {M Z : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] {C : Set M} {π : Z → M} {y₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ} {j : Fin n}
  {ℓ : LiftedOpen.{0} (monomialDomain Φ k j) → Z}

/-- **The kernel family is contained in the span of the generators** (at the image of a point of
the section). -/
theorem mem_span_of_stalkMap_mem (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target) {O : Set Z} {Wc : Z → ComplexModel n}
    (hWc : ∀ z' ∈ O, π z' ∈ flatDomain Φ ∧ monomial k j (Wc z') = flatMap Φ (π z'))
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hℓπ : π ∘ ℓ = monomialChart Φ k j)
    (hℓW : ∀ z' ∈ O, ∀ hw : Wc z' ∈ monomialDomain Φ k j, ℓ (LiftedOpen.mk _ (Wc z') hw) = z')
    (Ψ : ComplexModel n → ComplexModel n) {z : Z} (hzO : z ∈ O)
    (hzD : Wc z ∈ monomialDomain Φ k j)
    (hΨz : ∀ᶠ u in 𝓝 (monomial k j (Wc z)), DifferentiableAt ℂ Ψ u)
    (hfix : Ψ (monomial k j (Wc z)) = Wc z) {r : ℕ} (αf : Fin r → Z → ℂ)
    (hαf : ∀ i, HolomorphicAt n (αf i) z)
    (hgα : ∀ i, HolomorphicAt n (fun y' => chartExpr ℓ (αf i) (Ψ (flatMap Φ y'))) (π z))
    (hge : ∀ l, HolomorphicAt n
      (fun y' => flatMap Φ y' l - monomial k j (Ψ (flatMap Φ y')) l) (π z))
    (g : (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.stalk (π z))
    (hg : ((ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff).stalkMap z).hom g ∈
      Ideal.span (Set.range fun i => actualOriginalFunctionGerm z (αf i) (hαf i))) :
    g ∈ Ideal.span (Set.range fun i => actualOriginalFunctionGerm (π z)
        (fun y' => chartExpr ℓ (αf i) (Ψ (flatMap Φ y'))) (hgα i)) ⊔
      Ideal.span (Set.range fun l => actualOriginalFunctionGerm (π z)
        (fun y' => flatMap Φ y' l - monomial k j (Ψ (flatMap Φ y')) l) (hge l)) := by
  have hπz := hWc z hzO
  have hfl : flatMap Φ (π z) = monomial k j (Wc z) := hπz.2.symm
  have hyΨ : ∀ᶠ u in 𝓝 (flatMap Φ (π z)), DifferentiableAt ℂ Ψ u := by rw [hfl]; exact hΨz
  have hyD : Ψ (flatMap Φ (π z)) ∈ monomialDomain Φ k j := by rw [hfl, hfix]; exact hzD
  have hRz : ℓ (LiftedOpen.mk _ _ hyD) = z := by
    have key : ∀ (w : ComplexModel n) (hw : w ∈ monomialDomain Φ k j), w = Wc z →
        ℓ (LiftedOpen.mk _ w hw) = z := by
      rintro w hw rfl
      exact hℓW z hzO hw
    exact key _ hyD (by rw [hfl, hfix])
  have hcompπ : ∀ {F : M → ℂ} {z' : Z}, HolomorphicAt n F (π z') →
      HolomorphicAt n (fun z'' => F (π z'')) z' :=
    fun hF => hF.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
  obtain ⟨gf, hgf, rfl⟩ := exists_originalGerm_eq (π z) g
  have hg' : actualOriginalFunctionGerm z (fun z' => gf (π z')) (hcompπ hgf) ∈
      Ideal.span (Set.range fun i => actualOriginalFunctionGerm z (αf i) (hαf i)) := by
    have e : ((ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff).stalkMap z).hom
        (actualOriginalFunctionGerm (π z) gf hgf) =
          actualOriginalFunctionGerm z (fun z' => gf (π z')) (hcompπ hgf) :=
      stalkMap_originalGerm hπ.contMDiff z gf hgf
    rw [e] at hg
    exact hg
  obtain ⟨c, hc, hceq⟩ := exists_eq_sum_of_mem_span _ αf hαf hg'
  -- Hadamard on the base at the fixed point `π z`
  have hρd : ∀ᶠ u in 𝓝 (flatMap Φ (π z)), DifferentiableAt ℂ (fun u => monomial k j (Ψ u)) u := by
    filter_upwards [hyΨ] with u hu
    exact ((contDiff_monomial k j).differentiable (by simp) _).comp u hu
  have hρfix : monomial k j (Ψ (flatMap Φ (π z))) = flatMap Φ (π z) := by rw [hfl, hfix]
  obtain ⟨d, hd, hdeq⟩ := exists_sub_comp_flat_eq_sum hΦsrc hπz.1 (fun u => monomial k j (Ψ u))
    hρd hρfix hgf
  -- the substituted part
  have hcont : ContinuousAt (fun y' => Ψ (flatMap Φ y')) (π z) :=
    hyΨ.self_of_nhds.continuousAt.comp (continuousAt_flatMap Φ hπz.1)
  have hSmeq : (fun y' => gf (flatInvMap Φ (monomial k j (Ψ (flatMap Φ y'))))) =ᶠ[𝓝 (π z)]
      fun y' => chartExpr ℓ (fun z' => gf (π z')) (Ψ (flatMap Φ y')) := by
    filter_upwards [hcont.eventually ((monomialDomain Φ k j).isOpen.mem_nhds hyD)] with y' hy'
    rw [chartExpr_of_mem ℓ _ hy', blowup_monomialLift hℓπ hy']
  have hSm : HolomorphicAt n (fun y' => gf (flatInvMap Φ (monomial k j (Ψ (flatMap Φ y'))))) (π z) :=
    (subst_holomorphicAt hℓs Ψ hπz.1 hyΨ hyD (H := fun z' => gf (π z'))
      (by rw [hRz]; exact hcompπ hgf)).congr hSmeq.symm
  have h1 := subst_mem_span hℓs Ψ hπz.1 hyΨ hyD αf hgα c (by rw [hRz]; exact hc)
    (by rw [hRz]; exact hceq) hSm hSmeq
  have h2 := originalGerm_mem_span (holomorphicAt_sub hgf hSm) d
    (fun l y' => flatMap Φ y' l - monomial k j (Ψ (flatMap Φ y')) l) hd hge hdeq
  rw [originalGerm_sub (π z) gf _ hgf hSm] at h2
  have h3 : actualOriginalFunctionGerm (π z) gf hgf =
      actualOriginalFunctionGerm (π z) _ hSm +
        (actualOriginalFunctionGerm (π z) gf hgf - actualOriginalFunctionGerm (π z) _ hSm) := by
    ring
  rw [h3]
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mem_sup_left h1
  · exact Ideal.mem_sup_right h2

/-- **The substituted generators of `𝒜` lie in the kernel family**: their pull-backs lie in `𝒜` at
a point of the section. -/
theorem stalkMap_subst_mem (hπ : IsBlowupAlong n C π) {O : Set Z} (hO : IsOpen O)
    {Wc : Z → ComplexModel n}
    (hWcs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Wc z')
    (hWc : ∀ z' ∈ O, π z' ∈ flatDomain Φ ∧ monomial k j (Wc z') = flatMap Φ (π z'))
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hℓW : ∀ z' ∈ O, ∀ hw : Wc z' ∈ monomialDomain Φ k j, ℓ (LiftedOpen.mk _ (Wc z') hw) = z')
    (Ψ : ComplexModel n → ComplexModel n) {z : Z} (hzO : z ∈ O)
    (hzD : Wc z ∈ monomialDomain Φ k j)
    (hΨz : ∀ᶠ u in 𝓝 (monomial k j (Wc z)), DifferentiableAt ℂ Ψ u)
    (hfix : Ψ (monomial k j (Wc z)) = Wc z)
    (I : Ideal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z).presheaf.stalk z))
    (hs : ∀ l, ∃ hsl : HolomorphicAt n (fun z' => Wc z' l - Ψ (monomial k j (Wc z')) l) z,
      actualOriginalFunctionGerm z _ hsl ∈ I)
    {H : Z → ℂ} (hH : HolomorphicAt n H z) (hHI : actualOriginalFunctionGerm z H hH ∈ I)
    (hgH : HolomorphicAt n (fun y' => chartExpr ℓ H (Ψ (flatMap Φ y'))) (π z)) :
    ((ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff).stalkMap z).hom
      (actualOriginalFunctionGerm (π z) _ hgH) ∈ I := by
  rw [stalkMap_originalGerm hπ.contMDiff z _ hgH]
  obtain ⟨c, hc, hceq⟩ := exists_sub_chartExpr_eq_sum hℓs hO hWcs hℓW Ψ hzO hzD hΨz hfix hH
  set T : Z → ℂ := fun z' => chartExpr ℓ H (Ψ (flatMap Φ (π z'))) with hT
  have hTH : HolomorphicAt n T z :=
    hgH.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
  have heq : (fun z' => H z' - T z') =ᶠ[𝓝 z]
      fun z' => ∑ l, c l z' * (Wc z' l - Ψ (monomial k j (Wc z')) l) := by
    filter_upwards [hO.mem_nhds hzO, hceq] with z' hz' h'
    rw [hT]
    simp only
    rw [← (hWc z' hz').2]
    exact h'
  have hmem := originalGerm_mem_span (holomorphicAt_sub hH hTH) c
    (fun l z' => Wc z' l - Ψ (monomial k j (Wc z')) l) hc (fun l => (hs l).1) heq
  have hspan : Ideal.span (Set.range fun l => actualOriginalFunctionGerm z
      (fun z' => Wc z' l - Ψ (monomial k j (Wc z')) l) (hs l).1) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact (hs l).2
  have h1 := hspan hmem
  rw [originalGerm_sub z H T hH hTH] at h1
  have h2 : actualOriginalFunctionGerm z T hTH = actualOriginalFunctionGerm z H hH -
      (actualOriginalFunctionGerm z H hH - actualOriginalFunctionGerm z T hTH) := by ring
  exact h2 ▸ I.sub_mem hHI h1

/-- **The equations of the section lie in the kernel family.** -/
theorem stalkMap_eqn_mem (hπ : IsBlowupAlong n C π) {O : Set Z} (hO : IsOpen O)
    {Wc : Z → ComplexModel n}
    (hWc : ∀ z' ∈ O, π z' ∈ flatDomain Φ ∧ monomial k j (Wc z') = flatMap Φ (π z'))
    (Ψ : ComplexModel n → ComplexModel n) {z : Z} (hzO : z ∈ O)
    (hWl : ∀ l, HolomorphicAt n (fun z' => Wc z' l) z)
    (hVl : ∀ l, HolomorphicAt n (fun z' => Ψ (monomial k j (Wc z')) l) z)
    (I : Ideal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z).presheaf.stalk z))
    (hs : ∀ l, actualOriginalFunctionGerm z (fun z' => Wc z' l - Ψ (monomial k j (Wc z')) l)
      (holomorphicAt_sub (hWl l) (hVl l)) ∈ I)
    (l : Fin n)
    (hge : HolomorphicAt n (fun y' => flatMap Φ y' l - monomial k j (Ψ (flatMap Φ y')) l) (π z)) :
    ((ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff).stalkMap z).hom
      (actualOriginalFunctionGerm (π z) _ hge) ∈ I := by
  rw [stalkMap_originalGerm hπ.contMDiff z _ hge]
  have hsl := fun m => holomorphicAt_sub (hWl m) (hVl m)
  by_cases hl : k ≤ l.1 ∧ l ≠ j
  · have heq : (fun y' => flatMap Φ y' l - monomial k j (Ψ (flatMap Φ y')) l) ∘ π =ᶠ[𝓝 z]
        fun z' => (Wc z' l - Ψ (monomial k j (Wc z')) l) * Wc z' j +
          Ψ (monomial k j (Wc z')) l * (Wc z' j - Ψ (monomial k j (Wc z')) j) := by
      filter_upwards [hO.mem_nhds hzO] with z' hz'
      simp only [Function.comp_apply]
      rw [← (hWc z' hz').2, monomial_apply, monomial_apply, if_pos hl, if_pos hl]
      ring
    rw [originalGerm_congr z (hge.comp_contMDiff
        (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt))
        (((hsl l).mul (hWl j)).add ((hVl l).mul (hsl j))) heq,
      originalGerm_add' z _ _ ((hsl l).mul (hWl j)) ((hVl l).mul (hsl j)),
      originalGerm_mul z _ _ (hsl l) (hWl j), originalGerm_mul z _ _ (hVl l) (hsl j)]
    exact I.add_mem (I.mul_mem_right _ (hs l)) (I.mul_mem_left _ (hs j))
  · have heq : (fun y' => flatMap Φ y' l - monomial k j (Ψ (flatMap Φ y')) l) ∘ π =ᶠ[𝓝 z]
        fun z' => Wc z' l - Ψ (monomial k j (Wc z')) l := by
      filter_upwards [hO.mem_nhds hzO] with z' hz'
      simp only [Function.comp_apply]
      rw [← (hWc z' hz').2, monomial_apply, monomial_apply, if_neg hl, if_neg hl]
    rw [originalGerm_congr z (hge.comp_contMDiff
        (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)) (hsl l) heq]
    exact hs l

/-- **Off the image of `V(𝒜)` the generators span the unit ideal.** -/
theorem span_eq_top_of_subst (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (Ψ : ComplexModel n → ComplexModel n) {y : M} (hyF : y ∈ flatDomain Φ)
    (hyΨ : ∀ᶠ u in 𝓝 (flatMap Φ y), DifferentiableAt ℂ Ψ u)
    (hyD : Ψ (flatMap Φ y) ∈ monomialDomain Φ k j) {r : ℕ} (αf : Fin r → Z → ℂ)
    (hαf : ∀ i, HolomorphicAt n (αf i) (ℓ (LiftedOpen.mk _ _ hyD)))
    (hgα : ∀ i, HolomorphicAt n (fun y' => chartExpr ℓ (αf i) (Ψ (flatMap Φ y'))) y)
    (hge : ∀ l, HolomorphicAt n
      (fun y' => flatMap Φ y' l - monomial k j (Ψ (flatMap Φ y')) l) y)
    (htop : monomial k j (Ψ (flatMap Φ y)) = flatMap Φ y →
      (1 : (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z).presheaf.stalk
        (ℓ (LiftedOpen.mk _ _ hyD))) ∈
        Ideal.span (Set.range fun i => actualOriginalFunctionGerm _ (αf i) (hαf i))) :
    Ideal.span (Set.range fun i => actualOriginalFunctionGerm y
        (fun y' => chartExpr ℓ (αf i) (Ψ (flatMap Φ y'))) (hgα i)) ⊔
      Ideal.span (Set.range fun l => actualOriginalFunctionGerm y
        (fun y' => flatMap Φ y' l - monomial k j (Ψ (flatMap Φ y')) l) (hge l)) = ⊤ := by
  by_cases hρ : monomial k j (Ψ (flatMap Φ y)) = flatMap Φ y
  · have h1 := htop hρ
    rw [← originalGerm_one] at h1
    obtain ⟨c, hc, hceq⟩ := exists_eq_sum_of_mem_span _ αf hαf h1
    have hcont : ContinuousAt (fun y' => Ψ (flatMap Φ y')) y :=
      hyΨ.self_of_nhds.continuousAt.comp (continuousAt_flatMap Φ hyF)
    have h2 := subst_mem_span hℓs Ψ hyF hyΨ hyD αf hgα c hc hceq (holomorphicAt_const 1) (by
      filter_upwards [hcont.eventually ((monomialDomain Φ k j).isOpen.mem_nhds hyD)] with y' hy'
      exact (chartExpr_const ℓ 1 hy').symm)
    rw [originalGerm_one] at h2
    exact (Ideal.eq_top_iff_one _).mpr (Submodule.mem_sup_left h2)
  · obtain ⟨l, hl⟩ : ∃ l, flatMap Φ y l - monomial k j (Ψ (flatMap Φ y)) l ≠ 0 := by
      by_contra h
      push Not at h
      exact hρ (by ext l; exact (sub_eq_zero.mp (h l)).symm)
    exact Ideal.eq_top_of_isUnit_mem _ (Submodule.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩))
      (isUnit_originalGerm y (hge l) hl)

end Cases

section Main

variable {n : ℕ} {M Z : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] {C : Set M} {π : Z → M}

theorem eq_of_mk_eq {y₀ : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)}
    {k : ℕ} {j : Fin n} (ℓ : LiftedOpen.{0} (monomialDomain Φ k j) → Z) {w w' : ComplexModel n}
    (hw : w ∈ monomialDomain Φ k j) (hw' : w' ∈ monomialDomain Φ k j) (h : w = w') :
    ℓ (LiftedOpen.mk _ w hw) = ℓ (LiftedOpen.mk _ w' hw') := by
  subst h
  rfl

/-- **The ideal of the image of a blown-up fibre is coherent.**  For the blowup `π : Z → M` of a
complex manifold along a closed submanifold `C`, a locally finitely generated ideal family `𝒜` of
`𝒪_Z` and a point `z₀` over `C` such that (i) over a neighbourhood of `π z₀` the points where `𝒜` is
not the unit ideal stay in any given neighbourhood of `z₀`, and (ii) every germ at `z₀` is congruent
modulo `𝒜` to a germ pulled back from `M`, the kernel family `kerFamily π 𝒜` (the ideal of the image
of `V(𝒜)`) is locally finitely generated at `π z₀`. -/
theorem isLocallyFinitelyGeneratedAt_kerFamily_blowup (hπ : IsBlowupAlong n C π)
    (𝒜 : ∀ z : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z,
      Ideal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z).presheaf.stalk z))
    (h𝒜 : IsLocallyFinitelyGenerated _ 𝒜) (z₀ : Z) (hC : π z₀ ∈ C)
    (hloc : ∀ V : Set Z, IsOpen V → z₀ ∈ V → ∃ U : Set M, IsOpen U ∧ π z₀ ∈ U ∧
      ∀ z : Z, 𝒜 z ≠ ⊤ → π z ∈ U → z ∈ V)
    (hsurj : ∀ β : (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z).presheaf.stalk z₀,
      ∃ a : (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.stalk (π z₀),
        β - ((ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff).stalkMap z₀).hom a ∈ 𝒜 z₀) :
    IsLocallyFinitelyGeneratedAt (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M)
      (kerFamily (ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff) 𝒜) (π z₀) := by
  classical
  have hcompπ : ∀ {F : M → ℂ} {z : Z}, HolomorphicAt n F (π z) →
      HolomorphicAt n (fun z' => F (π z')) z :=
    fun hF => hF.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
  -- the trivial case: `𝒜` is the unit ideal at `z₀`
  by_cases h𝒜₀ : 𝒜 z₀ = ⊤
  · obtain ⟨V, hz₀V, hV⟩ := exists_nhds_eq_top_of_isLocallyFinitelyGenerated h𝒜 z₀ h𝒜₀
    obtain ⟨U, hUo, hU₀, hU⟩ := hloc {z : Z | z ∈ V} V.isOpen hz₀V
    refine isLocallyFinitelyGeneratedAt_of_eq_top ⟨U, hUo⟩ hU₀ fun y hy => ?_
    refine kerFamily_eq_top fun z hz => ?_
    by_contra hne
    have hz' : π z = y := hz
    exact hne (hV z (hU z hne (by rw [hz']; exact hy)))
  -- flattening coordinates and the monomial chart at `z₀`
  obtain ⟨k, -, -, Φ, hΦsrc, -, hflat⟩ := hπ.1.2 (π z₀) hC
  have hy₀F : π z₀ ∈ flatDomain Φ := mem_flatDomain_self Φ
  obtain ⟨j, hj, O, hO, hz₀O, Wc, hWcs, hWc₀, hℓW₀, -⟩ :=
    exists_monomialLocalInverse hπ hΦsrc hflat (z := z₀) hy₀F
  have hWc : ∀ z' ∈ O, π z' ∈ flatDomain Φ ∧ monomial k j (Wc z') = flatMap Φ (π z') := hWc₀
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  have hℓW : ∀ z' ∈ O, ∀ hw : Wc z' ∈ monomialDomain Φ k j, ℓ (LiftedOpen.mk _ (Wc z') hw) = z' :=
    hℓW₀ ℓ hℓs hℓπ
  have hWl : ∀ (l : Fin n) (z' : Z), z' ∈ O → HolomorphicAt n (fun z'' => Wc z'' l) z' := by
    intro l z' hz'
    filter_upwards [hO.mem_nhds hz'] with z'' hz''
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (fun y => Wc y l) z'' :=
      ((EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).contDiff.contMDiff.contMDiffAt).comp z''
        (hWcs z'' hz'')
    exact h1.mdifferentiableAt (by simp)
  -- the base germs `A_l` given by the fibre algebra at `z₀`
  have hA : ∀ l : Fin n, ∃ A : M → ℂ, ∃ hAh : HolomorphicAt n A (π z₀),
      actualOriginalFunctionGerm z₀ (fun z' => Wc z' l - A (π z'))
        (holomorphicAt_sub (hWl l z₀ hz₀O) (hcompπ (F := A) (z := z₀) hAh)) ∈ 𝒜 z₀ := by
    intro l
    obtain ⟨a, ha⟩ := hsurj (actualOriginalFunctionGerm z₀ (fun z' => Wc z' l) (hWl l z₀ hz₀O))
    obtain ⟨A, hAh, rfl⟩ := exists_originalGerm_eq (π z₀) a
    refine ⟨A, hAh, ?_⟩
    have e : ((ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff).stalkMap z₀).hom
        (actualOriginalFunctionGerm (π z₀) A hAh) =
          actualOriginalFunctionGerm z₀ (fun z' => A (π z')) (hcompπ hAh) :=
      stalkMap_originalGerm hπ.contMDiff z₀ A hAh
    rw [e] at ha
    rw [originalGerm_sub z₀ _ _ (hWl l z₀ hz₀O) (hcompπ hAh)]
    exact ha
  choose A hAh hAmem using hA
  have hAval : ∀ l, Wc z₀ l = A l (π z₀) := by
    intro l
    have h0 := eq_zero_of_originalGerm_mem (f := fun z' => Wc z' l - A l (π z')) (y := z₀) _ h𝒜₀
      (hAmem l)
    exact sub_eq_zero.mp h0
  -- the substitution `Ψ`
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ComplexModel n → ComplexModel n, Ψ = substΨ Φ k j A := ⟨_, rfl⟩
  have hΨd : ∀ᶠ u in 𝓝 (flatMap Φ (π z₀)), DifferentiableAt ℂ Ψ u := by
    rw [hΨdef]
    exact substΨ_eventually_differentiableAt Φ hΦsrc k j A hy₀F hAh
  have hΨO : ∀ z' ∈ O, ∀ l, Ψ (monomial k j (Wc z')) l =
      if k ≤ l.1 ∧ l ≠ j then A l (π z') else Wc z' l := by
    intro z' hz' l
    rw [hΨdef]
    show (if k ≤ l.1 ∧ l ≠ j then A l (flatInvMap Φ (monomial k j (Wc z')))
      else (monomial k j (Wc z')) l) = _
    rw [(hWc z' hz').2]
    split_ifs with hl
    · exact congrArg (A l) (flatInverse_flat Φ (hWc z' hz').1)
    · rw [← (hWc z' hz').2, monomial_apply, if_neg hl]
  have hfix₀ : Ψ (flatMap Φ (π z₀)) = Wc z₀ := by
    ext l
    have h := hΨO z₀ hz₀O l
    rw [(hWc z₀ hz₀O).2] at h
    rw [h]
    split_ifs
    · exact (hAval l).symm
    · rfl
  have hw₀D : Wc z₀ ∈ monomialDomain Φ k j := by
    show monomial k j (Wc z₀) ∈ Φ.target
    rw [(hWc z₀ hz₀O).2]
    exact Φ.mapsTo_toFun hy₀F.2
  have hℓ₀ : ℓ (LiftedOpen.mk _ (Wc z₀) hw₀D) = z₀ := hℓW z₀ hz₀O hw₀D
  have hWcc : ∀ z' ∈ O, ContinuousAt (fun z'' => monomial k j (Wc z'')) z' := fun z' hz' =>
    (contDiff_monomial k j).continuous.continuousAt.comp (hWcs z' hz').continuousAt
  have hVl : ∀ z' ∈ O, (∀ᶠ u in 𝓝 (monomial k j (Wc z')), DifferentiableAt ℂ Ψ u) →
      ∀ l, HolomorphicAt n (fun z'' => Ψ (monomial k j (Wc z'')) l) z' := by
    intro z' hz' hd l
    filter_upwards [hO.mem_nhds hz', (hWcc z' hz').eventually hd.eventually_nhds] with z'' hz'' hd''
    have h1 : DifferentiableAt ℂ (fun u => Ψ (monomial k j u) l) (Wc z'') :=
      ((EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).differentiableAt.comp _
        hd''.self_of_nhds).comp _ ((contDiff_monomial k j).contDiffAt.differentiableAt (by simp))
    exact h1.mdifferentiableAt.comp z'' ((hWcs z'' hz'').mdifferentiableAt (by simp))
  have hΨd₀ : ∀ᶠ u in 𝓝 (monomial k j (Wc z₀)), DifferentiableAt ℂ Ψ u := by
    rw [(hWc z₀ hz₀O).2]; exact hΨd
  have hs₀ : ∀ l, ∃ hsl : HolomorphicAt n (fun z' => Wc z' l - Ψ (monomial k j (Wc z')) l) z₀,
      actualOriginalFunctionGerm z₀ _ hsl ∈ 𝒜 z₀ := by
    intro l
    have hsl := holomorphicAt_sub (hWl l z₀ hz₀O) (hVl z₀ hz₀O hΨd₀ l)
    refine ⟨hsl, ?_⟩
    by_cases hl : k ≤ l.1 ∧ l ≠ j
    · have heq : (fun z' => Wc z' l - Ψ (monomial k j (Wc z')) l) =ᶠ[𝓝 z₀]
          fun z' => Wc z' l - A l (π z') := by
        filter_upwards [hO.mem_nhds hz₀O] with z' hz'
        rw [hΨO z' hz' l, if_pos hl]
      rw [originalGerm_congr z₀ hsl _ heq]
      exact hAmem l
    · have heq : (fun z' => Wc z' l - Ψ (monomial k j (Wc z')) l) =ᶠ[𝓝 z₀]
          fun _ => (0 : ℂ) := by
        filter_upwards [hO.mem_nhds hz₀O] with z' hz'
        rw [hΨO z' hz' l, if_neg hl, sub_self]
      rw [originalGerm_congr z₀ hsl (holomorphicAt_const 0) heq, originalGerm_zero]
      exact Ideal.zero_mem _
  -- generators of `𝒜` near `z₀`
  obtain ⟨Wα, hz₀Wα, r, α, hα⟩ : ∃ (W : Opens Z) (_ : z₀ ∈ W) (r : ℕ)
      (s : Fin r → (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z).presheaf.obj (op W)),
      ∀ (y : Z) (hy : y ∈ W), 𝒜 y = Ideal.span (Set.range fun i =>
        (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z).presheaf.germ W y hy (s i)) :=
    h𝒜 z₀
  obtain ⟨αf, hαfdef⟩ : ∃ αf : Fin r → Z → ℂ, αf = fun i => sectionExtension Wα (α i) :=
    ⟨_, rfl⟩
  have hαf : ∀ i, ∀ z ∈ Wα, HolomorphicAt n (αf i) z := fun i z hz => by
    rw [hαfdef]; exact sectionExtension_holomorphicAt Wα (α i) z hz
  have h𝒜span : ∀ z (hz : z ∈ Wα), 𝒜 z =
      Ideal.span (Set.range fun i => actualOriginalFunctionGerm z (αf i) (hαf i z hz)) := by
    intro z hz
    subst hαfdef
    rw [hα z hz]
    congr 1
    exact congrArg Set.range (funext fun i => germ_eq_originalGerm Wα (α i) z hz)
  -- the neighbourhood `V` of `z₀`
  have hVev : ∀ᶠ z in 𝓝 z₀, z ∈ O ∧ z ∈ Wα ∧ Wc z ∈ monomialDomain Φ k j ∧
      (∀ᶠ u in 𝓝 (monomial k j (Wc z)), DifferentiableAt ℂ Ψ u) ∧
      ∀ l, ∃ hsl : HolomorphicAt n (fun z' => Wc z' l - Ψ (monomial k j (Wc z')) l) z,
        actualOriginalFunctionGerm z _ hsl ∈ 𝒜 z := by
    filter_upwards [hO.mem_nhds hz₀O, Wα.isOpen.mem_nhds hz₀Wα,
      (hWcs z₀ hz₀O).continuousAt.eventually ((monomialDomain Φ k j).isOpen.mem_nhds hw₀D),
      (hWcc z₀ hz₀O).eventually hΨd₀.eventually_nhds,
      eventually_all.2 fun l => exists_nhds_originalGerm_mem h𝒜 (hs₀ l).1 (hs₀ l).2]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨V, hVsub, hVo, hz₀V⟩ := mem_nhds_iff.mp hVev
  obtain ⟨U₁, hU₁o, hU₁, hU₁V⟩ := hloc V hVo hz₀V
  -- the neighbourhood `U` of `π z₀`
  have hRev : ∀ᶠ y in 𝓝 (π z₀), y ∈ U₁ ∧ y ∈ flatDomain Φ ∧
      (∀ᶠ u in 𝓝 (flatMap Φ y), DifferentiableAt ℂ Ψ u) ∧
      ∃ hD : Ψ (flatMap Φ y) ∈ monomialDomain Φ k j, ℓ (LiftedOpen.mk _ _ hD) ∈ Wα := by
    have h1 : ∀ᶠ w in 𝓝 (Wc z₀), ∃ hw : w ∈ monomialDomain Φ k j,
        ℓ (LiftedOpen.mk _ w hw) ∈ Wα :=
      eventually_lift hℓs hw₀D (by rw [hℓ₀]; exact Wα.isOpen.mem_nhds hz₀Wα)
    have hcR : ContinuousAt (fun y => Ψ (flatMap Φ y)) (π z₀) :=
      hΨd.self_of_nhds.continuousAt.comp (continuousAt_flatMap Φ hy₀F)
    rw [← hfix₀] at h1
    filter_upwards [hU₁o.mem_nhds hU₁, (isOpen_flatDomain Φ).mem_nhds hy₀F,
      (continuousAt_flatMap Φ hy₀F).eventually hΨd.eventually_nhds, hcR.eventually h1]
      with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨U, hUsub, hUo, hU₀⟩ := mem_nhds_iff.mp hRev
  -- the generators
  have hgα : ∀ i, ∀ y ∈ U, HolomorphicAt n
      (fun y' => chartExpr ℓ (αf i) (Ψ (flatMap Φ y'))) y := by
    intro i y hy
    obtain ⟨-, hyF, hyΨ, hD, hDα⟩ := hUsub hy
    exact subst_holomorphicAt hℓs Ψ hyF hyΨ hD (hαf i _ hDα)
  have hge : ∀ l, ∀ y ∈ U, HolomorphicAt n
      (fun y' => flatMap Φ y' l - monomial k j (Ψ (flatMap Φ y')) l) y := by
    intro l y hy
    obtain ⟨-, hyF, hyΨ, -⟩ := hUsub hy
    refine holomorphicAt_comp_flat Φ hyF (G := fun u => u l - monomial k j (Ψ u) l) ?_
    filter_upwards [hyΨ] with u hu
    have h1 : DifferentiableAt ℂ (fun u => monomial k j (Ψ u)) u :=
      ((contDiff_monomial k j).differentiable (by simp) _).comp u hu
    exact (differentiableAt_euclidean.mp differentiableAt_id l).sub
      (differentiableAt_euclidean.mp h1 l)
  let U' : Opens M := ⟨U, hUo⟩
  refine ⟨U', hU₀, r + n, Fin.append (fun i => holSection U' _ (hgα i))
    (fun l => holSection U' _ (hge l)), fun y₁ hy₁ => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y : M, y = y₁ := ⟨y₁, rfl⟩
  have hy : y ∈ U := hy₁
  have hgerms : (fun i => (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.germ
      U' y hy₁ (Fin.append (fun i => holSection U' _ (hgα i)) (fun l => holSection U' _ (hge l)) i)) =
      Fin.append (fun i => actualOriginalFunctionGerm y _ (hgα i y hy))
        (fun l => actualOriginalFunctionGerm y _ (hge l y hy)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun l => ?_) i
    · simp only [Fin.append_left]
      exact germ_holSection U' _ (hgα i) y hy₁
    · simp only [Fin.append_right]
      exact germ_holSection U' _ (hge l) y hy₁
  rw [hgerms, HironakaG10PNIdealNoetherModel.range_fin_append, Ideal.span_union]
  obtain ⟨hyU₁, hyF, hyΨ, hyD, hyα⟩ := hUsub hy
  by_cases hex : ∃ z : Z, 𝒜 z ≠ ⊤ ∧ π z = y
  · obtain ⟨z, hz𝒜, rfl⟩ := hex
    have hzV := hU₁V z hz𝒜 hyU₁
    obtain ⟨hzO, hzα, hzD, hΨz, hsz⟩ := hVsub hzV
    have hfixV : ∀ z' ∈ V, 𝒜 z' ≠ ⊤ → Ψ (monomial k j (Wc z')) = Wc z' := by
      intro z' hz'V hz'𝒜
      obtain ⟨-, -, -, -, hs'⟩ := hVsub hz'V
      ext l
      have h0 := eq_zero_of_originalGerm_mem
        (f := fun z'' => Wc z'' l - Ψ (monomial k j (Wc z'')) l) (y := z') _ hz'𝒜 (hs' l).2
      exact (sub_eq_zero.mp h0).symm
    have hfix := hfixV z hzV hz𝒜
    have huniq : ∀ z' : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z,
        (ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff).base z' =
          (ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff).base z → 𝒜 z' ≠ ⊤ → z' = z := by
      intro z' hz' hz'𝒜
      have hz'' : π z' = π z := hz'
      have hz'V := hU₁V z' hz'𝒜 (by rw [hz'']; exact hyU₁)
      obtain ⟨hz'O, -, hz'D, -, -⟩ := hVsub hz'V
      have hW : Wc z' = Wc z := by
        rw [← hfixV z' hz'V hz'𝒜, ← hfix, (hWc z' hz'O).2, (hWc z hzO).2, hz'']
      rw [← hℓW z' hz'O hz'D, ← hℓW z hzO hzD]
      exact eq_of_mk_eq ℓ hz'D hzD hW
    apply le_antisymm
    · intro g hg
      have hg' := (mem_kerFamily_of_unique (Q := ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff)
        (y₀ := z) huniq g).mp hg
      rw [h𝒜span z hzα] at hg'
      exact mem_span_of_stalkMap_mem hπ hΦsrc hWc hℓs hℓπ hℓW Ψ hzO hzD hΨz hfix αf
        (fun i => hαf i z hzα) (fun i => hgα i _ hy) (fun l => hge l _ hy) g hg'
    · rw [sup_le_iff, Ideal.span_le, Ideal.span_le]
      constructor
      · rintro _ ⟨i, rfl⟩
        refine (mem_kerFamily_of_unique (Q := ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff)
          (y₀ := z) huniq _).mpr ?_
        refine stalkMap_subst_mem hπ hO hWcs hWc hℓs hℓW Ψ hzO hzD hΨz hfix (𝒜 z) hsz
          (hαf i z hzα) ?_ _
        rw [h𝒜span z hzα]
        exact Ideal.subset_span ⟨i, rfl⟩
      · rintro _ ⟨l, rfl⟩
        refine (mem_kerFamily_of_unique (Q := ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff)
          (y₀ := z) huniq _).mpr ?_
        exact stalkMap_eqn_mem hπ hO hWc Ψ hzO (fun l => hWl l z hzO) (hVl z hzO hΨz) (𝒜 z)
          (fun l => (hsz l).2) l _
  · have htop : kerFamily (ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff) 𝒜 y = ⊤ :=
      kerFamily_eq_top fun z hz => by
        by_contra h
        exact hex ⟨z, h, hz⟩
    rw [htop, eq_comm]
    refine span_eq_top_of_subst hℓs Ψ hyF hyΨ hyD αf (fun i => hαf i _ hyα)
      (fun i => hgα i y hy) (fun l => hge l y hy) ?_
    intro hρ
    have hπR : π (ℓ (LiftedOpen.mk _ _ hyD)) = y := by
      rw [blowup_monomialLift hℓπ hyD, hρ]
      exact flatInverse_flat Φ hyF
    have h1 : 𝒜 (ℓ (LiftedOpen.mk _ _ hyD)) = ⊤ := by
      by_contra h
      exact hex ⟨_, h, hπR⟩
    rw [← h𝒜span _ hyα, h1]
    exact Submodule.mem_top

end Main

end

end Hironaka.HironakaG10PNBlowupKernel
