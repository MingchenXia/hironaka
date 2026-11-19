import Hironaka.MarkedIdeal.HomogenizedEquivalence
import Hironaka.MarkedIdeal.DerivativeIdealInvariance

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The homogenized and coefficient ideals commute with restriction to open sets and with biholomorphisms

Hironaka phase H3 (TN23-ENVELOPES), requested by TN-CLASSICAL (I-0981 C-0027 item 1, the commutation part of
`hir:homogenized-coefficient`); blueprint `mc:pullback-finite-sum`, `mc:derivative-open-restriction`,
`mc:homogenized-etale` (`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, Lemmas `le:etale2`, `le:etale3`
(étale functoriality of `𝓓`, `𝓗` and `𝓒`), for the two kinds of étale maps used in the analytic setting: the inclusion of
an open set and a biholomorphism.

* `pullback_finSumIdeal`, `pullback_homSum`: pullbacks commute with finite sums `∑ᵢ 𝔍ᵢ` and with `∑ᵢ Aᵢ Bⁱ`.
* `pullback_val_derivIdeal`, `pullback_val_iterDerivIdeal`: **`𝓓` commutes with restriction to an open set**
  (`ι^*𝓓^j(𝔞) = 𝓓^j(ι^*𝔞)` for the inclusion `ι` of an open `U`); the charts of `U` are restrictions of charts of `M`.
* `pullback_homogenizedIdeal_of_iterDeriv`, `pullback_coeffMarked_of_iterDeriv`: for a holomorphic map along which `𝓓^j`
  commutes with pullback, so do `𝓗` and `𝓒`; instances: `pullback_val_homogenizedIdeal`, `pullback_val_coeffMarked`
  (restriction to an open set) and `pullback_homogenizedIdeal_of_inverse`, `pullback_coeffMarked_of_inverse`
  (biholomorphisms, from TN-CLASSICAL's `DerivativeIdealInvariance.pullback_iterDerivIdeal`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedEtale

open Hironaka.HolomorphicIdealSheaves GermIdealOrder DerivativeIdeal IdealWeightPowers MarkedIdeals
  MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal HomogenizedIdeal HomogenizedGlueing
  HomogenizedEquivalence MarkedIdealBiholomorphism GermIdealPullbackCalculus

noncomputable section

section Pullback

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M'] {f : M' → M}

/-- **Pullbacks commute with finite sums** (`m ≥ 1`, coherent summands). -/
theorem pullback_finSumIdeal (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {J : ℕ → GermIdeal n M} (hJ : ∀ i, (J i).IsCoherent) :
    ∀ {m : ℕ}, 1 ≤ m →
      GermIdeal.pullback (m := n) f (finSumIdeal J m) = finSumIdeal (fun i => GermIdeal.pullback (m := n) f (J i)) m
  | 0, h => absurd h (by omega)
  | 1, _ => by
    rw [finSumIdeal_one (hJ 0), finSumIdeal_one (isCoherent_pullback hf (hJ 0))]
  | m + 2, _ => by
    have hJ' : ∀ i, (GermIdeal.pullback (m := n) f (J i)).IsCoherent := fun i => isCoherent_pullback hf (hJ i)
    rw [finSumIdeal_succ (fun i _ => hJ i), finSumIdeal_succ (fun i _ => hJ' i),
      MarkedIdealOperationsTransform.pullback_sumIdeal hf
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (isCoherent_finSumIdeal_of_lt fun i _ => hJ i))
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (hJ (m + 1))),
      pullback_finSumIdeal hf hJ (m := m + 1) (by omega)]

/-- **Pullbacks commute with `∑ᵢ Aᵢ Bⁱ`** (`μ ≥ 1`, coherent `Aᵢ`, `B`). -/
theorem pullback_homSum (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {A : ℕ → GermIdeal n M} {B : GermIdeal n M} (hA : ∀ i, (A i).IsCoherent) (hB : B.IsCoherent) {μ : ℕ}
    (hμ : 1 ≤ μ) :
    GermIdeal.pullback (m := n) f (homSum A B μ) =
      homSum (fun i => GermIdeal.pullback (m := n) f (A i)) (GermIdeal.pullback (m := n) f B) μ := by
  unfold homSum
  rw [pullback_finSumIdeal hf (fun i => isCoherent_mul (hA i) (isCoherent_idealPow hB i)) hμ]
  refine finSumIdeal_congr fun i _ => ?_
  rw [GermIdealTotalTransform.pullback_mul hf (hA i) (isCoherent_idealPow hB i),
    BlowupExceptionalDivisor.pullback_idealPow hf hB]

/-- **`𝓗` commutes with pullbacks along which `𝓓` does.** -/
theorem pullback_homogenizedIdeal_of_iterDeriv (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (hD : ∀ j, GermIdeal.pullback (m := n) f (iterDerivIdeal 𝔞 j) =
      iterDerivIdeal (GermIdeal.pullback (m := n) f 𝔞) j) {μ : ℕ} (hμ : 1 ≤ μ) :
    GermIdeal.pullback (m := n) f (homogenizedIdeal 𝔞 μ) =
      homogenizedIdeal (GermIdeal.pullback (m := n) f 𝔞) μ := by
  rw [homogenizedIdeal_eq_homSum, homogenizedIdeal_eq_homSum,
    pullback_homSum hf (fun i => isCoherent_iterDerivIdeal h𝔞 i) (isCoherent_iterDerivIdeal h𝔞 _) hμ]
  exact homSum_congr (fun i _ => hD i) (hD _)

/-- **`𝓒` commutes with pullbacks along which `𝓓` does** (`d ≥ 1`). -/
theorem pullback_coeffMarked_of_iterDeriv (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hD : ∀ j, GermIdeal.pullback (m := n) f (iterDerivIdeal 𝔪.ideal j) =
      iterDerivIdeal (GermIdeal.pullback (m := n) f 𝔪.ideal) j) (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback f (coeffMarked 𝔪) = coeffMarked (MarkedIdeal.pullback f 𝔪) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  show GermIdeal.pullback (m := n) f (finSumIdeal (fun i => idealPow (iterDerivIdeal 𝔪.ideal i)
      (sumExp (fun j => 𝔪.d - j) 𝔪.d i)) 𝔪.d) =
    finSumIdeal (fun i => idealPow (iterDerivIdeal (GermIdeal.pullback (m := n) f 𝔪.ideal) i)
      (sumExp (fun j => 𝔪.d - j) 𝔪.d i)) 𝔪.d
  rw [pullback_finSumIdeal hf (fun i => isCoherent_idealPow (isCoherent_iterDerivIdeal h𝔞 i) _) hd]
  refine finSumIdeal_congr fun i _ => ?_
  rw [BlowupExceptionalDivisor.pullback_idealPow hf (isCoherent_iterDerivIdeal h𝔞 i), hD i]

/-- **`𝓗` commutes with pullbacks along which `𝓓` does**, marked form. -/
theorem pullback_homMarked_of_iterDeriv (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hD : ∀ j, GermIdeal.pullback (m := n) f (iterDerivIdeal 𝔪.ideal j) =
      iterDerivIdeal (GermIdeal.pullback (m := n) f 𝔪.ideal) j) (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback f (homMarked 𝔪) = homMarked (MarkedIdeal.pullback f 𝔪) :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
    (pullback_homogenizedIdeal_of_iterDeriv hf h𝔞 hD hd) rfl

/-! #### Biholomorphisms -/

variable {ψ : M → M'}

/-- **`𝓗` commutes with biholomorphisms** (`le:etale2/3` for biholomorphisms). -/
theorem pullback_homogenizedIdeal_of_inverse (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ) (hfψ : ∀ x, f (ψ x) = x)
    (hψf : ∀ p, ψ (f p) = p) {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ) :
    GermIdeal.pullback (m := n) f (homogenizedIdeal 𝔞 μ) =
      homogenizedIdeal (GermIdeal.pullback (m := n) f 𝔞) μ :=
  pullback_homogenizedIdeal_of_iterDeriv hf h𝔞
    (DerivativeIdealInvariance.pullback_iterDerivIdeal (fun p => (hf p).mdifferentiableAt (by simp))
      (fun x => (hψ x).mdifferentiableAt (by simp)) hfψ hψf
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞)) hμ

/-- **`𝓒` commutes with biholomorphisms** (`le:etale2/3` for biholomorphisms). -/
theorem pullback_coeffMarked_of_inverse (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ) (hfψ : ∀ x, f (ψ x) = x)
    (hψf : ∀ p, ψ (f p) = p) (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback f (coeffMarked 𝔪) = coeffMarked (MarkedIdeal.pullback f 𝔪) :=
  pullback_coeffMarked_of_iterDeriv hf 𝔪 h𝔞
    (DerivativeIdealInvariance.pullback_iterDerivIdeal (fun p => (hf p).mdifferentiableAt (by simp))
      (fun x => (hψ x).mdifferentiableAt (by simp)) hfψ hψf
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞)) hd

end Pullback

/-! ### Restriction to an open set -/

section OpenRestriction

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  (U : Opens M)

/-- **The charts of an open set are restrictions**: the chart derivative of `f ∘ ι` in the preferred chart of `U` at
`y` is the restriction of the chart derivative of `f` in the preferred chart of `M` at `ι y`. -/
theorem chartDeriv_comp_val (y : U) (f : M → ℂ) (v : ComplexModel n) :
    chartDeriv (complexChartAt (n := n) y) v (f ∘ Subtype.val) =ᶠ[𝓝 y]
      fun p => chartDeriv (complexChartAt (n := n) (y : M)) v f p := by
  set e := chartAt (ComplexModel n) (y : M) with he
  have hU : Nonempty U := ⟨y⟩
  have heU : chartAt (ComplexModel n) y = e.subtypeRestr hU := rfl
  have hsrc : (e.subtypeRestr hU).source ∈ 𝓝 y :=
    (e.subtypeRestr hU).open_source.mem_nhds (by rw [← heU]; exact mem_chart_source _ y)
  filter_upwards [hsrc] with p hp
  have hpt : e.subtypeRestr hU p ∈ (e.subtypeRestr hU).target := (e.subtypeRestr hU).map_source hp
  have hloc : (f ∘ Subtype.val) ∘ (e.subtypeRestr hU).symm =ᶠ[𝓝 (e.subtypeRestr hU p)] f ∘ e.symm := by
    filter_upwards [(e.subtypeRestr hU).open_target.mem_nhds hpt] with ζ hζ
    simp only [Function.comp_apply]
    rw [← e.subtypeRestr_symm_apply hU hζ]
    rfl
  show fderiv ℂ ((f ∘ Subtype.val) ∘ (chartAt (ComplexModel n) y).symm) (chartAt (ComplexModel n) y p) v =
    fderiv ℂ (f ∘ e.symm) (e p) v
  rw [heU, hloc.fderiv_eq]
  rfl

/-- **`𝓓` commutes with restriction to an open set**: `ι^*𝓓(𝔞) = 𝓓(ι^*𝔞)` for the inclusion `ι` of `U`. -/
theorem pullback_val_derivIdeal {𝔞 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    GermIdeal.pullback (m := n) (Subtype.val : U → M) (derivIdeal 𝔞) =
      derivIdeal (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞) := by
  have hval : ∀ p : U, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (Subtype.val : U → M) p :=
    fun p => (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) p).mdifferentiableAt (by simp)
  have hvalev : ∀ {y : U}, ∀ᶠ w in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (Subtype.val : U → M) w := Eventually.of_forall hval
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg =>
    DerivativeIdealInvariance.derivIdeal_pullback_le hval h𝔞 y g hg⟩)
  have hpb : ∀ {b : M → ℂ}, 𝔞.mem (y : M) b → (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞).mem y
      (b ∘ Subtype.val) := fun {b} hb =>
    RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔞.mem (y : M) a ∧ s = a ∘ Subtype.val)
        ⟨b, hb, rfl⟩ (HadamardBridge.holomorphicAt_comp_map hvalev (h𝔞 _ _ hb)))
  have hpbhol : ∀ x g, (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg).holomorphicAt
  refine IdealOrderArithmetic.mem_derivIdeal_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
    (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg))
  rintro s ⟨a, ha, rfl⟩
  obtain ⟨-, K, t, c, ht, hc, hsum⟩ := IdealOrderArithmetic.mem_derivIdeal_iff.mp ha
  have hcomp : (a ∘ Subtype.val) =ᶠ[𝓝 y] fun p => ∑ k, (c k ∘ Subtype.val) p * (t k ∘ Subtype.val) p :=
    (hval y).continuousAt.eventually hsum
  refine DerivativeIdeal.isInSpanAt_congr ?_ hcomp.symm
  refine RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun k _ => ?_
  refine RelativePrincipalizationSpan.IsInSpanAt.mul_left (HadamardBridge.holomorphicAt_comp_map hvalev (hc k)) ?_
  rcases ht k with htk | ⟨e, w, f, hx, hf, htk⟩
  · exact le_derivIdeal hpbhol y _ (hpb htk)
  · -- `∂_w^e f = ∑ⱼ cⱼ ∂ⱼ f` in the preferred chart at `ι y`, and those restrict to chart derivatives on `U`
    set e₀ := complexChartAt (n := n) (y : M) with he₀
    have hy₀ : (y : M) ∈ e₀.val.source := mem_complexChartAt_source _
    have hfhol : HolomorphicAt n f (id (y : M)) := h𝔞 _ _ hf
    have hchain := DerivativeIdealInvariance.chartDeriv_comp_eventuallyEq_sum e₀ e (φ := id)
      (fun p => mdifferentiableAt_id) hx hy₀ hfhol w
    have hchain' : (t k ∘ Subtype.val) =ᶠ[𝓝 y] fun p =>
        ∑ j, (DerivativeIdealInvariance.chainCoeff e₀ e id w j ∘ Subtype.val) p *
          chartDeriv (complexChartAt (n := n) y) (EuclideanSpace.single j 1) (f ∘ Subtype.val) p := by
      have h1 := (hval y).continuousAt.eventually hchain
      filter_upwards [h1, eventually_all.mpr fun j => chartDeriv_comp_val (n := n) U y f (EuclideanSpace.single j 1)]
        with p hp hp'
      simp only [Function.comp_apply, htk] at hp ⊢
      rw [show (f ∘ id) = f from rfl] at hp
      rw [hp]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hp' j]
      rfl
    refine DerivativeIdeal.isInSpanAt_congr ?_ hchain'.symm
    refine RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun j _ => ?_
    have hcoef : HolomorphicAt n (DerivativeIdealInvariance.chainCoeff e₀ e id w j ∘ Subtype.val) y :=
      HadamardBridge.holomorphicAt_comp_map hvalev
        (DerivativeIdealInvariance.holomorphicAt_chainCoeff e₀ e (fun p => mdifferentiableAt_id) hx hy₀ w j)
    have hgen : DerivGen (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞) y
        (chartDeriv (complexChartAt (n := n) y) (EuclideanSpace.single j 1) (f ∘ Subtype.val)) :=
      Or.inr ⟨complexChartAt (n := n) y, _, f ∘ Subtype.val, mem_complexChartAt_source y, hpb hf, rfl⟩
    exact IdealOrderArithmetic.isInSpanAt_mul_of_mem hgen hcoef
      (holomorphicAt_chartDeriv (mem_complexChartAt_source y) (HadamardBridge.holomorphicAt_comp_map hvalev (h𝔞 _ _ hf)))

/-- **`𝓓^j` commutes with restriction to an open set.** -/
theorem pullback_val_iterDerivIdeal {𝔞 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∀ j : ℕ, GermIdeal.pullback (m := n) (Subtype.val : U → M) (iterDerivIdeal 𝔞 j) =
      iterDerivIdeal (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞) j
  | 0 => rfl
  | j + 1 => by
    rw [iterDerivIdeal_succ, iterDerivIdeal_succ, pullback_val_derivIdeal U (holomorphicAt_of_mem_iterDerivIdeal h𝔞 j),
      pullback_val_iterDerivIdeal h𝔞 j]

/-- **`𝓗` commutes with restriction to an open set** (`le:etale2/3` for open inclusions). -/
theorem pullback_val_homogenizedIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ) :
    GermIdeal.pullback (m := n) (Subtype.val : U → M) (homogenizedIdeal 𝔞 μ) =
      homogenizedIdeal (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞) μ :=
  pullback_homogenizedIdeal_of_iterDeriv contMDiff_subtype_val h𝔞
    (pullback_val_iterDerivIdeal U (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞)) hμ

/-- **`𝓒` commutes with restriction to an open set** (`le:etale2/3` for open inclusions). -/
theorem pullback_val_coeffMarked (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback (Subtype.val : U → M) (coeffMarked 𝔪) =
      coeffMarked (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) :=
  pullback_coeffMarked_of_iterDeriv contMDiff_subtype_val 𝔪 h𝔞
    (pullback_val_iterDerivIdeal U (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞)) hd

/-- **`𝓗` commutes with restriction to an open set**, marked form. -/
theorem pullback_val_homMarked (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback (Subtype.val : U → M) (homMarked 𝔪) =
      homMarked (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) :=
  pullback_homMarked_of_iterDeriv contMDiff_subtype_val 𝔪 h𝔞
    (pullback_val_iterDerivIdeal U (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞)) hd

end OpenRestriction

end

end Hironaka.HomogenizedEtale
