import Hironaka.Analytic.NumericalRestrictedVolume
import Hironaka.Analytic.ClosedFormPullback
import Hironaka.Analytic.HolomorphicDDC
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Analytic.AdmissibleCurrentFormPositivity

set_option autoImplicit false

/-!
# Transporting regular patches across a local biholomorphism

Source: CT22, Lemma 4.3 (first inequality: "identify absolutely continuous masses
through the biholomorphism `W̃ \ E ≅ W \ C`"); blueprint `ana:rv-birational-blowup`.

Let `g : Z → Y` be holomorphic, `W ⊆ Y` and `W̃ ⊆ Z` subvarieties of the same dimension
which correspond under `g` on an open set `O` (`u ∈ W̃ ↔ g u ∈ W` for `u ∈ O`), and
`P` a regular patch of `W` with parameter `w₀` over `g z`, where `z ∈ O` is not
exceptional.  Write `F = φ_{P} ∘ g ∘ φ_z⁻¹` for the chart expression of `g`
(`φ_z` the preferred chart at `z`, `φ_P` the one at the centre of `P`); it is a local
biholomorphism at `φ_z z`.  Put `Φ' = τ ∘ Φ_P ∘ F` with `τ` the translation by `-(w₀, 0)`.
This is a flattening of `W̃` at `z`, so it defines a regular patch `Q` with
`g (Q (w - w₀)) = P w` for `w` near `w₀`.  Its parametrization is
`F⁻¹ ∘ γ_P ∘ (· + w₀)`, so `γ_P = F ∘ γ_Q ∘ (· - w₀)` near `w₀`, and by the chain rule
the restriction of `g^*β` along `γ_Q` equals the restriction of `β` along `γ_P`, for
smooth forms `β` (`SmoothRealForm.pullback_coeff`) and for `ddᶜ` of smooth functions
(`HolomorphicDDC.smoothDDC_comp`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka

namespace ClosedIrreducibleAnalyticSubvariety

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The same subvariety, with its dimension field replaced by a propositionally equal
number (so that parameter spaces of patches agree definitionally). -/
def withDim (V : ClosedIrreducibleAnalyticSubvariety n M) (k : ℕ) (h : V.dim = k) :
    ClosedIrreducibleAnalyticSubvariety n M where
  carrier := V.carrier
  isClosed_carrier := V.isClosed_carrier
  irreducible_carrier := V.irreducible_carrier
  dim := k
  dim_le := h ▸ V.dim_le
  regularLocus_nonempty := h ▸ V.regularLocus_nonempty

@[simp] theorem withDim_carrier (V : ClosedIrreducibleAnalyticSubvariety n M) (k : ℕ)
    (h : V.dim = k) : (V.withDim k h).carrier = V.carrier := rfl

@[simp] theorem withDim_dim (V : ClosedIrreducibleAnalyticSubvariety n M) (k : ℕ)
    (h : V.dim = k) : (V.withDim k h).dim = k := rfl

theorem withDim_eq (V : ClosedIrreducibleAnalyticSubvariety n M) (k : ℕ) (h : V.dim = k) :
    V.withDim k h = V := by
  cases V
  subst h
  rfl

end ClosedIrreducibleAnalyticSubvariety

namespace RegularPatchPullback

open Hironaka.BlowupSequences Hironaka.NumericalRestrictedVolume

noncomputable section

section Planar

variable {n : ℕ}

theorem planeInclusion_add (k n : ℕ) (a b : ComplexModel k) :
    planeInclusion k n (a + b) = planeInclusion k n a + planeInclusion k n b :=
  (AdmissibleCurrentFormPositivity.planeInclusionCLM k n).map_add a b

theorem planeInclusion_mem_complexCoordinatePlane (k n : ℕ) (w : ComplexModel k) :
    planeInclusion k n w ∈ complexCoordinatePlane n k := by
  intro i hi
  simp [planeInclusion, not_lt.mpr hi]

theorem sub_planeInclusion_mem_iff {k : ℕ} {x : ComplexModel n} (a : ComplexModel k) :
    x - planeInclusion k n a ∈ complexCoordinatePlane n k ↔
      x ∈ complexCoordinatePlane n k := by
  simp only [complexCoordinatePlane, mem_ofPred_eq]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  simp [planeInclusion, not_lt.mpr hi]

/-- The same local holomorphic equivalence, recentred at another point of its source. -/
def recenter {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p) (q : ComplexModel n)
    (hq : q ∈ Φ.source) : LocalHolomorphicEquivAt (n := n) q :=
  { Φ with center_mem_source := hq }

/-- Post-composition of a local holomorphic equivalence with the translation `x ↦ x - a`. -/
def subConst {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (a : ComplexModel n) : LocalHolomorphicEquivAt (n := n) p where
  source := Φ.source
  target := (fun x => x + a) ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source
  isOpen_target := Φ.isOpen_target.preimage (continuous_add_const a)
  center_mem_source := Φ.center_mem_source
  toFun := fun u => Φ.toFun u - a
  invFun := fun x => Φ.invFun (x + a)
  toFun_holomorphic := Φ.toFun_holomorphic.sub_const a
  invFun_holomorphic :=
    Φ.invFun_holomorphic.comp (differentiableOn_id.add_const a) (fun _ hx => hx)
  mapsTo_toFun := fun u hu => by
    simpa only [mem_preimage, sub_add_cancel] using Φ.mapsTo_toFun hu
  mapsTo_invFun := fun _ hx => Φ.mapsTo_invFun hx
  left_inv := fun u hu => by
    simp only [sub_add_cancel]
    exact Φ.left_inv u hu
  right_inv := fun x hx => by
    simp only [Φ.right_inv _ hx, add_sub_cancel_right]

/-- Chain rule for `p = F ∘ q ∘ (· - w₀)` near `w`. -/
theorem fderiv_eq_comp_of_eventuallyEq {k : ℕ} {p q : ComplexModel k → ComplexModel n}
    {F : ComplexModel n → ComplexModel n} {w w₀ : ComplexModel k}
    (heq : p =ᶠ[𝓝 w] fun x => F (q (x - w₀)))
    (hF : DifferentiableAt ℝ F (q (w - w₀))) (hq : DifferentiableAt ℝ q (w - w₀)) :
    fderiv ℝ p w = (fderiv ℝ F (q (w - w₀))).comp (fderiv ℝ q (w - w₀)) := by
  rw [heq.fderiv_eq]
  have hsub : DifferentiableAt ℝ (fun x => q (x - w₀)) w :=
    (differentiableAt_comp_sub w₀).mpr hq
  rw [show (fun x => F (q (x - w₀))) = F ∘ (fun x => q (x - w₀)) from rfl,
    fderiv_comp w hF hsub, fderiv_comp_sub w₀]

theorem compContinuousLinearMap_comp' {ι : Type*} [Fintype ι] {k m : ℕ}
    (f : (ComplexModel n) [⋀^ι]→L[ℝ] ℝ) (A : ComplexModel m →L[ℝ] ComplexModel n)
    (B : ComplexModel k →L[ℝ] ComplexModel m) :
    f.compContinuousLinearMap (A.comp B) =
      (f.compContinuousLinearMap A).compContinuousLinearMap B := by
  ext v
  rfl

end Planar

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- At a non-exceptional point, the chart expression of `g` in the preferred chart at `z`
and any atlas chart around `g z` has injective complex derivative. -/
theorem injective_fderiv_chartExpr {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ exceptionalLocus n g) (d : ComplexChart n Y) (hgz : g z ∈ d.val.source) :
    Function.Injective (fderiv ℂ (fun u => d.val (g ((complexChartAt (n := n) z).val.symm u)))
      ((complexChartAt (n := n) z).val z)) := by
  set I := 𝓘(ℂ, ComplexModel n) with hI
  set e := (complexChartAt (n := n) z).val with he_def
  have hze : z ∈ e.source := mem_complexChartAt_source z
  have hez : e.symm (e z) = z := e.left_inv hze
  have he : e.MDifferentiable I I := mdifferentiable_of_mem_atlas (complexChartAt (n := n) z).2
  have hd : d.val.MDifferentiable I I := mdifferentiable_of_mem_atlas d.2
  have h1 : MDifferentiableAt I I e.symm (e z) := he.mdifferentiableAt_symm (e.map_source hze)
  have h2 : MDifferentiableAt I I g (e.symm (e z)) := (hg _).mdifferentiableAt (by simp)
  have h3 : MDifferentiableAt I I d.val (g (e.symm (e z))) :=
    hd.mdifferentiableAt (by rwa [hez])
  have hchain : mfderiv I I (d.val ∘ g ∘ e.symm) (e z) =
      (mfderiv I I d.val (g (e.symm (e z)))).comp
        ((mfderiv I I g (e.symm (e z))).comp (mfderiv I I e.symm (e z))) := by
    rw [mfderiv_comp (e z) h3 (h2.comp (e z) h1), Function.comp_apply,
      mfderiv_comp (e z) h2 h1]
    rfl
  have hbij : Function.Bijective (mfderiv I I g z) := by
    simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hz
  rw [show (fun u => d.val (g (e.symm u))) = d.val ∘ g ∘ e.symm from rfl,
    ← mfderiv_eq_fderiv, hchain]
  have hA : Function.Injective (mfderiv I I d.val (g (e.symm (e z)))) :=
    hd.mfderiv_injective (by rwa [hez])
  have hB : Function.Injective (mfderiv I I g (e.symm (e z))) := by
    rw [hez]; exact hbij.1
  have hC : Function.Injective (mfderiv I I e.symm (e z)) :=
    he.symm.mfderiv_injective (e.map_source hze)
  exact hA.comp (hB.comp hC)

/-- The transported patch `Q`, with flattening `(Φ_P ∘ Ψ) - (w₀, 0)`, from a local
holomorphic equivalence `Ψ` at `φ_z z` compatible with `P`. -/
def transportPatch {W : ClosedIrreducibleAnalyticSubvariety n Y}
    {Wt : ClosedIrreducibleAnalyticSubvariety n Z} (hdim : Wt.dim = W.dim)
    (P : RegularPatch W) {w₀ : ComplexModel W.dim} (hw₀ : w₀ ∈ P.parameterDomain)
    {z : Z} (hzW : z ∈ Wt.carrier)
    (Ψ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) z).val z))
    (hΨe : Ψ.source ⊆ (complexChartAt (n := n) z).val.target)
    (hΨz : Ψ.toFun ((complexChartAt (n := n) z).val z) = P.coordinateParametrization w₀)
    (hflat : ∀ {y : Z}, y ∈ (complexChartAt (n := n) z).val.source →
      (complexChartAt (n := n) z).val y ∈ Ψ.source →
      Ψ.toFun ((complexChartAt (n := n) z).val y) ∈ P.flattening.source →
      (y ∈ Wt.carrier ↔ P.flattening.toFun (Ψ.toFun ((complexChartAt (n := n) z).val y)) ∈
        complexCoordinatePlane n W.dim)) :
    RegularPatch (Wt.withDim W.dim hdim) where
  center := z
  center_mem := hzW
  flattening := subConst (Hironaka.RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ψ
      (recenter P.flattening _ (P.flattening.mapsTo_invFun hw₀)) hΨz)
      (planeInclusion W.dim n w₀)
  source_subset := fun _ hu => hΨe hu.1
  center_to_zero := by
    change P.flattening.toFun (Ψ.toFun _) - _ = 0
    rw [hΨz]
    exact sub_eq_zero.mpr (P.flattening.right_inv _ hw₀)
  flattens := fun hy hyΘ => by
    change _ ∈ Wt.carrier ↔ P.flattening.toFun (Ψ.toFun _) - planeInclusion W.dim n w₀ ∈
      complexCoordinatePlane n W.dim
    rw [sub_planeInclusion_mem_iff]
    exact hflat hy hyΘ.1 hyΘ.2

section TransportPatch

variable {W : ClosedIrreducibleAnalyticSubvariety n Y}
    {Wt : ClosedIrreducibleAnalyticSubvariety n Z} {hdim : Wt.dim = W.dim}
    {P : RegularPatch W} {w₀ : ComplexModel W.dim} {hw₀ : w₀ ∈ P.parameterDomain}
    {z : Z} {hzW : z ∈ Wt.carrier}
    {Ψ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) z).val z)}
    {hΨe : Ψ.source ⊆ (complexChartAt (n := n) z).val.target}
    {hΨz : Ψ.toFun ((complexChartAt (n := n) z).val z) = P.coordinateParametrization w₀}
    {hflat : ∀ {y : Z}, y ∈ (complexChartAt (n := n) z).val.source →
      (complexChartAt (n := n) z).val y ∈ Ψ.source →
      Ψ.toFun ((complexChartAt (n := n) z).val y) ∈ P.flattening.source →
      (y ∈ Wt.carrier ↔ P.flattening.toFun (Ψ.toFun ((complexChartAt (n := n) z).val y)) ∈
        complexCoordinatePlane n W.dim)}

theorem transportPatch_coordinateParametrization (v : ComplexModel W.dim) :
    (transportPatch hdim P hw₀ hzW Ψ hΨe hΨz hflat).coordinateParametrization v =
      Ψ.invFun (P.coordinateParametrization (v + w₀)) := by
  change Ψ.invFun (P.flattening.invFun
    (planeInclusion W.dim n v + planeInclusion W.dim n w₀)) = _
  rw [← planeInclusion_add]
  rfl

theorem mem_transportPatch_parameterDomain {v : ComplexModel W.dim}
    (hv : v + w₀ ∈ P.parameterDomain)
    (hv' : P.coordinateParametrization (v + w₀) ∈ Ψ.target) :
    v ∈ (transportPatch hdim P hw₀ hzW Ψ hΨe hΨz hflat).parameterDomain := by
  change planeInclusion W.dim n v + planeInclusion W.dim n w₀ ∈
    P.flattening.target ∩ P.flattening.invFun ⁻¹' Ψ.target
  rw [← planeInclusion_add]
  exact ⟨hv, hv'⟩

end TransportPatch

/-- **Patch transport.**  Near a non-exceptional point `z` over the parameter `w₀` of a
regular patch `P` of `W`, there is a regular patch `Q` of `W̃` centred at `z` with
`g (Q (w - w₀)) = P w`, along which restrictions of pulled-back forms and of `ddᶜ` of
composed smooth functions agree with the restrictions along `P`. -/
theorem exists_regularPatch_pullback {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {W : ClosedIrreducibleAnalyticSubvariety n Y} {Wt : ClosedIrreducibleAnalyticSubvariety n Z}
    (hdim : Wt.dim = W.dim) {O : Set Z} (hO : IsOpen O)
    (hWO : ∀ x ∈ O, x ∈ Wt.carrier ↔ g x ∈ W.carrier)
    (P : RegularPatch W) {w₀ : ComplexModel W.dim} (hw₀ : w₀ ∈ P.parameterDomain)
    {z : Z} (hzO : z ∈ O) (hz : z ∉ exceptionalLocus n g) (hgz : g z = P.toManifold w₀) :
    ∃ (Q : RegularPatch (Wt.withDim W.dim hdim)) (r : ℝ), 0 < r ∧
      ∀ w ∈ Metric.ball w₀ r,
        w ∈ P.parameterDomain ∧ w - w₀ ∈ Q.parameterDomain ∧
        Q.toManifold (w - w₀) ∈ O ∧ Q.toManifold (w - w₀) ∉ exceptionalLocus n g ∧
        g (Q.toManifold (w - w₀)) = P.toManifold w ∧
        (∀ β : ClosedRealOneOneForm n Y,
          ((ClosedRealOneOneForm.pullback hg β).val.coeff (complexChartAt (n := n) Q.center)
              (Q.coordinateParametrization (w - w₀))).compContinuousLinearMap
            (fderiv ℝ Q.coordinateParametrization (w - w₀)) =
          (β.val.coeff (complexChartAt (n := n) P.center)
              (P.coordinateParametrization w)).compContinuousLinearMap
            (fderiv ℝ P.coordinateParametrization w)) ∧
        (∀ v : Y → ℝ,
          (∀ᶠ y in 𝓝 (P.coordinateParametrization w),
            ContDiffAt ℝ ∞ (fun y => v ((complexChartAt (n := n) P.center).val.symm y)) y) →
          (smoothDDC (fun y => v (g ((complexChartAt (n := n) Q.center).val.symm y)))
              (Q.coordinateParametrization (w - w₀))).compContinuousLinearMap
            (fderiv ℝ Q.coordinateParametrization (w - w₀)) =
          (smoothDDC (fun y => v ((complexChartAt (n := n) P.center).val.symm y))
              (P.coordinateParametrization w)).compContinuousLinearMap
            (fderiv ℝ P.coordinateParametrization w)) := by
  classical
  set F : ComplexModel n → ComplexModel n :=
    fun u => (complexChartAt (n := n) P.center).val (g ((complexChartAt (n := n) z).val.symm u))
    with hF
  have hExc : IsOpen (exceptionalLocus n g)ᶜ :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hg
  set N : Set (ComplexModel n) := (complexChartAt (n := n) z).val.target ∩
    (complexChartAt (n := n) z).val.symm ⁻¹'
      ((O ∩ (exceptionalLocus n g)ᶜ) ∩ g ⁻¹' (complexChartAt (n := n) P.center).val.source)
    with hN
  have hNo : IsOpen N :=
    (complexChartAt (n := n) z).val.continuousOn_symm.isOpen_inter_preimage
      (complexChartAt (n := n) z).val.open_target
      ((hO.inter hExc).inter
        (hg.continuous.isOpen_preimage _ (complexChartAt (n := n) P.center).val.open_source))
  have hze : z ∈ (complexChartAt (n := n) z).val.source := mem_complexChartAt_source z
  have hpw₀ : P.coordinateParametrization w₀ ∈ P.flattening.source :=
    P.flattening.mapsTo_invFun hw₀
  have hpw₀d : P.coordinateParametrization w₀ ∈ (complexChartAt (n := n) P.center).val.target :=
    P.source_subset hpw₀
  have hgzd : g z ∈ (complexChartAt (n := n) P.center).val.source := by
    rw [hgz]; exact (complexChartAt (n := n) P.center).val.map_target hpw₀d
  have hdgz : (complexChartAt (n := n) P.center).val (g z) = P.coordinateParametrization w₀ := by
    rw [hgz]; exact (complexChartAt (n := n) P.center).val.right_inv hpw₀d
  have hzN : (complexChartAt (n := n) z).val z ∈ N :=
    ⟨(complexChartAt (n := n) z).val.map_source hze, by
      rw [mem_preimage, (complexChartAt (n := n) z).val.left_inv hze]
      exact ⟨⟨hzO, hz⟩, hgzd⟩⟩
  have hNdom : N ⊆ HolomorphicMaps.coordinateDomain g (complexChartAt (n := n) z)
      (complexChartAt (n := n) P.center) := fun u hu => ⟨hu.1, hu.2.2⟩
  have hFsmooth : ContDiffOn ℂ ∞ F N :=
    (HolomorphicMaps.coordinateMap_contDiffOn hg _ _).mono hNdom
  have hFN : DifferentiableOn ℂ F N := hFsmooth.differentiableOn (by simp)
  have hinj := injective_fderiv_chartExpr hg hz (complexChartAt (n := n) P.center) hgzd
  obtain ⟨Ψ, hΨN, hΨF, -⟩ := exists_localHolomorphicEquivAt hNo hzN hFN hinj
  have hFz : F ((complexChartAt (n := n) z).val z) = P.coordinateParametrization w₀ := by
    simp only [hF, (complexChartAt (n := n) z).val.left_inv hze, hdgz]
  have hPW : P.toManifold w₀ ∈ W.carrier := by
    have hy : P.toManifold w₀ ∈ (complexChartAt (n := n) P.center).val.source :=
      (complexChartAt (n := n) P.center).val.map_target hpw₀d
    have hdy : (complexChartAt (n := n) P.center).val (P.toManifold w₀) =
        P.coordinateParametrization w₀ :=
      (complexChartAt (n := n) P.center).val.right_inv hpw₀d
    refine (P.flattens hy (by rw [hdy]; exact hpw₀)).mpr ?_
    rw [hdy]
    change P.flattening.toFun (P.flattening.invFun _) ∈ _
    rw [P.flattening.right_inv _ hw₀]
    exact planeInclusion_mem_complexCoordinatePlane _ _ _
  have hzW : z ∈ Wt.carrier := (hWO z hzO).mpr (hgz ▸ hPW)
  have hΨe : Ψ.source ⊆ (complexChartAt (n := n) z).val.target := fun u hu => (hΨN hu).1
  have hΨz : Ψ.toFun ((complexChartAt (n := n) z).val z) = P.coordinateParametrization w₀ := by
    rw [hΨF]; exact hFz
  have hflat : ∀ {y : Z}, y ∈ (complexChartAt (n := n) z).val.source →
      (complexChartAt (n := n) z).val y ∈ Ψ.source →
      Ψ.toFun ((complexChartAt (n := n) z).val y) ∈ P.flattening.source →
      (y ∈ Wt.carrier ↔ P.flattening.toFun (Ψ.toFun ((complexChartAt (n := n) z).val y)) ∈
        complexCoordinatePlane n W.dim) := by
    intro y hy hyΨ hyΦ
    have hyN := (hΨN hyΨ).2
    rw [mem_preimage, (complexChartAt (n := n) z).val.left_inv hy] at hyN
    have hFy : Ψ.toFun ((complexChartAt (n := n) z).val y) =
        (complexChartAt (n := n) P.center).val (g y) := by
      rw [hΨF]; simp only [hF, (complexChartAt (n := n) z).val.left_inv hy]
    rw [hFy] at hyΦ ⊢
    rw [hWO y hyN.1.1]
    exact P.flattens hyN.2 hyΦ
  -- the set of good parameters
  set S : Set (ComplexModel W.dim) :=
    P.parameterDomain ∩ P.coordinateParametrization ⁻¹' Ψ.target with hS
  have hPcont : ContinuousOn P.coordinateParametrization P.parameterDomain := fun w hw =>
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      P hw).continuousAt.continuousWithinAt
  have hSo : IsOpen S := hPcont.isOpen_inter_preimage
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P)
    Ψ.isOpen_target
  have hw₀S : w₀ ∈ S := ⟨hw₀, by rw [mem_preimage, ← hΨz]; exact Ψ.mapsTo_toFun Ψ.center_mem_source⟩
  set Q := transportPatch hdim P hw₀ hzW Ψ hΨe hΨz hflat with hQ
  have hQp : ∀ w : ComplexModel W.dim, Q.coordinateParametrization (w - w₀) =
      Ψ.invFun (P.coordinateParametrization w) := fun w => by
    rw [hQ, transportPatch_coordinateParametrization, sub_add_cancel]
  have hQd : ∀ w ∈ S, w - w₀ ∈ Q.parameterDomain := fun w hw =>
    mem_transportPatch_parameterDomain (by rw [sub_add_cancel]; exact hw.1)
      (by rw [sub_add_cancel]; exact hw.2)
  have huN : ∀ w ∈ S, Q.coordinateParametrization (w - w₀) ∈ N := fun w hw => by
    rw [hQp]; exact hΨN (Ψ.mapsTo_invFun hw.2)
  have hFu : ∀ w ∈ S, F (Q.coordinateParametrization (w - w₀)) =
      P.coordinateParametrization w := fun w hw => by
    rw [hQp, ← hΨF]; exact Ψ.right_inv _ hw.2
  have hchain : ∀ w ∈ S, fderiv ℝ P.coordinateParametrization w =
      (fderiv ℝ F (Q.coordinateParametrization (w - w₀))).comp
        (fderiv ℝ Q.coordinateParametrization (w - w₀)) := fun w hw => by
    have heq : P.coordinateParametrization =ᶠ[𝓝 w]
        fun x => F (Q.coordinateParametrization (x - w₀)) := by
      filter_upwards [hSo.mem_nhds hw] with x hx
      exact (hFu x hx).symm
    exact fderiv_eq_comp_of_eventuallyEq heq
      (((hFsmooth.contDiffAt (hNo.mem_nhds (huN w hw))).differentiableAt
        (by simp)).restrictScalars ℝ)
      ((AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
        Q (hQd w hw)).restrictScalars ℝ)
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp hSo w₀ hw₀S
  refine ⟨Q, r, hr, fun w hw => ?_⟩
  have hwS : w ∈ S := hrS hw
  have hman : Q.toManifold (w - w₀) =
      (complexChartAt (n := n) z).val.symm (Q.coordinateParametrization (w - w₀)) := rfl
  refine ⟨hwS.1, hQd w hwS, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hman]; exact (huN w hwS).2.1.1
  · rw [hman]; exact (huN w hwS).2.1.2
  · rw [hman]
    change _ = (complexChartAt (n := n) P.center).val.symm (P.coordinateParametrization w)
    rw [← hFu w hwS]
    exact ((complexChartAt (n := n) P.center).val.left_inv (huN w hwS).2.2).symm
  · intro β
    change ((ClosedRealOneOneForm.pullback hg β).val.coeff (complexChartAt (n := n) z)
      (Q.coordinateParametrization (w - w₀))).compContinuousLinearMap
        (fderiv ℝ Q.coordinateParametrization (w - w₀)) = _
    rw [ClosedRealOneOneForm.pullback_val,
      SmoothRealForm.pullback_coeff hg β.val _ _ (hNdom (huN w hwS))]
    change ((β.val.coeff _ (F (Q.coordinateParametrization (w - w₀)))).compContinuousLinearMap
      (fderiv ℝ F (Q.coordinateParametrization (w - w₀)))).compContinuousLinearMap _ = _
    rw [hFu w hwS, hchain w hwS]
    exact (compContinuousLinearMap_comp' _ _ _).symm
  · intro v hv
    set ρ : ComplexModel n → ℝ :=
      fun y => v ((complexChartAt (n := n) P.center).val.symm y) with hρ
    have hqN := huN w hwS
    have heqv : (fun y => v (g ((complexChartAt (n := n) z).val.symm y))) =ᶠ[𝓝
        (Q.coordinateParametrization (w - w₀))] fun y => ρ (F y) := by
      filter_upwards [hNo.mem_nhds hqN] with y hy
      simp only [hρ, hF, (complexChartAt (n := n) P.center).val.left_inv hy.2.2]
    have hρV : ContDiffOn ℝ ∞ ρ (interior {y | ContDiffAt ℝ ∞ ρ y}) := fun y hy =>
      (show ContDiffAt ℝ ∞ ρ y from interior_subset hy).contDiffWithinAt
    have hPV : P.coordinateParametrization w ∈ interior {y | ContDiffAt ℝ ∞ ρ y} :=
      mem_interior_iff_mem_nhds.mpr hv
    have hUo : IsOpen (N ∩ F ⁻¹' interior {y | ContDiffAt ℝ ∞ ρ y}) :=
      hFN.continuousOn.isOpen_inter_preimage hNo isOpen_interior
    have hqU : Q.coordinateParametrization (w - w₀) ∈
        N ∩ F ⁻¹' interior {y | ContDiffAt ℝ ∞ ρ y} :=
      ⟨hqN, by rw [mem_preimage, hFu w hwS]; exact hPV⟩
    change (smoothDDC (fun y => v (g ((complexChartAt (n := n) z).val.symm y)))
      (Q.coordinateParametrization (w - w₀))).compContinuousLinearMap
        (fderiv ℝ Q.coordinateParametrization (w - w₀)) = _
    rw [smoothDDC_congr heqv, HolomorphicDDC.smoothDDC_comp hUo isOpen_interior
      (hFsmooth.mono inter_subset_left) hρV (fun y hy => hy.2) hqU, hFu w hwS, hchain w hwS]
    exact (compContinuousLinearMap_comp' _ _ _).symm

end

end RegularPatchPullback

end Hironaka
