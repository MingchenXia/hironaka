import Hironaka.Blowup.RegularPatchPullback
import Hironaka.Analytic.RegularPatchNeighborhood

set_option autoImplicit false

/-!
# Transporting regular patches DOWN a local biholomorphism

Source: CT22, Lemma 4.3 (the identification "`W̃ ∖ E ≅ W ∖ g(E)` carries the absolutely
continuous restricted mass"); blueprint `ana:rv-birational-blowup`.

`Hironaka.RegularPatchPullback.exists_regularPatch_pullback` transports a regular patch of
`W` upstairs, to a patch of the strict transform `W̃` near a prescribed non-exceptional
point.  This module is the converse, and it is the direction the mass identity ACROSS the
centre consumes: a regular patch `Q` of `W̃`, read at a parameter `v₀` whose point
`z = Q(v₀)` is not exceptional, is pushed to a regular patch `P` of `W` centred at `g z`,
with `g (Q v) = P (v - v₀)` for `v` near `v₀`.

Write `F = φ_{g z} ∘ g ∘ φ_{Q.center}⁻¹` for the chart expression of `g`, read in the
preferred chart at the CENTRE of `Q` (not at `z`) and the preferred chart at `g z`.  Since
`z` is not exceptional, `F` is a local biholomorphism at `u₀ = γ_Q(v₀)`, represented by
`Ψ`.  The flattening of `W` at `g z` is `(Φ_Q ∘ Ψ⁻¹) - (v₀, 0)`, so

* `γ_P(v - v₀) = Ψ(γ_Q v) = F(γ_Q v)`, hence `P(v - v₀) = g (Q v)`;
* by the chain rule the restriction of a smooth form `β` along `γ_P` equals the
  restriction of `g^*β` along `γ_Q`, and likewise for `ddᶜ` of smooth functions composed
  with `g` (`SmoothRealForm.pullback_coeff`, `HolomorphicDDC.smoothDDC_comp`).

The two identities are stated exactly in the shape consumed by
`Hironaka.RestrictedVolumePullbackLower.patchDensity_le_pullback`, with the roles of the
two patches exchanged.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka

namespace RegularPatchPushforward

open Hironaka.BlowupSequences Hironaka.NumericalRestrictedVolume
  Hironaka.ClosedIrreducibleAnalyticSubvariety Hironaka.RegularPatchPullback

noncomputable section

variable {n : ℕ}

/-- The inverse of a local holomorphic equivalence, centred at a point of its target. -/
def symmAt {p q : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p)
    (hq : q ∈ Ψ.target) : LocalHolomorphicEquivAt (n := n) q where
  source := Ψ.target
  target := Ψ.source
  isOpen_source := Ψ.isOpen_target
  isOpen_target := Ψ.isOpen_source
  center_mem_source := hq
  toFun := Ψ.invFun
  invFun := Ψ.toFun
  toFun_holomorphic := Ψ.invFun_holomorphic
  invFun_holomorphic := Ψ.toFun_holomorphic
  mapsTo_toFun := Ψ.mapsTo_invFun
  mapsTo_invFun := Ψ.mapsTo_toFun
  left_inv := Ψ.right_inv
  right_inv := Ψ.left_inv

/-- Chain rule for `p ∘ (· - w₀) = F ∘ q` near `w`. -/
theorem fderiv_eq_comp_of_eventuallyEq' {k : ℕ} {p q : ComplexModel k → ComplexModel n}
    {F : ComplexModel n → ComplexModel n} {w w₀ : ComplexModel k}
    (heq : p =ᶠ[𝓝 (w - w₀)] fun x => F (q (x + w₀)))
    (hF : DifferentiableAt ℝ F (q w)) (hq : DifferentiableAt ℝ q w) :
    fderiv ℝ p (w - w₀) = (fderiv ℝ F (q w)).comp (fderiv ℝ q w) := by
  have hadd : (w - w₀) + w₀ = w := sub_add_cancel w w₀
  have hq' : DifferentiableAt ℝ (fun x => q (x + w₀)) (w - w₀) :=
    (differentiableAt_comp_add_right w₀).mpr (by rw [hadd]; exact hq)
  have hF' : DifferentiableAt ℝ F (q ((w - w₀) + w₀)) := by rw [hadd]; exact hF
  rw [heq.fderiv_eq,
    show (fun x => F (q (x + w₀))) = F ∘ (fun x => q (x + w₀)) from rfl,
    fderiv_comp (w - w₀) hF' hq', fderiv_comp_add_right w₀, hadd]

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- At a non-exceptional point, the chart expression of `g` in ANY atlas chart around `z`
and any atlas chart around `g z` has injective complex derivative.  This is
`RegularPatchPullback.injective_fderiv_chartExpr` with the source chart freed from the
preferred chart at `z`. -/
theorem injective_fderiv_chartExpr' {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ exceptionalLocus n g) (e : ComplexChart n Z) (hze : z ∈ e.val.source)
    (d : ComplexChart n Y) (hgz : g z ∈ d.val.source) :
    Function.Injective (fderiv ℂ (fun u => d.val (g (e.val.symm u))) (e.val z)) := by
  set I := 𝓘(ℂ, ComplexModel n) with hI
  have hez : e.val.symm (e.val z) = z := e.val.left_inv hze
  have he : e.val.MDifferentiable I I := mdifferentiable_of_mem_atlas e.2
  have hd : d.val.MDifferentiable I I := mdifferentiable_of_mem_atlas d.2
  have h1 : MDifferentiableAt I I e.val.symm (e.val z) := he.mdifferentiableAt_symm
    (e.val.map_source hze)
  have h2 : MDifferentiableAt I I g (e.val.symm (e.val z)) := (hg _).mdifferentiableAt (by simp)
  have h3 : MDifferentiableAt I I d.val (g (e.val.symm (e.val z))) :=
    hd.mdifferentiableAt (by rwa [hez])
  have hchain : mfderiv I I (d.val ∘ g ∘ e.val.symm) (e.val z) =
      (mfderiv I I d.val (g (e.val.symm (e.val z)))).comp
        ((mfderiv I I g (e.val.symm (e.val z))).comp (mfderiv I I e.val.symm (e.val z))) := by
    rw [mfderiv_comp (e.val z) h3 (h2.comp (e.val z) h1), Function.comp_apply,
      mfderiv_comp (e.val z) h2 h1]
    rfl
  have hbij : Function.Bijective (mfderiv I I g z) := by
    simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hz
  rw [show (fun u => d.val (g (e.val.symm u))) = d.val ∘ g ∘ e.val.symm from rfl,
    ← mfderiv_eq_fderiv, hchain]
  have hA : Function.Injective (mfderiv I I d.val (g (e.val.symm (e.val z)))) :=
    hd.mfderiv_injective (by rwa [hez])
  have hB : Function.Injective (mfderiv I I g (e.val.symm (e.val z))) := by
    rw [hez]; exact hbij.1
  have hC : Function.Injective (mfderiv I I e.val.symm (e.val z)) :=
    he.symm.mfderiv_injective (e.val.map_source hze)
  exact hA.comp (hB.comp hC)

/-- The pushed patch `P`, with flattening `(Φ_Q ∘ Ψ⁻¹) - (v₀, 0)`, from a local holomorphic
equivalence `Ψ` at `γ_Q(v₀)` carrying `γ_Q(v₀)` to `φ_{y₀} y₀`. -/
def pushPatch {W : ClosedIrreducibleAnalyticSubvariety n Y}
    {Wt : ClosedIrreducibleAnalyticSubvariety n Z} (hdim : Wt.dim = W.dim)
    (Q : RegularPatch (Wt.withDim W.dim hdim)) {v₀ : ComplexModel W.dim}
    (hv₀ : v₀ ∈ Q.parameterDomain) {y₀ : Y} (hy₀ : y₀ ∈ W.carrier)
    (Ψ : LocalHolomorphicEquivAt (n := n) (Q.coordinateParametrization v₀))
    (hmem : (complexChartAt (n := n) y₀).val y₀ ∈ Ψ.target)
    (hΨt : Ψ.target ⊆ (complexChartAt (n := n) y₀).val.target)
    (hΨz : Ψ.invFun ((complexChartAt (n := n) y₀).val y₀) = Q.coordinateParametrization v₀)
    (hflat : ∀ {y : Y}, y ∈ (complexChartAt (n := n) y₀).val.source →
      (complexChartAt (n := n) y₀).val y ∈ Ψ.target →
      Ψ.invFun ((complexChartAt (n := n) y₀).val y) ∈ Q.flattening.source →
      (y ∈ W.carrier ↔ Q.flattening.toFun (Ψ.invFun ((complexChartAt (n := n) y₀).val y)) ∈
        complexCoordinatePlane n W.dim)) :
    RegularPatch W where
  center := y₀
  center_mem := hy₀
  flattening :=
    subConst (Hironaka.RegularAtDimTransport.LocalHolomorphicEquivAt.comp (symmAt Ψ hmem)
        (recenter Q.flattening _ (Q.flattening.mapsTo_invFun hv₀)) hΨz)
      (planeInclusion W.dim n v₀)
  source_subset := fun _ hu => hΨt hu.1
  center_to_zero := by
    change Q.flattening.toFun (Ψ.invFun _) - _ = 0
    rw [hΨz]
    exact sub_eq_zero.mpr (Q.flattening.right_inv _ hv₀)
  flattens := fun hy hyΘ => by
    change _ ∈ W.carrier ↔ Q.flattening.toFun (Ψ.invFun _) - planeInclusion W.dim n v₀ ∈
      complexCoordinatePlane n W.dim
    rw [sub_planeInclusion_mem_iff]
    exact hflat hy hyΘ.1 hyΘ.2

section PushPatch

variable {W : ClosedIrreducibleAnalyticSubvariety n Y}
  {Wt : ClosedIrreducibleAnalyticSubvariety n Z} {hdim : Wt.dim = W.dim}
  {Q : RegularPatch (Wt.withDim W.dim hdim)} {v₀ : ComplexModel W.dim}
  {hv₀ : v₀ ∈ Q.parameterDomain} {y₀ : Y} {hy₀ : y₀ ∈ W.carrier}
  {Ψ : LocalHolomorphicEquivAt (n := n) (Q.coordinateParametrization v₀)}
  {hmem : (complexChartAt (n := n) y₀).val y₀ ∈ Ψ.target}
  {hΨt : Ψ.target ⊆ (complexChartAt (n := n) y₀).val.target}
  {hΨz : Ψ.invFun ((complexChartAt (n := n) y₀).val y₀) = Q.coordinateParametrization v₀}
  {hflat : ∀ {y : Y}, y ∈ (complexChartAt (n := n) y₀).val.source →
    (complexChartAt (n := n) y₀).val y ∈ Ψ.target →
    Ψ.invFun ((complexChartAt (n := n) y₀).val y) ∈ Q.flattening.source →
    (y ∈ W.carrier ↔ Q.flattening.toFun (Ψ.invFun ((complexChartAt (n := n) y₀).val y)) ∈
      complexCoordinatePlane n W.dim)}

theorem pushPatch_center :
    (pushPatch hdim Q hv₀ hy₀ Ψ hmem hΨt hΨz hflat).center = y₀ := rfl

theorem pushPatch_coordinateParametrization (v : ComplexModel W.dim) :
    (pushPatch hdim Q hv₀ hy₀ Ψ hmem hΨt hΨz hflat).coordinateParametrization v =
      Ψ.toFun (Q.coordinateParametrization (v + v₀)) := by
  change Ψ.toFun (Q.flattening.invFun
    (planeInclusion W.dim n v + planeInclusion W.dim n v₀)) = _
  rw [← planeInclusion_add]
  rfl

theorem mem_pushPatch_parameterDomain {v : ComplexModel W.dim}
    (hv : v + v₀ ∈ Q.parameterDomain)
    (hv' : Q.coordinateParametrization (v + v₀) ∈ Ψ.source) :
    v ∈ (pushPatch hdim Q hv₀ hy₀ Ψ hmem hΨt hΨz hflat).parameterDomain := by
  change planeInclusion W.dim n v + planeInclusion W.dim n v₀ ∈ Q.flattening.target ∩
    Q.flattening.invFun ⁻¹' Ψ.source
  rw [← planeInclusion_add]
  exact ⟨hv, hv'⟩

end PushPatch

/-- **Patch pushforward.**  Let `g` be holomorphic, `W̃ ⊆ Z` and `W ⊆ Y` of the same
dimension, corresponding under `g` on the open set `O`.  A regular patch `Q` of `W̃`, read
at a parameter `v₀` whose point is a non-exceptional point of `O`, pushes to a regular
patch `P` of `W` centred at `g (Q v₀)`, with `g (Q v) = P (v - v₀)` near `v₀` and with
matching restrictions of smooth forms and of `ddᶜ` of smooth functions. -/
theorem exists_regularPatch_pushforward {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {W : ClosedIrreducibleAnalyticSubvariety n Y}
    {Wt : ClosedIrreducibleAnalyticSubvariety n Z} (hdim : Wt.dim = W.dim)
    {O : Set Z} (hO : IsOpen O) (hWO : ∀ x ∈ O, x ∈ Wt.carrier ↔ g x ∈ W.carrier)
    (Q : RegularPatch (Wt.withDim W.dim hdim)) {v₀ : ComplexModel W.dim}
    (hv₀ : v₀ ∈ Q.parameterDomain) (hzO : Q.toManifold v₀ ∈ O)
    (hz : Q.toManifold v₀ ∉ exceptionalLocus n g) :
    ∃ (P : RegularPatch W) (r : ℝ), 0 < r ∧
      ∀ v ∈ Metric.ball v₀ r,
        v ∈ Q.parameterDomain ∧ v - v₀ ∈ P.parameterDomain ∧
        Q.toManifold v ∈ O ∧ Q.toManifold v ∉ exceptionalLocus n g ∧
        g (Q.toManifold v) = P.toManifold (v - v₀) ∧
        (∀ β : ClosedRealOneOneForm n Y,
          ((ClosedRealOneOneForm.pullback hg β).val.coeff (complexChartAt (n := n) Q.center)
              (Q.coordinateParametrization v)).compContinuousLinearMap
            (fderiv ℝ Q.coordinateParametrization v) =
          (β.val.coeff (complexChartAt (n := n) P.center)
              (P.coordinateParametrization (v - v₀))).compContinuousLinearMap
            (fderiv ℝ P.coordinateParametrization (v - v₀))) ∧
        (∀ u : Y → ℝ,
          (∀ᶠ y in 𝓝 (P.coordinateParametrization (v - v₀)),
            ContDiffAt ℝ ∞ (fun y => u ((complexChartAt (n := n) P.center).val.symm y)) y) →
          (smoothDDC (fun y => u (g ((complexChartAt (n := n) Q.center).val.symm y)))
              (Q.coordinateParametrization v)).compContinuousLinearMap
            (fderiv ℝ Q.coordinateParametrization v) =
          (smoothDDC (fun y => u ((complexChartAt (n := n) P.center).val.symm y))
              (P.coordinateParametrization (v - v₀))).compContinuousLinearMap
            (fderiv ℝ P.coordinateParametrization (v - v₀))) := by
  classical
  set F : ComplexModel n → ComplexModel n :=
    fun u => (complexChartAt (n := n) (g (Q.toManifold v₀))).val
      (g ((complexChartAt (n := n) Q.center).val.symm u)) with hF
  have hExc : IsOpen (exceptionalLocus n g)ᶜ :=
    Hironaka.StrictTransformComposition.isOpen_compl_exceptionalLocus hg
  set N : Set (ComplexModel n) := (complexChartAt (n := n) Q.center).val.target ∩
    (complexChartAt (n := n) Q.center).val.symm ⁻¹'
      ((O ∩ (exceptionalLocus n g)ᶜ) ∩
        g ⁻¹' (complexChartAt (n := n) (g (Q.toManifold v₀))).val.source) with hN
  have hNo : IsOpen N :=
    (complexChartAt (n := n) Q.center).val.continuousOn_symm.isOpen_inter_preimage
      (complexChartAt (n := n) Q.center).val.open_target
      ((hO.inter hExc).inter (hg.continuous.isOpen_preimage _
        (complexChartAt (n := n) (g (Q.toManifold v₀))).val.open_source))
  have hu₀src : Q.coordinateParametrization v₀ ∈ Q.flattening.source :=
    Q.flattening.mapsTo_invFun hv₀
  have hu₀e : Q.coordinateParametrization v₀ ∈ (complexChartAt (n := n) Q.center).val.target :=
    Q.source_subset hu₀src
  have hzsym : (complexChartAt (n := n) Q.center).val.symm (Q.coordinateParametrization v₀) =
    Q.toManifold v₀ := rfl
  have hzsrc : Q.toManifold v₀ ∈ (complexChartAt (n := n) Q.center).val.source := by
    rw [← hzsym]; exact (complexChartAt (n := n) Q.center).val.map_target hu₀e
  have hzchart : (complexChartAt (n := n) Q.center).val (Q.toManifold v₀) =
      Q.coordinateParametrization v₀ := by
    rw [← hzsym]; exact (complexChartAt (n := n) Q.center).val.right_inv hu₀e
  have hgze : g (Q.toManifold v₀) ∈
      (complexChartAt (n := n) (g (Q.toManifold v₀))).val.source :=
    mem_complexChartAt_source _
  have hu₀N : Q.coordinateParametrization v₀ ∈ N :=
    ⟨hu₀e, by rw [mem_preimage, hzsym]; exact ⟨⟨hzO, hz⟩, hgze⟩⟩
  have hNdom : N ⊆ HolomorphicMaps.coordinateDomain g (complexChartAt (n := n) Q.center)
      (complexChartAt (n := n) (g (Q.toManifold v₀))) := fun u hu => ⟨hu.1, hu.2.2⟩
  have hFsmooth : ContDiffOn ℂ ∞ F N :=
    (HolomorphicMaps.coordinateMap_contDiffOn hg _ _).mono hNdom
  have hFN : DifferentiableOn ℂ F N := hFsmooth.differentiableOn (by simp)
  have hinj : Function.Injective (fderiv ℂ F (Q.coordinateParametrization v₀)) := by
    rw [hF, ← hzchart]
    exact injective_fderiv_chartExpr' hg hz (complexChartAt (n := n) Q.center) hzsrc
      (complexChartAt (n := n) (g (Q.toManifold v₀))) hgze
  obtain ⟨Ψ, hΨN, hΨF, -⟩ := exists_localHolomorphicEquivAt hNo hu₀N hFN hinj
  have hFz : F (Q.coordinateParametrization v₀) =
      (complexChartAt (n := n) (g (Q.toManifold v₀))).val (g (Q.toManifold v₀)) := by
    simp only [hF, hzsym]
  have hΨc : Ψ.toFun (Q.coordinateParametrization v₀) =
      (complexChartAt (n := n) (g (Q.toManifold v₀))).val (g (Q.toManifold v₀)) := by
    rw [hΨF]; exact hFz
  have hmem : (complexChartAt (n := n) (g (Q.toManifold v₀))).val (g (Q.toManifold v₀)) ∈
      Ψ.target := by
    rw [← hΨc]; exact Ψ.mapsTo_toFun Ψ.center_mem_source
  have hΨz : Ψ.invFun ((complexChartAt (n := n) (g (Q.toManifold v₀))).val
      (g (Q.toManifold v₀))) = Q.coordinateParametrization v₀ := by
    rw [← hΨc]; exact Ψ.left_inv _ Ψ.center_mem_source
  have hΨt : Ψ.target ⊆ (complexChartAt (n := n) (g (Q.toManifold v₀))).val.target := by
    intro w hw
    have hws : Ψ.invFun w ∈ Ψ.source := Ψ.mapsTo_invFun hw
    have hrw : Ψ.toFun (Ψ.invFun w) = w := Ψ.right_inv w hw
    rw [← hrw, hΨF, hF]
    exact (complexChartAt (n := n) (g (Q.toManifold v₀))).val.map_source (hΨN hws).2.2
  have hy₀ : g (Q.toManifold v₀) ∈ W.carrier :=
    (hWO _ hzO).mp (RegularPatchNeighborhood.RegularPatch.toManifold_mem_carrier Q hv₀)
  have hflat : ∀ {y : Y}, y ∈ (complexChartAt (n := n) (g (Q.toManifold v₀))).val.source →
      (complexChartAt (n := n) (g (Q.toManifold v₀))).val y ∈ Ψ.target →
      Ψ.invFun ((complexChartAt (n := n) (g (Q.toManifold v₀))).val y) ∈ Q.flattening.source →
      (y ∈ W.carrier ↔
        Q.flattening.toFun (Ψ.invFun
          ((complexChartAt (n := n) (g (Q.toManifold v₀))).val y)) ∈
          complexCoordinatePlane n W.dim) := by
    intro y hy hyΨ hyΦ
    set u := Ψ.invFun ((complexChartAt (n := n) (g (Q.toManifold v₀))).val y) with hu
    have huS : u ∈ Ψ.source := Ψ.mapsTo_invFun hyΨ
    have huN : u ∈ N := hΨN huS
    have hxsrc : (complexChartAt (n := n) Q.center).val.symm u ∈
        (complexChartAt (n := n) Q.center).val.source :=
      (complexChartAt (n := n) Q.center).val.map_target huN.1
    have hxu : (complexChartAt (n := n) Q.center).val
        ((complexChartAt (n := n) Q.center).val.symm u) = u :=
      (complexChartAt (n := n) Q.center).val.right_inv huN.1
    have hgx : g ((complexChartAt (n := n) Q.center).val.symm u) = y := by
      have h1 : F u = (complexChartAt (n := n) (g (Q.toManifold v₀))).val y := by
        rw [← hΨF]; exact Ψ.right_inv _ hyΨ
      rw [hF] at h1
      exact (complexChartAt (n := n) (g (Q.toManifold v₀))).val.injOn huN.2.2 hy h1
    have hQflat := Q.flattens hxsrc (by rw [hxu]; exact hyΦ)
    rw [hxu] at hQflat
    rw [← hgx, ← hWO _ huN.2.1.1]
    exact hQflat
  refine ⟨pushPatch hdim Q hv₀ hy₀ Ψ hmem hΨt hΨz hflat, ?_⟩
  set P := pushPatch hdim Q hv₀ hy₀ Ψ hmem hΨt hΨz hflat with hP
  set S : Set (ComplexModel W.dim) :=
    Q.parameterDomain ∩ Q.coordinateParametrization ⁻¹' Ψ.source with hS
  have hQcont : ContinuousOn Q.coordinateParametrization Q.parameterDomain := fun w hw =>
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      Q hw).continuousAt.continuousWithinAt
  have hSo : IsOpen S := hQcont.isOpen_inter_preimage
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain Q)
    Ψ.isOpen_source
  have hv₀S : v₀ ∈ S := ⟨hv₀, Ψ.center_mem_source⟩
  have huN : ∀ v ∈ S, Q.coordinateParametrization v ∈ N := fun v hv => hΨN hv.2
  have hPpar : ∀ v : ComplexModel W.dim,
      P.coordinateParametrization (v - v₀) = F (Q.coordinateParametrization v) := fun v => by
    rw [hP, pushPatch_coordinateParametrization, sub_add_cancel, hΨF]
  have hchain : ∀ v ∈ S, fderiv ℝ P.coordinateParametrization (v - v₀) =
      (fderiv ℝ F (Q.coordinateParametrization v)).comp
        (fderiv ℝ Q.coordinateParametrization v) := by
    intro v hv
    have heq : P.coordinateParametrization =ᶠ[𝓝 (v - v₀)]
        fun x => F (Q.coordinateParametrization (x + v₀)) := by
      have hpre : IsOpen ((fun x : ComplexModel W.dim => x + v₀) ⁻¹' S) :=
        hSo.preimage (continuous_add_const v₀)
      have hvpre : (v - v₀) ∈ (fun x : ComplexModel W.dim => x + v₀) ⁻¹' S := by
        rw [mem_preimage, sub_add_cancel]; exact hv
      filter_upwards [hpre.mem_nhds hvpre] with x hx
      have := hPpar (x + v₀)
      rwa [add_sub_cancel_right] at this
    refine fderiv_eq_comp_of_eventuallyEq' heq
      (((hFsmooth.contDiffAt (hNo.mem_nhds (huN v hv))).differentiableAt
        (by simp)).restrictScalars ℝ) ?_
    exact (AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      Q hv.1).restrictScalars ℝ
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp hSo v₀ hv₀S
  refine ⟨r, hr, fun v hv => ?_⟩
  have hvS : v ∈ S := hrS hv
  have hman : Q.toManifold v =
    (complexChartAt (n := n) Q.center).val.symm (Q.coordinateParametrization v) := rfl
  have hPcenter : (complexChartAt (n := n) P.center) =
    complexChartAt (n := n) (g (Q.toManifold v₀)) := rfl
  refine ⟨hvS.1, mem_pushPatch_parameterDomain (by rw [sub_add_cancel]; exact hvS.1)
    (by rw [sub_add_cancel]; exact hvS.2), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hman]; exact (huN v hvS).2.1.1
  · rw [hman]; exact (huN v hvS).2.1.2
  · show _ = (complexChartAt (n := n) (g (Q.toManifold v₀))).val.symm
      (P.coordinateParametrization (v - v₀))
    rw [hPpar, hF, hman]
    exact ((complexChartAt (n := n) (g (Q.toManifold v₀))).val.left_inv
      (huN v hvS).2.2).symm
  · intro β
    rw [ClosedRealOneOneForm.pullback_val,
      SmoothRealForm.pullback_coeff hg β.val _ _ (hNdom (huN v hvS))]
    show ((β.val.coeff _ (F (Q.coordinateParametrization v))).compContinuousLinearMap
      (fderiv ℝ F (Q.coordinateParametrization v))).compContinuousLinearMap _ = _
    rw [hPcenter, ← hPpar, hchain v hvS]
    exact (compContinuousLinearMap_comp' _ _ _).symm
  · intro uu huu
    set ρ : ComplexModel n → ℝ :=
      fun y => uu ((complexChartAt (n := n) (g (Q.toManifold v₀))).val.symm y) with hρ
    have hqN := huN v hvS
    have heqv : (fun y => uu (g ((complexChartAt (n := n) Q.center).val.symm y))) =ᶠ[𝓝
        (Q.coordinateParametrization v)] fun y => ρ (F y) := by
      filter_upwards [hNo.mem_nhds hqN] with y hy
      simp only [hρ, hF,
        (complexChartAt (n := n) (g (Q.toManifold v₀))).val.left_inv hy.2.2]
    have hρV : ContDiffOn ℝ ∞ ρ (interior {y | ContDiffAt ℝ ∞ ρ y}) := fun y hy =>
      (show ContDiffAt ℝ ∞ ρ y from interior_subset hy).contDiffWithinAt
    have hPV : P.coordinateParametrization (v - v₀) ∈ interior {y | ContDiffAt ℝ ∞ ρ y} :=
      mem_interior_iff_mem_nhds.mpr huu
    have hUo : IsOpen (N ∩ F ⁻¹' interior {y | ContDiffAt ℝ ∞ ρ y}) :=
      hFN.continuousOn.isOpen_inter_preimage hNo isOpen_interior
    have hqU : Q.coordinateParametrization v ∈ N ∩ F ⁻¹' interior {y | ContDiffAt ℝ ∞ ρ y} :=
      ⟨hqN, by rw [mem_preimage, ← hPpar]; exact hPV⟩
    rw [smoothDDC_congr heqv, HolomorphicDDC.smoothDDC_comp hUo isOpen_interior
      (hFsmooth.mono inter_subset_left) hρV (fun y hy => hy.2) hqU,
      hPcenter, ← hρ, ← hPpar, hchain v hvS]
    exact (compContinuousLinearMap_comp' _ _ _).symm

end

end RegularPatchPushforward

end Hironaka
