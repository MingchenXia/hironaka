import Hironaka.Analytic.BlanchardWeightChart
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Analytic.FactorizedWeightForm
import Hironaka.Blowup.BlowupIsomorphismOff

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Blanchard weight on a blowup

Let `π : Z → M` be a blowup along `C` and `U` the Blanchard weight of `C`
(`BlanchardWeight.BlanchardData.weight`).  Then `U ∘ π` vanishes on no nonempty open subset of
`Z` (`exists_notMem_of_isOpen`), and every `z ∈ Z` has a local factorization
`U ∘ π = |h|² U'` with `h` holomorphic and `U'` smooth and positive (`exists_localFactor`):
off `π⁻¹ C` take `h = 1`; over `C` take `h = wⱼ` and `U' = Ũ ∘ W` in a monomial chart.

Moreover `ddᶜ log U'` is strictly positive at `z` on every nonzero `v` with `dπ_z v = 0`:
over `C` the derivative of the local inverse `W` sends `v` to a nonzero fibre direction
(`BlowupFibreDirection`), along which `ddᶜ log Ũ > 0` (`BlowupWeightLevi`); off `C` there is no
such `v`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlanchardForm

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.HolomorphicMaps
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlanchardWeight
  BlanchardWeightChart BlowupWeightLevi BlowupFibreDirection

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M}

theorem monomial_line {k : ℕ} {j : Fin n} {w v : ComplexModel n} (hwj : w j = 0) (hvj : v j = 0)
    (hvk : ∀ i : Fin n, i.1 < k → v i = 0) (t : ℂ) :
    monomial k j (w + t • v) = monomial k j w := by
  ext i
  simp only [monomial_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hi : k ≤ i.1 ∧ i ≠ j
  · simp [hi, hwj, hvj]
  · rw [if_neg hi, if_neg hi]
    by_cases hij : i = j
    · subst hij; simp [hvj]
    · have : i.1 < k := by
        by_contra h; exact hi ⟨by omega, hij⟩
      simp [hvk i this]

/-- The pullback of the ideal of `C` is locally principal with a generator vanishing on no open
set, so `π⁻¹ C` has empty interior. -/
theorem exists_notMem_of_isOpen (hπ : IsBlowupAlong n C π) {W : Set Z} (hW : IsOpen W)
    (hne : W.Nonempty) : ∃ z ∈ W, π z ∉ C := by
  obtain ⟨z, hz⟩ := hne
  by_contra hall
  push Not at hall
  obtain ⟨U, hU, hzU, h, hhd, hnon, hiff⟩ := hπ.2.2.2.1 z
  have hhol : HolomorphicAt n h z := by
    filter_upwards [hU.mem_nhds hzU] with z' hz'
    exact (hhd z' hz').mdifferentiableAt (hU.mem_nhds hz')
  have hmemh : IsInSpanAt (n := n) (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π z) a ∧
      s = a ∘ π) z h :=
    (hiff z hzU h).mpr (isInSpanAt_of_eq_mul rfl hhol (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp))
  obtain ⟨-, N, s, β, hs, -, hsum⟩ := hmemh
  choose a ha hsa using hs
  have hvan : ∀ᶠ z' in 𝓝 z, h z' = 0 := by
    have h1 : ∀ᶠ z' in 𝓝 z, ∀ i, π z' ∈ C → a i (π z') = 0 :=
      hπ.contMDiff.continuous.continuousAt.eventually (eventually_all.2 fun i => (ha i).2)
    filter_upwards [hsum, h1, hW.mem_nhds hz] with z' h1' h2' h3'
    rw [h1']
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsa i, Function.comp_apply, h2' i (hall z' h3'), mul_zero]
  obtain ⟨V, hVsub, hV, hzV⟩ := mem_nhds_iff.mp (hvan.and (hU.mem_nhds hzU))
  obtain ⟨y, hy, hy0⟩ := hnon V hV (fun y hy => (hVsub hy).2) ⟨z, hzV⟩
  exact hy0 (hVsub hy).1

omit [IsComplexManifold n M] in
theorem contDiffOn_chartSmooth_comp [IsComplexManifold n M]
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {g : M → ℝ}
    (hg : ChartSmooth (n := n) g) (e : ComplexChart n Z) :
    ContDiffOn ℝ ∞ (fun u => g (π (e.val.symm u))) e.val.target := by
  intro u hu
  set d := complexChartAt (n := n) (π (e.val.symm u))
  have hud : u ∈ coordinateDomain π e d := ⟨hu, mem_complexChartAt_source _⟩
  have h1 := coordinateMap_contDiffAt_real hπ e d hud
  have h2 := (hg d).contDiffAt (d.val.open_target.mem_nhds (coordinateMap_mem_target hud))
  have h3 := ContDiffAt.comp (g := fun z => g (d.val.symm z)) u h2 h1
  refine (h3.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(coordinateDomain_isOpen hπ e d).mem_nhds hud] with u' hu'
  show g (π (e.val.symm u')) = g (d.val.symm (d.val (π (e.val.symm u'))))
  rw [d.val.left_inv hu'.2]

/-- **Local factorization of the Blanchard weight of a closed part `C'` of the centre** whose
flattenings also flatten `C` and over whose complement `π` is unramified, with positivity of the
smooth part on the kernel of `dπ`. -/
theorem exists_localFactor_of_flat (hπ : IsBlowupAlong n C π) {C' : Set M}
    (D : BlanchardData n C')
    (hflatC : ∀ (q : C') {y : M}, y ∈ (chartAt (ComplexModel n) q.1).source →
      chartAt (ComplexModel n) q.1 y ∈ (D.flat q).source →
        (y ∈ C ↔ (D.flat q).toFun (chartAt (ComplexModel n) q.1 y) ∈
          complexCoordinatePlane n (D.kdim q)))
    (hC' : IsClosed C') (hexc : ∀ z, π z ∉ C' → z ∉ exceptionalLocus n π) (z : Z) :
    ∃ (S : Set Z) (h : Z → ℂ) (U' : Z → ℝ), IsOpen S ∧ z ∈ S ∧
      (∀ y ∈ S, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h y) ∧
      (∀ e : ComplexChart n Z,
        ContDiffOn ℝ ∞ (fun u => U' (e.val.symm u)) (e.val.target ∩ e.val.symm ⁻¹' S)) ∧
      (∀ y ∈ S, 0 < U' y) ∧
      (∀ y ∈ S, D.weight (π y) = Complex.normSq (h y) * U' y) ∧
      ∀ v : ComplexModel n, v ≠ 0 →
        mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z v = 0 →
        0 < smoothDDC (fun u => Real.log (U' ((chartAt (ComplexModel n) z).symm u)))
          (chartAt (ComplexModel n) z z) ![v, Complex.I • v] := by
  classical
  by_cases hz : π z ∈ C'
  swap
  · refine ⟨π ⁻¹' C'ᶜ, fun _ => 1, fun y => D.weight (π y),
      hC'.isOpen_compl.preimage hπ.contMDiff.continuous, hz,
      fun y _ => mdifferentiableAt_const, fun e => ?_, fun y hy => D.weight_pos_of_notMem hy,
      fun y _ => by simp, fun v hv hdv => ?_⟩
    · exact (contDiffOn_chartSmooth_comp hπ.contMDiff D.chartSmooth_weight e).mono
        inter_subset_left
    · have hexc := hexc z hz
      simp only [exceptionalLocus, mem_ofPred_eq, not_not] at hexc
      exact absurd (hexc.1 (hdv.trans (map_zero _).symm)) hv
  -- over the centre
  obtain ⟨a₀, -, ha₀⟩ : ∃ a ∈ Finset.univ, 0 < D.χ a (π z) := by
    by_contra h
    push Not at h
    have : ∑ a, D.χ a (π z) ≤ 0 := Finset.sum_nonpos fun a _ => h a (Finset.mem_univ a)
    rw [D.sum_one] at this
    exact absurd this (by norm_num)
  cases hq : D.center a₀ with
  | none => exact absurd hz (D.supp_none a₀ hq (subset_tsupport _ ha₀.ne'))
  | some q =>
  have hzq : π z ∈ flatDomain (D.flat q) := D.supp_some a₀ q hq (subset_tsupport _ ha₀.ne')
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ (D.flat_src q) (hflatC q) hzq
  set k := D.kdim q
  set Φ := D.flat q
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ k j := fun z' hz' => by
    show monomial k j (W z') ∈ Φ.target
    rw [(hWeq z' hz').2]; exact Φ.mapsTo_toFun (hWeq z' hz').1.2
  have hγ : ∀ z' ∈ O, monomialMap Φ k j (W z') = π z' := fun z' hz' => by
    simp only [monomialMap, (hWeq z' hz').2]
    exact flatInverse_flat Φ (hWeq z' hz').1
  obtain ⟨B, V, hV, hw₀V, -, hUs, hUpos, hUfac, hBa⟩ :=
    BlanchardData.exists_blowupWeight_factor D hq hj (hWmem z hzO)
      (by rw [hγ z hzO]; exact hz) (by rw [hγ z hzO]; exact ha₀)
  set Ut := blowupWeight j (fun b w => D.χ b (monomialMap Φ k j w))
    (fun b i l w => B b i l (monomialMap Φ k j w)) with hUt
  have hWc : ContinuousOn W O := fun z' hz' => (hWs z' hz').continuousAt.continuousWithinAt
  set S := O ∩ W ⁻¹' V
  have hS : IsOpen S := hWc.isOpen_inter_preimage hO hV
  have hGd : ∀ e : ComplexChart n Z, DifferentiableOn ℂ (fun u => W (e.val.symm u))
      (e.val.target ∩ e.val.symm ⁻¹' S) := fun e u hu =>
    (mdifferentiableAt_iff_differentiableAt.mp (((hWs _ hu.2.1).mdifferentiableAt (by simp)).comp u
      (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hu.1))).differentiableWithinAt
  have hlogs : ContDiffOn ℝ ∞ (fun w => Real.log (Ut w)) V :=
    hUs.log fun w hw => (hUpos w hw).ne'
  refine ⟨S, fun z' => W z' j, fun z' => Ut (W z'), hS, ⟨hzO, hw₀V⟩, fun y hy => ?_,
    fun e => ?_, fun y hy => hUpos _ hy.2, fun y hy => ?_, fun v hv hdv => ?_⟩
  · exact (((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).contMDiff.contMDiffAt.comp y
      (hWs y hy.1)).mdifferentiableAt (by simp))
  · have hUo : IsOpen (e.val.target ∩ e.val.symm ⁻¹' S) := e.val.isOpen_inter_preimage_symm hS
    have hG := contDiffOn_of_differentiableOn_complex (hGd e) hUo
    exact hUs.comp (hG.restrict_scalars ℝ) fun u hu => hu.2.2
  · show D.weight (π y) = Complex.normSq (W y j) * Ut (W y)
    rw [← hγ y hy.1]
    exact hUfac _ hy.2
  -- positivity on the kernel of `dπ`
  set e := complexChartAt (n := n) z
  set ζ₀ := chartAt (ComplexModel n) z z
  set G := fun u => W (e.val.symm u)
  have hUo : IsOpen (e.val.target ∩ e.val.symm ⁻¹' S) := e.val.isOpen_inter_preimage_symm hS
  have hζ₀ : ζ₀ ∈ e.val.target ∩ e.val.symm ⁻¹' S := by
    refine ⟨e.val.map_source (mem_complexChartAt_source z), ?_⟩
    show e.val.symm (e.val z) ∈ S
    rw [e.val.left_inv (mem_complexChartAt_source z)]; exact ⟨hzO, hw₀V⟩
  have hG := contDiffOn_of_differentiableOn_complex (hGd e) hUo
  have hGζ₀ : G ζ₀ = W z := by
    show W (e.val.symm (e.val z)) = W z
    rw [e.val.left_inv (mem_complexChartAt_source z)]
  have hcomp := HolomorphicDDC.smoothDDC_comp hUo hV hG hlogs (fun u hu => hu.2.2) hζ₀
  change 0 < smoothDDC (fun u => Real.log (Ut (G u))) ζ₀ ![v, Complex.I • v]
  rw [hcomp, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hGdiff : DifferentiableAt ℂ G ζ₀ := (hGd e ζ₀ hζ₀).differentiableAt (hUo.mem_nhds hζ₀)
  set Dv := fderiv ℝ G ζ₀ v
  have hvec : (⇑(fderiv ℝ G ζ₀) ∘ (![v, Complex.I • v] : Fin 2 → ComplexModel n)) =
      ![Dv, Complex.I • Dv] := by
    funext i
    fin_cases i
    · rfl
    · show fderiv ℝ G ζ₀ (Complex.I • v) = Complex.I • fderiv ℝ G ζ₀ v
      rw [hGdiff.fderiv_restrictScalars ℝ]
      exact (fderiv ℂ G ζ₀).map_smul Complex.I v
  rw [show (fun u => W (e.val.symm u)) = G from rfl, hvec,
    show W (e.val.symm ζ₀) = W z from hGζ₀]
  -- `Dv` is a nonzero fibre direction
  have hvj : Dv j = 0 :=
    fderiv_monomialInverse_apply_eq_zero hπ hO hWs hWeq hzO hdv j (by simp)
  have hvk : ∀ i : Fin n, i.1 < k → Dv i = 0 := fun i hi =>
    fderiv_monomialInverse_apply_eq_zero hπ hO hWs hWeq hzO hdv i (by omega)
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ (D.flat_src q) (hflatC q) hj
  have hv0 : Dv ≠ 0 :=
    fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hzO hv
  have hw₀j : W z j = 0 := by
    have h1 := congrArg (fun w : ComplexModel n => w j) (hWeq z hzO).2
    simp only [monomial_apply, ne_eq, not_true_eq_false, and_false, if_false] at h1
    rw [h1]
    exact ((D.flat_eq q hzq.1 hzq.2).mp hz) j hj
  have hline : ∀ t : ℂ, monomialMap Φ k j (W z + t • Dv) = monomialMap Φ k j (W z) := fun t => by
    simp only [monomialMap, monomial_line hw₀j hvj hvk t]
  refine quad_smoothDDC_log_blowupWeight_pos hj
    (((hlogs.contDiffAt (hV.mem_nhds hw₀V))).of_le (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun b t => by simp only [hline t]) (fun b i l t => by simp only [hline t])
    (fun b => D.nonneg b _) a₀ (by rw [hγ z hzO]; exact ha₀)
    (fun i l => hBa i l _) hvj hvk hv0


/-- **Local factorization of the Blanchard weight on a blowup**, with positivity of the smooth
part on the kernel of `dπ`. -/
theorem exists_localFactor (hπ : IsBlowupAlong n C π) (D : BlanchardData n C) (z : Z) :
    ∃ (S : Set Z) (h : Z → ℂ) (U' : Z → ℝ), IsOpen S ∧ z ∈ S ∧
      (∀ y ∈ S, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h y) ∧
      (∀ e : ComplexChart n Z,
        ContDiffOn ℝ ∞ (fun u => U' (e.val.symm u)) (e.val.target ∩ e.val.symm ⁻¹' S)) ∧
      (∀ y ∈ S, 0 < U' y) ∧
      (∀ y ∈ S, D.weight (π y) = Complex.normSq (h y) * U' y) ∧
      ∀ v : ComplexModel n, v ≠ 0 →
        mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z v = 0 →
        0 < smoothDDC (fun u => Real.log (U' ((chartAt (ComplexModel n) z).symm u)))
          (chartAt (ComplexModel n) z z) ![v, Complex.I • v] :=
  exists_localFactor_of_flat hπ D (fun q => D.flat_eq q) hπ.1.1 (fun _ hz h =>
    hz (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)) z

end

end Hironaka.BlanchardForm
