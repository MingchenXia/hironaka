import TranscendentalNakamaye.Pending.HadamardBridge
import TranscendentalNakamaye.Pending.OrderMultiplicativity
import TranscendentalNakamaye.Pending.GlueingTrivialAction
import TranscendentalNakamaye.Pending.BlowupStrictIdeal
import TranscendentalNakamaye.Pending.BlowupLocalSurjectivity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The pushforward of `𝒪(-KD)`: a germ whose pullback lies in `𝒪(-D)^K` lies in `𝓘_C^K`

Hironaka phase H2 (TN3), H4 list item 3, blowup half (I-0977 C-0045 / C-0050).  Blueprint
`bcalc:exceptional-pushforward`, `bcalc:controlled-not-exceptional` (chapter `blowup-calculus.tex`).
Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`) §2.2 (the controlled transform
`y^{-μ}(f ∘ σ)`, `y` a generator of the ideal of the exceptional divisor) and Step 2a of the proof
of `pr:resol` (the decomposition `𝓘 = 𝓜(𝓘) 𝓝(𝓘)` with a nonmonomial part divisible by no ideal of a
divisor in `E`, to be kept along the transforms); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`).  The first result is the local form of `π_* 𝒪(-KD) = 𝓘_C^K`
for a smooth centre `C`.

* `mem_idealPow_vanishingIdeal_of_pullback_mem`: for the blowup `π` along `C`, a point `z` over
  `C`, and `f` holomorphic at `π z`: if `f ∘ π ∈ 𝒪(-D)^K` at `z`, then `f ∈ 𝓘_C^K` at `π z`.
* `mem_cosupport_succ_of_controlledTransform_le`, `exists_not_mem_exceptionalDivisor`: if
  `C ⊆ cosupp(𝔞, μ)` (`𝔞` coherent) and `σ^c(𝔞, μ) ⊆ 𝒪(-D)` at a point `z` over `C`, then
  `ord_{π z} 𝔞 ≥ μ + 1`; so where the order is exactly `μ`, `σ^c(𝔞, μ)` is not in `𝒪(-D)`.
* `frequently_le_vanishingIdeal_of_controlledTransform_le`,
  `exists_not_mem_vanishingIdeal_geoStrictTransform`: if `σ^c(𝔟, o) ⊆ 𝓘_{H'}` at a point of the
  strict transform `H'` of a closed `H`, then `𝔟 ⊆ 𝓘_H` at points of `H \ C` arbitrarily close to
  its image; so if `𝔟 ⊄ 𝓘_H` at the points of `H \ C` near `π z`, `σ^c(𝔟, o) ⊄ 𝓘_{H'}` at `z`
  (helper `eventually_le_vanishingIdeal_of_isCoherent`).

## Proof

Take flattening coordinates `Φ ∘ e` at `x = π z` with `C = ℂᵏ × 0`, `F = f ∘ e⁻¹ ∘ Φ⁻¹`, and the
monomial chart `σⱼ` of the blowup through `z` (`exists_monomialLocalInverse`, with its lift `ℓ`,
`existsUnique_monomialLift`; `extendLifted` reads `ℓ` on `ℂⁿ`). The germs of `𝒪(-D)` vanish on `D`,
so `f ∘ π ∈ 𝔪_u^K` at every `u ∈ D` near `z` (`eventually_mem_idealPow_pointIdeal`); pulling back
along `ℓ`, every derivative of order `< K` of `G = F ∘ σⱼ` vanishes at the points `λ` near `W z`
with `λⱼ = 0`. For `w ∈ ℂᵏ × 0` near `0` and a direction `h` near `h₀ = W z + eⱼ`, the line
`t ↦ w + t h` is `σⱼ(λ + t v)`, with `λ = liftPoint k j w h` (the tangential part of `w`, the
ratios `hᵢ / hⱼ`, and `λⱼ = 0`) and `v = liftDir k j h` (`monomial_liftPoint_add`). Hence
`D^a F(w)(h, …, h) = D^a G(λ)(v, …, v) = 0` for `a < K` and all `h` in an open set. The diagonal
of the symmetric form `D^a F(w)` is a polynomial, so it vanishes everywhere (identity principle),
and polarization (TN-CLASSICAL's `OrderMultiplicativity.eq_zero_of_symmetric_of_apply_diag`) gives
`D^a F(w) = 0` (`eq_zero_of_symmetric_of_apply_diag_on_open`). TN23's
`inNormalPow_of_iterDeriv_eq_zero` and `OrderTaylor.mem_idealPow_of_inNormalPow` turn the vanishing
along `ℂᵏ × 0` into `f ∈ 𝓘_C^K`, as in the Hadamard bridge.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.ExceptionalIdealPushforward

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open TranscendentalNakamaye.Pending.GermIdealOrder TranscendentalNakamaye.Pending.OrderTaylor
open TranscendentalNakamaye.Pending.HolomorphicTaylorTail
open TranscendentalNakamaye.Pending.HadamardBridge
open TranscendentalNakamaye.Pending.OrderMultiplicativity
open TranscendentalNakamaye.Pending.HolomorphicAnalytic
open TranscendentalNakamaye.Pending.BlowupFlatCoordinates
open TranscendentalNakamaye.Pending.BlowupMonomialCharts
open TranscendentalNakamaye.Pending.BlowupLocalSurjectivity
open TranscendentalNakamaye.Pending.BlowupExceptionalDivisor
open TranscendentalNakamaye.Pending.BlowupStrictIdeal
open TranscendentalNakamaye.Pending.GlueingTrivialAction
open TranscendentalNakamaye.Pending.IdealWeightPowers
open TranscendentalNakamaye.Pending.BlowupFunctionTransform
open TranscendentalNakamaye.Pending.BlowupStrictSubmanifold

noncomputable section

variable {n : ℕ}

/-! ### Polarization on an open set of directions -/

section Polarization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **A symmetric multilinear form vanishing on an open set of the diagonal is zero**: its diagonal
`h ↦ Ψ(h, …, h)` is a polynomial, hence vanishes everywhere (identity principle), and polarization
(`OrderMultiplicativity.eq_zero_of_symmetric_of_apply_diag`) concludes. -/
theorem eq_zero_of_symmetric_of_apply_diag_on_open {a : ℕ}
    (Ψ : ContinuousMultilinearMap ℂ (fun _ : Fin a => E) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin a)) (m : Fin a → E), Ψ (m ∘ σ) = Ψ m) {V : Set E}
    (hV : IsOpen V) (hVne : V.Nonempty) (h0 : ∀ h ∈ V, Ψ (fun _ => h) = 0) : Ψ = 0 := by
  refine eq_zero_of_symmetric_of_apply_diag a Ψ hsym fun y => ?_
  have hdiag : Differentiable ℂ fun h : E => (fun _ : Fin a => h) :=
    differentiable_pi.2 fun _ => differentiable_id
  have hd : DifferentiableOn ℂ (fun h : E => Ψ (fun _ => h)) univ := fun h _ =>
    ((Ψ.hasFDerivAt (fun _ => h)).differentiableAt.comp h (hdiag h)).differentiableWithinAt
  have han : AnalyticOnNhd ℂ (fun h : E => Ψ (fun _ => h)) univ :=
    analyticOnNhd_of_differentiableOn isOpen_univ hd
  obtain ⟨h₀, hh₀⟩ := hVne
  have hev : (fun h : E => Ψ (fun _ => h)) =ᶠ[𝓝 h₀] 0 := by
    filter_upwards [hV.mem_nhds hh₀] with h hh
    exact h0 h hh
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ h₀) hev
    (mem_univ y)

end Polarization

/-! ### Powers of an ideal of germs vanishing on a set -/

section Vanishing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- If the germs of `I` at `z` are holomorphic and vanish on `A` near `z`, a germ of `I^K` at `z`
lies in `𝔪_u^K` at every point `u ∈ A` near `z`. -/
theorem eventually_mem_idealPow_pointIdeal {I : GermIdeal n M} {A : Set M} {z : M}
    (hI : ∀ b, I.mem z b → HolomorphicAt n b z ∧ ∀ᶠ y in 𝓝 z, y ∈ A → b y = 0) :
    ∀ (K : ℕ) {g : M → ℂ}, (idealPow I K).mem z g →
      ∀ᶠ u in 𝓝 z, u ∈ A → (idealPow (pointIdeal n u) K).mem u g
  | 0, g, hg => by
    have hg' : HolomorphicAt n g z := hg
    filter_upwards [hg'.eventually_nhds] with u hu _
    exact hu
  | K + 1, g, hg => by
    obtain ⟨hgh, N, r, c, hr, hc, hsum⟩ := mem_idealPow_succ_iff.mp hg
    choose a b ha hb hab using hr
    have hA : ∀ i, ∀ᶠ u in 𝓝 z, u ∈ A → (idealPow (pointIdeal n u) K).mem u (a i) := fun i =>
      eventually_mem_idealPow_pointIdeal hI K (ha i)
    have hB : ∀ i, ∀ᶠ u in 𝓝 z, u ∈ A → (pointIdeal n u).mem u (b i) := fun i => by
      obtain ⟨hbh, hb0⟩ := hI _ (hb i)
      filter_upwards [hbh.eventually_nhds, hb0] with u hu hu0 huA
      exact mem_pointIdeal_of_apply_eq_zero hu (hu0 huA)
    have hgh' : HolomorphicAt n g z := hgh
    filter_upwards [eventually_all.mpr hA, eventually_all.mpr hB, hgh'.eventually_nhds,
      eventually_all.mpr fun i => (hc i).eventually_nhds, hsum.eventuallyEq_nhds]
      with u hua hub hgu hcu hsu huA
    exact mem_idealPow_succ_iff.mpr
      ⟨hgu, N, r, c, fun i => ⟨a i, b i, hua i huA, hub i huA, hab i⟩, hcu, hsu⟩

/-- **Powers are monotone at a point**: if the germs of `𝔞` at `x` are germs of `𝔟` at `x`, so are
those of `𝔞^q`. -/
theorem mem_idealPow_of_mem_at {𝔞 𝔟 : GermIdeal n M} {x : M} (h : ∀ g, 𝔞.mem x g → 𝔟.mem x g) :
    ∀ (q : ℕ) {g : M → ℂ}, (idealPow 𝔞 q).mem x g → (idealPow 𝔟 q).mem x g
  | 0, _, hg => hg
  | q + 1, _, hg => mem_idealPow_succ_iff.mpr ((mem_idealPow_succ_iff.mp hg).mono
      fun _ ⟨a, b, ha, hb, hs⟩ => ⟨a, b, mem_idealPow_of_mem_at h q ha, h b hb, hs⟩)

/-- **Containment in the ideal of a set propagates for a coherent ideal**: if the germs of `𝔟` at
`z` vanish on `A` near `z`, then at every point `z'` near `z` the germs of `𝔟` vanish on `A` near
`z'`. -/
theorem eventually_le_vanishingIdeal_of_isCoherent {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent)
    {A : Set M} {z : M} (hz : ∀ g, 𝔟.mem z g → (vanishingIdeal (n := n) A).mem z g) :
    ∀ᶠ z' in 𝓝 z, ∀ g, 𝔟.mem z' g → (vanishingIdeal (n := n) A).mem z' g := by
  obtain ⟨U, hU, hzU, N, s, hs, hgen⟩ := h𝔟 z
  have hsz : ∀ i, 𝔟.mem z (s i) := fun i => by
    have hhol : HolomorphicAt n (s i) z := by
      filter_upwards [hU.mem_nhds hzU] with y hy
      exact (hs i).mdifferentiableAt (hU.mem_nhds hy)
    exact (hgen z hzU (s i)).mpr (isInSpanAt_of_eq_mul ⟨i, rfl⟩ hhol (holomorphicAt_const 1)
      (Eventually.of_forall fun y => (one_mul _).symm))
  have hvan : ∀ i, ∀ᶠ y in 𝓝 z, y ∈ A → s i y = 0 := fun i => (hz _ (hsz i)).2
  filter_upwards [hU.mem_nhds hzU, (eventually_all.mpr hvan).eventually_nhds] with z' hz'U hz'v g hg
  obtain ⟨hgh, K, t, c, ht, hc, hsum⟩ := (hgen z' hz'U g).mp hg
  refine ⟨hgh, ?_⟩
  filter_upwards [hsum, hz'v] with y hy hyv hyA
  rw [hy]
  refine Finset.sum_eq_zero fun k _ => ?_
  obtain ⟨i, hi⟩ := ht k
  rw [← hi, hyv i hyA]
  simp

end Vanishing

/-! ### The line through a point of the plane, lifted to the `j`-th monomial chart -/

section Line

variable {k : ℕ} {j : Fin n}

/-- The point of the `j`-th monomial chart over `w` in the direction `h` (`h j ≠ 0`): tangential
coordinates of `w`, the ratios `h i / h j` in the other normal coordinates, `0` in the `j`-th. -/
def liftPoint (k : ℕ) (j : Fin n) (w h : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun i => if i.1 < k then w i else if i = j then 0 else h i / h j

/-- The direction of the lifted line: the tangential coordinates of `h` and `h j`. -/
def liftDir (k : ℕ) (j : Fin n) (h : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun i => if i.1 < k then h i else if i = j then h j else 0

@[simp] theorem liftPoint_apply (w h : ComplexModel n) (i : Fin n) :
    liftPoint k j w h i = if i.1 < k then w i else if i = j then 0 else h i / h j := rfl

@[simp] theorem liftDir_apply (h : ComplexModel n) (i : Fin n) :
    liftDir k j h i = if i.1 < k then h i else if i = j then h j else 0 := rfl

/-- **The lifted line maps onto the line**: `σⱼ(λ + t v) = w + t h` for `w ∈ ℂᵏ × 0`, `h j ≠ 0`. -/
theorem monomial_liftPoint_add (hj : k ≤ j.1) {w h : ComplexModel n}
    (hw : w ∈ complexCoordinatePlane n k) (hh : h j ≠ 0) (t : ℂ) :
    monomial k j (liftPoint k j w h + t • liftDir k j h) = w + t • h := by
  ext i
  simp only [monomial_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, liftPoint_apply,
    liftDir_apply]
  by_cases hik : i.1 < k
  · have : ¬ (k ≤ i.1 ∧ i ≠ j) := fun h' => absurd h'.1 (not_le.mpr hik)
    simp [this, hik]
  · have hjk : ¬ j.1 < k := not_lt.mpr hj
    have hwi : w i = 0 := hw i (not_lt.mp hik)
    have hwj : w j = 0 := hw j hj
    by_cases hij : i = j
    · subst hij
      simp [hik, hwi]
    · have hki : k ≤ i.1 ∧ i ≠ j := ⟨not_lt.mp hik, hij⟩
      rw [if_pos hki]
      simp only [hik, hij, hjk, hwi, if_false, if_true]
      field_simp
      ring

end Line

/-! ### The pushforward -/

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **`π_* 𝒪(-K D) = 𝓘_C^K`, locally on the blowup**: if `f` is holomorphic at a point `π z` of the
centre and `f ∘ π` lies in `𝒪(-D)^K` at the single point `z`, then `f ∈ 𝓘_C^K` at `π z`. -/
theorem mem_idealPow_vanishingIdeal_of_pullback_mem (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : π z ∈ C) {f : X → ℂ} (hf : HolomorphicAt n f (π z)) {K : ℕ}
    (hK : (idealPow (exceptionalDivisor hπ).ideal K).mem z (f ∘ π)) :
    (idealPow (vanishingIdeal (n := n) C) K).mem (π z) f := by
  classical
  obtain ⟨k, -, -, Φ, hΦsrc, hΦx, hflat⟩ := hπ.1.2 (π z) hz
  have hx' : π z ∈ flatDomain Φ := mem_flatDomain_self Φ
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ := exists_monomialLocalInverse hπ hΦsrc hflat hx'
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  -- the point `W z` of the monomial chart over `π z`
  have hw₀ : W z ∈ monomialDomain Φ k j := by
    show monomial k j (W z) ∈ Φ.target
    rw [(hWeq z hzO).2]; exact Φ.mapsTo_toFun (hWeq z hzO).1.2
  have hℓz : ℓ (LiftedOpen.mk _ (W z) hw₀) = z := hℓ ℓ hℓs hℓπ z hzO hw₀
  have hσ₀ : monomial k j (W z) = 0 := by rw [(hWeq z hzO).2]; exact hΦx
  have hWj : W z j = 0 := by
    have h := congrArg (fun w : ComplexModel n => w j) hσ₀
    simpa [monomial_apply] using h
  have hWt : ∀ i : Fin n, i.1 < k → W z i = 0 := fun i hi => by
    have h := congrArg (fun w : ComplexModel n => w i) hσ₀
    have : ¬ (k ≤ i.1 ∧ i ≠ j) := fun h' => absurd h'.1 (not_le.mpr hi)
    simpa [monomial_apply, this] using h
  -- the extension of the lift to `ℂⁿ`
  have hφS : ∀ v (hv : v ∈ monomialDomain Φ k j),
      extendLifted ℓ hw₀ v = ℓ (LiftedOpen.mk _ v hv) :=
    fun v hv => extendLifted_of_mem ℓ hw₀ hv
  have hφd : ∀ v ∈ monomialDomain Φ k j,
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (extendLifted ℓ hw₀) v :=
    fun v hv => mdifferentiableAt_extendLifted hℓs hw₀ hv
  have hπφ : ∀ v ∈ monomialDomain Φ k j, π (extendLifted ℓ hw₀ v) =
      (chartAt (ComplexModel n) (π z)).symm (Φ.invFun (monomial k j v)) := fun v hv => by
    rw [hφS v hv]; exact congrFun hℓπ _
  have hφz : extendLifted ℓ hw₀ (W z) = z := by rw [hφS _ hw₀, hℓz]
  -- the hypothesis at the points of `D` near `z`
  have hI : ∀ b, (exceptionalDivisor hπ).ideal.mem z b →
      HolomorphicAt n b z ∧ ∀ᶠ y in 𝓝 z, y ∈ π ⁻¹' C → b y = 0 :=
    fun b hb => pullback_vanishingIdeal_le hπ.contMDiff.continuous C z b hb
  have hev := eventually_mem_idealPow_pointIdeal hI K hK
  have hev' : ∀ᶠ v in 𝓝 (W z), extendLifted ℓ hw₀ v ∈ π ⁻¹' C →
      (idealPow (pointIdeal n (extendLifted ℓ hw₀ v)) K).mem (extendLifted ℓ hw₀ v) (f ∘ π) := by
    have hc := (hφd _ hw₀).continuousAt
    rw [ContinuousAt, hφz] at hc
    exact hc.eventually hev
  -- `G = F ∘ σⱼ` on the chart, `F = f ∘ e⁻¹ ∘ Φ⁻¹`: its derivatives of order `< K` vanish on `D`
  set F : ComplexModel n → ℂ := fun v => f ((chartAt (ComplexModel n) (π z)).symm (Φ.invFun v))
    with hFdef
  set G : ComplexModel n → ℂ := fun v => F (monomial k j v) with hGdef
  have hderG : ∀ᶠ v in 𝓝 (W z), v j = 0 → ∀ i < K, ∀ y : ComplexModel n,
      iteratedFDeriv ℂ i G v (fun _ => y) = 0 := by
    filter_upwards [hev', (monomialDomain Φ k j).isOpen.mem_nhds hw₀] with v hv hvS hvj i hi y
    have hvC : π (extendLifted ℓ hw₀ v) ∈ C := by
      rw [hπφ v hvS]
      obtain ⟨hmem, hΦv⟩ := flatInverse_mem Φ hvS hΦsrc
      refine (hflat hmem.1 hmem.2).mpr ?_
      show Φ.toFun (chartAt (ComplexModel n) (π z) _) ∈ _
      rw [hΦv]
      exact (monomial_mem_plane_iff hj).mpr hvj
    have h1 := hv hvC
    have hφn : ∀ᶠ w in 𝓝 v,
        MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (extendLifted ℓ hw₀) w := by
      filter_upwards [(monomialDomain Φ k j).isOpen.mem_nhds hvS] with w hw
      exact hφd w hw
    have h2 := comp_mem_idealPow_pointIdeal hφn K h1
    have heq : (f ∘ π) ∘ extendLifted ℓ hw₀ =ᶠ[𝓝 v] G := by
      filter_upwards [(monomialDomain Φ k j).isOpen.mem_nhds hvS] with w hw
      simp only [Function.comp_apply, hGdef, hFdef]
      rw [hπφ w hw]
    have h3 := mem_idealPow_congr h2 heq
    have hGhol : HolomorphicAt n G v := GermIdealOrder.holomorphicAt_of_mem_idealPow h3
    have h4 := (mem_idealPow_pointIdeal_iff_iteratedFDeriv hGhol K).mp h3 i hi
    simp only [complexChartAt, chartAt_self_eq] at h4
    have h5 : iteratedFDeriv ℂ i G v = 0 := by simpa using h4
    rw [h5]
    rfl
  -- `F` is holomorphic near `0 = Φ (e (π z))`
  have hTnhds : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ Φ.target := by
    rw [← hΦx]
    exact Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun hx'.2)
  have hιT : Tendsto (fun w => (chartAt (ComplexModel n) (π z)).symm (Φ.invFun w)) (𝓝 0)
      (𝓝 (π z)) := by
    rw [← hΦx]
    exact tendsto_flatInverse Φ hx'
  have hιd : ∀ w ∈ Φ.target, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (fun w => (chartAt (ComplexModel n) (π z)).symm (Φ.invFun w)) w := by
    intro w hw
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.invFun w :=
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hw)).mdifferentiableAt
    exact (mdifferentiableAt_chart_symm (hΦsrc (Φ.mapsTo_invFun hw))).comp w h1
  have hFd : ∀ᶠ w in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F w := by
    filter_upwards [hTnhds.eventually_nhds, hιT.eventually hf.eventually] with w hw hfw
    have hιw : ∀ᶠ w' in 𝓝 w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
        (fun w => (chartAt (ComplexModel n) (π z)).symm (Φ.invFun w)) w' :=
      hw.mono fun w' hw' => hιd w' hw'
    exact mdifferentiableAt_iff_differentiableAt.mp (holomorphicAt_comp_map hιw hfw).self_of_nhds
  obtain ⟨U₀, hU₀F, hU₀o, h0U₀⟩ := eventually_nhds_iff.mp hFd
  have hFU₀ : DifferentiableOn ℂ F U₀ := fun w hw => (hU₀F w hw).differentiableWithinAt
  have hFan : AnalyticOnNhd ℂ F U₀ := analyticOnNhd_of_differentiableOn hU₀o hFU₀
  have hFcd : ContDiffOn ℂ ∞ F U₀ := hFan.contDiffOn hU₀o.uniqueDiffOn
  have hU₁o : IsOpen (monomial k j ⁻¹' U₀) := hU₀o.preimage (contDiff_monomial k j).continuous
  have hGcd : ContDiffOn ℂ ∞ G (monomial k j ⁻¹' U₀) :=
    hFcd.comp (contDiff_monomial k j).contDiffOn fun _ hv => hv
  -- the base direction `h₀ = W z + e_j`, whose lifted point over `0` is `W z`
  have hh₀j : (W z + EuclideanSpace.single j (1 : ℂ)) j = 1 := by simp [hWj]
  have hlift₀ : liftPoint k j 0 (W z + EuclideanSpace.single j (1 : ℂ)) = W z := by
    ext i
    simp only [liftPoint_apply, hh₀j, div_one]
    by_cases hik : i.1 < k
    · simp [hik, hWt i hik]
    · by_cases hij : i = j
      · subst hij; simp [hik, hWj]
      · simp [hik, hij]
  have hcont : ContinuousAt (fun p : ComplexModel n × ComplexModel n => liftPoint k j p.1 p.2)
      (0, W z + EuclideanSpace.single j (1 : ℂ)) := by
    have hcd : ContDiffAt ℂ 1 (fun p : ComplexModel n × ComplexModel n => liftPoint k j p.1 p.2)
        (0, W z + EuclideanSpace.single j (1 : ℂ)) := by
      refine (contDiffAt_piLp (p := 2)).2 fun i => ?_
      have hc1 : ∀ l : Fin n, ContDiff ℂ 1 fun p : ComplexModel n × ComplexModel n => p.1 l :=
        fun l => (EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).contDiff.comp contDiff_fst
      have hc2 : ∀ l : Fin n, ContDiff ℂ 1 fun p : ComplexModel n × ComplexModel n => p.2 l :=
        fun l => (EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).contDiff.comp contDiff_snd
      simp only [liftPoint_apply]
      split_ifs
      · exact (hc1 i).contDiffAt
      · exact contDiffAt_const
      · exact (hc2 i).contDiffAt.div (hc2 j).contDiffAt (by simp [hh₀j])
    exact hcd.continuousAt
  have hT : Tendsto (fun p : ComplexModel n × ComplexModel n => liftPoint k j p.1 p.2)
      (𝓝 (0, W z + EuclideanSpace.single j (1 : ℂ))) (𝓝 (W z)) := by
    have h := hcont.tendsto
    simp only [hlift₀] at h
    exact h
  have hcj : ContinuousAt (fun p : ComplexModel n × ComplexModel n => p.2 j)
      (0, W z + EuclideanSpace.single j (1 : ℂ)) :=
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous.comp continuous_snd).continuousAt
  have hP : ∀ᶠ p : ComplexModel n × ComplexModel n in 𝓝 (0, W z + EuclideanSpace.single j (1 : ℂ)),
      (liftPoint k j p.1 p.2 j = 0 → ∀ i < K, ∀ y : ComplexModel n,
        iteratedFDeriv ℂ i G (liftPoint k j p.1 p.2) (fun _ => y) = 0) ∧ p.2 j ≠ 0 ∧ p.1 ∈ U₀ :=
    (hT.eventually hderG).and ((hcj.eventually_ne (by simp [hh₀j])).and
      (continuousAt_fst.eventually (hU₀o.mem_nhds h0U₀)))
  rw [nhds_prod_eq] at hP
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := Filter.eventually_prod_iff.mp hP
  obtain ⟨V, hVpb, hVo, hh₀V⟩ := mem_nhds_iff.mp hpb
  -- the derivatives of order `< K` of `F` vanish on the plane near `0`
  have hmain : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ complexCoordinatePlane n k →
      ∀ a < K, iteratedFDeriv ℂ a F w = 0 := by
    filter_upwards [hpa] with w hw hwk a ha
    have hwU : w ∈ U₀ := (hpab hw (hVpb hh₀V)).2.2
    refine eq_zero_of_symmetric_of_apply_diag_on_open _
      (fun σ m => ((hFan w hwU).contDiffAt).iteratedFDeriv_comp_perm m σ) hVo ⟨_, hh₀V⟩
      fun h hh => ?_
    obtain ⟨hG0, hhj, -⟩ := hpab hw (hVpb hh)
    have hline : (fun t : ℂ => F (w + t • h)) =
        fun t : ℂ => G (liftPoint k j w h + t • liftDir k j h) := by
      funext t
      simp only [hGdef]
      rw [monomial_liftPoint_add hj hwk hhj t]
    have hlU : liftPoint k j w h ∈ monomial k j ⁻¹' U₀ := by
      show monomial k j (liftPoint k j w h) ∈ U₀
      have h0 := monomial_liftPoint_add hj hwk hhj 0
      simp only [zero_smul, add_zero] at h0
      rw [h0]; exact hwU
    rw [← iteratedDeriv_comp_line hU₀o hFcd hwU h a, hline,
      iteratedDeriv_comp_line hU₁o hGcd hlU (liftDir k j h) a]
    exact hG0 (by simp [liftPoint_apply, not_lt.mpr hj]) a ha (liftDir k j h)
  have hvan : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ complexCoordinatePlane n k →
      ∀ L : List (ComplexModel n), L.length < K → iterDeriv L F w = 0 := by
    filter_upwards [hmain, hU₀o.mem_nhds h0U₀] with w hw hwU hwk L hL
    rw [iterDeriv_eq_iteratedFDeriv hU₀o hFU₀ L hwU, hw hwk L.length hL]
    rfl
  have hq : (0 : ComplexModel n) ∈ complexCoordinatePlane n k := fun i _ => rfl
  have hNP : InNormalPow k 0 K F := inNormalPow_of_iterDeriv_eq_zero K hq hFd hvan
  -- pull back along the flattening coordinates
  have hψx : (fun p => Φ.toFun (chartAt (ComplexModel n) (π z) p)) (π z) = 0 := hΦx
  have hψ : ∀ᶠ p in 𝓝 (π z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (fun p => Φ.toFun (chartAt (ComplexModel n) (π z) p)) p := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hx'] with p hp
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.toFun
        (chartAt (ComplexModel n) (π z) p) :=
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hp.2)).mdifferentiableAt
    exact h1.comp p (mdifferentiableAt_chart hp.1)
  have hψI : ∀ i : Fin n, k ≤ i.1 → (vanishingIdeal (n := n) C).mem (π z)
      (fun p => Φ.toFun (chartAt (ComplexModel n) (π z) p) i) :=
    fun i hi => flatCoord_mem_vanishingIdeal Φ hflat hi hx'
  refine mem_idealPow_of_inNormalPow (x := π z)
    (ψ := fun p => Φ.toFun (chartAt (ComplexModel n) (π z) p)) hψx hψ hψI K hNP ?_
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hx'] with p hp
  simp only [hFdef]
  rw [flatInverse_flat Φ hp]

/-! ### The controlled transform at the points of the exceptional divisor -/

/-- **A controlled transform inside `𝒪(-D)` forces a higher order** (for Włodarczyk 2005, Step 2a
of `pr:resol`; the blowup half of TN-CLASSICAL's `hir:nonmonomial-transform`): if `C ⊆ cosupp(𝔞, μ)`
for a coherent `𝔞` and `σ^c(𝔞, μ) ⊆ 𝒪(-D)` at a point `z` over `C`, then `ord_{π z} 𝔞 ≥ μ + 1`.
Indeed `π^*𝔞 = 𝒪(-μD) σ^c(𝔞, μ) ⊆ 𝒪(-D)^{μ+1}` at `z`, so `𝔞 ⊆ 𝓘_C^{μ+1}` at `π z`. -/
theorem mem_cosupport_succ_of_controlledTransform_le (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hsub : C ⊆ cosupport n univ 𝔞 μ) {z : Y}
    (hz : π z ∈ C)
    (hle : ∀ g, (BlowupControlledTransform.controlledTransform hπ 𝔞 μ).mem z g →
      (exceptionalDivisor hπ).ideal.mem z g) :
    π z ∈ cosupport n univ 𝔞 (μ + 1) := by
  refine ⟨mem_univ _, fun a ha => ?_⟩
  have hahol : HolomorphicAt n a (π z) :=
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 ha
  have hπd : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have haπ : HolomorphicAt n (a ∘ π) z := holomorphicAt_comp_map hπd hahol
  have h1 : (GermIdeal.pullback (m := n) π 𝔞).mem z (a ∘ π) :=
    BlowupDerivativeIdeal.comp_mem_pullback ha haπ (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp)
  rw [pullback_eq_mul_controlledTransform_of_subset_cosupport hπ h𝔞 hsub] at h1
  have h2 : (idealPow (exceptionalDivisor hπ).ideal (μ + 1)).mem z (a ∘ π) :=
    mem_idealPow_succ_iff.mpr ((show IsInSpanAt (n := n) (fun s => ∃ p q,
      (idealPow (exceptionalDivisor hπ).ideal μ).mem z p ∧
        (BlowupControlledTransform.controlledTransform hπ 𝔞 μ).mem z q ∧ s = p * q) z (a ∘ π)
      from h1).mono fun _ ⟨p, q, hp, hq, hs⟩ => ⟨p, q, hp, hle q hq, hs⟩)
  have h3 := mem_idealPow_vanishingIdeal_of_pullback_mem hπ hz hahol h2
  have h4 : (idealPow (pointIdeal n (π z)) (μ + 1)).mem (π z) a :=
    mem_idealPow_of_mem_at (𝔞 := vanishingIdeal (n := n) C)
      (fun g (hg : (vanishingIdeal (n := n) C).mem (π z) g) =>
        mem_pointIdeal_of_apply_eq_zero hg.1 (hg.2.self_of_nhds hz)) (μ + 1) h3
  exact ⟨a, h4, Eventually.of_forall fun _ _ => rfl⟩

/-- **Where the order along the centre is exactly `μ`, the controlled transform is not in `𝒪(-D)`**:
if `C ⊆ cosupp(𝔞, μ)` and `ord_{π z} 𝔞 ≤ μ`, some germ of `σ^c(𝔞, μ)` at `z` is not in `𝒪(-D)`. -/
theorem exists_not_mem_exceptionalDivisor (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hsub : C ⊆ cosupport n univ 𝔞 μ) {z : Y} (hz : π z ∈ C)
    (hord : π z ∉ cosupport n univ 𝔞 (μ + 1)) :
    ∃ g, (BlowupControlledTransform.controlledTransform hπ 𝔞 μ).mem z g ∧
      ¬ (exceptionalDivisor hπ).ideal.mem z g := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact hord (mem_cosupport_succ_of_controlledTransform_le hπ h𝔞 hsub hz h)

/-- **The controlled transform and the strict transform of a closed set** (the second clause of the
blowup half of `hir:nonmonomial-transform`): if `C ⊆ cosupp(𝔟, o)`, `𝔟` coherent, and at a point `z`
of the strict transform `H'` of a closed `H` the controlled transform `σ^c(𝔟, o)` lies in `𝓘_{H'}`,
then arbitrarily close to `π z` there are points `y ∈ H \ C` with `𝔟 ⊆ 𝓘_H` at `y`.  Proof:
`σ^c(𝔟, o) ⊆ 𝓘_{H'}` propagates to the points of `H' \ D` near `z` (coherence), which are dense in
`H'`; there `π^*𝔟 = 𝒪(-oD) σ^c(𝔟, o) ⊆ 𝓘_{H'}`, and the section of `π` over `X \ C` carries the
vanishing down to `H` near `π z'`. -/
theorem frequently_le_vanishingIdeal_of_controlledTransform_le (hπ : IsBlowupAlong n C π)
    {𝔟 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) {o : ℕ} (hsub : C ⊆ cosupport n univ 𝔟 o)
    {H : Set X} {z : Y} (hzH : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C H)
    (hle : ∀ g, (BlowupControlledTransform.controlledTransform hπ 𝔟 o).mem z g →
      (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H)).mem z g) :
    ∃ᶠ y in 𝓝 (π z), y ∈ H \ C ∧ ∀ a, 𝔟.mem y a → (vanishingIdeal (n := n) H).mem y a := by
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hσc := isCoherent_controlledTransform_of_subset_cosupport hπ h𝔟 hsub
  have hev := eventually_le_vanishingIdeal_of_isCoherent hσc hle
  have hfreq : ∃ᶠ z' in 𝓝 z, z' ∈ π ⁻¹' (H \ C) := mem_closure_iff_frequently.mp hzH
  obtain ⟨sec, hsec, hπsec, hsecπ⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  refine (hπc.tendsto z).frequently ((hfreq.and_eventually hev).mono fun z' ⟨hz'HC, hz'le⟩ => ?_)
  refine ⟨hz'HC, fun a ha => ?_⟩
  have hahol : HolomorphicAt n a (π z') :=
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 ha
  have hπd : ∀ᶠ w in 𝓝 z', MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have haπ : HolomorphicAt n (a ∘ π) z' := holomorphicAt_comp_map hπd hahol
  have h1 : (GermIdeal.pullback (m := n) π 𝔟).mem z' (a ∘ π) :=
    BlowupDerivativeIdeal.comp_mem_pullback ha haπ (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp)
  rw [pullback_eq_mul_controlledTransform_of_subset_cosupport hπ h𝔟 hsub] at h1
  -- `a ∘ π` vanishes on `H'` near `z'`
  have hvanish : ∀ᶠ w in 𝓝 z', w ∈ BlowupStrictSubmanifold.geoStrictTransform π C H →
      (a ∘ π) w = 0 := by
    obtain ⟨-, K, r, c, hr, -, hsum⟩ := (show IsInSpanAt (n := n) (fun s => ∃ p q,
      (idealPow (exceptionalDivisor hπ).ideal o).mem z' p ∧
        (BlowupControlledTransform.controlledTransform hπ 𝔟 o).mem z' q ∧ s = p * q) z' (a ∘ π)
      from h1)
    choose p q hp hq hpq using hr
    have hqv : ∀ k, ∀ᶠ w in 𝓝 z', w ∈ BlowupStrictSubmanifold.geoStrictTransform π C H →
        q k w = 0 := fun k => (hz'le _ (hq k)).2
    filter_upwards [hsum, eventually_all.mpr hqv] with w hw hwq hwH
    rw [hw]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hpq k]
    simp [hwq k hwH]
  -- carry the vanishing down along the section of `π` over `X \ C`
  have hz'C : π z' ∈ Cᶜ := hz'HC.2
  have hcont : Tendsto sec (𝓝 ⟨π z', hz'C⟩) (𝓝 z') := by
    have h := hsec.continuous.continuousAt (x := ⟨π z', hz'C⟩)
    rwa [ContinuousAt, hsecπ z' hz'C] at h
  have h2 := hcont.eventually hvanish
  rw [nhds_subtype_eq_comap, Filter.eventually_comap] at h2
  refine ⟨hahol, ?_⟩
  filter_upwards [h2, hπ.1.1.isOpen_compl.mem_nhds hz'C] with y hy hyC hyH
  have hsy : π (sec ⟨y, hyC⟩) = y := congrFun hπsec ⟨y, hyC⟩
  have hmem : sec ⟨y, hyC⟩ ∈ BlowupStrictSubmanifold.geoStrictTransform π C H :=
    subset_closure (show π (sec ⟨y, hyC⟩) ∈ H \ C by rw [hsy]; exact ⟨hyH, hyC⟩)
  have := hy ⟨y, hyC⟩ rfl hmem
  simpa [Function.comp_apply, hsy] using this

/-- **Contrapositive**: if near `π z` the ideal `𝔟` lies in `𝓘_H` at no point of `H \ C`, then at a
point `z` of `H'` some germ of `σ^c(𝔟, o)` is not in `𝓘_{H'}`. -/
theorem exists_not_mem_vanishingIdeal_geoStrictTransform (hπ : IsBlowupAlong n C π)
    {𝔟 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) {o : ℕ} (hsub : C ⊆ cosupport n univ 𝔟 o)
    {H : Set X} {z : Y} (hzH : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C H)
    (hnot : ∀ᶠ y in 𝓝 (π z), y ∈ H \ C → ∃ a, 𝔟.mem y a ∧ ¬ (vanishingIdeal (n := n) H).mem y a) :
    ∃ g, (BlowupControlledTransform.controlledTransform hπ 𝔟 o).mem z g ∧
      ¬ (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H)).mem z g := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  obtain ⟨y, hy, hyle⟩ :=
    ((frequently_le_vanishingIdeal_of_controlledTransform_le hπ h𝔟 hsub hzH h).and_eventually
      hnot).exists
  obtain ⟨a, ha, hna⟩ := hyle hy.1
  exact hna (hy.2 a ha)

end Blowup

end

end TranscendentalNakamaye.Pending.ExceptionalIdealPushforward
