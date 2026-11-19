import Hironaka.Analytic.Unibranch.HironakaG10FrRouteG

/-!
# Route G at varying fibre points (step G2): Frisch's acyclicity locus is constructible

Plan item G10FR-2.G2 (`work/hironaka-run0081-20261117/G10FR/frisch-constructibility.md` §4.2).
Frisch's Prop. (III,1), step 2 (Invent. Math. 4 (1967), p. 128) moves the fibre point into the parameters:
`u'((s,x), y) = u(s, x + y)`; the fibre complex of `u'` at the parameter `(s,x)` and the point `0` is the
fibre complex of `u` at `s` and the point `x` (`fibreExactAt_translate`). With a linear identification
`e : ℂᵐ ≃ ℂᵈ × ℂᵗ` of the new parameter space, route G (`HironakaG10FrRouteG.isConstructibleNear_fibreExact`)
gives **`isConstructibleNear_fibreExact_varying`**: for a complex `(u, v)` over `T × ℂᵗ` (`T` analytic near
`s₀`), the set `{(s, x) | s ∈ T, (u(s,·), v(s,·)) exact at x}` is constructible near `(s₀, x₀)` (read in the
coordinates `e`) — Frisch's Prop. (III,6) + Lemme (IV,5) conclusion — under the two explicit hypotheses of
route G (relative exact starts, generic flatness at a fixed fibre point) for the parameter space `ℂᵐ`.

Lane G10FR, run 0081. Blueprint: `hironaka-g10fr-route-g.tex`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Matrix

namespace Hironaka.Analytic.Unibranch.HironakaG10FrTranslate

open Hironaka Hironaka
open OkaRelationSheaf OkaGermBridge HolGerm HironakaG10FlatResolutionStart
  HironakaG10FlatGermChain HironakaG10LocSheafExact HironakaG10LocFibreOpen HironakaG10LocRelative
  Hironaka.Analytic.Unibranch.HironakaG10FrRouteG

noncomputable section

section Translate

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem germMat_translate {ι κ : Type*} (f : ι → κ → X → ℂ) (x : X) (hf : ∀ i j, HolAt (f i j) x) :
    germMat (0 : X) (fun i j y => f i j (x + y)) = germMat x f := by
  refine Matrix.ext fun i j => ?_
  simp only [germMat, Matrix.of_apply]
  rw [germAt_of_holAt (hf i j).translate, germAt_of_holAt (hf i j)]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp only [zero_add]

/-- Germ exactness is invariant under translation of the point to `0`. -/
theorem exact_translate_iff {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁]
    (G : ι₁ → ι₂ → X → ℂ) (F : ι₀ → ι₁ → X → ℂ) (x : X) (hG : ∀ j k, HolAt (G j k) x)
    (hF : ∀ i j, HolAt (F i j) x) :
    (∀ a, IsRelationAt (fun i j y => F i j (x + y)) 0 a →
        IsCombinationAt (columns fun j k y => G j k (x + y)) 0 a) ↔
      ∀ a, IsRelationAt F x a → IsCombinationAt (columns G) x a := by
  rw [exact_iff_matExact (fun i j => (hF i j).translate) (fun j k => (hG j k).translate),
    exact_iff_matExact hF hG, germMat_translate F x hF, germMat_translate G x hG]

end Translate

variable {d t m : ℕ}

/-- The translated matrix: the fibre point becomes a parameter, read through `e`. -/
def translateMat (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t) {ι κ : Type*}
    (F : ι → κ → ComplexModel d × ComplexModel t → ℂ) : ι → κ → ComplexModel m × ComplexModel t → ℂ :=
  fun i j q => F i j ((e q.1).1, (e q.1).2 + q.2)

/-- The translation map `(w, y) ↦ ((e w).1, (e w).2 + y)`. -/
def transMap (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t) :
    ComplexModel m × ComplexModel t → ComplexModel d × ComplexModel t :=
  fun q => ((e q.1).1, (e q.1).2 + q.2)

theorem continuous_transMap (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t) :
    Continuous (transMap e) :=
  ((continuous_fst.comp (e.continuous.comp continuous_fst))).prodMk
    ((continuous_snd.comp (e.continuous.comp continuous_fst)).add continuous_snd)

theorem differentiable_transMap (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t) :
    Differentiable ℂ (transMap e) := by
  intro q
  have h1 : DifferentiableAt ℂ (fun q : ComplexModel m × ComplexModel t => e q.1) q :=
    e.differentiableAt.comp q differentiableAt_fst
  exact h1.fst.prodMk (h1.snd.add differentiableAt_snd)

theorem holAt_translateMat (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t)
    {f : ComplexModel d × ComplexModel t → ℂ} {q : ComplexModel m × ComplexModel t}
    (hf : HolAt f (transMap e q)) : HolAt (fun q => f (transMap e q)) q :=
  hf.comp (continuous_transMap e) fun r => differentiable_transMap e r

theorem transMap_zero (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t)
    (w : ComplexModel m) : transMap e (w, 0) = e w := by
  simp [transMap]

/-- **Translation of the fibre point (Frisch (III,1), step 2).** -/
theorem fibreExactAt_translate (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t)
    {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
    (G : ι₁ → ι₂ → ComplexModel d × ComplexModel t → ℂ)
    (F : ι₀ → ι₁ → ComplexModel d × ComplexModel t → ℂ) (w : ComplexModel m)
    (hG : ∀ j k, HolAt (fib G (e w).1 j k) (e w).2) (hF : ∀ i j, HolAt (fib F (e w).1 i j) (e w).2) :
    FibreExactAt (translateMat e G) (translateMat e F) w 0 ↔ FibreExactAt G F (e w).1 (e w).2 :=
  exact_translate_iff (fib G (e w).1) (fib F (e w).1) (e w).2 hG hF

/-- **Item 2 (route G), varying fibre points.** For a complex `(u, v)` over `T × ℂᵗ` near `(s₀, x₀)`, with `T`
analytic near `s₀`, the set of `(s, x)` with `s ∈ T` at which the fibre complex is exact at `x` is constructible
near `(s₀, x₀)` (read in the coordinates `e`), under the route-G hypotheses for the parameter space `ℂᵐ`. -/
theorem isConstructibleNear_fibreExact_varying
    (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t)
    (T : Set (ComplexModel d)) (s₀ : ComplexModel d) (x₀ : ComplexModel t) (hT : IsAnalyticNear T s₀)
    (hstart : ∀ P : Set (ComplexModel m), IsAnalyticNear P (e.symm (s₀, x₀)) → ∀ {a b : ℕ}
      (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ),
      (∀ i j, HolAt (A i j) (e.symm (s₀, x₀), 0)) →
      ∃ (c : ℕ) (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
        (Wn : Set (ComplexModel m × ComplexModel t)),
        IsOpen Wn ∧ (e.symm (s₀, x₀), (0 : ComplexModel t)) ∈ Wn ∧ RelExactStartOn P Wn G A)
    (hGF : ∀ P : Set (ComplexModel m), IsAnalyticNear P (e.symm (s₀, x₀)) → e.symm (s₀, x₀) ∈ P →
      ∀ {a b c : ℕ} (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn →
      (e.symm (s₀, x₀), (0 : ComplexModel t)) ∈ Wn → RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ e.symm (s₀, x₀) ∈ N ∧ IsHolZeroSetOn N P'' ∧
        P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 (e.symm (s₀, x₀)), p ∈ P → p ∉ P'' → FibreExactAt G A p 0)
    {a b n : ℕ} (u : Fin b → Fin n → ComplexModel d × ComplexModel t → ℂ)
    (v : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (hu : ∀ j l, HolAt (u j l) (s₀, x₀)) (hv : ∀ i j, HolAt (v i j) (s₀, x₀))
    (hcomp : ∀ᶠ q in 𝓝 (s₀, x₀), q.1 ∈ T → ∀ i l, ∑ j, v i j q * u j l q = 0) :
    IsConstructibleNear (e ⁻¹' {q | q.1 ∈ T ∧ FibreExactAt u v q.1 q.2}) (e.symm (s₀, x₀)) := by
  set w₀ := e.symm (s₀, x₀) with hw₀
  have hew₀ : e w₀ = (s₀, x₀) := by simp [hw₀]
  have htr₀ : transMap e (w₀, 0) = (s₀, x₀) := by rw [transMap_zero, hew₀]
  -- the translated parameter set
  set P' : Set (ComplexModel m) := e ⁻¹' {q | q.1 ∈ T} with hP'def
  have hP' : IsAnalyticNear P' w₀ := by
    obtain ⟨N, hN, hsN, r, g, hg, hgT⟩ := hT
    have hcont : Continuous fun w : ComplexModel m => (e w).1 :=
      continuous_fst.comp e.continuous
    refine ⟨(fun w => (e w).1) ⁻¹' N, hN.preimage hcont, by simpa [hew₀] using hsN, r,
      fun i w => g i (e w).1, fun i => ?_, ?_⟩
    · intro w hw
      have hd : DifferentiableAt ℂ (fun w : ComplexModel m => (e w).1) w :=
        (e.differentiableAt (x := w)).fst
      exact ((hg i _ hw).differentiableAt (hN.mem_nhds hw)).comp w hd |>.differentiableWithinAt
    · ext w
      have h := Set.ext_iff.mp hgT (e w).1
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hP'def] at h ⊢
      exact h
  -- the translated complex
  have htend : Tendsto (transMap e) (𝓝 (w₀, 0)) (𝓝 (s₀, x₀)) := by
    have := (continuous_transMap e).tendsto (w₀, 0)
    rwa [htr₀] at this
  have hu' : ∀ j l, HolAt (translateMat e u j l) (w₀, 0) := fun j l =>
    holAt_translateMat e (f := u j l) (by rw [htr₀]; exact hu j l)
  have hv' : ∀ i j, HolAt (translateMat e v i j) (w₀, 0) := fun i j =>
    holAt_translateMat e (f := v i j) (by rw [htr₀]; exact hv i j)
  have hcomp' : ∀ᶠ q in 𝓝 (w₀, (0 : ComplexModel t)), q.1 ∈ P' →
      ∀ i l, ∑ j, translateMat e v i j q * translateMat e u j l q = 0 := by
    filter_upwards [htend.eventually hcomp] with q hq hqP
    exact hq hqP
  have hmain := isConstructibleNear_fibreExact (0 : ComplexModel t) w₀ hstart hGF
    (translateMat e u) (translateMat e v) hu' hv' P' hP' hcomp'
  -- identify the two loci near `w₀`
  have hhol : ∀ᶠ w in 𝓝 w₀, (∀ j l, HolAt (fib u (e w).1 j l) (e w).2) ∧
      ∀ i j, HolAt (fib v (e w).1 i j) (e w).2 := by
    have he : Tendsto (fun w => e w) (𝓝 w₀) (𝓝 (s₀, x₀)) := by
      have := e.continuous.tendsto w₀
      rwa [hew₀] at this
    have hall : ∀ᶠ q in 𝓝 (s₀, x₀), (∀ j l, HolAt (u j l) q) ∧ ∀ i j, HolAt (v i j) q :=
      (eventually_all.mpr fun j => eventually_all.mpr fun l => (hu j l).eventually_nhds).and
        (eventually_all.mpr fun i => eventually_all.mpr fun j => (hv i j).eventually_nhds)
    filter_upwards [he.eventually hall] with w hw
    have hpt : ((fun y : ComplexModel t => ((e w).1, y)) (e w).2) = e w := rfl
    refine ⟨fun j l => ?_, fun i j => ?_⟩
    · have h := hw.1 j l
      rw [← hpt] at h
      exact HolAt.comp (φ := fun y : ComplexModel t => ((e w).1, y)) h
        (continuous_const.prodMk continuous_id)
        fun y => (differentiableAt_const _).prodMk differentiableAt_id
    · have h := hw.2 i j
      rw [← hpt] at h
      exact HolAt.comp (φ := fun y : ComplexModel t => ((e w).1, y)) h
        (continuous_const.prodMk continuous_id)
        fun y => (differentiableAt_const _).prodMk differentiableAt_id
  obtain ⟨N₀, hN₀, hN₀o, hw₀N₀⟩ := eventually_nhds_iff.mp hhol
  refine hmain.congr hN₀o hw₀N₀ ?_
  ext w
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hP'def]
  constructor
  · rintro ⟨⟨hwT, hex⟩, hwN⟩
    exact ⟨⟨hwT, (fibreExactAt_translate e u v w (hN₀ w hwN).1 (hN₀ w hwN).2).mp hex⟩, hwN⟩
  · rintro ⟨⟨hwT, hex⟩, hwN⟩
    exact ⟨⟨hwT, (fibreExactAt_translate e u v w (hN₀ w hwN).1 (hN₀ w hwN).2).mpr hex⟩, hwN⟩

end
end Hironaka.Analytic.Unibranch.HironakaG10FrTranslate
