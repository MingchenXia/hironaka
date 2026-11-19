import Hironaka.Analytic.BergmanSubadditivity

set_option autoImplicit false

/-!
# Tools for the subadditivity of multiplier ideals (Demailly--Ein--Lazarsfeld)

Source: Demailly--Ein--Lazarsfeld, *A subadditivity property of multiplier ideals*, Michigan
Math. J. **48** (2000), Theorem 2.6, cited by Copy-4 as `eq:subadditivity`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex`, `sec:positive-current`):
`𝓘(φ₁ + φ₂) ⊆ 𝓘(φ₁) 𝓘(φ₂)`.  This module records two self-contained ingredients of our proof
of it.

* `exists_productExtension` — **`L²` extension from the diagonal for two weights.**  On a bounded
  convex open `B ⊆ ℂ^d`, for `P₁, P₂` plurisubharmonic on `B` and `f` holomorphic on `B`, there is
  `G` holomorphic on `B × B` with `G(y, y) = f(y)` and
  `∫∫_{B×B} |G(a,b)|² e^{-P₁(a)} e^{-P₂(b)} ≤ C ∫_B |f|² e^{-(P₁+P₂)}`, `C = C(d, R)`.  This is the
  extension step of TN23's `BergmanSubadditivity.bergmanSup_add_le` (Ohsawa--Takegoshi from the
  coordinate subspace `u = 0` after `(a, b) ↦ (a, b - a)`), with the weights `c₁P, c₂P` there
  replaced by two arbitrary plurisubharmonic weights; the proof is the same.
* `exists_sum_mul_of_cols_rows` — **the tensor step, in coordinates.**  If every column of a
  finite matrix `C` lies in a subspace `A` and every row lies in a subspace `B`, then
  `C = ∑ₖ aₖ bₖᵀ` with `aₖ ∈ A`, `bₖ ∈ B`; that is, `(A ⊗ W) ∩ (V ⊗ B) = A ⊗ B`.

Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.MultiplierSubadditivityTools

noncomputable section

open BergmanSupWeight OhsawaTakegoshiSubspace BergmanSubadditivity

/-! ### The tensor step -/

section Tensor

variable {ι κ : Type*} [Fintype κ]

/-- **`(A ⊗ W) ∩ (V ⊗ B) = A ⊗ B`, in coordinates.**  A matrix all of whose columns lie in `A` and
all of whose rows lie in `B` is a finite sum of products `a bᵀ` with `a ∈ A`, `b ∈ B`. -/
theorem exists_sum_mul_of_cols_rows (A : Submodule ℂ (ι → ℂ)) (B : Submodule ℂ (κ → ℂ))
    (C : ι → κ → ℂ) (hcol : ∀ β, (fun α => C α β) ∈ A) (hrow : ∀ α, C α ∈ B) :
    ∃ (r : ℕ) (a : Fin r → ι → ℂ) (b : Fin r → κ → ℂ), (∀ k, a k ∈ A) ∧ (∀ k, b k ∈ B) ∧
      ∀ α β, C α β = ∑ k, a k α * b k β := by
  classical
  set r := Module.finrank ℂ B with hr
  let bas : Module.Basis (Fin r) ℂ B := Module.finBasis ℂ B
  -- coordinates of the rows in the basis, extended to linear functionals on `κ → ℂ`
  have hext : ∀ k : Fin r, ∃ g : (κ → ℂ) →ₗ[ℂ] ℂ, g.comp B.subtype = bas.coord k :=
    fun k => LinearMap.exists_extend (bas.coord k)
  choose g hg using hext
  refine ⟨r, fun k α => bas.coord k ⟨C α, hrow α⟩, fun k => (bas k : κ → ℂ), ?_, ?_, ?_⟩
  · intro k
    -- `α ↦ g_k (C α) = ∑_β g_k(e_β) C α β` is a combination of columns
    have hgk : (fun α => bas.coord k ⟨C α, hrow α⟩) =
        ∑ β, g k (Pi.single β 1) • fun α => C α β := by
      funext α
      have h1 : bas.coord k ⟨C α, hrow α⟩ = g k (C α) := by
        rw [← hg k]
        rfl
      rw [h1, Finset.sum_apply]
      have h2 : C α = ∑ β, C α β • (Pi.single β (1 : ℂ) : κ → ℂ) := by
        funext β'
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [h2]
      simp only [map_sum, map_smul, smul_eq_mul, Pi.smul_apply]
      exact Finset.sum_congr rfl fun β _ => mul_comm _ _
    show (fun α => bas.coord k ⟨C α, hrow α⟩) ∈ A
    rw [hgk]
    exact Submodule.sum_mem _ fun β _ => Submodule.smul_mem _ _ (hcol β)
  · intro k
    exact (bas k).2
  · intro α β
    have h := bas.sum_repr ⟨C α, hrow α⟩
    have h' := congrArg (fun v : B => (v : κ → ℂ) β) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h'
    rw [← h']
    rfl

end Tensor

/-! ### `L²` extension from the diagonal for two weights -/

section Extension

/-- `e^{-(x + y)} = e^{-x} e^{-y}` below `+∞`. -/
theorem multiplierWeight_one_add_one {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    multiplierWeight 1 (x + y) = multiplierWeight 1 x * multiplierWeight 1 y := by
  have h := multiplierWeight_one_add one_pos one_pos hx hy
  simpa only [EReal.coe_one, one_mul] using h

/-- **`L²` extension from the diagonal of `B × B` for two weights** (Ohsawa--Takegoshi), for the
Borel structure `borel (ℂ^d)`. -/
theorem exists_productExtension (d : ℕ) : by
    letI : MeasurableSpace (ComplexModel d) := borel _
    letI : BorelSpace (ComplexModel d) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ B : Set (ComplexModel d), IsOpen B → Convex ℝ B → (∀ z ∈ B, ‖z‖ < R) →
      ∀ P₁ P₂ : ComplexModel d → EReal, PlurisubharmonicOn P₁ B → PlurisubharmonicOn P₂ B →
      ∀ f : ComplexModel d → ℂ, DifferentiableOn ℂ f B →
      ∃ G : ComplexModel d × ComplexModel d → ℂ, DifferentiableOn ℂ G (B ×ˢ B) ∧
        (∀ y ∈ B, G (y, y) = f y) ∧
        (∫⁻ p in B ×ˢ B, ENNReal.ofReal (‖G p‖ ^ 2) *
            (multiplierWeight 1 (P₁ p.1) * multiplierWeight 1 (P₂ p.2))
              ∂(volume.prod volume)) ≤
          ENNReal.ofReal C * ∫⁻ y in B, multiplierDensity (fun y => P₁ y + P₂ y) 1 f y := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  let _ : MeasurableSpace (ComplexModel (d + d)) := borel _
  have _ : BorelSpace (ComplexModel (d + d)) := ⟨rfl⟩
  intro R hR
  obtain ⟨C, hC, hOT⟩ := exists_extension_from_subspace d d (3 * R) (by linarith)
  refine ⟨C, hC, fun B hB hconv hbd P₁ P₂ hP₁ hP₂ f hf => ?_⟩
  have hBm : MeasurableSet B := hB.measurableSet
  have hP₁top : ∀ z ∈ B, P₁ z ≠ ⊤ := fun z hz => (hP₁ z hz).ne_top
  have hP₂top : ∀ z ∈ B, P₂ z ≠ ⊤ := fun z hz => (hP₂ z hz).ne_top
  -- the domain `Ω = {(z, u) : z ∈ B, z + u ∈ B}`
  set L : ComplexModel (d + d) →L[ℂ] ComplexModel d := fstCLM d + sndCLM d with hLdef
  have hL : ∀ a b : ComplexModel d, L (join a b) = a + b := fun a b => by
    simp only [hLdef, FunLike.coe_add, Pi.add_apply, fstCLM_join, sndCLM_join]
  set Ω : Set (ComplexModel (d + d)) := fstCLM d ⁻¹' B ∩ L ⁻¹' B with hΩdef
  have hΩo : IsOpen Ω := (hB.preimage (fstCLM d).continuous).inter (hB.preimage L.continuous)
  have hΩc : Convex ℝ Ω :=
    (hconv.linear_preimage ((fstCLM d).toLinearMap.restrictScalars ℝ)).inter
      (hconv.linear_preimage (L.toLinearMap.restrictScalars ℝ))
  have hΩb : ∀ z ∈ Ω, ‖z‖ < 3 * R := by
    intro z hz
    have h1 : ‖fstCLM d z‖ < R := hbd _ hz.1
    have h2 : ‖L z‖ < R := hbd _ hz.2
    have h3 : sndCLM d z = L z - fstCLM d z := by
      simp only [hLdef, FunLike.coe_add, Pi.add_apply, add_sub_cancel_left]
    have h4 : ‖sndCLM d z‖ < 2 * R := by
      rw [h3]
      calc ‖L z - fstCLM d z‖ ≤ ‖L z‖ + ‖fstCLM d z‖ := norm_sub_le _ _
        _ < 2 * R := by linarith
    rw [← join_fst_snd z]
    calc ‖join (fstCLM d z) (sndCLM d z)‖ ≤ ‖fstCLM d z‖ + ‖sndCLM d z‖ := norm_join_le _ _
      _ < 3 * R := by linarith
  -- the weight `Φ(z, u) = P₁(z) + P₂(z + u)`
  set φ : ComplexModel (d + d) → EReal := fun z => P₁ (fstCLM d z) + P₂ (L z) with hφdef
  have hφ : PlurisubharmonicOn φ Ω :=
    PlurisubharmonicOn.add
      (PlurisubharmonicOn.mono (hP₁.comp_continuousLinearMap (fstCLM d)) inter_subset_left)
      (PlurisubharmonicOn.mono (hP₂.comp_continuousLinearMap L) inter_subset_right)
  have hslice : subspaceCLM d d ⁻¹' Ω = B := by
    ext w
    simp only [hΩdef, mem_preimage, mem_inter_iff, subspaceCLM_eq_join, fstCLM_join, hL,
      add_zero, and_self]
  have hfB : DifferentiableOn ℂ f (subspaceCLM d d ⁻¹' Ω) := by rw [hslice]; exact hf
  obtain ⟨F, hFhol, hFext, hFint⟩ := hOT Ω hΩo hΩc hΩb φ hφ 1 one_pos f hfB
  have hsliceint : ∫⁻ w in subspaceCLM d d ⁻¹' Ω,
      multiplierDensity (fun w => φ (subspaceCLM d d w)) 1 f w =
        ∫⁻ y in B, multiplierDensity (fun y => P₁ y + P₂ y) 1 f y := by
    rw [hslice]
    refine setLIntegral_congr_fun hBm fun w _ => ?_
    simp only [multiplierDensity, hφdef, subspaceCLM_eq_join, fstCLM_join, hL, add_zero]
  -- `G(a, b) = F(a, b - a)` on `B × B`
  set G : ComplexModel d × ComplexModel d → ℂ := fun p => F (chartT d p) with hGdef
  have hmaps : ∀ a ∈ B, ∀ b ∈ B, chartT d (a, b) ∈ Ω := fun a ha b hb => by
    refine ⟨?_, ?_⟩
    · simp only [mem_preimage, chartT_apply, fstCLM_join]; exact ha
    · simp only [mem_preimage, chartT_apply, hL, add_neg_cancel_left]; exact hb
  have hchartT : ∀ p, chartT d p = (joinCLE d) (p.1, -p.1 + p.2) := fun _ => rfl
  have hdiffT : Differentiable ℂ fun p : ComplexModel d × ComplexModel d => chartT d p := by
    simp only [hchartT]
    exact (joinCLE d).differentiable.comp (differentiable_fst.prodMk
      (differentiable_fst.neg.add differentiable_snd))
  have hGhol : DifferentiableOn ℂ G (B ×ˢ B) :=
    hFhol.comp hdiffT.differentiableOn fun p hp => hmaps p.1 hp.1 p.2 hp.2
  have hpre : chartT d ⁻¹' Ω = B ×ˢ B := by
    ext ⟨a, b⟩
    simp only [hΩdef, mem_preimage, mem_inter_iff, chartT_apply, fstCLM_join, hL,
      add_neg_cancel_left, mem_prod]
  have hmp : MeasurePreserving (chartT d) (volume.prod volume) volume := by
    have hshear : MeasurePreserving (shear (d := d)) (volume.prod volume) (volume.prod volume) :=
      measurePreserving_prod_neg_add volume volume
    have hiso := (IsometryEquiv.toRealLinearIsometryEquivOfMapZero (joinEquiv d).toIsometryEquiv
      (by rw [LinearIsometryEquiv.coe_toIsometryEquiv]; exact map_zero _)).measurePreserving
    rw [IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero] at hiso
    have hjoin : MeasurePreserving (joinCLE d) (volume.prod volume) volume := by
      have := hiso.comp (WithLp.volume_preserving_toLp (ComplexModel d) (ComplexModel d))
      rw [← Measure.volume_eq_prod]
      exact this
    exact hjoin.comp hshear
  refine ⟨G, hGhol, fun y hy => ?_, ?_⟩
  · simp only [hGdef, chartT_apply, neg_add_cancel, ← subspaceCLM_eq_join]
    exact hFext y (by rw [hslice]; exact hy)
  · rw [← hsliceint]
    refine le_trans (le_of_eq ?_) hFint
    calc ∫⁻ p in B ×ˢ B, ENNReal.ofReal (‖G p‖ ^ 2) *
          (multiplierWeight 1 (P₁ p.1) * multiplierWeight 1 (P₂ p.2)) ∂(volume.prod volume)
        = ∫⁻ p in chartT d ⁻¹' Ω, multiplierDensity φ 1 F (chartT d p) ∂(volume.prod volume) := by
          rw [hpre]
          refine setLIntegral_congr_fun (hBm.prod hBm) fun p hp => ?_
          simp only [multiplierDensity, hGdef, hφdef, chartT_apply, fstCLM_join, hL,
            add_neg_cancel_left]
          rw [multiplierWeight_one_add_one (hP₁top _ hp.1) (hP₂top _ hp.2)]
      _ = ∫⁻ z in Ω, multiplierDensity φ 1 F z :=
          hmp.setLIntegral_comp_preimage_emb (chartT d).measurableEmbedding _ _

end Extension

end

end Hironaka.MultiplierSubadditivityTools
