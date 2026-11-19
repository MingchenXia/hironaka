import Hironaka.Analytic.BoxCoeffsIdeal
import Hironaka.Analytic.BergmanSubadditivity

set_option autoImplicit false

/-!
# Torus coefficients on `ℂ^d × ℂ^d`

Step 2 of our route to the DEL00 subadditivity theorem.  For a
function `G` of two variables `a, b ∈ ℂ^d`, read on `ℂ^{d+d}` through `join`, the torus
coefficient at `(x, x)` of index `(α, β)` is the iterated one:

  `torusCoeff (x, x) s (α, β) G = torusCoeff x s α (a ↦ torusCoeff x s β (G a))`

(`torusCoeff_join`), and for a product `G a b = g a * h b` it is
`torusCoeff x s α g * torusCoeff x s β h` (`torusCoeff_join_mul`).  Fubini on the angle box
(`BoxCoeffsIdeal.setIntegral_Icc_eq_angleIntegral`), split along `Fin (d + d) ≃ Fin d ⊕ Fin d`.

The dimension is written `d = d' + 1`, so that `Fin (d + d)` is definitionally
`Fin ((d' + 1 + d') + 1)`, the shape `torusCoeff` is stated for.

Sorry-free.
-/

open Set Filter MeasureTheory Complex
open scoped Topology Real

namespace Hironaka.TorusCoefficientsProduct

noncomputable section

open BergmanSubadditivity

variable {d' : ℕ}

/-- The angle box of `ℂ^{d+d}` is the product of the two angle boxes. -/
theorem setIntegral_Icc_append {G : (Fin (d' + 1 + (d' + 1)) → ℝ) → ℂ} (hG : Continuous G) :
    ∫ θ in Icc (0 : Fin (d' + 1 + (d' + 1)) → ℝ) (fun _ => 2 * π), G θ =
      ∫ θL in Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π),
        ∫ θR in Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π), G (Fin.append θL θR) := by
  set e : ((Fin (d' + 1) → ℝ) × (Fin (d' + 1) → ℝ)) ≃ᵐ (Fin (d' + 1 + (d' + 1)) → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (d' + 1) ⊕ Fin (d' + 1) => ℝ)).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv) with hedef
  have he : ∀ p, e p = Fin.append p.1 p.2 := by
    intro p
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left, ← finSumFinEquiv_apply_left, hedef, MeasurableEquiv.trans_apply,
        MeasurableEquiv.piCongrLeft_apply_apply]
      rfl
    · rw [Fin.append_right, ← finSumFinEquiv_apply_right, hedef, MeasurableEquiv.trans_apply,
        MeasurableEquiv.piCongrLeft_apply_apply]
      rfl
  have hem : MeasurePreserving e (volume.prod volume) volume := by
    have h1 := volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin (d' + 1) ⊕ Fin (d' + 1) => ℝ)
    have h2 := volume_measurePreserving_piCongrLeft (fun _ : Fin (d' + 1 + (d' + 1)) => ℝ)
      finSumFinEquiv
    exact h2.comp h1
  have hpre : e ⁻¹' Icc (0 : Fin (d' + 1 + (d' + 1)) → ℝ) (fun _ => 2 * π) =
      Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π) ×ˢ Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π) := by
    ext p
    simp only [mem_preimage, he, mem_Icc, mem_prod, Pi.le_def]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun i => ?_, fun i => ?_⟩, ⟨fun i => ?_, fun i => ?_⟩⟩
      · have := h1 (Fin.castAdd _ i); rwa [Fin.append_left] at this
      · have := h2 (Fin.castAdd _ i); rwa [Fin.append_left] at this
      · have := h1 (Fin.natAdd _ i); rwa [Fin.append_right] at this
      · have := h2 (Fin.natAdd _ i); rwa [Fin.append_right] at this
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      refine ⟨fun k => ?_, fun k => ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
        · rw [Fin.append_left]; exact h1 i
        · rw [Fin.append_right]; exact h3 i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
        · rw [Fin.append_left]; exact h2 i
        · rw [Fin.append_right]; exact h4 i
  have hint : IntegrableOn (fun p => G (e p))
      (Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π) ×ˢ Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π))
      (volume.prod volume) := by
    have : IntegrableOn G (Icc (0 : Fin (d' + 1 + (d' + 1)) → ℝ) fun _ => 2 * π) volume :=
      hG.integrableOn_Icc
    rwa [← hem.integrableOn_comp_preimage e.measurableEmbedding, hpre] at this
  rw [← hem.map_eq, setIntegral_map_equiv, hpre, setIntegral_prod _ hint]
  simp only [he]

/-! ### Torus points and phases on `ℂ^{d+d}` -/

theorem torusPoint_join (x : ComplexModel (d' + 1)) (s : ℝ) (θ : Fin (d' + 1 + (d' + 1)) → ℝ) :
    torusPoint (m := d' + 1 + d') (join x x) s θ =
      join (torusPoint x s fun i => θ (Fin.castAdd _ i))
        (torusPoint x s fun i => θ (Fin.natAdd _ i)) := by
  ext k
  refine Fin.addCases (m := d' + 1) (n := d' + 1) (fun i => ?_) (fun i => ?_) k
  · have hjc : (join x x) (Fin.castAdd (d' + 1) i) = x i := join_castAdd x x i
    rw [join_castAdd]
    simp [torusPoint, hjc]
  · have hjn : (join x x) (i.addNat (d' + 1)) = x i := by
      rw [← Fin.natAdd_eq_addNat]; exact join_natAdd x x i
    rw [join_natAdd]
    simp [torusPoint, hjn]

theorem anglePhase_split (α β : Fin (d' + 1) → ℤ) (θ : Fin (d' + 1 + (d' + 1)) → ℝ) :
    anglePhase (m := d' + 1 + d') (Fin.append (m := d' + 1) (n := d' + 1) α β) θ =
      anglePhase α (fun i => θ (Fin.castAdd _ i)) * anglePhase β (fun i => θ (Fin.natAdd _ i)) := by
  have hsum : (∑ i : Fin (d' + 1 + (d' + 1)),
      ((Fin.append (m := d' + 1) (n := d' + 1) α β i : ℤ) : ℂ) * (θ i : ℂ)) =
      (∑ i : Fin (d' + 1), (α i : ℂ) * (θ (Fin.castAdd _ i) : ℂ)) +
        ∑ i : Fin (d' + 1), (β i : ℂ) * (θ (Fin.natAdd _ i) : ℂ) := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  unfold anglePhase
  show cexp (-(∑ i : Fin (d' + 1 + (d' + 1)),
      ((Fin.append (m := d' + 1) (n := d' + 1) α β i : ℤ) : ℂ) * (θ i : ℂ)) * I) = _
  rw [hsum, ← Complex.exp_add]
  ring_nf

/-! ### Iterated torus coefficients -/

/-- **Torus coefficients of a function of two variables are iterated torus coefficients.** -/
theorem torusCoeff_join (x : ComplexModel (d' + 1)) (s : ℝ) (α β : Fin (d' + 1) → ℤ)
    (G : ComplexModel (d' + 1) → ComplexModel (d' + 1) → ℂ)
    (hG : Continuous fun p : (Fin (d' + 1) → ℝ) × (Fin (d' + 1) → ℝ) =>
      G (torusPoint x s p.1) (torusPoint x s p.2)) :
    torusCoeff (m := d' + 1 + d') (join x x) s (Fin.append (m := d' + 1) (n := d' + 1) α β)
        (fun z => G (fstCLM _ z) (sndCLM _ z)) =
      torusCoeff x s α (fun a => torusCoeff x s β (G a)) := by
  -- the integrand of the left side
  set H : (Fin (d' + 1 + (d' + 1)) → ℝ) → ℂ := fun θ =>
    G (torusPoint x s fun i => θ (Fin.castAdd _ i)) (torusPoint x s fun i => θ (Fin.natAdd _ i)) *
      (anglePhase α (fun i => θ (Fin.castAdd _ i)) *
        anglePhase β (fun i => θ (Fin.natAdd _ i))) with hHdef
  have hsplit : Continuous fun θ : Fin (d' + 1 + (d' + 1)) → ℝ =>
      ((fun i => θ (Fin.castAdd _ i)), (fun i => θ (Fin.natAdd _ i))) := by fun_prop
  have hHc : Continuous H := by
    refine (hG.comp hsplit).mul ?_
    exact ((continuous_anglePhase α).comp (by fun_prop)).mul
      ((continuous_anglePhase β).comp (by fun_prop))
  have hlhs : torusCoeff (m := d' + 1 + d') (join x x) s (Fin.append (m := d' + 1) (n := d' + 1) α β)
      (fun z => G (fstCLM _ z) (sndCLM _ z)) = angleIntegral (m := d' + 1 + d') H := by
    unfold torusCoeff
    refine angleIntegral_congr fun θ => ?_
    simp only [torusPoint_join, fstCLM_join, sndCLM_join, anglePhase_split, hHdef]
  -- the inner coefficient as a set integral, continuous in the outer angles
  have hKc : Continuous fun p : (Fin (d' + 1) → ℝ) × (Fin (d' + 1) → ℝ) =>
      G (torusPoint x s p.1) (torusPoint x s p.2) * anglePhase β p.2 :=
    hG.mul ((continuous_anglePhase β).comp continuous_snd)
  have hinner : ∀ θL, torusCoeff x s β (G (torusPoint x s θL)) =
      ∫ θR in Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π),
        G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR := by
    intro θL
    have hc : Continuous fun θR =>
        G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR :=
      ((hG.comp (continuous_const.prodMk continuous_id)).mul (continuous_anglePhase β))
    rw [setIntegral_Icc_eq_angleIntegral hc]
    rfl
  have hc2 : Continuous fun θL =>
      (∫ θR in Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π),
        G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR) * anglePhase α θL :=
    (continuous_parametric_integral_of_continuous
      (f := fun θL θR => G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR)
      hKc isCompact_Icc).mul (continuous_anglePhase α)
  have hrhs : torusCoeff x s α (fun a => torusCoeff x s β (G a)) =
      ∫ θL in Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π),
        (∫ θR in Icc (0 : Fin (d' + 1) → ℝ) (fun _ => 2 * π),
          G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR) * anglePhase α θL := by
    rw [setIntegral_Icc_eq_angleIntegral hc2]
    show angleIntegral (fun θL => torusCoeff x s β (G (torusPoint x s θL)) * anglePhase α θL) = _
    exact angleIntegral_congr fun θL => by rw [hinner θL]
  rw [hlhs, ← setIntegral_Icc_eq_angleIntegral hHc]
  refine (setIntegral_Icc_append hHc).trans ?_
  rw [hrhs]
  refine setIntegral_congr_fun measurableSet_Icc fun θL _ => ?_
  rw [← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Icc fun θR _ => ?_
  simp only [hHdef, Fin.append_left, Fin.append_right]
  ring

/-- **Torus coefficients of a product of functions of separate variables.** -/
theorem torusCoeff_join_mul (x : ComplexModel (d' + 1)) (s : ℝ) (α β : Fin (d' + 1) → ℤ)
    (g h : ComplexModel (d' + 1) → ℂ) (hg : Continuous fun θ => g (torusPoint x s θ))
    (hh : Continuous fun θ => h (torusPoint x s θ)) :
    torusCoeff (m := d' + 1 + d') (join x x) s (Fin.append (m := d' + 1) (n := d' + 1) α β)
        (fun z => g (fstCLM _ z) * h (sndCLM _ z)) =
      torusCoeff x s α g * torusCoeff x s β h := by
  rw [torusCoeff_join x s α β (fun a b => g a * h b)
    ((hg.comp continuous_fst).mul (hh.comp continuous_snd))]
  have h1 : ∀ a, torusCoeff x s β (fun b => g a * h b) = g a * torusCoeff x s β h :=
    fun a => torusCoeff_const_mul (g a) h β
  simp only [h1]
  rw [show (fun a => g a * torusCoeff x s β h) = fun a => torusCoeff x s β h * g a from
    funext fun a => mul_comm _ _, torusCoeff_const_mul, mul_comm]

end

end Hironaka.TorusCoefficientsProduct
