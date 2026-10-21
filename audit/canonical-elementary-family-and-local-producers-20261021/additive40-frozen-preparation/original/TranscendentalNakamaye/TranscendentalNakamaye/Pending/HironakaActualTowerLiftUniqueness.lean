import TranscendentalNakamaye.Pending.HironakaOriginalTerminalProjectionUniqueness

/-!
# Genuine uniqueness of a holomorphic lift along an actual finite extension

The whole actual tail supplies invertibility internally at every induction
step. No canonical history, inverse map or invertibility certificate is input.
Blueprint: `hironaka-actual-tower-lift-uniqueness-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaActualTowerLiftUniqueness
noncomputable section
open FirstPass FirstPass.BlowupSequences FirstPass.HolomorphicIdealSheaves BlowupTowers
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Every holomorphic lift through an actual extension is the TRUE tail projection. -/
theorem actual_lift_unique (T : BlowupTower X Y) (R : BlowupTower Y Z) (f : Z → Y)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hproj : ∀ z,T.proj (f z)=(T.append R).proj z) : f=R.proj := by
  induction T generalizing Z with
  | refl =>
    funext z
    simpa only [BlowupTower.refl_append,BlowupTower.proj,id_eq] using hproj z
  | @step Y W T C π hπ ih =>
    let R₀ : BlowupTower Y Z := (BlowupTower.refl.step C π hπ).append R
    have hbase : π ∘ f=R₀.proj := ih R₀ (π ∘ f) (hπ.contMDiff.comp hf) (by
      intro z
      have hh := hproj z
      simpa only [R₀,BlowupTower.proj_append,BlowupTower.proj,Function.comp_apply,
        id_eq] using hh)
    have hJ : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsInvertible :=
      hπ.2.2.2.1
    have hInv := HironakaNormalCrossingsTotalIdeal.isInvertible_original_pullback_tower R hJ
    have hCcoh := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
    rw [←GermIdealTotalTransform.pullback_comp hπ.contMDiff R.contMDiff_proj hCcoh] at hInv
    obtain ⟨w,_hw,huniq⟩ := hπ.2.2.2.2 n Z (π ∘ R.proj)
      (hπ.contMDiff.comp R.contMDiff_proj) hInv
    have hfbase : π ∘ f=π ∘ R.proj := by
      simpa only [R₀,BlowupTower.proj_append,BlowupTower.proj,Function.id_comp] using hbase
    exact (huniq f ⟨hf,hfbase⟩).trans (huniq R.proj ⟨R.contMDiff_proj,rfl⟩).symm

end
end TranscendentalNakamaye.Pending.HironakaActualTowerLiftUniqueness
