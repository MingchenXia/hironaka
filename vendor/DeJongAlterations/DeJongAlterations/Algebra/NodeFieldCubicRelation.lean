import DeJongAlterations.Algebra.NodeFieldCubicSeriesJet
import DeJongAlterations.Algebra.NodeFieldCotangentGeneratorsJet
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Lift a nonzero actual cubic-jet kernel class to an ENTIRE original relation. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFieldCubicRelation

open NodeFormalMorse NodeVariableMorse

universe u v
variable (K : Type u) [Field K] (C : Type v) [CommRing C] [IsLocalRing C]
  [Algebra K C] (φ : Series K →ₐ[K] C)
  (hV : (variableIdeal K).map φ.toRingHom = maximalIdeal C)

include hV in
theorem variablePower_image (n : ℕ) :
    (variableIdeal K ^ n).map φ.toRingHom = maximalIdeal C ^ n := by
  rw [Ideal.map_pow, hV]

def cubicMap : (Series K ⧸ variableIdeal K ^ 3) →ₐ[K] C ⧸ maximalIdeal C ^ 3 :=
  Ideal.quotientMapₐ (maximalIdeal C ^ 3) φ
    (Ideal.map_le_iff_le_comap.mp (variablePower_image K C φ hV 3).le)

theorem cubicMap_mk (f : Series K) :
    cubicMap K C φ hV (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (φ f) := rfl

theorem cubicMap_surjective (hφ : Function.Surjective φ) :
    Function.Surjective (cubicMap K C φ hV) := by
  intro z
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨f, rfl⟩ := hφ c
  exact ⟨Ideal.Quotient.mk _ f, rfl⟩

theorem cubicMap_kernel_finrank (hφ : Function.Surjective φ)
    (hdim : Module.finrank K (C ⧸ maximalIdeal C ^ 3) = 5) :
    Module.finrank K (LinearMap.ker (cubicMap K C φ hV).toLinearMap) = 1 := by
  have hs : Function.Surjective (cubicMap K C φ hV).toLinearMap :=
    cubicMap_surjective K C φ hV hφ
  have h := (cubicMap K C φ hV).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, hdim,
    NodeFieldCubicSeriesJet.jet_finrank K] at h
  omega

include hV in
theorem exists_relation_not_mem_cube (hφ : Function.Surjective φ)
    (hdim : Module.finrank K (C ⧸ maximalIdeal C ^ 3) = 5) :
    ∃ F : Series K, φ F = 0 ∧ F ∉ variableIdeal K ^ 3 := by
  let : Nontrivial (LinearMap.ker (cubicMap K C φ hV).toLinearMap) :=
    Module.nontrivial_of_finrank_pos (R := K) (by
      rw [cubicMap_kernel_finrank K C φ hV hφ hdim]
      exact Nat.zero_lt_one)
  obtain ⟨z, hz⟩ := exists_ne (0 : LinearMap.ker (cubicMap K C φ hV).toLinearMap)
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective z.val
  have hzero : cubicMap K C φ hV (Ideal.Quotient.mk _ f) = 0 := by
    rw [hf]
    exact z.property
  have hm : φ f ∈ maximalIdeal C ^ 3 := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [← variablePower_image K C φ hV 3] at hm
  obtain ⟨g, hg, hgf⟩ := (Ideal.mem_map_iff_of_surjective φ.toRingHom hφ).mp hm
  change φ g = φ f at hgf
  refine ⟨f - g, by rw [map_sub, hgf, sub_self], ?_⟩
  intro hfg
  have hfm : f ∈ variableIdeal K ^ 3 := by
    simpa only [sub_add_cancel] using (variableIdeal K ^ 3).add_mem hfg hg
  apply hz
  apply Subtype.ext
  change z.val = 0
  rw [← hf]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hfm

variable [IsNoetherianRing C] [IsAdicComplete (maximalIdeal C) C]
  (hres : Function.Bijective ((residue C).comp (algebraMap K C)))
  (hdim2 : Module.finrank K (C ⧸ maximalIdeal C ^ 2) = 3)

theorem originalEvaluation_relation
    (hdim3 : Module.finrank K (C ⧸ maximalIdeal C ^ 3) = 5) :
    ∃ F : Series K,
      NodeFieldCotangentGeneratorsPresentation.evaluation K C hres hdim2 F = 0 ∧
      F ∈ variableIdeal K ^ 2 ∧ F ∉ variableIdeal K ^ 3 := by
  let φ := NodeFieldCotangentGeneratorsPresentation.evaluation K C hres hdim2
  have hV : (variableIdeal K).map φ.toRingHom = maximalIdeal C := by
    simpa only [pow_one] using
      NodeFieldCotangentGeneratorsPresentation.variableIdeal_pow_image K C hres hdim2 1
  obtain ⟨F, hF, hn⟩ := exists_relation_not_mem_cube K C φ hV
    (NodeFieldCotangentGeneratorsPresentation.evaluation_surjective K C hres hdim2) hdim3
  exact ⟨F, hF, NodeFieldCotangentGeneratorsJet.kernel_le_variableSquare K C hres hdim2 hF, hn⟩

end DeJongAlterations.Algebra.NodeFieldCubicRelation
