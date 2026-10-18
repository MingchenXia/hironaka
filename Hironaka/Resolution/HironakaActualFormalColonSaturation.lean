/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalIdealIntersections
import Hironaka.Resolution.HironakaRelativeNormalCoherentSaturation

/-! Genuine whole Taylor colons and a common internally chosen saturation index. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFormalColonSaturation
noncomputable section
open HolGerm HironakaActualOriginalFormalTaylor HironakaActualTaylorFaithfullyFlat
  HironakaRelativeNormalCoherentSaturation

private theorem actual_extension_finite_expression (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ Ideal.map (originalTaylorAlgHom n).toRingHom I) :
    ∃ (r : ℕ) (G : Fin r → HolGerm (ComplexModel (0+n)))
      (A : Fin r → MvPowerSeries (Fin n) ℂ),
      (∀ i,G i ∈ I) ∧ F=∑ i,originalTaylorAlgHom n (G i)*A i := by
  let := isNoetherianRing_holGerm_euclidean (0+n)
  obtain ⟨r,G,hG⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  have hspan : Ideal.span (range G)=I := hG
  have hmap : Ideal.map (originalTaylorAlgHom n).toRingHom I=
      Ideal.span (range fun i => originalTaylorAlgHom n (G i)) := by
    rw [← hspan,Ideal.map_span,← Set.range_comp]
    rfl
  rw [hmap] at hF
  obtain ⟨A,hA⟩ := Ideal.mem_span_range_iff_exists_fun.mp hF
  refine ⟨r,G,A,?_,?_⟩
  · intro i
    rw [← hspan]
    exact Ideal.mem_span_range_self (x := i)
  · simpa only [mul_comm] using hA.symm

/-- Whole principal colons commute with actual original Taylor extension, even for the zero germ. -/
theorem map_colon_originalTaylorAlgHom (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (a : HolGerm (ComplexModel (0+n))) :
    Ideal.map (originalTaylorAlgHom n).toRingHom (I.colon {a})=
      (Ideal.map (originalTaylorAlgHom n).toRingHom I).colon {originalTaylorAlgHom n a} := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro g hg
    change originalTaylorAlgHom n g ∈
      (Ideal.map (originalTaylorAlgHom n).toRingHom I).colon {originalTaylorAlgHom n a}
    rw [Submodule.mem_colon_singleton,smul_eq_mul] at hg ⊢
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ hg
  · intro F hF
    rw [Submodule.mem_colon_singleton,smul_eq_mul] at hF
    obtain ⟨r,G,A,hGI,hA⟩ := actual_extension_finite_expression n I _ hF
    let L := Fin.append G (fun _ : Fin 1 => -a)
    let V := Fin.append A (fun _ : Fin 1 => F)
    have hrel : (∑ i,originalTaylorAlgHom n (L i)*V i)=0 := by
      simp only [L,V,Fin.sum_univ_add,Fin.append_left,Fin.append_right,
        Fin.sum_univ_one,map_neg,neg_mul]
      rw [← hA]
      ring
    obtain ⟨k,c,B,hc,hL⟩ :=
      (actual_formal_relation_iff_original_syzygies n (r+1) L V).mp hrel
    let K := fun j : Fin k => c ((0 : Fin 1).natAdd r) j
    have hK : ∀ j,K j ∈ I.colon {a} := by
      intro j
      rw [Submodule.mem_colon_singleton,smul_eq_mul]
      have he : (∑ i : Fin r,G i*c (i.castAdd 1) j)-a*K j=0 := by
        simpa only [L,K,Fin.sum_univ_add,Fin.append_left,Fin.append_right,
          Fin.sum_univ_one,neg_mul,sub_eq_add_neg] using hL j
      have hk : K j*a=∑ i : Fin r,G i*c (i.castAdd 1) j := by
        have h := sub_eq_zero.mp he
        simpa only [mul_comm] using h.symm
      rw [hk]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hGI i)
    have he : F=∑ j,originalTaylorAlgHom n (K j)*B j := by
      simpa only [V,K,Fin.append_right] using hc ((0 : Fin 1).natAdd r)
    rw [he]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hK j))

/-- Every true original colon term has exactly the corresponding whole formal extension. -/
theorem map_actualOriginColonChain (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (a : HolGerm (ComplexModel (0+n))) (q : ℕ) :
    Ideal.map (originalTaylorAlgHom n).toRingHom (actualOriginColonChain I a q)=
      actualOriginColonChain (Ideal.map (originalTaylorAlgHom n).toRingHom I)
        (originalTaylorAlgHom n a) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [actualOriginColonChain,map_colon_originalTaylorAlgHom,ih,actualOriginColonChain]

/-- ONE internally selected original Noetherian index computes the ENTIRE actual formal saturation. -/
theorem exists_actual_original_formal_saturation_index (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (a : HolGerm (ComplexModel (0+n))) :
    ∃ N : ℕ,
      (∀ q,N≤q → actualOriginColonChain I a q=actualOriginColonChain I a N) ∧
      (∀ q,N≤q → actualOriginColonChain (Ideal.map (originalTaylorAlgHom n).toRingHom I)
        (originalTaylorAlgHom n a) q=
          Ideal.map (originalTaylorAlgHom n).toRingHom (actualOriginColonChain I a N)) ∧
      ∀ F : MvPowerSeries (Fin n) ℂ,
        (∃ q,F ∈ actualOriginColonChain (Ideal.map (originalTaylorAlgHom n).toRingHom I)
          (originalTaylorAlgHom n a) q) ↔
        F ∈ Ideal.map (originalTaylorAlgHom n).toRingHom (actualOriginColonChain I a N) := by
  let R := HolGerm (ComplexModel (0+n))
  let := isNoetherianRing_holGerm_euclidean (0+n)
  let f : ℕ →o Submodule R R := ⟨actualOriginColonChain I a,actualOriginColonChain_monotone I a⟩
  obtain ⟨N,hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) f
  have ho : ∀ q,N≤q → actualOriginColonChain I a q=actualOriginColonChain I a N :=
    fun q hq => (hN q hq).symm
  have hf : ∀ q,N≤q → actualOriginColonChain (Ideal.map (originalTaylorAlgHom n).toRingHom I)
      (originalTaylorAlgHom n a) q=
        Ideal.map (originalTaylorAlgHom n).toRingHom (actualOriginColonChain I a N) := by
    intro q hq
    rw [← map_actualOriginColonChain,ho q hq]
  refine ⟨N,ho,hf,?_⟩
  intro F
  constructor
  · rintro ⟨q,hF⟩
    have hm := actualOriginColonChain_monotone
      (Ideal.map (originalTaylorAlgHom n).toRingHom I) (originalTaylorAlgHom n a)
      (le_max_left q N) hF
    rwa [hf (max q N) (le_max_right q N)] at hm
  · intro hF
    refine ⟨N,?_⟩
    rwa [hf N le_rfl]

end
end Hironaka.HironakaActualFormalColonSaturation
