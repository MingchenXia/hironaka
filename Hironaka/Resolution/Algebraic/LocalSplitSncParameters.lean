import Hironaka.Resolution.Algebraic.ActualPrincipalizationCanonicalBoundary
import Hironaka.Scheme.Snc.EtaleParameters

/-!
# Fixed SNC component ideals through genuine local retractions

Source-first proof: `local-split-snc-parameters-20261102.tex`.
The input is an actual local ring retract and genuine ideal-extension equations.
The downstairs parameter system is derived, never supplied as a certificate.
-/

set_option autoImplicit false

open IsLocalRing Ideal
universe u v w

namespace Hironaka.Resolution.Algebraic.LocalSplitSncParameters

noncomputable section

/-- Cotangent independence reflects through an actual local ring homomorphism. -/
theorem linearIndependent_toCotangent_of_local_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] {ι : Type w} [Fintype ι]
    (w : ι → R) (hw : ∀ i, w i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField S) fun i =>
      (maximalIdeal S).toCotangent ⟨φ (w i), map_nonunit φ _ (hw i)⟩) :
    LinearIndependent (ResidueField R) fun i => (maximalIdeal R).toCotangent ⟨w i, hw i⟩ := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun j => residue_surjective (R := R) (g j)
  let W : ι → maximalIdeal R := fun j => ⟨w j,hw j⟩
  have hsum : (∑ j, g j • (maximalIdeal R).toCotangent (W j)) =
      (maximalIdeal R).toCotangent (∑ j, a j • W j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul,← ha j,← ResidueField.algebraMap_eq,algebraMap_smul]
  have hmem : (∑ j, a j * w j) ∈ maximalIdeal R ^ 2 := by
    have h := ((maximalIdeal R).toCotangent_eq_zero _).mp (hsum.symm.trans hg)
    simpa only [Submodule.coe_sum,Submodule.coe_smul,smul_eq_mul] using h
  have hmap : Ideal.map φ (maximalIdeal R ^ 2) ≤ maximalIdeal S ^ 2 := by
    rw [pow_two,Ideal.map_mul,pow_two]
    exact Ideal.mul_mono (map_maximalIdeal_le φ) (map_maximalIdeal_le φ)
  have hmem' : (∑ j, φ (a j) * φ (w j)) ∈ maximalIdeal S ^ 2 := by
    simpa only [map_sum,map_mul] using hmap (Ideal.mem_map_of_mem φ hmem)
  let V : ι → maximalIdeal S := fun j => ⟨φ (w j),map_nonunit φ _ (hw j)⟩
  have hsum' : (∑ j, residue S (φ (a j)) • (maximalIdeal S).toCotangent (V j)) =
      (maximalIdeal S).toCotangent (∑ j, φ (a j) • V j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul,← ResidueField.algebraMap_eq,algebraMap_smul]
  have hz : (∑ j, residue S (φ (a j)) • (maximalIdeal S).toCotangent (V j)) = 0 := by
    rw [hsum']
    apply (maximalIdeal S).toCotangent_eq_zero _ |>.mpr
    simpa only [Submodule.coe_sum,Submodule.coe_smul,smul_eq_mul] using hmem'
  have haiS : φ (a i) ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff]
    exact (Fintype.linearIndependent_iff.mp hli) _ hz i
  have haiR : a i ∈ maximalIdeal R := by
    change a i ∈ Ideal.comap φ (maximalIdeal S) at haiS
    rwa [maximalIdeal_comap] at haiS
  rw [← ha i,residue_eq_zero_iff]
  exact haiR

/-- Actual fixed ideals extending to distinct parameters descend through a regular local retract. -/
theorem fixed_ideals_are_parameters_of_local_retract
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    (α : R →+* S) [IsLocalHom α] (β : S →+* R) (hβα : β.comp α = RingHom.id R)
    {ι : Type w} [Fintype ι] (I : ι → Ideal R)
    {n : ℕ} (z : Fin n → S) (hz : IsRegularSystemOfParameters z)
    (c : ι → Fin n) (hc : Function.Injective c)
    (hI : ∀ i, Ideal.map α (I i) = Ideal.span {z (c i)}) :
    ∃ (m : ℕ) (t : Fin m → R), IsRegularSystemOfParameters t ∧
      ∃ d : ι → Fin m, Function.Injective d ∧ ∀ i, I i = Ideal.span {t (d i)} := by
  classical
  have hβsurj : Function.Surjective β := fun r => ⟨α r,DFunLike.congr_fun hβα r⟩
  have : IsLocalHom β := hβsurj.isLocalHom
  let w : ι → R := fun i => β (z (c i))
  have hzmem : ∀ j, z j ∈ maximalIdeal S := fun j =>
    hz.1 ▸ Ideal.subset_span ⟨j,rfl⟩
  have hw : ∀ i, w i ∈ maximalIdeal R := fun i => map_nonunit β _ (hzmem (c i))
  have hIw : ∀ i, I i = Ideal.span {w i} := by
    intro i
    have h := congrArg (Ideal.map β) (hI i)
    simpa only [Ideal.map_map,hβα,Ideal.map_id,Ideal.map_span,Set.image_singleton] using h
  have hspan : ∀ i, Ideal.span {α (w i)} = Ideal.span {z (c i)} := by
    intro i
    rw [← hI i,hIw i,Ideal.map_span,Set.image_singleton]
  choose U hU using fun i => Ideal.span_singleton_eq_span_singleton.mp (hspan i).symm
  obtain ⟨b,hb⟩ := exists_basis_cotangentSpace_of_span_eq z hz.1.symm hz.2
  have hv : LinearIndependent (ResidueField S) fun i =>
      (maximalIdeal S).toCotangent ⟨α (w i),map_nonunit α _ (hw i)⟩ := by
    have hli := (b.linearIndependent.comp c hc).units_smul
      (fun i => Units.map (residue S).toMonoidHom (U i))
    convert hli using 1
    funext i
    change _ = residue S (U i) • b (c i)
    rw [hb]
    rw [← ResidueField.algebraMap_eq,algebraMap_smul,← map_smul]
    congr 1
    apply Subtype.ext
    exact (hU i).symm.trans (mul_comm _ _)
  have hli := linearIndependent_toCotangent_of_local_map α w hw hv
  obtain ⟨m,t,ht,d,hd,hdt⟩ := AlgebraicGeometry.exists_span_eq_maximalIdeal_of_linearIndependent w hw hli
  refine ⟨m,t,ht,d,hd,fun i => ?_⟩
  rw [hdt i]
  exact hIw i

end
end Hironaka.Resolution.Algebraic.LocalSplitSncParameters
