/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureLocalNode

/-!
# The local structure of a hypersurface at a critical point

Let `R` be an integrally closed local domain, `P` étale over `R[X₀, X₁]` and `g ∈ P` with
invertible Hessian. At a prime `Q` of `T = P/(g)` over the closed point of `R` containing the
partial derivatives of `g` (a node of the closed fibre), the local ring `T_Q` has
`LocalStructure` (`localStructure_hypersurface`). This is the local input of Temkin's
closure-component lemma (M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom.
19 (2010), T:3164–3166; blueprint `lem:sm-bd-closure-component`).

The proof uses lane SS3's node chart (`Curves.SemistableNormal.exists_nodeChart`) over the local
ring `O'` of the critical locus at `Q`: a ring `W` étale over `O' ⊗_R T` and over the node
`O'[u, v]/(uv - c)`. If `c ≠ 0` the node, hence `W_𝔔`, is an integrally closed domain and so is
`T_Q` (`Curves.SemistableNormal.isDomain_isIntegrallyClosed_localization_of_flat`). If `c = 0`
the node is split and `localStructure_of_split` applies to the faithfully flat `T_Q → W_𝔔`: its
branches `(u)`, `(v)` are prime (`isDomain_localization_quotient_of_etale` with
`isDomain_isIntegrallyClosed_quot_coordinate`), their fibres over the closed point are reduced
(`isDomain_isIntegrallyClosed_quot_coordinate_sup`; `𝔪_R O' = 𝔪_{O'}` since `R → O'` is
unramified), and they meet in a point over the generic point of `R` (going down from the origin
of the node, `isPrime_originIdeal`).

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-hypersurface-structure`.
-/

noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace DeJongAlterations.StableModification.BlowDown.ClosureLocal

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open DeJongAlterations.Algebra.NodeBlowupChart (Node coordinate)
open Curves.SemistableNormal
open Curves.SemistableOpen (coord planeDerivation hessian)

section Hypersurface

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
  (P : Type u) [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]
  [Algebra.Etale (MvPolynomial (Fin 2) R) P]

/-- **The local structure of a hypersurface at a node of the closed fibre** (blueprint
`lem:sm-bdu-hypersurface-structure`). -/
theorem localStructure_hypersurface (g : P) (hg : IsUnit (hessian R P g))
    (Q : Ideal (P ⧸ Ideal.span {g})) [Q.IsPrime]
    (hcrit : ∀ i, Ideal.Quotient.mk _ (planeDerivation R P i g) ∈ Q)
    (hQ : Q.comap (algebraMap R (P ⧸ Ideal.span {g})) = maximalIdeal R) :
    LocalStructure R (Localization.AtPrime Q) (maximalIdeal R) := by
  set T := P ⧸ Ideal.span {g}
  set Q₀ := Q.comap (Ideal.Quotient.mk (Ideal.span {g})) with hQ₀
  -- the critical locus `O` and its local ring `O'` at `Q`
  have : Algebra.Etale R (P ⧸ critIdeal R P g) := etale_critical R P g hg
  set O := P ⧸ critIdeal R P g
  have hcritQ₀ : critIdeal R P g ≤ Q₀ := by
    rw [critIdeal, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hcrit 0
    · exact hcrit 1
  set 𝔮 := Q₀.map (Ideal.Quotient.mk (critIdeal R P g))
  have : 𝔮.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hcritQ₀)
  have h𝔮 : ∀ p, Ideal.Quotient.mk (critIdeal R P g) p ∈ 𝔮 ↔ p ∈ Q₀ := by
    intro p
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hcritQ₀]
  set O' := Localization.AtPrime 𝔮
  obtain ⟨hO'dom, hO'int⟩ := Curves.isDomain_isIntegrallyClosed_localization_of_etale R 𝔮
  let π : P →ₐ[R] O' := (IsScalarTower.toAlgHom R O O').comp (Ideal.Quotient.mkₐ R _)
  have hπ : ∀ i, π (planeDerivation R P i g) = 0 := by
    intro i
    change algebraMap O O' (Ideal.Quotient.mk _ _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr, map_zero]
    fin_cases i
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hπmem : ∀ p, π p ∈ maximalIdeal O' ↔ p ∈ Q₀ := by
    intro p
    change algebraMap O O' _ ∈ _ ↔ _
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O' 𝔮]
    exact h𝔮 p
  have hgQ₀ : g ∈ Q₀ := by
    rw [hQ₀, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g)]
    exact Q.zero_mem
  have hπg : π g ∈ maximalIdeal O' := (hπmem g).mpr hgQ₀
  obtain ⟨W, _, _, _, _, _, 𝔔, _, hcompat, hPW, hOW, hcoord⟩ :=
    exists_nodeChart R P O' g hg π hπ (maximalIdeal O') hπg
  -- the flat map `T → W` and the faithfully flat local map `T_Q → W_𝔔`
  have : Module.Flat R O' := Module.Flat.trans R O O'
  let : Algebra T W := ((algebraMap (O' ⊗[R] T) W).comp
    (Algebra.TensorProduct.includeRight : T →ₐ[R] O' ⊗[R] T).toRingHom).toAlgebra
  have : Module.Flat T W := by
    rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.comp (flat_includeRight R O' T)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hQ𝔔 : 𝔔.comap (algebraMap T W) = Q := by
    ext t
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [Ideal.mem_comap]
    change algebraMap (O' ⊗[R] T) W ((1 : O') ⊗ₜ Ideal.Quotient.mk _ p) ∈ 𝔔 ↔ _
    rw [hPW, hπmem]
    rfl
  set A := Localization.AtPrime Q
  set A' := Localization.AtPrime 𝔔
  let : Algebra A A' := Localization.localRingHom Q 𝔔 (algebraMap T W) hQ𝔔.symm |>.toAlgebra
  have : IsLocalHom (algebraMap A A') :=
    Localization.isLocalHom_localRingHom Q 𝔔 (algebraMap T W) hQ𝔔.symm
  have : Module.Flat A A' := by
    rw [← RingHom.flat_algebraMap_iff]
    exact (RingHom.flat_algebraMap_iff.mpr inferInstance).localRingHom 𝔔 Q hQ𝔔.symm
  have : Module.FaithfullyFlat A A' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  by_cases hc : -π g = 0
  swap
  · -- `c ≠ 0`: the node and its étale neighbourhood are integrally closed domains
    have : IsDomain (Node O' (-π g)) :=
      DeJongAlterations.Algebra.NodeDomain.nodeQuotient_isDomain _ hc
    have : IsIntegrallyClosed (Node O' (-π g)) :=
      DeJongAlterations.Algebra.NodeNormal.node_isIntegrallyClosed _ hc
    obtain ⟨hWdom, hWint⟩ := Curves.isDomain_isIntegrallyClosed_localization_of_etale
      (Node O' (-π g)) 𝔔
    obtain ⟨hAdom, -⟩ := isDomain_isIntegrallyClosed_localization_of_flat 𝔔 Q hQ𝔔
    exact LocalStructure.of_isDomain
  -- `c = 0`: the split node
  let : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  set ιN := algebraMap (Node O' (-π g)) W
  set ιA := algebraMap W A'
  -- `R → A'` through the node
  have hRN : ∀ r : R, algebraMap R A' r =
      ιA (ιN (algebraMap O' (Node O' (-π g)) (algebraMap R O' r))) := by
    intro r
    change algebraMap A A' (algebraMap R A r) = _
    rw [IsScalarTower.algebraMap_apply R T A]
    change Localization.localRingHom Q 𝔔 (algebraMap T W) hQ𝔔.symm
      (algebraMap T A (algebraMap R T r)) = _
    rw [Localization.localRingHom_to_map]
    change ιA (algebraMap (O' ⊗[R] T) W ((1 : O') ⊗ₜ algebraMap R T r)) = _
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul, hcompat]
  -- the branches `u = 0`, `v = 0`
  set u := ιA (ιN (coordinate (-π g) 0))
  set v := ιA (ιN (coordinate (-π g) 1))
  have hcoordmul : coordinate (-π g) 0 * coordinate (-π g) 1 = 0 := by
    rw [coordinate, coordinate, ← map_mul]
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [Algebra.NodeChart.uChartIdeal, hc, map_zero, sub_zero]
    exact Ideal.mem_span_singleton_self _
  have huv : u * v = 0 := by
    rw [← map_mul, ← map_mul, hcoordmul, map_zero, map_zero]
  have hcoordW : ∀ i, (Ideal.span {coordinate (-π g) i}).map ιN ≤ 𝔔 := fun i => by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hcoord i
  have hspan : ∀ i, (Ideal.span {coordinate (-π g) i}).map
      (algebraMap (Node O' (-π g)) A') = Ideal.span {ιA (ιN (coordinate (-π g) i))} := by
    intro i
    rw [Ideal.map_span, Set.image_singleton, IsScalarTower.algebraMap_apply (Node O' (-π g)) W A']
  have hprime : ∀ i, (Ideal.span {ιA (ιN (coordinate (-π g) i))}).IsPrime := by
    intro i
    obtain ⟨h1, h2⟩ := isDomain_isIntegrallyClosed_quot_coordinate (-π g) hc i
    have := isDomain_localization_quotient_of_etale _ 𝔔 (hcoordW i)
    rw [hspan i] at this
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  -- `𝔪_R O' = 𝔪_{O'}` (`R → O'` is unramified)
  have hRO' : (maximalIdeal O').comap (algebraMap R O') = maximalIdeal R := by
    ext r
    rw [Ideal.mem_comap, ← hQ, Ideal.mem_comap]
    change π (algebraMap R P r) ∈ maximalIdeal O' ↔ _
    rw [hπmem, hQ₀, Ideal.mem_comap, Ideal.Quotient.mk_algebraMap]
  have : IsLocalHom (algebraMap R O') :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R O')).out 0 4).mpr hRO'
  have hunr : (maximalIdeal R).map (algebraMap R O') = maximalIdeal O' :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hmaxW : ((maximalIdeal O').map (algebraMap O' (Node O' (-π g)))).map ιN ≤ 𝔔 := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro o ho
    rw [Ideal.mem_comap]
    change ιN (algebraMap O' (Node O' (-π g)) o) ∈ 𝔔
    rw [← hcompat, hOW]
    exact ho
  have hmapR : (maximalIdeal R).map (algebraMap R A') =
      ((maximalIdeal O').map (algebraMap O' (Node O' (-π g)))).map
        (algebraMap (Node O' (-π g)) A') := by
    rw [← hunr, Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun r => ?_
    rw [hRN r]
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Node O' (-π g)) W A']
  have hred : ∀ i, IsReduced (A' ⧸ (Ideal.span {ιA (ιN (coordinate (-π g) i))} ⊔
      (maximalIdeal R).map (algebraMap R A'))) := by
    intro i
    obtain ⟨h1, h2⟩ := isDomain_isIntegrallyClosed_quot_coordinate_sup (-π g) hc i
      (maximalIdeal O')
    have hle : (Ideal.span {coordinate (-π g) i} ⊔
        (maximalIdeal O').map (algebraMap O' (Node O' (-π g)))).map ιN ≤ 𝔔 := by
      rw [Ideal.map_sup]
      exact sup_le (hcoordW i) hmaxW
    have := isDomain_localization_quotient_of_etale _ 𝔔 hle
    rw [Ideal.map_sup, hspan i, ← hmapR] at this
    exact inferInstance
  -- a point of `W_𝔔` on both branches over the generic point of `R`
  obtain ⟨h𝔫₀, h𝔫₀O'⟩ := isPrime_originIdeal (-π g) hc
  have h𝔫₀𝔔 : originIdeal (-π g) ≤ 𝔔.comap ιN := by
    rw [originIdeal, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hcoord 0
    · exact hcoord 1
  have : 𝔔.LiesOver (𝔔.comap ιN) := ⟨rfl⟩
  obtain ⟨𝔫'', h𝔫''𝔔, h𝔫'', h𝔫''lies⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := originIdeal (-π g)) (q := 𝔔.comap ιN) 𝔔 h𝔫₀𝔔
  have hlies : 𝔫''.comap ιN = originIdeal (-π g) := h𝔫''lies.over.symm
  have hdisj : Disjoint (𝔔.primeCompl : Set W) 𝔫'' := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (h𝔫''𝔔 hx')
  set 𝔫 := 𝔫''.map ιA
  have h𝔫 : 𝔫.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔔.primeCompl A' 𝔫'' h𝔫'' hdisj
  have h𝔫comap : 𝔫.comap ιA = 𝔫'' :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔔.primeCompl A' h𝔫'' hdisj
  have hmem : ∀ i, ιA (ιN (coordinate (-π g) i)) ∈ 𝔫 := by
    intro i
    refine Ideal.mem_map_of_mem _ ?_
    have : coordinate (-π g) i ∈ 𝔫''.comap ιN := by
      rw [hlies]
      fin_cases i
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    exact this
  have h𝔫R : 𝔫.comap (algebraMap R A') = ⊥ := by
    ext r
    rw [Ideal.mem_comap, hRN r, Ideal.mem_bot, ← Ideal.mem_comap (f := ιA), h𝔫comap,
      ← Ideal.mem_comap (f := ιN), hlies, ← Ideal.mem_comap, h𝔫₀O', Ideal.mem_bot]
    exact map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R O')
  exact localStructure_of_split (maximalIdeal R) huv (hprime 0) (hprime 1) (hred 0) (hred 1) 𝔫
    (hmem 0) (hmem 1) h𝔫R

end Hypersurface

end DeJongAlterations.StableModification.BlowDown.ClosureLocal
