import DeJongAlterations.StableModification.Curves.SemistableNormalLocal

/-!
# Étale local structure of a nodal family at a node: the main statement

Let `R → B` be flat and finitely presented, `K` an algebraically closed field over `R` and
`z ⊂ K ⊗_R B` a geometric node (`Ô_z ≅ K[[u, v]]/(uv)`). Then, after replacing `B` by `B_f` for
some `f` outside the point under `z`, every geometric node `z'` of `B_f` has an étale
neighbourhood `W` which is étale over the standard node `O[u, v]/(uv - c)`, for an étale
`R`-algebra `O` and `c ∈ O` (`exists_away_etale_nodeChart`; Stacks, Tag 0CBY). This is the étale
local form of de Jong's completed description (de Jong 1996, 2.23) used by Temkin (T:2966–2967,
normality of semi-stable curves with smooth generic fibre; Lemma 5.1(i)).

The proof combines SS2's hypersurface presentation (`exists_principal_kernel_crit`, a copy of
`SemistableOpen.exists_principal_kernel` recording that the node is a critical point) with the
critical locus `O = P/(∂₀g, ∂₁g)` (`etale_critical`) and the node chart over `O`
(`exists_nodeChart`).
-/

noncomputable section

open IsLocalRing TensorProduct MvPowerSeries

namespace DeJongAlterations.StableModification.Curves.SemistableNormal

open SemistableOpen
open Algebra.NodeFormalMorse Algebra.NodeVariableMorse Algebra.NodeGeometricCompletionFormalUV

universe u

section Crit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {P : Type u} [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]
  [Algebra.Etale (MvPolynomial (Fin 2) R) P]
  {B : Type u} [CommRing B] [Algebra R B] [Module.Flat R B] [Algebra.FinitePresentation R B]
  (φ : P →ₐ[R] B) (hφ : Function.Surjective φ)
  {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K]
  (z : Ideal (K ⊗[R] B)) [z.IsMaximal]

include hφ in
/-- **Near a node the kernel of a plane presentation is principal, and the node is critical.**
This is `SemistableOpen.exists_principal_kernel` (lane SS2), whose proof is reproduced here to
record in addition that the point `Q₀` of `P` under the node is a critical point of `g`:
`∂₀g, ∂₁g ∈ Q₀`. -/
theorem exists_principal_kernel_crit
    (e : AdicCompletion (maximalIdeal (Localization.AtPrime z)) (Localization.AtPrime z) ≃ₐ[K]
      FormalUV K) :
    ∃ g ∈ RingHom.ker φ.toRingHom, ∃ h : P,
      h ∉ z.comap ((Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).comp φ).toRingHom ∧
      hessian R P g ∉
        z.comap ((Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).comp φ).toRingHom ∧
      (∀ i, planeDerivation R P i g ∈
        z.comap ((Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).comp φ).toRingHom) ∧
      ∀ j ∈ RingHom.ker φ.toRingHom, h * j ∈ Ideal.span {g} := by
  classical
  have : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.trans R (MvPolynomial (Fin 2) R) P
  set J := RingHom.ker φ.toRingHom with hJ
  set Q₀ := z.comap ((Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).comp φ).toRingHom
    with hQ₀def
  -- base change to `K`
  let Φ : PlaneBaseChange R K P →ₐ[K] K ⊗[R] B := Algebra.TensorProduct.map (AlgHom.id K K) φ
  have hΦ : Function.Surjective Φ := LinearMap.lTensor_surjective K hφ
  have hΦker : RingHom.ker Φ.toRingHom = J.map (toPlaneBaseChange R K P).toRingHom :=
    Algebra.TensorProduct.lTensor_ker φ hφ
  have hΦinc : ∀ p, Φ (toPlaneBaseChange R K P p) = (1 : K) ⊗ₜ φ p := fun p => rfl
  set Q := z.comap Φ.toRingHom with hQdef
  have : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hΦ
  have : Algebra.FiniteType K (PlaneBaseChange R K P) :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin 2) K) inferInstance inferInstance
  have hres := algebraMap_quotient_surjective_of_isAlgClosed K (PlaneBaseChange R K P) Q
  choose c hc using fun j : Fin 2 =>
    hres (Ideal.Quotient.mk Q (coord K (PlaneBaseChange R K P) j))
  have hQ : IsRationalPoint Q c := by
    refine ⟨fun j => ?_, hres⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc j, Ideal.Quotient.mk_algebraMap, sub_self]
  have hQ₀ : ∀ p, p ∈ Q₀ ↔ toPlaneBaseChange R K P p ∈ Q := fun p => Iff.rfl
  -- the kernel of `K[[X₀, X₁]] → Ô_{K ⊗ B, z}` is principal
  let I' := (RingHom.ker Φ.toRingHom).map hQ.taylor.toRingHom
  let eB : (Series K ⧸ I') ≃ₐ[K] FormalUV K :=
    (hQ.quotientCompletionEquiv' Φ z rfl hΦ).symm.trans e
  have : Nontrivial (Series K ⧸ I') := eB.toEquiv.nontrivial
  have : IsLocalRing (Series K ⧸ I') :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I') Ideal.Quotient.mk_surjective
  obtain ⟨F, hFker, hF2, hF3, hFΔ⟩ := exists_ker_eq_span_of_formalUV
    (Ideal.Quotient.mkₐ K I') (Ideal.Quotient.mkₐ_surjective K I') eB
  have hI' : J.map (hQ.taylor.toRingHom.comp (toPlaneBaseChange R K P).toRingHom) =
      Ideal.span {F} := by
    rw [← Ideal.map_map, ← hΦker, ← hFker]
    exact (Ideal.Quotient.mkₐ_ker K I').symm
  have hF0 : F ≠ 0 := fun h0 => hF3 (h0 ▸ zero_mem _)
  obtain ⟨g, hgJ, b, hb, hgb⟩ := exists_mem_map_eq_unit_mul J _ hF0 hI'
  -- the Taylor expansion of `1 ⊗ g` is a nondegenerate quadratic germ
  have hG : hQ.taylor (toPlaneBaseChange R K P g) = b * F := hgb
  have hG2 : hQ.taylor (toPlaneBaseChange R K P g) ∈ variableIdeal K ^ 2 := by
    rw [hG]
    exact Ideal.mul_mem_left _ _ hF2
  have hGΔ : jetDiscriminant (hQ.taylor (toPlaneBaseChange R K P g)) ≠ 0 := by
    rw [hG, jetDiscriminant_mul_of_mem b F hF2]
    exact mul_ne_zero (pow_ne_zero 2 (MvPowerSeries.isUnit_iff_constantCoeff.mp hb).ne_zero) hFΔ
  rw [mem_variableIdeal_sq_iff] at hG2
  have hd : ∀ i, planeDerivation K (PlaneBaseChange R K P) i (toPlaneBaseChange R K P g) ∈ Q := by
    intro i
    rw [hQ.mem_iff_taylor, ← hQ.coeff_single_taylor]
    fin_cases i
    · exact hG2.2.1
    · exact hG2.2.2
  have hhQ : hessian K (PlaneBaseChange R K P) (toPlaneBaseChange R K P g) ∉ Q := by
    rw [hQ.mem_iff_taylor, hQ.taylor_hessian, constantCoeff_hessian, neg_eq_zero]
    exact hGΔ
  have hhQ₀ : hessian R P g ∉ Q₀ := by
    rw [hQ₀, ← hessian_baseChange]
    exact hhQ
  -- the hypersurface `T = P/(g)` and the surjection `T → B`
  have hgker : ∀ a ∈ Ideal.span {g}, φ a = 0 := fun a ha => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, show φ g = 0 from RingHom.mem_ker.mp hgJ, mul_zero]
  let Φbar : (P ⧸ Ideal.span {g}) →ₐ[R] B := Ideal.Quotient.liftₐ (Ideal.span {g}) φ hgker
  have hΦbar : Function.Surjective Φbar := fun x => by
    obtain ⟨p, rfl⟩ := hφ x
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  let πT := baseQuotientMap R K P g
  let ΦT : HypersurfaceFibre R K P g →ₐ[K] K ⊗[R] B :=
    Algebra.TensorProduct.map (AlgHom.id K K) Φbar
  have hΦT : Function.Surjective ΦT := LinearMap.lTensor_surjective K hΦbar
  have hcomp : ∀ x : K ⊗[R] P, ΦT (πT x) = Φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul k p => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  set QT := z.comap ΦT.toRingHom with hQTdef
  have : QT.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hΦT
  have hQT : QT.comap πT.toRingHom = Q := by
    ext x
    change ΦT (πT x) ∈ z ↔ Φ x ∈ z
    rw [hcomp]
  -- the hypersurface has a node at `QT`, and is the family locally on the fibre
  let eT := hQ.nodeEquiv πT QT hQT (baseQuotientMap_surjective R K P g) _
    (ker_baseQuotientMap R K P g) hd hhQ
  have : Algebra.FinitePresentation R (P ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  have : Algebra.FiniteType K (HypersurfaceFibre R K P g) :=
    inferInstanceAs (Algebra.FiniteType K (K ⊗[R] (P ⧸ Ideal.span {g})))
  have : IsNoetherianRing (HypersurfaceFibre R K P g) := Algebra.FiniteType.isNoetherianRing K _
  have hinjT := localRingHom_injective_of_formalUV K ΦT hΦT z eT e
  obtain ⟨s, hsQT, hs⟩ := exists_notMem_forall_mul_eq_zero (RingHom.ker ΦT.toRingHom)
    (IsNoetherian.noetherian _) QT fun x hx => by
      have h0 : algebraMap _ (Localization.AtPrime QT) x = 0 := by
        apply hinjT
        rw [Localization.localRingHom_to_map, map_zero]
        change algebraMap _ _ (ΦT x) = 0
        rw [show ΦT x = 0 from RingHom.mem_ker.mp hx, map_zero]
      obtain ⟨⟨m, hm⟩, hmx⟩ := (IsLocalization.map_eq_zero_iff QT.primeCompl _ x).mp h0
      exact ⟨m, hm, hmx⟩
  -- the kernel `M` of `T → B` and its fibre
  set M := RingHom.ker Φbar.toRingHom with hMdef
  have hMfg : M.FG := Algebra.FinitePresentation.ker_fG_of_surjective Φbar hΦbar
  have : Module.Finite (P ⧸ Ideal.span {g}) M := Module.Finite.iff_fg.mpr hMfg
  have hflat : Function.Injective ((M.subtype.restrictScalars R).lTensor K) :=
    LinearMap.lTensor_injective_of_exact_of_flat Φbar.toLinearMap hΦbar
      (M.subtype.restrictScalars R) Subtype.val_injective (fun t => by
        constructor
        · intro ht
          exact ⟨⟨t, ht⟩, rfl⟩
        · rintro ⟨m, rfl⟩
          exact m.2) K
  let : Field (HypersurfaceFibre R K P g ⧸ QT) := Ideal.Quotient.field QT
  let ρ : K ⊗[R] (P ⧸ Ideal.span {g}) →+* HypersurfaceFibre R K P g ⧸ QT := Ideal.Quotient.mk QT
  have hρs : ρ s ≠ 0 := by
    change Ideal.Quotient.mk QT s ≠ 0
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hsub := subsingleton_tensor_of_lTensor_injective M K hflat ρ s hρs fun m hm => hs _ (by
    rw [RingHom.mem_ker]
    change (1 : K) ⊗ₜ Φbar m = 0
    rw [show Φbar m = 0 from hm, tmul_zero])
  let : Algebra (P ⧸ Ideal.span {g}) (HypersurfaceFibre R K P g ⧸ QT) :=
    (ρ.comp (Algebra.TensorProduct.includeRight :
      (P ⧸ Ideal.span {g}) →ₐ[R] K ⊗[R] (P ⧸ Ideal.span {g})).toRingHom).toAlgebra
  set Qbar := QT.comap (Algebra.TensorProduct.includeRight :
      (P ⧸ Ideal.span {g}) →ₐ[R] K ⊗[R] (P ⧸ Ideal.span {g})).toRingHom with hQbar
  have hker : RingHom.ker (algebraMap (P ⧸ Ideal.span {g}) (HypersurfaceFibre R K P g ⧸ QT)) =
      Qbar := by
    ext t
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hsupp := notMem_support_of_subsingleton_tensor (B := P ⧸ Ideal.span {g}) (M := M)
    (F := HypersurfaceFibre R K P g ⧸ QT) ⟨Qbar, inferInstance⟩ hker
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hsupp
  obtain ⟨hbar, hann, hhbar⟩ := hsupp
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective hbar
  refine ⟨g, hgJ, h, ?_, hhQ₀, fun i => ?_, fun j hj => ?_⟩
  · exact hhbar
  · rw [hQ₀, ← planeDerivation_map (toPlaneBaseChange R K P) (toPlaneBaseChange_coord R K P)]
    exact hd i
  · have hjM : Ideal.Quotient.mk (Ideal.span {g}) j ∈ M := by
      rw [RingHom.mem_ker]
      exact RingHom.mem_ker.mp hj
    have := congrArg Subtype.val (Module.mem_annihilator.mp hann ⟨_, hjM⟩)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact this

end Crit

section Away

variable {R : Type u} [CommRing R] {P : Type u} [CommRing P] [Algebra R P]
  {B : Type u} [CommRing B] [Algebra R B] (φ : P →ₐ[R] B)

/-- After inverting `a = h · e` (with `h · ker φ ⊆ (g)`), the kernel of `φ` becomes `(g)`. -/
theorem ker_awayMap_eq_span (g : P) (hgJ : g ∈ RingHom.ker φ.toRingHom) (h e : P)
    (hJ : ∀ j ∈ RingHom.ker φ.toRingHom, h * j ∈ Ideal.span {g}) :
    RingHom.ker (Localization.awayMapₐ φ (h * e)).toRingHom =
      Ideal.span {algebraMap P (Localization.Away (h * e)) g} := by
  set a := h * e
  have haunit : IsUnit (algebraMap P (Localization.Away a) a) :=
    IsLocalization.Away.algebraMap_isUnit a
  have hhunit : IsUnit (algebraMap P (Localization.Away a) h) := by
    rw [show a = h * e from rfl, map_mul] at haunit
    exact isUnit_of_mul_isUnit_left haunit
  have h₀ : RingHom.ker (Localization.awayMapₐ φ a).toRingHom =
      (RingHom.ker φ.toRingHom).map (algebraMap P (Localization.Away a)) :=
    IsLocalization.ker_map (Localization.Away (φ a)) φ.toRingHom
      (Submonoid.map_powers φ.toRingHom a)
  rw [h₀]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hJ j hj)
    obtain ⟨v, hv⟩ := hhunit
    rw [Ideal.mem_comap]
    have : algebraMap P (Localization.Away a) j =
        (↑v⁻¹ * algebraMap P (Localization.Away a) r) * algebraMap P (Localization.Away a) g := by
      rw [mul_assoc, ← map_mul, hr, map_mul, ← hv, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hgJ

end Away

section Helpers

/-- A ring isomorphism is étale. -/
theorem etale_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    letI := e.toRingHom.toAlgebra
    Algebra.Etale A B := by
  let := e.toRingHom.toAlgebra
  exact Algebra.Etale.of_equiv { e with commutes' := fun _ => rfl }

/-- Base change of an étale algebra, with the base on the right. -/
theorem etale_rightAlgebra (R O B : Type u) [CommRing R] [CommRing O] [CommRing B] [Algebra R O]
    [Algebra R B] [Algebra.Etale R O] :
    letI : Algebra B (O ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    Algebra.Etale B (O ⊗[R] B) := by
  let : Algebra B (O ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  exact Algebra.Etale.of_equiv
    { Algebra.TensorProduct.comm R B O with
      commutes' := fun b => by
        change Algebra.TensorProduct.comm R B O (b ⊗ₜ 1) = (1 : O) ⊗ₜ b
        rfl }

end Helpers

section Hypersurface

variable (R : Type u) [CommRing R] (P : Type u) [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]
  [Algebra.Etale (MvPolynomial (Fin 2) R) P]

open DeJongAlterations.Algebra.NodeBlowupChart in
/-- **Étale local structure of a hypersurface with invertible Hessian at a critical point.**
Let `P` be étale over `R[X₀, X₁]`, `g ∈ P` with invertible Hessian and `Q₀` a prime of `P`
containing `g, ∂₀g, ∂₁g`. Then there is an étale `R`-algebra `O`, `c ∈ O`, and a ring `W` étale
over `P/(g)` and over the standard node `O[u, v]/(uv - c)`, compatibly over `R`, with a prime `𝔔`
over `Q₀` at which `u`, `v` and `c` vanish. (`O` is the critical locus `P/(∂₀g, ∂₁g)`.) -/
theorem exists_hypersurface_nodeChart (g : P) (hg : IsUnit (hessian R P g)) (Q₀ : Ideal P)
    [Q₀.IsPrime] (hgQ : g ∈ Q₀) (hcrit : ∀ i, planeDerivation R P i g ∈ Q₀) :
    ∃ (O : Type u) (_ : CommRing O) (_ : Algebra R O) (_ : Algebra.Etale R O) (c : O)
      (W : Type u) (_ : CommRing W) (_ : Algebra (P ⧸ Ideal.span {g}) W)
      (_ : Algebra.Etale (P ⧸ Ideal.span {g}) W) (_ : Algebra (Node O c) W)
      (_ : Algebra.Etale (Node O c) W) (𝔔 : Ideal W) (_ : 𝔔.IsPrime),
      (∀ p : P, algebraMap (P ⧸ Ideal.span {g}) W (Ideal.Quotient.mk _ p) ∈ 𝔔 ↔ p ∈ Q₀) ∧
      (∀ r : R, algebraMap (P ⧸ Ideal.span {g}) W (Ideal.Quotient.mk _ (algebraMap R P r)) =
        algebraMap (Node O c) W (algebraMap O (Node O c) (algebraMap R O r))) ∧
      (∀ i, algebraMap (Node O c) W (coordinate c i) ∈ 𝔔) ∧
      algebraMap (Node O c) W (algebraMap O (Node O c) c) ∈ 𝔔 := by
  -- the critical locus
  have : Algebra.Etale R (P ⧸ critIdeal R P g) := etale_critical R P g hg
  let π : P →ₐ[R] P ⧸ critIdeal R P g := Ideal.Quotient.mkₐ R _
  have hπ : ∀ i, π (planeDerivation R P i g) = 0 := by
    intro i
    change Ideal.Quotient.mk _ _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    fin_cases i
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hcritle : critIdeal R P g ≤ Q₀ := by
    rw [critIdeal, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hcrit 0
    · exact hcrit 1
  set 𝔮 : Ideal (P ⧸ critIdeal R P g) := Q₀.map (Ideal.Quotient.mk (critIdeal R P g))
  have : 𝔮.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hcritle)
  have hπ𝔮 : ∀ x, π x ∈ 𝔮 ↔ x ∈ Q₀ := by
    intro x
    change Ideal.Quotient.mk _ x ∈ 𝔮 ↔ _
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hcritle]
  have hg𝔮 : π g ∈ 𝔮 := (hπ𝔮 g).mpr hgQ
  obtain ⟨W, _, _, _, _, _, 𝔔, _, hcompat, hP, hO, hcoordW⟩ :=
    exists_nodeChart R P (P ⧸ critIdeal R P g) g hg π hπ 𝔮 hg𝔮
  -- `W` over `P/(g)` through `P/(g) → O ⊗_R P/(g)`
  let : Algebra (P ⧸ Ideal.span {g}) ((P ⧸ critIdeal R P g) ⊗[R] (P ⧸ Ideal.span {g})) :=
    Algebra.TensorProduct.rightAlgebra
  have : Algebra.Etale (P ⧸ Ideal.span {g})
      ((P ⧸ critIdeal R P g) ⊗[R] (P ⧸ Ideal.span {g})) :=
    etale_rightAlgebra R (P ⧸ critIdeal R P g) (P ⧸ Ideal.span {g})
  let : Algebra (P ⧸ Ideal.span {g}) W :=
    ((algebraMap ((P ⧸ critIdeal R P g) ⊗[R] (P ⧸ Ideal.span {g})) W).comp
      (algebraMap (P ⧸ Ideal.span {g}) ((P ⧸ critIdeal R P g) ⊗[R] (P ⧸ Ideal.span {g})))).toAlgebra
  have : IsScalarTower (P ⧸ Ideal.span {g}) ((P ⧸ critIdeal R P g) ⊗[R] (P ⧸ Ideal.span {g})) W :=
    .of_algebraMap_eq' rfl
  have : Algebra.Etale (P ⧸ Ideal.span {g}) W := Algebra.Etale.comp _
    ((P ⧸ critIdeal R P g) ⊗[R] (P ⧸ Ideal.span {g})) W
  refine ⟨P ⧸ critIdeal R P g, inferInstance, inferInstance, inferInstance, -π g, W,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, 𝔔, inferInstance,
    fun p => ?_, fun r => ?_, hcoordW, ?_⟩
  · change algebraMap _ W ((1 : P ⧸ critIdeal R P g) ⊗ₜ Ideal.Quotient.mk _ p) ∈ 𝔔 ↔ _
    rw [hP, hπ𝔮]
  · change algebraMap _ W ((1 : P ⧸ critIdeal R P g) ⊗ₜ
      Ideal.Quotient.mk (Ideal.span {g}) (algebraMap R P r)) = _
    rw [← hcompat, Ideal.Quotient.mk_algebraMap, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  · rw [← hcompat, hO]
    exact neg_mem hg𝔮

end Hypersurface

section Main

variable {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
  [Module.Flat R B] [Algebra.FinitePresentation R B]

open DeJongAlterations.Algebra.NodeBlowupChart in
/-- **Étale local structure of a nodal family at a node** (Stacks, Tag 0CBY). Let `R → B` be flat
and finitely presented and `z ⊂ K ⊗_R B` a geometric node. There is `f ∈ B` outside the point under
`z` such that every geometric node `z'` of `B_f` has an étale neighbourhood: an étale `B_f`-algebra
`W` with a prime `𝔔` over the point under `z'`, which is also étale over the standard node
`O[u, v]/(uv - c)` for an étale `R`-algebra `O` and some `c ∈ O`, compatibly with the
`R`-structures; at `𝔔` the coordinates `u, v` and the parameter `c` vanish. -/
theorem exists_away_etale_nodeChart {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K]
    (z : Ideal (K ⊗[R] B)) [z.IsMaximal] (hz : IsFormalNode K z) :
    ∃ f : B, f ∉ z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ∧
      ∀ (K' : Type u) [Field K'] [IsAlgClosed K'] [Algebra R K']
        (z' : Ideal (K' ⊗[R] Localization.Away f)) [z'.IsMaximal], IsFormalNode K' z' →
        ∃ (O : Type u) (_ : CommRing O) (_ : Algebra R O) (_ : Algebra.Etale R O) (c : O)
          (W : Type u) (_ : CommRing W) (_ : Algebra (Localization.Away f) W)
          (_ : Algebra.Etale (Localization.Away f) W) (_ : Algebra (Node O c) W)
          (_ : Algebra.Etale (Node O c) W) (𝔔 : Ideal W) (_ : 𝔔.IsPrime),
          𝔔.comap (algebraMap (Localization.Away f) W) =
            z'.comap (Algebra.TensorProduct.includeRight :
              Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).toRingHom ∧
          (∀ r : R, algebraMap (Localization.Away f) W (algebraMap R _ r) =
            algebraMap (Node O c) W (algebraMap O (Node O c) (algebraMap R O r))) ∧
          (∀ i, algebraMap (Node O c) W (coordinate c i) ∈ 𝔔) ∧
          algebraMap (Node O c) W (algebraMap O (Node O c) c) ∈ 𝔔 := by
  obtain ⟨e⟩ := hz
  have : IsNoetherianRing (K ⊗[R] B) := Algebra.FiniteType.isNoetherianRing K _
  have h2 : (maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 2 := by
    rw [← AdicCompletion.spanFinrank_maximalIdeal_eq,
      ← Ideal.spanFinrank_map_eq_of_ringEquiv e.toRingEquiv,
      map_ringEquiv_maximalIdeal e.toRingEquiv]
    exact spanFinrank_maximalIdeal_formalUV_le_two K
  obtain ⟨b, -, hunr⟩ := exists_isUnramifiedAt_plane z 2 le_rfl h2
  let : Algebra (MvPolynomial (Fin 2) R) B := (MvPolynomial.aeval (R := R) b).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin 2) R) B := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R B r = MvPolynomial.aeval b (MvPolynomial.C r)
    rw [MvPolynomial.aeval_C]
  have : Algebra.FiniteType (MvPolynomial (Fin 2) R) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (MvPolynomial (Fin 2) R) B
  have := hunr
  obtain ⟨f, hfq, Pe, ψ, hψ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := MvPolynomial (Fin 2) R)
      (z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom)
  refine ⟨f, hfq, fun K' _ _ _ z' _ ⟨e'⟩ => ?_⟩
  let : Algebra R Pe.Ring := ((algebraMap (MvPolynomial (Fin 2) R) Pe.Ring).comp
    (algebraMap R (MvPolynomial (Fin 2) R))).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin 2) R) Pe.Ring :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψR : Pe.Ring →ₐ[R] Localization.Away f := ψ.restrictScalars R
  have : Module.Flat R (Localization.Away f) := Module.Flat.trans R B (Localization.Away f)
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    Algebra.FinitePresentation.trans R B (Localization.Away f)
  obtain ⟨g, hgJ, h, hhQ, hhessQ, hcrit, hJ⟩ := exists_principal_kernel_crit ψR hψ z' e'
  set Q₀ := z'.comap ((Algebra.TensorProduct.includeRight :
      Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).comp ψR).toRingHom with hQ₀
  have : Q₀.IsPrime := Ideal.comap_isPrime _ _
  set a := h * hessian R Pe.Ring g with ha
  have haQ : a ∉ Q₀ := fun hmem => (Ideal.IsPrime.mem_or_mem ‹_› hmem).elim hhQ hhessQ
  -- localize at `a`
  let Pa := Localization.Away a
  have : Algebra.Etale Pe.Ring Pa := Algebra.Etale.of_isLocalizationAway a
  have : Algebra.Etale (MvPolynomial (Fin 2) R) Pa := Algebra.Etale.comp _ Pe.Ring Pa
  have : IsScalarTower R (MvPolynomial (Fin 2) R) Pa := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R Pe.Ring Pa,
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) Pe.Ring,
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) Pe.Ring Pa]
  have hca : ∀ i, (IsScalarTower.toAlgHom R Pe.Ring Pa) (coord R Pe.Ring i) = coord R Pa i :=
    fun i => (IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) Pe.Ring Pa _).symm
  have hhess : IsUnit (hessian R Pa (algebraMap Pe.Ring Pa g)) := by
    have := hessian_map (IsScalarTower.toAlgHom R Pe.Ring Pa) hca g
    simp only [IsScalarTower.coe_toAlgHom'] at this
    rw [this]
    have hau : IsUnit (algebraMap Pe.Ring Pa a) := IsLocalization.Away.algebraMap_isUnit a
    have hmul : algebraMap Pe.Ring Pa a = algebraMap Pe.Ring Pa h *
        algebraMap Pe.Ring Pa (hessian R Pe.Ring g) := map_mul _ _ _
    rw [hmul] at hau
    exact isUnit_of_mul_isUnit_right hau
  have hdisj : Disjoint (Submonoid.powers a : Set Pe.Ring) Q₀ :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr haQ
  set Q₀a := Q₀.map (algebraMap Pe.Ring Pa)
  have : Q₀a.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) Pa Q₀ ‹_› hdisj
  have hQ₀a : Q₀a.comap (algebraMap Pe.Ring Pa) = Q₀ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) Pa ‹_› hdisj
  have hcrita : ∀ i, planeDerivation R Pa i (algebraMap Pe.Ring Pa g) ∈ Q₀a := by
    intro i
    have := planeDerivation_map (IsScalarTower.toAlgHom R Pe.Ring Pa) hca i g
    simp only [IsScalarTower.coe_toAlgHom'] at this
    rw [this]
    exact Ideal.mem_map_of_mem _ (hcrit i)
  have hgQ₀ : g ∈ Q₀ := by
    rw [hQ₀, Ideal.mem_comap]
    change (Algebra.TensorProduct.includeRight : Localization.Away f →ₐ[R] _) (ψR g) ∈ z'
    rw [show ψR g = 0 from RingHom.mem_ker.mp hgJ, map_zero]
    exact z'.zero_mem
  have hgaQ : algebraMap Pe.Ring Pa g ∈ Q₀a := Ideal.mem_map_of_mem _ hgQ₀
  obtain ⟨O, _, _, _, c, W, _, _, _, _, _, 𝔔, _, hP, hR, hcoordW, hcW⟩ :=
    exists_hypersurface_nodeChart R Pa (algebraMap Pe.Ring Pa g) hhess Q₀a hgaQ hcrita
  -- the hypersurface `Pa/(g) ≅ (B_f)_{ψ a}`
  let Bfs := Localization.Away (ψR a)
  let φa : Pa →ₐ[R] Bfs := Localization.awayMapₐ ψR a
  have hφa : Function.Surjective φa := IsLocalization.Away.mapₐ_surjective_of_surjective a hψ
  have hker : RingHom.ker φa.toRingHom = Ideal.span {algebraMap Pe.Ring Pa g} :=
    ker_awayMap_eq_span ψR g hgJ h (hessian R Pe.Ring g) hJ
  let eB : (Pa ⧸ Ideal.span {algebraMap Pe.Ring Pa g}) ≃+* Bfs :=
    (Ideal.quotientEquivAlgOfEq R hker.symm).toRingEquiv.trans
      (Ideal.quotientKerAlgEquivOfSurjective hφa).toRingEquiv
  have heB : ∀ x, eB (Ideal.Quotient.mk _ x) = φa x := fun _ => rfl
  -- the étale `B_f`-structure of `W`: `B_f → Bfs ≅ Pa/(g) → W`
  let : Algebra Bfs (Pa ⧸ Ideal.span {algebraMap Pe.Ring Pa g}) := eB.symm.toRingHom.toAlgebra
  have : Algebra.Etale Bfs (Pa ⧸ Ideal.span {algebraMap Pe.Ring Pa g}) :=
    etale_of_ringEquiv eB.symm
  let : Algebra Bfs W := ((algebraMap (Pa ⧸ Ideal.span {algebraMap Pe.Ring Pa g}) W).comp
    (algebraMap Bfs (Pa ⧸ Ideal.span {algebraMap Pe.Ring Pa g}))).toAlgebra
  have : IsScalarTower Bfs (Pa ⧸ Ideal.span {algebraMap Pe.Ring Pa g}) W :=
    .of_algebraMap_eq' rfl
  have : Algebra.Etale Bfs W := Algebra.Etale.comp Bfs (Pa ⧸ Ideal.span {algebraMap Pe.Ring Pa g}) W
  have : Algebra.Etale (Localization.Away f) Bfs := Algebra.Etale.of_isLocalizationAway (ψR a)
  let : Algebra (Localization.Away f) W :=
    ((algebraMap Bfs W).comp (algebraMap (Localization.Away f) Bfs)).toAlgebra
  have : Algebra.Etale (Localization.Away f) W :=
    RingHom.etale_algebraMap.mp (RingHom.Etale.stableUnderComposition _ _
      (RingHom.etale_algebraMap.mpr inferInstance) (RingHom.etale_algebraMap.mpr inferInstance))
  -- the image of `ψ p` in `W`
  have himg : ∀ p : Pe.Ring, algebraMap (Localization.Away f) W (ψR p) =
      algebraMap (Pa ⧸ Ideal.span {algebraMap Pe.Ring Pa g}) W
        (Ideal.Quotient.mk _ (algebraMap Pe.Ring Pa p)) := by
    intro p
    have h1 : algebraMap (Localization.Away f) Bfs (ψR p) = φa (algebraMap Pe.Ring Pa p) := by
      change _ = IsLocalization.Away.map Pa Bfs ψR.toRingHom a (algebraMap Pe.Ring Pa p)
      rw [IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    change algebraMap (Pa ⧸ Ideal.span {algebraMap Pe.Ring Pa g}) W
      (eB.symm (algebraMap (Localization.Away f) Bfs (ψR p))) = _
    rw [h1, ← heB, RingEquiv.symm_apply_apply]
  refine ⟨O, inferInstance, inferInstance, inferInstance, c, W, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, 𝔔, inferInstance, ?_, ?_, hcoordW, hcW⟩
  · apply Ideal.comap_injective_of_surjective ψR.toRingHom hψ
    ext p
    simp only [Ideal.mem_comap]
    change algebraMap (Localization.Away f) W (ψR p) ∈ 𝔔 ↔ _
    rw [himg, hP, ← Ideal.mem_comap, hQ₀a, hQ₀]
    rfl
  · intro r
    rw [show algebraMap R (Localization.Away f) r = ψR (algebraMap R Pe.Ring r) from
      (ψR.commutes r).symm, himg, ← IsScalarTower.algebraMap_apply, hR]

end Main

end DeJongAlterations.StableModification.Curves.SemistableNormal
