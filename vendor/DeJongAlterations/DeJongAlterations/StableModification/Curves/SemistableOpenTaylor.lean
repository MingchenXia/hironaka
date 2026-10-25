import DeJongAlterations.StableModification.Curves.SemistableOpenSeries
import DeJongAlterations.StableModification.Curves.SemistableOpenPlane
import DeJongAlterations.Algebra.AdicCompletionEtale
import DeJongAlterations.Algebra.AdicCompletionTransportLocalization
import DeJongAlterations.Algebra.AdicCompletionTransportQuotient
import DeJongAlterations.Algebra.NodeCompletionPolynomial
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Taylor expansion on a surface étale over the affine plane

Let `K` be a field and `P` a `K`-algebra which is étale over the polynomial ring `K[X₀, X₁]`
(write `uᵢ` for the image of `Xᵢ`). At a maximal ideal `Q` of `P` with residue field `K`, where
`uᵢ` takes the value `cᵢ`, the completed local ring of `P` is the formal power series ring:
`Ô_{P,Q} ≅ K[[X₀, X₁]]`, `uᵢ ↦ cᵢ + Xᵢ` (Codex's étale completion comparison
`Algebra.AdicCompletionEtale.completedAlgEquiv` and Mathlib's
`MvPowerSeries.toAdicCompletionAlgEquiv`). The composite `taylor Q c : P → K[[X₀, X₁]]` is the
Taylor expansion at `Q`. This file proves:

* `comap_taylor_maximalIdeal`: `taylor⁻¹(𝔪) = Q`;
* `taylor_derivation`: for a `K`-derivation `D` of `P` with `D uⱼ = δᵢⱼ`,
  `taylor (D p) = ∂ᵢ (taylor p)` (derivations of an étale `K[X₀, X₁]`-algebra are determined by
  their values on the coordinates);
* `nonempty_completion_quotient_equiv`: for a surjection `π : P → T` with kernel `(g)` and a
  maximal ideal `y` of `T` over `Q`, the completed local ring of `T` at `y` is
  `K[[X₀, X₁]]/(taylor g)`.

This is the formal input of the openness of the semi-stable locus (M. Temkin, *Stable
modification of relative curves*, Lemma 5.1(i), T:3282–3292): near a node, a family of curves is
a hypersurface in a smooth surface (blueprint `sm-semistable-curves.tex`).
-/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.StableModification.Curves.SemistableOpen

open Algebra.NodeFormalMorse Algebra.NodeVariableMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section Plane

variable (K : Type u) [Field K]

/-- The coordinate shift `Xᵢ ↦ Xᵢ + cᵢ` of the affine plane. -/
def shiftEquiv (c : Fin 2 → K) : MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (c i))
    (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (c i))
    (by apply MvPolynomial.algHom_ext; intro i; simp)
    (by apply MvPolynomial.algHom_ext; intro i; simp)

@[simp]
theorem shiftEquiv_X (c : Fin 2 → K) (i : Fin 2) :
    shiftEquiv K c (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (c i) := by
  simp [shiftEquiv]

@[simp]
theorem shiftEquiv_symm_X (c : Fin 2 → K) (i : Fin 2) :
    (shiftEquiv K c).symm (MvPolynomial.X i) = MvPolynomial.X i - MvPolynomial.C (c i) := by
  simp [shiftEquiv]

/-- The maximal ideal of the rational point `c` of the plane. -/
def pointIdeal (c : Fin 2 → K) : Ideal (MvPolynomial (Fin 2) K) :=
  (MvPolynomial.idealOfVars (Fin 2) K).map
    ((shiftEquiv K c).symm : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K)

instance pointIdeal_isMaximal (c : Fin 2 → K) : (pointIdeal K c).IsMaximal :=
  Ideal.map_isMaximal_of_equiv _

theorem pointIdeal_eq_span (c : Fin 2 → K) :
    pointIdeal K c = Ideal.span (Set.range fun i => MvPolynomial.X i - MvPolynomial.C (c i)) := by
  rw [pointIdeal, MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext i
  simp

theorem sub_mem_pointIdeal (c : Fin 2 → K) (i : Fin 2) :
    MvPolynomial.X i - MvPolynomial.C (c i) ∈ pointIdeal K c := by
  rw [pointIdeal_eq_span]
  exact Ideal.subset_span ⟨i, rfl⟩

theorem map_pointIdeal_shiftEquiv (c : Fin 2 → K) :
    MvPolynomial.idealOfVars (Fin 2) K = (pointIdeal K c).map
      ((shiftEquiv K c : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K)) := by
  rw [pointIdeal, Ideal.map_map]
  have : ((shiftEquiv K c : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K).comp
      ((shiftEquiv K c).symm : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K)) =
      RingHom.id _ :=
    RingHom.ext fun a => (shiftEquiv K c).apply_symm_apply a
  rw [this, Ideal.map_id]

/-- The completion of the plane at the rational point `c` is the formal power series ring, with
`Xᵢ ↦ cᵢ + Xᵢ` (Taylor expansion at `c`). -/
def planeCompletionEquiv (c : Fin 2 → K) :
    AdicCompletion (pointIdeal K c) (MvPolynomial (Fin 2) K) ≃ₐ[K] Series K :=
  (AdicCompletion.congrAlgEquiv (pointIdeal K c) (MvPolynomial.idealOfVars (Fin 2) K)
    (shiftEquiv K c) (map_pointIdeal_shiftEquiv K c)).trans
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) K).symm.restrictScalars K)

theorem planeCompletionEquiv_of (c : Fin 2 → K) (a : MvPolynomial (Fin 2) K) :
    planeCompletionEquiv K c (AdicCompletion.of _ _ a) =
      ((shiftEquiv K c a : MvPolynomial (Fin 2) K) : Series K) := by
  rw [planeCompletionEquiv, AlgEquiv.trans_apply, AdicCompletion.congrAlgEquiv_of,
    AlgEquiv.restrictScalars_apply, AlgEquiv.symm_apply_eq,
    MvPowerSeries.toAdicCompletionAlgEquiv_apply, MvPowerSeries.toAdicCompletion_coe]

end Plane

section Etale

variable {K : Type u} [Field K] {P : Type u} [CommRing P] [Algebra K P]
  [Algebra (MvPolynomial (Fin 2) K) P] [IsScalarTower K (MvPolynomial (Fin 2) K) P]
  [Algebra.Etale (MvPolynomial (Fin 2) K) P]

local notation "A" => MvPolynomial (Fin 2) K

variable (Q : Ideal P) [Q.IsMaximal] (c : Fin 2 → K)

/-- A rational point of `P`: `Q` is maximal with residue field `K`, and `uᵢ ≡ cᵢ mod Q`. -/
structure IsRationalPoint : Prop where
  coord_sub_mem : ∀ i, coord K P i - algebraMap K P (c i) ∈ Q
  residue_surjective : Function.Surjective (algebraMap K (P ⧸ Q))

variable {Q c}

omit [Algebra.Etale A P] in
theorem IsRationalPoint.under_eq (hQ : IsRationalPoint Q c) :
    Q.under A = pointIdeal K c := by
  symm
  apply (pointIdeal_isMaximal K c).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
  rw [pointIdeal_eq_span, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change algebraMap A P _ ∈ Q
  rw [map_sub, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  exact hQ.coord_sub_mem i

omit [Algebra.Etale A P] in
theorem IsRationalPoint.liesOver (hQ : IsRationalPoint Q c) : Q.LiesOver (pointIdeal K c) :=
  ⟨hQ.under_eq.symm⟩

section Local

omit [Algebra.Etale A P] in
/-- The residue field map of `𝒪_{A,c} → 𝒪_{P,Q}` is bijective at a rational point. -/
theorem IsRationalPoint.residueField_map_bijective (hQ : IsRationalPoint Q c) :
    letI := hQ.liesOver
    letI := Localization.AtPrime.algebraOfLiesOver (pointIdeal K c) Q
    Function.Bijective (ResidueField.map (algebraMap (Localization.AtPrime (pointIdeal K c)) (Localization.AtPrime Q))) := by
  let := hQ.liesOver
  let := Localization.AtPrime.algebraOfLiesOver (pointIdeal K c) Q
  refine ⟨(ResidueField.map (algebraMap (Localization.AtPrime (pointIdeal K c)) (Localization.AtPrime Q))).injective, fun z => ?_⟩
  obtain ⟨w, hw⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal Q (Localization.AtPrime Q)).surjective z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨k, hk⟩ := hQ.residue_surjective (Ideal.Quotient.mk Q p)
  refine ⟨residue _ (algebraMap K (Localization.AtPrime (pointIdeal K c)) k), ?_⟩
  rw [← hw, IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk, ResidueField.map_residue,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K P (Localization.AtPrime Q)]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
  change _ ∈ (maximalIdeal (Localization.AtPrime Q)).under P
  rw [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime Q) Q]
  rw [← Ideal.Quotient.eq]
  exact hk

/-- The completed local ring of `P` at a rational point, as a ring: `Ô_{P,Q} ≅ K[[X₀, X₁]]`. -/
def IsRationalPoint.completionRingEquiv (hQ : IsRationalPoint Q c) :
    AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) ≃+*
      Series K := by
  letI := hQ.liesOver
  letI := Localization.AtPrime.algebraOfLiesOver (pointIdeal K c) Q
  haveI : IsLocalHom (algebraMap (Localization.AtPrime (pointIdeal K c))
      (Localization.AtPrime Q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  haveI : Algebra.FormallyEtale (Localization.AtPrime (pointIdeal K c))
      (Localization.AtPrime Q) := .localization_base (pointIdeal K c).primeCompl
  haveI : Algebra.EssFiniteType A (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.comp A P (Localization.AtPrime Q)
  haveI : Algebra.EssFiniteType (Localization.AtPrime (pointIdeal K c))
      (Localization.AtPrime Q) := .of_comp A _ _
  exact (Algebra.AdicCompletionEtale.completedRingEquiv hQ.residueField_map_bijective).symm.trans
    ((AdicCompletion.localizationAlgEquiv (pointIdeal K c)
      (Localization.AtPrime (pointIdeal K c))).symm.toRingEquiv.trans
      (planeCompletionEquiv K c).toRingEquiv)

theorem IsRationalPoint.completionRingEquiv_of_algebraMap (hQ : IsRationalPoint Q c) (a : A) :
    hQ.completionRingEquiv (AdicCompletion.of _ _ (algebraMap P (Localization.AtPrime Q)
      (algebraMap A P a))) = ((shiftEquiv K c a : A) : Series K) := by
  let := hQ.liesOver
  let := Localization.AtPrime.algebraOfLiesOver (pointIdeal K c) Q
  have : IsLocalHom (algebraMap (Localization.AtPrime (pointIdeal K c))
      (Localization.AtPrime Q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have : Algebra.FormallyEtale (Localization.AtPrime (pointIdeal K c))
      (Localization.AtPrime Q) := .localization_base (pointIdeal K c).primeCompl
  have : Algebra.EssFiniteType A (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.comp A P (Localization.AtPrime Q)
  have : Algebra.EssFiniteType (Localization.AtPrime (pointIdeal K c))
      (Localization.AtPrime Q) := .of_comp A _ _
  have htower : algebraMap P (Localization.AtPrime Q) (algebraMap A P a) =
      algebraMap (Localization.AtPrime (pointIdeal K c)) (Localization.AtPrime Q)
        (algebraMap A (Localization.AtPrime (pointIdeal K c)) a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [htower]
  have h1 : (Algebra.AdicCompletionEtale.completedRingEquiv hQ.residueField_map_bijective).symm
      (AdicCompletion.of _ _ (algebraMap (Localization.AtPrime (pointIdeal K c))
        (Localization.AtPrime Q) (algebraMap A (Localization.AtPrime (pointIdeal K c)) a))) =
      AdicCompletion.of _ _ (algebraMap A (Localization.AtPrime (pointIdeal K c)) a) := by
    rw [RingEquiv.symm_apply_eq, Algebra.AdicCompletionEtale.completedRingEquiv_of]
  have h2 : (AdicCompletion.localizationAlgEquiv (pointIdeal K c)
      (Localization.AtPrime (pointIdeal K c))).symm
      (AdicCompletion.of _ _ (algebraMap A (Localization.AtPrime (pointIdeal K c)) a)) =
      AdicCompletion.of _ _ a := by
    rw [AlgEquiv.symm_apply_eq, AdicCompletion.localizationAlgEquiv_of]
  unfold IsRationalPoint.completionRingEquiv
  rw [RingEquiv.trans_apply, h1, RingEquiv.trans_apply]
  change (planeCompletionEquiv K c) ((AdicCompletion.localizationAlgEquiv (pointIdeal K c)
      (Localization.AtPrime (pointIdeal K c))).symm _) = _
  rw [h2, planeCompletionEquiv_of]

/-- The completed local ring of `P` at a rational point: `Ô_{P,Q} ≅ K[[X₀, X₁]]` as
`K`-algebras, with `uᵢ ↦ cᵢ + Xᵢ`. -/
def IsRationalPoint.completionEquiv (hQ : IsRationalPoint Q c) :
    AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) ≃ₐ[K]
      Series K :=
  AlgEquiv.ofRingEquiv (f := hQ.completionRingEquiv) fun k => by
    have hk : algebraMap K (Localization.AtPrime Q) k =
        algebraMap P (Localization.AtPrime Q) (algebraMap A P (MvPolynomial.C k)) := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K A P,
        ← IsScalarTower.algebraMap_apply K P]
    rw [AdicCompletion.algebraMap_apply, hk, hQ.completionRingEquiv_of_algebraMap,
      ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, MvPolynomial.algebraMap_eq,
      MvPolynomial.coe_C]
    rfl

/-- The **Taylor expansion** of `P` at the rational point `Q`: `P → 𝒪_{P,Q} → Ô_{P,Q} ≅ K[[X₀, X₁]]`,
with `uᵢ ↦ cᵢ + Xᵢ`. -/
def IsRationalPoint.taylor (hQ : IsRationalPoint Q c) : P →ₐ[K] Series K where
  toRingHom := hQ.completionRingEquiv.toRingHom.comp
    ((algebraMap (Localization.AtPrime Q)
      (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q))).comp
      (algebraMap P (Localization.AtPrime Q)))
  commutes' k := by
    change hQ.completionEquiv (algebraMap _ _ (algebraMap P _ (algebraMap K P k))) = _
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      AlgEquiv.commutes]

theorem IsRationalPoint.taylor_apply (hQ : IsRationalPoint Q c) (p : P) :
    hQ.taylor p = hQ.completionRingEquiv (AdicCompletion.of _ _
      (algebraMap P (Localization.AtPrime Q) p)) := by
  change hQ.completionRingEquiv (algebraMap _ _ _) = _
  rfl

theorem IsRationalPoint.taylor_algebraMap (hQ : IsRationalPoint Q c) (a : A) :
    hQ.taylor (algebraMap A P a) = ((shiftEquiv K c a : A) : Series K) := by
  rw [hQ.taylor_apply, hQ.completionRingEquiv_of_algebraMap]

theorem IsRationalPoint.taylor_coord (hQ : IsRationalPoint Q c) (i : Fin 2) :
    hQ.taylor (coord K P i) = X i + C (c i) := by
  rw [coord, hQ.taylor_algebraMap, shiftEquiv_X, MvPolynomial.coe_add, MvPolynomial.coe_X,
    MvPolynomial.coe_C]

/-- The maximal ideal of `K[[X₀, X₁]]` is the kernel of the constant coefficient. -/
theorem mem_maximalIdeal_series_iff (f : Series K) :
    f ∈ maximalIdeal (Series K) ↔ constantCoeff f = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not]

/-- Units of `𝒪_{P,Q}` stay units after Taylor expansion: `taylor⁻¹(𝔪) = Q`. -/
theorem IsRationalPoint.comap_taylor_maximalIdeal (hQ : IsRationalPoint Q c) :
    (maximalIdeal (Series K)).comap hQ.taylor.toRingHom = Q := by
  have hle : (maximalIdeal (Series K)).comap hQ.taylor.toRingHom ≤ Q := by
    intro p hp
    by_contra hpQ
    apply hp
    change IsUnit (hQ.completionRingEquiv (algebraMap (Localization.AtPrime Q)
      (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q))
      (algebraMap P (Localization.AtPrime Q) p)))
    apply IsUnit.map
    apply IsUnit.map
    exact IsLocalization.map_units (Localization.AtPrime Q) (⟨p, hpQ⟩ : Q.primeCompl)
  have hmax : ((maximalIdeal (Series K)).comap hQ.taylor.toRingHom).IsMaximal := by
    have h : (maximalIdeal (Series K)).comap hQ.taylor.toRingHom =
        RingHom.ker ((constantCoeff : Series K →+* K).comp hQ.taylor.toRingHom) := by
      ext p
      rw [Ideal.mem_comap, mem_maximalIdeal_series_iff, RingHom.mem_ker, RingHom.comp_apply]
    rw [h]
    apply RingHom.ker_isMaximal_of_surjective
    intro k
    refine ⟨algebraMap K P k, ?_⟩
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      MvPowerSeries.constantCoeff_C]
  exact hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle

theorem IsRationalPoint.mem_iff_taylor (hQ : IsRationalPoint Q c) (p : P) :
    p ∈ Q ↔ constantCoeff (hQ.taylor p) = 0 := by
  constructor
  · intro h
    have h' : p ∈ (maximalIdeal (Series K)).comap hQ.taylor.toRingHom :=
      hQ.comap_taylor_maximalIdeal.symm ▸ h
    exact (mem_maximalIdeal_series_iff _).mp h'
  · intro h
    have h' : p ∈ (maximalIdeal (Series K)).comap hQ.taylor.toRingHom :=
      (mem_maximalIdeal_series_iff _).mpr h
    exact hQ.comap_taylor_maximalIdeal ▸ h'

end Local

section Derivations

/-- **Taylor expansion intertwines partial derivatives.** If `D` is a `K`-derivation of `P` with
`D uⱼ = δᵢⱼ`, then `taylor (D p) = ∂ᵢ (taylor p)`. -/
theorem IsRationalPoint.taylor_derivation (hQ : IsRationalPoint Q c) (D : Derivation K P P)
    (i : Fin 2) (hD : ∀ j, D (coord K P j) = if j = i then 1 else 0) (p : P) :
    hQ.taylor (D p) = MvPowerSeries.pderiv K i (hQ.taylor p) := by
  let : Algebra P (Series K) := hQ.taylor.toRingHom.toAlgebra
  have : IsScalarTower K P (Series K) :=
    IsScalarTower.of_algebraMap_eq fun k => (hQ.taylor.commutes k).symm
  let D₁ : Derivation K P (Series K) := (Algebra.linearMap P (Series K)).compDer D
  let D₂ : Derivation K P (Series K) := (MvPowerSeries.pderiv K i).compAlgebraMap P
  have hD₁₂ : D₁ = D₂ := by
    apply derivation_ext K P
    intro j
    change hQ.taylor (D (coord K P j)) = MvPowerSeries.pderiv K i (hQ.taylor (coord K P j))
    rw [hD j, hQ.taylor_coord, map_add, MvPowerSeries.pderiv_C, add_zero]
    by_cases hji : j = i
    · subst hji; simp
    · rw [if_neg hji, MvPowerSeries.pderiv_X_of_ne hji, map_zero]
  exact Derivation.congr_fun hD₁₂ p

end Derivations


section Quotient

variable {T : Type u} [CommRing T] [Algebra K T] (π : P →ₐ[K] T)
  (y : Ideal T) [y.IsMaximal] (hy : y.comap π.toRingHom = Q)

omit [Algebra A P] [IsScalarTower K A P] [Algebra.Etale A P] in
include hy in
/-- The local map `𝒪_{P,Q} → 𝒪_{T,y}` induced by `π`. -/
abbrev localQuotientMap : Localization.AtPrime Q →+* Localization.AtPrime y :=
  Localization.localRingHom Q y π.toRingHom hy.symm

omit [Algebra A P] [IsScalarTower K A P] [Algebra.Etale A P] in
theorem localQuotientMap_surjective (hπ : Function.Surjective π) :
    Function.Surjective (localQuotientMap π y hy) := by
  intro z
  obtain ⟨t, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq y.primeCompl z
  obtain ⟨p, rfl⟩ := hπ t
  obtain ⟨p', rfl⟩ := hπ s
  have hp' : p' ∈ Q.primeCompl := by
    change p' ∉ Q
    rw [← hy]
    exact hs
  refine ⟨IsLocalization.mk' (Localization.AtPrime Q) p ⟨p', hp'⟩, ?_⟩
  rw [Localization.localRingHom_mk']
  rfl

omit [Algebra A P] [IsScalarTower K A P] [Algebra.Etale A P] in
/-- The kernel of the local map `𝒪_{P,Q} → 𝒪_{T,y}` is the localization of `ker π`. -/
theorem ker_localQuotientMap_eq_map (hπ : Function.Surjective π) :
    RingHom.ker (localQuotientMap π y hy) =
      (RingHom.ker π.toRingHom).map (algebraMap P (Localization.AtPrime Q)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq Q.primeCompl x
    rw [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htp⟩ := hx
    obtain ⟨p'', rfl⟩ := hπ t
    have hp'' : p'' ∉ Q := by rw [← hy]; exact ht
    have hmem : p'' * p ∈ RingHom.ker π.toRingHom := by
      rw [RingHom.mem_ker, map_mul]
      exact htp
    obtain ⟨v, hv⟩ :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨p'', hp''⟩ : Q.primeCompl)
    have hvi : (↑v⁻¹ : Localization.AtPrime Q) * ↑v = 1 := Units.inv_mul v
    have h3 : IsLocalization.mk' (Localization.AtPrime Q) p (⟨s, hs⟩ : Q.primeCompl) =
        (IsLocalization.mk' (Localization.AtPrime Q) (1 : P) (⟨s, hs⟩ : Q.primeCompl) * ↑v⁻¹) *
          algebraMap P (Localization.AtPrime Q) (p'' * p) := by
      rw [map_mul, IsLocalization.mk'_eq_mul_mk'_one, ← hv]
      linear_combination (-(algebraMap P (Localization.AtPrime Q) p *
        IsLocalization.mk' (Localization.AtPrime Q) (1 : P) (⟨s, hs⟩ : Q.primeCompl))) * hvi
    rw [h3]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hmem)
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, Localization.localRingHom_to_map]
    change algebraMap T (Localization.AtPrime y) (π.toRingHom p) = 0
    rw [RingHom.mem_ker.mp hp, map_zero]

omit [Algebra A P] [IsScalarTower K A P] [Algebra.Etale A P] in
theorem ker_localQuotientMap (hπ : Function.Surjective π) (g : P)
    (hg : RingHom.ker π.toRingHom = Ideal.span {g}) :
    RingHom.ker (localQuotientMap π y hy) =
      Ideal.span {algebraMap P (Localization.AtPrime Q) g} := by
  rw [ker_localQuotientMap_eq_map π y hy hπ, hg, Ideal.map_span, Set.image_singleton]

omit [Algebra K T] in
variable (K) in
include K in
theorem isNoetherianRing_of_etale : IsNoetherianRing P := by
  have : Algebra.FiniteType K P := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  exact Algebra.FiniteType.isNoetherianRing K P

/-- **Completion of a quotient of a surface étale over the plane.** Let `π : P → T` be a
surjective `K`-algebra map and `y ⊂ T` a maximal ideal with `π⁻¹ y = Q` a rational point. Then
`Ô_{T,y} ≅ K[[X₀, X₁]]/(taylor (ker π))`. -/
def IsRationalPoint.quotientCompletionEquiv' (hQ : IsRationalPoint Q c)
    (hπ : Function.Surjective π) :
    AdicCompletion (maximalIdeal (Localization.AtPrime y)) (Localization.AtPrime y) ≃ₐ[K]
      Series K ⧸ (RingHom.ker π.toRingHom).map hQ.taylor.toRingHom := by
  letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime y) :=
    (localQuotientMap π y hy).toAlgebra
  haveI : IsNoetherianRing P := isNoetherianRing_of_etale K
  have hsurj : Function.Surjective
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime y)) :=
    localQuotientMap_surjective π y hy hπ
  have hmax : (maximalIdeal (Localization.AtPrime Q)).map
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime y)) =
      maximalIdeal (Localization.AtPrime y) := map_maximalIdeal_of_surjective _ hsurj
  let Φ := AdicCompletion.mapRingHom (B := Localization.AtPrime y)
    (maximalIdeal (Localization.AtPrime Q))
  have hΦ : Function.Surjective Φ := AdicCompletion.mapRingHom_surjective _ hsurj
  have hΦker : RingHom.ker Φ =
      ((RingHom.ker π.toRingHom).map (algebraMap P (Localization.AtPrime Q))).map
        (algebraMap (Localization.AtPrime Q)
          (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q))) := by
    rw [AdicCompletion.ker_mapRingHom_eq_idealMap _ hsurj]
    change Ideal.map _ (RingHom.ker (localQuotientMap π y hy)) = _
    rw [ker_localQuotientMap_eq_map π y hy hπ]
  let e₁ := RingHom.quotientKerEquivOfSurjective hΦ
  let e₂ := AdicCompletion.congrRingEquiv
    ((maximalIdeal (Localization.AtPrime Q)).map
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime y)))
    (maximalIdeal (Localization.AtPrime y)) (RingEquiv.refl _) (by rw [hmax]; simp)
  have htay : hQ.taylor.toRingHom = hQ.completionRingEquiv.toRingHom.comp
      ((algebraMap (Localization.AtPrime Q)
        (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q))).comp
        (algebraMap P (Localization.AtPrime Q))) := rfl
  have hspan : (RingHom.ker π.toRingHom).map hQ.taylor.toRingHom =
      (RingHom.ker Φ).map hQ.completionRingEquiv := by
    rw [htay, ← Ideal.map_map, ← Ideal.map_map, ← hΦker]
    rfl
  let e₃ := Ideal.quotientEquiv (RingHom.ker Φ)
    ((RingHom.ker π.toRingHom).map hQ.taylor.toRingHom) hQ.completionRingEquiv hspan
  refine AlgEquiv.ofRingEquiv (f := (e₂.symm.trans e₁.symm).trans e₃) fun k => ?_
  have hk : algebraMap (Localization.AtPrime Q) (Localization.AtPrime y)
      (algebraMap K (Localization.AtPrime Q) k) = algebraMap K (Localization.AtPrime y) k := by
    change localQuotientMap π y hy (algebraMap K (Localization.AtPrime Q) k) = _
    rw [IsScalarTower.algebraMap_apply K P (Localization.AtPrime Q),
      Localization.localRingHom_to_map]
    change algebraMap T (Localization.AtPrime y) (π (algebraMap K P k)) = _
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have h₂ : e₂.symm (algebraMap K _ k) = AdicCompletion.of _ _
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime y)
        (algebraMap K (Localization.AtPrime Q) k)) := by
    rw [RingEquiv.symm_apply_eq, AdicCompletion.algebraMap_apply,
      AdicCompletion.congrRingEquiv_of, hk]
    rfl
  have h₁ : e₁.symm (AdicCompletion.of _ _
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime y)
        (algebraMap K (Localization.AtPrime Q) k))) =
      Ideal.Quotient.mk _ (AdicCompletion.of _ _ (algebraMap K (Localization.AtPrime Q) k)) := by
    rw [RingEquiv.symm_apply_eq]
    change _ = Φ _
    rw [AdicCompletion.mapRingHom_of]
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h₂, h₁]
  change Ideal.Quotient.mk _ (hQ.completionEquiv (algebraMap K _ k)) = _
  rw [AlgEquiv.commutes]
  rfl

/-- **Completion of a hypersurface in a surface étale over the plane.** Let `π : P → T` be a
surjective `K`-algebra map with kernel `(g)`, `y ⊂ T` a maximal ideal with `π⁻¹ y = Q` a
rational point. Then `Ô_{T,y} ≅ K[[X₀, X₁]]/(taylor g)`. -/
def IsRationalPoint.quotientCompletionEquiv (hQ : IsRationalPoint Q c)
    (hπ : Function.Surjective π) (g : P) (hg : RingHom.ker π.toRingHom = Ideal.span {g}) :
    AdicCompletion (maximalIdeal (Localization.AtPrime y)) (Localization.AtPrime y) ≃ₐ[K]
      Equation (hQ.taylor g) :=
  (hQ.quotientCompletionEquiv' π y hy hπ).trans (Ideal.quotientEquivAlgOfEq K (by
    rw [hg, Ideal.map_span, Set.image_singleton]
    rfl))


end Quotient


section Classification

variable (hQ : IsRationalPoint Q c)

theorem IsRationalPoint.taylor_planeDerivation (i : Fin 2) (p : P) :
    hQ.taylor (planeDerivation K P i p) = MvPowerSeries.pderiv K i (hQ.taylor p) :=
  hQ.taylor_derivation _ i (fun j => planeDerivation_coord K P i j) p

theorem IsRationalPoint.taylor_hessian (g : P) :
    hQ.taylor (hessian K P g) =
      MvPowerSeries.pderiv K 0 (MvPowerSeries.pderiv K 0 (hQ.taylor g)) *
          MvPowerSeries.pderiv K 1 (MvPowerSeries.pderiv K 1 (hQ.taylor g)) -
        MvPowerSeries.pderiv K 0 (MvPowerSeries.pderiv K 1 (hQ.taylor g)) *
          MvPowerSeries.pderiv K 1 (MvPowerSeries.pderiv K 0 (hQ.taylor g)) := by
  simp only [hessian, map_sub, map_mul, hQ.taylor_planeDerivation]

theorem IsRationalPoint.coeff_single_taylor (g : P) (i : Fin 2) :
    coeff (Finsupp.single i 1) (hQ.taylor g) =
      constantCoeff (hQ.taylor (planeDerivation K P i g)) := by
  rw [hQ.taylor_planeDerivation, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
  simp

variable {T : Type u} [CommRing T] [Algebra K T] (π : P →ₐ[K] T)
  (y : Ideal T) [y.IsMaximal] (hy : y.comap π.toRingHom = Q)
  (hπ : Function.Surjective π) (g : P) (hg : RingHom.ker π.toRingHom = Ideal.span {g})

omit [Algebra A P] [IsScalarTower K A P] [Algebra.Etale A P] [Q.IsMaximal] [y.IsMaximal] in
include hy hg in
theorem mem_of_ker_eq_span : g ∈ Q := by
  rw [← hy, Ideal.mem_comap]
  have : π.toRingHom g = 0 := by rw [← RingHom.mem_ker, hg]; exact Ideal.subset_span rfl
  rw [this]
  exact zero_mem _

omit [y.IsMaximal] in
theorem IsRationalPoint.constantCoeff_taylor_of_ker (hy : y.comap π.toRingHom = Q)
    (hg : RingHom.ker π.toRingHom = Ideal.span {g}) : constantCoeff (hQ.taylor g) = 0 :=
  (hQ.mem_iff_taylor g).mp (mem_of_ker_eq_span π y hy g hg)

include hQ hy hπ hg in
/-- **Smooth points of a hypersurface.** If some partial derivative of `g` does not vanish at the
rational point, the local ring of `T = P/(g)` at `y` has principal maximal ideal. -/
theorem IsRationalPoint.spanFinrank_maximalIdeal_le_one (i : Fin 2)
    (hd : planeDerivation K P i g ∉ Q) :
    (maximalIdeal (Localization.AtPrime y)).spanFinrank ≤ 1 := by
  have hc := hQ.constantCoeff_taylor_of_ker π y g hy hg
  have hi : coeff (Finsupp.single i 1) (hQ.taylor g) ≠ 0 := by
    rw [hQ.coeff_single_taylor]
    exact fun h => hd ((hQ.mem_iff_taylor _).mpr h)
  have : IsNoetherianRing P := isNoetherianRing_of_etale K
  have : IsNoetherianRing T := isNoetherianRing_of_surjective P T π.toRingHom hπ
  let := Algebra.NodeFieldQuadraticSource.equationLocalRing K (hQ.taylor g) hc
  let e := hQ.quotientCompletionEquiv π y hy hπ g hg
  rw [← AdicCompletion.spanFinrank_maximalIdeal_eq,
    ← Ideal.spanFinrank_map_eq_of_ringEquiv e.toRingEquiv,
    map_ringEquiv_maximalIdeal e.toRingEquiv]
  exact spanFinrank_maximalIdeal_equation_le_one (hQ.taylor g) hc i hi

variable [IsAlgClosed K]

/-- **Nodes of a hypersurface.** At a singular rational point of `g = 0` where the Hessian of `g`
is nonzero, `T = P/(g)` has an ordinary double point: `Ô_{T,y} ≅ K[[u, v]]/(uv)`. -/
def IsRationalPoint.nodeEquiv (hd : ∀ i, planeDerivation K P i g ∈ Q)
    (hh : hessian K P g ∉ Q) :
    AdicCompletion (maximalIdeal (Localization.AtPrime y)) (Localization.AtPrime y) ≃ₐ[K]
      Algebra.NodeGeometricCompletionFormalUV.FormalUV K :=
  (hQ.quotientCompletionEquiv π y hy hπ g hg).trans
    (equationEquivFormalUV (hQ.taylor g) (hQ.constantCoeff_taylor_of_ker π y g hy hg)
      (by rw [hQ.coeff_single_taylor]; exact (hQ.mem_iff_taylor _).mp (hd 0))
      (by rw [hQ.coeff_single_taylor]; exact (hQ.mem_iff_taylor _).mp (hd 1))
      (by
        intro hΔ
        apply hh
        rw [hQ.mem_iff_taylor, hQ.taylor_hessian, constantCoeff_hessian, hΔ, neg_zero]))

include hQ hy hπ hg in
/-- **At an ordinary double point of a hypersurface the gradient vanishes and the Hessian is
nonzero.** -/
theorem IsRationalPoint.planeDerivation_mem_and_hessian_not_mem
    (e : AdicCompletion (maximalIdeal (Localization.AtPrime y)) (Localization.AtPrime y) ≃ₐ[K]
      Algebra.NodeGeometricCompletionFormalUV.FormalUV K) :
    (∀ i, planeDerivation K P i g ∈ Q) ∧ hessian K P g ∉ Q := by
  have hc := hQ.constantCoeff_taylor_of_ker π y g hy hg
  obtain ⟨h2, hΔ⟩ := jetDiscriminant_ne_zero_of_equationEquiv (hQ.taylor g)
    ((hQ.quotientCompletionEquiv π y hy hπ g hg).symm.trans e) hc
  rw [mem_variableIdeal_sq_iff] at h2
  refine ⟨fun i => ?_, fun hh => hΔ ?_⟩
  · rw [hQ.mem_iff_taylor, ← hQ.coeff_single_taylor]
    fin_cases i
    · exact h2.2.1
    · exact h2.2.2
  · rw [hQ.mem_iff_taylor, hQ.taylor_hessian, constantCoeff_hessian, neg_eq_zero] at hh
    exact hh

end Classification

end Etale

end DeJongAlterations.StableModification.Curves.SemistableOpen
