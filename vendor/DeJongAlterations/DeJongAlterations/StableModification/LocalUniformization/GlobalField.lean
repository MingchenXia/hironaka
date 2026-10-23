import DeJongAlterations.StableModification.LocalUniformization.GlobalResidue
import DeJongAlterations.StableModification.LocalUniformization.Reduction

/-!
# The function field of a curve over a valuation ring, and ring maps of charts

For an integral scheme `C` flat over `Spec O` (`O` a valuation ring of `K`), the generic point of
`C` lies over the generic point of `Spec O`, so `O → K(C)` is injective and `L = K(C)` is a
`K`-algebra (`functionFieldAlgebra`); the transcendence degree of `L/K` is the fibre dimension
of the generic point (`trdeg_functionField_eq`), at most one for a relative curve. For an
étale chart `e : Y → Spec N` of an open `Y` of `C` (`N` a domain) the ring map `ι : N → L` of
the generic point is injective, and a valuation of `L` centred at a point `y` of `Y` contains
`ι(N)` and has centre `e(y)` on `Spec N` (`exists_chartRingHom`). These are the bridges between
Temkin's valued-field situation (`L` with the valuation `𝔵`, T:2978–2983) and the schemes of
BL1/BND. Blueprint `lem:sm-cofinal-field` (`sm-local-uniformization.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open ValCurves RiemannZariskiSpace
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- **A flat morphism to the spectrum of a domain maps the generic point to the generic point.** -/
theorem flat_apply_genericPoint {X : Scheme.{u}} [IsIntegral X] {N : Type u} [CommRing N]
    [IsDomain N] (f : X ⟶ Spec (.of N)) [Flat f] : (f (genericPoint X)).asIdeal = ⊥ := by
  have hgen : (⊥ : PrimeSpectrum N) ⤳ f (genericPoint X) := by
    rw [← PrimeSpectrum.le_iff_specializes]
    exact bot_le
  obtain ⟨w, hw, hfw⟩ := Flat.generalizingMap f hgen
  have hξw : genericPoint X ⤳ w := (genericPoint_spec X).specializes (Set.mem_univ w)
  have : w = genericPoint X := (hw.antisymm hξw).eq
  rw [← this, hfw]
  rfl

variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
/-- The kernel of the ring map of a point `η : Spec L → X` composed with `q : X → Spec N` is the
prime `q (η pt)`. -/
theorem mem_asIdeal_iff_eq_zero {L : Type u} [Field L] {η : Spec (.of L) ⟶ X}
    {N : Type u} [CommRing N] (q : X ⟶ Spec (.of N)) (θ : N →+* L)
    (hq : η ≫ q = Spec.map (CommRingCat.ofHom θ)) (z : Spec (.of L)) (n : N) :
    n ∈ (q (η z)).asIdeal ↔ θ n = 0 := by
  rw [((isCentre_top (η := η) z).ringHom q θ hq n).2]
  constructor
  · intro h
    by_contra h0
    have : (⊤ : ValuationSubring L).valuation (θ n) = 1 :=
      ((⊤ : ValuationSubring L).valuation_eq_one_iff ⟨θ n, trivial⟩).mp
        (IsUnit.of_mul_eq_one (⟨(θ n)⁻¹, trivial⟩ : (⊤ : ValuationSubring L))
          (Subtype.ext (mul_inv_cancel₀ h0)))
    exact absurd h (by rw [this]; exact lt_irrefl 1)
  · intro h
    change (⊤ : ValuationSubring L).valuation (θ n) < 1
    rw [h, map_zero]
    exact zero_lt_one

/-- **The ring map of the generic point to an affine target.** For `q : X → Spec N` flat, `N` a
domain, the ring map `N → K(X)` of the generic point is injective. -/
theorem injective_of_flat {L : Type u} [Field L] {η : Spec (.of L) ⟶ X}
    (hη : ∀ z, η z = genericPoint X) {N : Type u} [CommRing N] [IsDomain N]
    (q : X ⟶ Spec (.of N)) [Flat q] (θ : N →+* L)
    (hq : η ≫ q = Spec.map (CommRingCat.ofHom θ)) : Function.Injective θ := by
  obtain ⟨z⟩ : Nonempty (Spec (.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  rw [injective_iff_map_eq_zero]
  intro n hn
  have := (mem_asIdeal_iff_eq_zero q θ hq z n).mpr hn
  rw [hη, flat_apply_genericPoint q] at this
  exact this

section FunctionField

variable {K : Type u} [Field K] {O : ValuationSubring K} (φ : X ⟶ Spec (.of O))

/-- The ring map `O → K(X)` of the generic point. -/
def fieldMap : O →+* X.functionField := (Spec.preimage (genericPt X ≫ φ)).hom

/-- `fieldMap φ` induces the composite `Spec K(X) → X → Spec O`. -/
theorem fieldMap_spec : Spec.map (CommRingCat.ofHom (fieldMap φ)) = genericPt X ≫ φ :=
  Spec.map_preimage _

/-- For flat `φ` the map `O → K(X)` is injective. -/
theorem fieldMap_injective [Flat φ] : Function.Injective (fieldMap φ) :=
  injective_of_flat (genericPt_apply (C := X)) φ (fieldMap φ) (fieldMap_spec φ).symm

/-- **The function field of a flat integral `O`-scheme is a `K`-algebra.** -/
abbrev functionFieldAlgebra [Flat φ] : Algebra K X.functionField :=
  (IsFractionRing.lift (fieldMap_injective φ)).toAlgebra

/-- The `K`-algebra structure extends `fieldMap φ`. -/
theorem functionFieldAlgebra_algebraMap_coe [Flat φ] (o : O) :
    letI := functionFieldAlgebra φ
    algebraMap K X.functionField (o : K) = fieldMap φ o :=
  IsFractionRing.lift_algebraMap (fieldMap_injective φ) o

/-- The `K`-algebra structure restricted to `O` is `fieldMap φ`. -/
theorem functionFieldAlgebra_comp [Flat φ] :
    letI := functionFieldAlgebra φ
    (algebraMap K X.functionField).comp O.subtype = fieldMap φ :=
  RingHom.ext (functionFieldAlgebra_algebraMap_coe φ)

/-- `Spec K(X) → X → Spec O` is the spectrum of `O ⊆ K ⊆ K(X)`. -/
theorem genericPt_comp [Flat φ] :
    letI := functionFieldAlgebra φ
    genericPt X ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K X.functionField).comp O.subtype)) := by
  rw [functionFieldAlgebra_comp, fieldMap_spec]

/-- The map `O → 𝒪_{Spec O, p}`. -/
abbrev toStalk' (p : Spec (.of O)) : CommRingCat.of O ⟶ (Spec (.of O)).presheaf.stalk p :=
  (Scheme.ΓSpecIso (.of O)).inv ≫ (Spec (.of O)).presheaf.germ ⊤ p trivial

/-- The ring map `O → K(X)` factors through the stalk at the generic point. -/
theorem fieldMap_eq_stalkMap (o : O) :
    fieldMap φ o = (φ.stalkMap (genericPoint X)).hom ((toStalk' (φ (genericPoint X))).hom o) := by
  have h : genericPt X ≫ φ = Spec.map (toStalk' (φ (genericPoint X)) ≫
      φ.stalkMap (genericPoint X)) := by
    rw [Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
    rfl
  have : fieldMap φ = (toStalk' (φ (genericPoint X)) ≫ φ.stalkMap (genericPoint X)).hom := by
    rw [fieldMap, h, Spec.preimage_map]
  rw [this]
  rfl

/-- **The transcendence degree of `K(X)/K` is the fibre dimension of the generic point.** -/
theorem trdeg_functionField_eq [Flat φ] :
    letI := functionFieldAlgebra φ
    Algebra.trdeg K X.functionField = fiberTrdeg φ (genericPoint X) := by
  let := functionFieldAlgebra φ
  have hφξ : (φ (genericPoint X)).asIdeal = ⊥ := flat_apply_genericPoint φ
  let S := (Spec (.of O)).presheaf.stalk (φ (genericPoint X))
  let : Algebra O S := StructureSheaf.stalkAlgebra O (φ (genericPoint X))
  have hS : IsLocalization.AtPrime S (PrimeSpectrum.asIdeal (φ (genericPoint X))) :=
    StructureSheaf.IsLocalization.to_stalk O (φ (genericPoint X))
  have halg : ∀ o : O, algebraMap O S o = (toStalk' (φ (genericPoint X))).hom o := fun _ ↦ rfl
  -- the residue field at `φ ξ` is a `K`-algebra
  let κs := (Spec (.of O)).residueField (φ (genericPoint X))
  let κx := X.residueField (genericPoint X)
  let ts : O →+* κs := (residue S).comp (algebraMap O S)
  have hts : Function.Injective ts := by
    rw [injective_iff_map_eq_zero]
    intro o ho
    have hmem : algebraMap O S o ∈ maximalIdeal S := (residue_eq_zero_iff _).mp ho
    have h2 : o ∈ PrimeSpectrum.asIdeal (φ (genericPoint X)) := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff S
        (PrimeSpectrum.asIdeal (φ (genericPoint X))) o]
      exact hmem
    rw [hφξ] at h2
    exact h2
  let := (IsFractionRing.lift (K := K) hts).toAlgebra
  let := (φ.residueFieldMap (genericPoint X)).hom.toAlgebra
  let : Algebra K κx :=
    ((X.residue (genericPoint X)).hom.comp (algebraMap K X.functionField)).toAlgebra
  have htower : IsScalarTower K κs κx := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (RingHom.ext fun o ↦ ?_)
    simp only [RingHom.comp_apply]
    change (X.residue (genericPoint X)).hom (algebraMap K X.functionField (o : K)) =
      (φ.residueFieldMap (genericPoint X)).hom (IsFractionRing.lift hts (algebraMap O K o))
    rw [IsFractionRing.lift_algebraMap, functionFieldAlgebra_algebraMap_coe,
      fieldMap_eq_stalkMap]
    change _ = (φ.residueFieldMap (genericPoint X)).hom
      ((Spec (.of O)).residue (φ (genericPoint X)) ((toStalk' (φ (genericPoint X))).hom o))
    have h2 := congrArg (fun f ↦ f.hom ((toStalk' (φ (genericPoint X))).hom o))
      (Scheme.residue_residueFieldMap φ (genericPoint X))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    exact h2.symm
  -- `K → κ(φ ξ)` is surjective, hence algebraic
  have hsurj : Function.Surjective (algebraMap K κs) := by
    intro z
    obtain ⟨s, rfl⟩ := residue_surjective (R := S) z
    obtain ⟨⟨a, b, hb⟩, hab⟩ :=
      IsLocalization.surj (PrimeSpectrum.asIdeal (φ (genericPoint X))).primeCompl s
    have hb0 : (b : K) ≠ 0 := by
      intro h0
      apply hb
      rw [hφξ]
      exact Subtype.ext h0
    refine ⟨(a : K) / b, ?_⟩
    rw [map_div₀]
    change IsFractionRing.lift hts (algebraMap O K a) / IsFractionRing.lift hts (algebraMap O K b) =
      _
    rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    have htb : ts b ≠ 0 := (map_ne_zero_iff ts hts).mpr fun h ↦ hb0 (by rw [h]; rfl)
    rw [div_eq_iff htb]
    change residue S (algebraMap O S a) = residue S s * residue S (algebraMap O S b)
    rw [← map_mul, ← hab]
  have halgs : Algebra.IsAlgebraic K κs := ⟨fun z ↦ by
    obtain ⟨w, rfl⟩ := hsurj z
    exact isAlgebraic_algebraMap w⟩
  -- `K(X) ≅ κ(ξ)` over `K`
  have hres : Function.Bijective (X.residue (genericPoint X)).hom :=
    ⟨(X.residue (genericPoint X)).hom.injective, residue_surjective⟩
  let e : X.functionField ≃ₐ[K] κx :=
    { RingEquiv.ofBijective (X.residue (genericPoint X)).hom hres with commutes' := fun _ ↦ rfl }
  rw [e.trdeg_eq, ← trdeg_add_eq K κs (A := κx), trdeg_eq_zero_iff.mpr halgs, zero_add]
  rfl

end FunctionField

end DeJongAlterations.StableModification.LocalUniformization
