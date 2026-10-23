/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.Mumford
import DeJongAlterations.StableModification.Cohomology.FiniteProjective
import DeJongAlterations.StableModification.Cohomology.ValuationPerfect
import DeJongAlterations.StableModification.Cohomology.CurveCover

/-!
# Cohomology of projective schemes over a valuation ring

Let `V` be a valuation ring (not necessarily Noetherian), `p : X → Spec V` with projective
coordinates over `V` whose coefficient map is the structure map of `p` (for instance `X` projective
over `V`, `nonempty_projectiveCoordinates_of_isProjectiveOver`), and `F` a quasi-coherent module
with finitely generated, `V`-flat sections on the coordinate charts. Then:

* every Čech cohomology module `Ȟᵖ(U, F)` is a finitely presented `V`-module
  (`ProjectiveCoordinates.finitePresentation_cechCohomology_valuation`; cover-free:
  `finitePresentation_cohomology_of_isProjectiveOver_valuation`);
* **the Mumford complex over `V`** (`ProjectiveCoordinates.exists_mumfordComplex_valuation`,
  blueprint `thm:sm-cohomology-valuation`): if `Ȟⁱ(U, F) = 0` for `i > q`, there is a complex `K`
  of finite free `V`-modules in degrees `≤ q` with a universal quasi-isomorphism
  `K → Č(U, F)`, so `Hⁱ(K ⊗_V B) ≅ Ȟⁱ(X_B, F_B)` for every `V → B`. For a curve (`q = 1`; the
  vanishing for `i ≥ 2` holds as soon as `X` is the union of two affine opens or has an affine
  morphism to `ℙ¹`, `CurveCover.lean`) this is a two-term complex `K⁰ → K¹`;
* the consequences used by Temkin, *Stable modification of relative curves*, J. Algebraic Geom.
  19 (2010), Lemma 4.4.2 and Proposition 4.4.6 (`semi-stable.tex` lines 3120–3131, 3212–3219):
  the Euler characteristic of the fibres is constant (`exists_eulerChar_fibre_valuation`), the
  vanishing of `h^{s+1}` on the closed fibre propagates to all fibres
  (`isZero_cech_fibre_of_residue_valuation`; `h¹(F_s) = 0 ⇒ h¹(F_η) = 0`), and then
  `Hˢ(X, F) → Hˢ(X_s, F_s)` is onto (`epi_cechPullbackMap_of_residue_valuation`).

Temkin derives these from the Noetherian results (EGA III 7.6.9, 7.7.5, 7.9.4, Hartshorne
III.12.9) "by noetherian approximation" (`semi-stable.tex` line 3219). We do not approximate.
The finite generation and `V`-flatness of the sections make Serre's graded module of `F` flat
over `V`, hence finitely presented over `V[T]` (Raynaud–Gruson for valuation rings,
`ValuationRing.finitePresentation_of_flat`, lane NAG), and coherence of `V` and `V[T]` gives the
finite presentation of its coordinate Čech cohomology (`ValuationCoherent.lean`); perfect models
then exist over `V` (`ValuationPerfect.lean`). In particular no finite presentation of `X` or `F`
and no flatness of `X` is assumed: finite type plus `V`-flatness of `F` suffice.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open DeJongAlterations.Geometry.ProperSteinProjectiveCech
open DeJongAlterations.StableModification.ValuationRing

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false

section TorsionFree

variable {R P M : Type u} [CommRing R] [CommRing P] [Algebra R P] [AddCommGroup M] [Module P M]
  [Module R M] [IsScalarTower R P M]

/-- Localizing a module at a submonoid of the algebra preserves `v`-torsion-freeness. -/
theorem localizedModule_eq_zero_of_smul_eq_zero (S : Submonoid P) {v : R}
    (hM : ∀ m : M, v • m = 0 → m = 0) (z : LocalizedModule S M) (hz : v • z = 0) : z = 0 := by
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def] at hu
    have h0 : (u : P) • (s : P) • m = 0 := hM _ (by
      rw [smul_comm v (u : P), smul_comm v (s : P)]
      exact hu)
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨u, ?_⟩
    rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def]
    exact h0

end TorsionFree

section Serre

variable {X : Scheme.{u}} {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  {c : V →+* Γ(X, ⊤)}

namespace ProjectiveCoordinates

variable (D : ProjectiveCoordinates X V c) (F : X.Modules) [F.IsQuasicoherent]
  (hF : ∀ i, Module.Finite Γ(X, D.U i) Γ(F, D.U i))
  (hflat : ∀ i, Module.Flat V (sectionsModuleCat F c (D.U i) le_top))

omit [F.IsQuasicoherent] in
include hflat in
/-- The ambient module `∏ Γ(U_i, F)[t]` of twisted sections has no `V`-torsion when the sections
on the charts are `V`-flat. -/
theorem ambient_eq_zero_of_smul_eq_zero {v : V} (hv : v ≠ 0) (e : D.Ambient F) (he : v • e = 0) :
    e = 0 := by
  ext i : 1
  apply PolynomialModule.coeff_injective
  ext n
  have h := congrArg (fun e : D.Ambient F => (e i).coeff n) he
  simp only [Ambient.coeff_smul', PolynomialModule.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply] at h
  have := (flat_iff_forall_smul_eq_zero.mp (hflat i)) v hv
    (show sectionsModuleCat F c (D.U i) le_top from (e i).coeff n) h
  simpa using this

include hflat in
/-- **Serre's module is `V`-flat** when the sections on the charts are `V`-flat. -/
theorem flat_serreModule_valuation : Module.Flat V (D.serreModule F hF) := by
  rw [flat_iff_forall_smul_eq_zero]
  intro v hv m hm
  exact Subtype.ext (D.ambient_eq_zero_of_smul_eq_zero F hflat hv m.val (congrArg Subtype.val hm))

include hflat in
/-- **Serre's module is finitely presented** over `V[T]` (Raynaud–Gruson for valuation rings,
`thm:sm-nagata-fp`: finite and `V`-flat). -/
theorem finitePresentation_serreModule_valuation :
    Module.FinitePresentation (MvPolynomial D.ι V) (D.serreModule F hF) := by
  have := D.finite_serreModule F hF
  have := D.flat_serreModule_valuation F hF hflat
  exact finitePresentation_of_flat V

include hF hflat in
/-- **Finite presentation of Čech cohomology over a valuation ring** (blueprint
`thm:sm-val-cech-fp`): for projective coordinates over a valuation ring and `F` quasi-coherent
with finite, `V`-flat sections on the charts, every `Ȟᵖ(U, F)` is a finitely presented
`V`-module. -/
theorem finitePresentation_cechCohomology_valuation (p : ℕ) :
    Module.FinitePresentation V (cechCohomology F D.U c p) := by
  let _ := D.serreDecomposition F hF
  have := D.finitePresentation_serreModule_valuation F hF hflat
  have h := finitePresentation_homogeneousCoordinateCech_homology (V := V) (I := D.ι)
    (D.serreModule F hF) (D.serrePiece F hF) 0 p
  have : Module.FinitePresentation V ((subsetCechComplex (D.serreDiagram F hF)).homology p) := h
  let e := SubsetNonemptyComparison.complexIso (D.serreDiagram F hF) (cechDiagram F D.U c)
    (D.comparisonIso F hF) (D.comparisonIso_naturality F hF)
  exact Module.FinitePresentation.of_equiv (HomologicalComplex.homologyMapIso e p).toLinearEquiv

include hF hflat in
/-- The sections of `F` on all nonempty intersections `U_T` of the charts are `V`-flat when those
on the charts are. -/
theorem flat_cechDiagram_valuation (T : Finset D.ι) (hT : T.Nonempty) :
    Module.Flat V ((cechDiagram F D.U c).obj T) := by
  suffices h : Module.Flat V ((D.serreDiagram F hF).obj T) from
    flat_of_iso (D.comparisonIso F hF T hT).symm
  rw [flat_iff_forall_smul_eq_zero]
  intro v hv z hz
  apply Subtype.ext
  refine localizedModule_eq_zero_of_smul_eq_zero (R := V) _ (fun m hm => ?_) z.val
    (congrArg Subtype.val hz)
  exact (flat_iff_forall_smul_eq_zero.mp (D.flat_serreModule_valuation F hF hflat)) v hv m hm

end ProjectiveCoordinates

end Serre

section Corollaries

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **Top cohomology commutes with surjective base change over a valuation ring**: for `C` flat,
bounded, with finitely presented cohomology vanishing above `t`, `Hᵗ(C) → Hᵗ(C ⊗_V B)` is
surjective for every surjective `V → B`. -/
theorem epi_homologyMap_toBaseChange_valuation
    (C : CochainComplex (ModuleCat.{u} V) ℕ) (n t : ℕ) (hflat : ∀ k, Module.Flat V (C.X k))
    (hzero : ∀ k, n < k → IsZero (C.X k)) (hH : ∀ k, Module.FinitePresentation V (C.homology k))
    (hvan : ∀ k, t < k → IsZero (C.homology k)) {B : Type u} [CommRing B] (φ : V →+* B)
    (hφ : Function.Surjective φ) :
    Epi (HomologicalComplex.homologyMap (toBaseChange φ C) t) := by
  obtain ⟨K, g, hg, -, -, hzeroK⟩ := exists_perfect_model_le_valuation C n t hflat hzero hH hvan
  have := hg.1
  have := hg.2 B φ
  have hK : Epi (HomologicalComplex.homologyMap (toBaseChange φ K) t) := by
    have : Epi ((toBaseChange φ K).f t) :=
      (ModuleCat.epi_iff_surjective _).mpr (surjective_toBaseChange_f φ hφ K t)
    apply epi_homologyMap_of_top
    · exact (hzeroK (t + 1) (by omega)).eq_of_tgt _ _
    · exact (Functor.map_isZero (ModuleCat.restrictScalars.{u} φ)
        (Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} φ)
          (hzeroK (t + 1) (by omega)))).eq_of_tgt _ _
  have hnat := congrArg (fun f => HomologicalComplex.homologyMap f t) (toBaseChange_naturality φ g)
  simp only [HomologicalComplex.homologyMap_comp] at hnat
  have := isIso_homologyMap_of_quasiIso g t
  have := isIso_homologyMap_of_quasiIso ((restrictComplex φ).map ((baseChange φ).map g)) t
  have e : HomologicalComplex.homologyMap (toBaseChange φ C) t =
      inv (HomologicalComplex.homologyMap g t) ≫
        HomologicalComplex.homologyMap (toBaseChange φ K) t ≫
          HomologicalComplex.homologyMap ((restrictComplex φ).map ((baseChange φ).map g)) t := by
    rw [← hnat, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- **Vanishing from the closed fibre over a valuation ring**: for `C` flat, bounded, with finitely
presented cohomology vanishing above `s + 1`, if `H^{s+1}(C ⊗_V k) = 0` for the residue field
`k`, then `H^{s+1}(C) = 0` and `H^{s+1}(C ⊗_V B) = 0` for every `V → B`. -/
theorem isZero_homology_baseChange_of_residue_valuation
    (C : CochainComplex (ModuleCat.{u} V) ℕ) (n s : ℕ) (hflat : ∀ k, Module.Flat V (C.X k))
    (hzero : ∀ k, n < k → IsZero (C.X k)) (hH : ∀ k, Module.FinitePresentation V (C.homology k))
    (hvan : ∀ k, s + 1 < k → IsZero (C.homology k))
    (hk : IsZero (((baseChange (IsLocalRing.residue V)).obj C).homology (s + 1))) :
    IsZero (C.homology (s + 1)) ∧ ∀ (B : Type u) [CommRing B] (φ : V →+* B),
      IsZero (((baseChange φ).obj C).homology (s + 1)) := by
  obtain ⟨K, g, hg, hfin, -, hzeroK⟩ :=
    exists_perfect_model_le_valuation C n (s + 1) hflat hzero hH hvan
  have hk' : IsZero (((baseChange (IsLocalRing.residue V)).obj K).homology (s + 1)) := by
    have := hg.2 _ (IsLocalRing.residue V)
    exact hk.of_iso (isoOfQuasiIsoAt ((baseChange (IsLocalRing.residue V)).map g) (s + 1))
  have hsurjk : Function.Surjective
      ((ModuleCat.extendScalars.{u, u, u} (IsLocalRing.residue V)).map (K.d s (s + 1))) := by
    intro y
    obtain ⟨x, hx⟩ := (isZero_homology_succ_iff _ s).mp hk' y
      (eq_zero_of_isZero (Functor.map_isZero (ModuleCat.extendScalars.{u, u, u}
        (IsLocalRing.residue V)) (hzeroK (s + 2) (by omega))) _)
    exact ⟨x, hx⟩
  have := hfin (s + 1)
  have hsurj : Function.Surjective (K.d s (s + 1)) :=
    surjective_of_extendScalars_residue _ hsurjk
  refine ⟨?_, fun B _ φ => ?_⟩
  · have := hg.1
    have hK0 : IsZero (K.homology (s + 1)) := by
      rw [isZero_homology_succ_iff]
      intro y _
      exact hsurj y
    exact hK0.of_iso (isoOfQuasiIsoAt g _).symm
  · have := hg.2 B φ
    have hKB : IsZero (((baseChange φ).obj K).homology (s + 1)) := by
      rw [isZero_homology_succ_iff]
      intro y _
      have h : Function.Surjective
          ((ModuleCat.extendScalars.{u, u, u} φ).map (K.d s (s + 1))) := by
        rw [extendScalars_map_eq_lTensor]
        exact LinearMap.lTensor_surjective _ hsurj
      exact h y
    exact hKB.of_iso (isoOfQuasiIsoAt ((baseChange φ).map g) (s + 1)).symm

/-- **Cohomology and base change, onto form, over a valuation ring**: under the hypotheses of
`isZero_homology_baseChange_of_residue_valuation`, `Hˢ(C) → Hˢ(C ⊗_V B)` is surjective for every
surjective `V → B`. -/
theorem epi_homologyMap_toBaseChange_of_residue_valuation
    (C : CochainComplex (ModuleCat.{u} V) ℕ) (n s : ℕ) (hflat : ∀ k, Module.Flat V (C.X k))
    (hzero : ∀ k, n < k → IsZero (C.X k)) (hH : ∀ k, Module.FinitePresentation V (C.homology k))
    (hvan : ∀ k, s + 1 < k → IsZero (C.homology k))
    (hk : IsZero (((baseChange (IsLocalRing.residue V)).obj C).homology (s + 1)))
    {B : Type u} [CommRing B] (φ : V →+* B) (hφ : Function.Surjective φ) :
    Epi (HomologicalComplex.homologyMap (toBaseChange φ C) s) := by
  refine epi_homologyMap_toBaseChange_valuation C n s hflat hzero hH (fun k hk' => ?_) φ hφ
  by_cases h : k = s + 1
  · subst h
    exact (isZero_homology_baseChange_of_residue_valuation C n s hflat hzero hH hvan hk).1
  · exact hvan k (by omega)

/-- **Constancy of the Euler characteristic over a valuation ring**: for `C` flat, bounded, with
finitely presented cohomology vanishing above `q`, `∑_{i ≤ q} (-1)^i dim_κ Hⁱ(C ⊗_V κ)` is the
same for all fields `κ` over `V`. -/
theorem exists_eulerChar_baseChange_valuation
    (C : CochainComplex (ModuleCat.{u} V) ℕ) (n q : ℕ) (hflat : ∀ k, Module.Flat V (C.X k))
    (hzero : ∀ k, n < k → IsZero (C.X k)) (hH : ∀ k, Module.FinitePresentation V (C.homology k))
    (hvan : ∀ k, q < k → IsZero (C.homology k)) :
    ∃ χ : ℤ, ∀ (κ : Type u) [Field κ] (φ : V →+* κ),
      ∑ i ∈ Finset.range (q + 1),
        (-1 : ℤ) ^ i * (Module.finrank κ (((baseChange φ).obj C).homology i) : ℤ) = χ := by
  obtain ⟨K, g, hg, hfin, hfree, hzeroK⟩ :=
    exists_perfect_model_le_valuation C n q hflat hzero hH hvan
  refine ⟨∑ i ∈ Finset.range (q + 1), (-1 : ℤ) ^ i * (Module.finrank V (K.X i) : ℤ),
    fun κ _ φ => ?_⟩
  have := hg.2 κ φ
  let _ := φ.toAlgebra
  have hfd : ∀ i, FiniteDimensional κ (((baseChange φ).obj K).X i) := fun i => by
    have := hfin i
    exact Module.Finite.base_change V κ (K.X i)
  have hz : IsZero (((baseChange φ).obj K).X (q + 1)) :=
    Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} φ) (hzeroK (q + 1) (by omega))
  have e := sum_finrank_homology_eq ((baseChange φ).obj K) q hz
  have hH' : ∀ i, Module.finrank κ (((baseChange φ).obj C).homology i) =
      Module.finrank κ (((baseChange φ).obj K).homology i) := fun i =>
    (LinearEquiv.finrank_eq (isoOfQuasiIsoAt ((baseChange φ).map g) i).toLinearEquiv).symm
  have hX : ∀ i, Module.finrank κ (((baseChange φ).obj K).X i) = Module.finrank V (K.X i) :=
    fun i => by
      have := hfin i
      have := hfree i
      exact Module.finrank_baseChange
  simp only [hH']
  rw [e]
  simp only [hX]

end Corollaries

section MumfordValuation

variable {X : Scheme.{u}} {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  {p : X ⟶ Spec (CommRingCat.of V)}

namespace ProjectiveCoordinates

variable (D : ProjectiveCoordinates X V (structureCoeff p)) (F : X.Modules) [F.IsQuasicoherent]
  (hF : ∀ i, Module.Finite Γ(X, D.U i) Γ(F, D.U i))
  (hflat : ∀ i, Module.Flat V (sectionsModuleCat F (structureCoeff p) (D.U i) le_top))

include hF hflat in
/-- **The Mumford complex over a valuation ring** (blueprint `thm:sm-cohomology-valuation`): for
projective coordinates over a valuation ring `V` (coefficients the structure map of
`p : X → Spec V`) and `F` quasi-coherent with finite, `V`-flat sections on the charts, if
`Ȟⁱ(U, F) = 0` for `i > q`, there is a complex `K` of finite free `V`-modules concentrated in
degrees `≤ q` with a universal quasi-isomorphism `K → Č(U, F)`; consequently
`Hⁱ(K ⊗_V B) ≅ Ȟⁱ(q⁻¹U, q^*F)` on `X_B = X ×_V Spec B` for every `V → B`. For curves (`q = 1`)
`K` is a two-term complex `K⁰ → K¹` of finite free `V`-modules. -/
theorem exists_mumfordComplex_valuation (q : ℕ)
    (hvan : ∀ k, q < k → IsZero (cechCohomology F D.U (structureCoeff p) k)) :
    ∃ (K : CochainComplex (ModuleCat.{u} V) ℕ) (g : K ⟶ cechComplex F D.U (structureCoeff p)),
      IsUnivQuasiIso g ∧ (∀ k, Module.Finite V (K.X k)) ∧ (∀ k, Module.Free V (K.X k)) ∧
      (∀ k, q < k → IsZero (K.X k)) ∧
      ∀ (B : Type u) [CommRing B] (φ : V →+* B) (i : ℕ),
        Nonempty (((baseChange φ).obj K).homology i ≅
          cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj F)
            (fun j => bcFst φ p ⁻¹ᵁ D.U j) (structureCoeff (bcSnd φ p)) i) := by
  obtain ⟨K, g, hg, hfin, hfree, hzero⟩ := exists_perfect_model_le_valuation
    (cechComplex F D.U (structureCoeff p)) (Fintype.card D.ι - 1) q
    (D.flat_cechComplex_X F (D.flat_cechDiagram_valuation F hF hflat)) (D.isZero_cechComplex_X F)
    (fun k => D.finitePresentation_cechCohomology_valuation F hF hflat k) hvan
  refine ⟨K, g, hg, hfin, hfree, hzero, fun B _ φ i => ?_⟩
  have := hg.2 B φ
  exact ⟨isoOfQuasiIsoAt ((baseChange φ).map g) i ≪≫
    HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F φ) i⟩

include hF hflat in
/-- **Constancy of the Euler characteristic of the fibres** over a valuation ring (blueprint
`cor:sm-val-euler`): if `Ȟⁱ(U, F) = 0` for `i > q`, then `∑_{i ≤ q} (-1)^i dim_κ Ȟⁱ(X_κ, F_κ)`
is the same for all fields `κ` over `V`; in particular `χ(F_η) = χ(F_s)` for the generic and the
closed point. -/
theorem exists_eulerChar_fibre_valuation (q : ℕ)
    (hvan : ∀ k, q < k → IsZero (cechCohomology F D.U (structureCoeff p) k)) :
    ∃ χ : ℤ, ∀ (κ : Type u) [Field κ] (φ : V →+* κ),
      ∑ i ∈ Finset.range (q + 1), (-1 : ℤ) ^ i *
        (Module.finrank κ (cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj F)
          (fun j => bcFst φ p ⁻¹ᵁ D.U j) (structureCoeff (bcSnd φ p)) i) : ℤ) = χ := by
  obtain ⟨χ, hχ⟩ := exists_eulerChar_baseChange_valuation (cechComplex F D.U (structureCoeff p))
    (Fintype.card D.ι - 1) q
    (D.flat_cechComplex_X F (D.flat_cechDiagram_valuation F hF hflat)) (D.isZero_cechComplex_X F)
    (fun k => D.finitePresentation_cechCohomology_valuation F hF hflat k) hvan
  refine ⟨χ, fun κ _ φ => ?_⟩
  rw [← hχ κ φ]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact (LinearEquiv.finrank_eq
    (HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F φ) i).toLinearEquiv).symm

include hF hflat in
/-- **Vanishing from the closed fibre** over a valuation ring (blueprint `cor:sm-val-semicont`):
if `Ȟⁱ(U, F) = 0` for `i > s + 1` and `Ȟ^{s+1}(X_k, F_k) = 0` on the closed fibre, then
`Ȟ^{s+1}(U, F) = 0` and `Ȟ^{s+1}(X_B, F_B) = 0` for every `V → B`. For curves (`s = 0`):
`h¹(F_s) = 0` implies `h¹(F) = 0` and `h¹(F_η) = 0`. -/
theorem isZero_cech_fibre_of_residue_valuation (s : ℕ)
    (hvan : ∀ k, s + 1 < k → IsZero (cechCohomology F D.U (structureCoeff p) k))
    (hk : IsZero (cechCohomology ((Scheme.Modules.pullback (bcFst (IsLocalRing.residue V) p)).obj F)
      (fun j => bcFst (IsLocalRing.residue V) p ⁻¹ᵁ D.U j)
      (structureCoeff (bcSnd (IsLocalRing.residue V) p)) (s + 1))) :
    IsZero (cechCohomology F D.U (structureCoeff p) (s + 1)) ∧
      ∀ (B : Type u) [CommRing B] (φ : V →+* B),
        IsZero (cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj F)
          (fun j => bcFst φ p ⁻¹ᵁ D.U j) (structureCoeff (bcSnd φ p)) (s + 1)) := by
  have h := isZero_homology_baseChange_of_residue_valuation
    (cechComplex F D.U (structureCoeff p)) (Fintype.card D.ι - 1) s
    (D.flat_cechComplex_X F (D.flat_cechDiagram_valuation F hF hflat)) (D.isZero_cechComplex_X F)
    (fun k => D.finitePresentation_cechCohomology_valuation F hF hflat k) hvan
    (hk.of_iso (HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F _) (s + 1)))
  exact ⟨h.1, fun B _ φ =>
    (h.2 B φ).of_iso (HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F φ) (s + 1)).symm⟩

include hF hflat in
/-- **Cohomology and base change, onto form**, over a valuation ring (blueprint
`cor:sm-val-onto`): under the hypotheses of `isZero_cech_fibre_of_residue_valuation`, the
pullback map `Ȟˢ(U, F) → Ȟˢ(X_B, F_B)` is surjective for every surjective `V → B`. For curves
(`s = 0`, `B = k`): `h¹(F_s) = 0` implies that `H⁰(X, F) → H⁰(X_s, F_s)` is onto. -/
theorem epi_cechPullbackMap_of_residue_valuation (s : ℕ)
    (hvan : ∀ k, s + 1 < k → IsZero (cechCohomology F D.U (structureCoeff p) k))
    (hk : IsZero (cechCohomology ((Scheme.Modules.pullback (bcFst (IsLocalRing.residue V) p)).obj F)
      (fun j => bcFst (IsLocalRing.residue V) p ⁻¹ᵁ D.U j)
      (structureCoeff (bcSnd (IsLocalRing.residue V) p)) (s + 1)))
    {B : Type u} [CommRing B] (φ : V →+* B) (hφ : Function.Surjective φ) :
    Epi (HomologicalComplex.homologyMap (D.cechPullbackMap F φ) s) := by
  have h := epi_homologyMap_toBaseChange_of_residue_valuation
    (cechComplex F D.U (structureCoeff p)) (Fintype.card D.ι - 1) s
    (D.flat_cechComplex_X F (D.flat_cechDiagram_valuation F hF hflat)) (D.isZero_cechComplex_X F)
    (fun k => D.finitePresentation_cechCohomology_valuation F hF hflat k) hvan
    (hk.of_iso (HomologicalComplex.homologyMapIso (D.cechBaseChangeIso F _) (s + 1))) φ hφ
  have : IsIso ((restrictComplex φ).map (D.cechBaseChangeIso F φ).hom) := inferInstance
  rw [cechPullbackMap, HomologicalComplex.homologyMap_comp]
  infer_instance

include hF hflat in
/-- **Vanishing is detected on the closed fibre** (blueprint `cor:sm-val-vanishing-fibre`): if
`Ȟⁱ(X_k, F_k) = 0` for all `i > q` on the closed fibre, then `Ȟⁱ(U, F) = 0` for all `i > q`.
Together with `exists_mumfordComplex_valuation` this reduces the vanishing in degrees `≥ 2` needed
for curves to curves over the residue field (e.g. `isZero_cechCohomology_of_two_affine` on
`X_k`). -/
theorem isZero_cech_of_residue_valuation (q : ℕ)
    (hk : ∀ i, q < i →
      IsZero (cechCohomology ((Scheme.Modules.pullback (bcFst (IsLocalRing.residue V) p)).obj F)
        (fun j => bcFst (IsLocalRing.residue V) p ⁻¹ᵁ D.U j)
        (structureCoeff (bcSnd (IsLocalRing.residue V) p)) i)) :
    ∀ i, q < i → IsZero (cechCohomology F D.U (structureCoeff p) i) := by
  have key : ∀ t i, Fintype.card D.ι ≤ i + t → q < i →
      IsZero (cechCohomology F D.U (structureCoeff p) i) := by
    intro t
    induction t with
    | zero =>
      intro i hi _
      exact isZero_cechCohomology_of_card_le F D.U _ i (by omega)
    | succ t ih =>
      intro i hi hqi
      obtain ⟨s, rfl⟩ : ∃ s, i = s + 1 := ⟨i - 1, by omega⟩
      exact (D.isZero_cech_fibre_of_residue_valuation F hF hflat s
        (fun k hk' => ih k (by omega) (by omega)) (hk (s + 1) hqi)).1
  exact fun i hi => key (Fintype.card D.ι) i (by omega) hi

include hF hflat in
/-- **The Mumford complex from the closed fibre**: if `Ȟⁱ(X_k, F_k) = 0` for `i > q` on the
closed fibre (for a curve: `q = 1`), there is a complex of finite free `V`-modules in degrees
`≤ q` (for a curve: a two-term complex `K⁰ → K¹`) computing `Ȟⁱ(X_B, F_B)` for every `V → B`. -/
theorem exists_mumfordComplex_valuation_of_residue (q : ℕ)
    (hk : ∀ i, q < i →
      IsZero (cechCohomology ((Scheme.Modules.pullback (bcFst (IsLocalRing.residue V) p)).obj F)
        (fun j => bcFst (IsLocalRing.residue V) p ⁻¹ᵁ D.U j)
        (structureCoeff (bcSnd (IsLocalRing.residue V) p)) i)) :
    ∃ (K : CochainComplex (ModuleCat.{u} V) ℕ) (g : K ⟶ cechComplex F D.U (structureCoeff p)),
      IsUnivQuasiIso g ∧ (∀ k, Module.Finite V (K.X k)) ∧ (∀ k, Module.Free V (K.X k)) ∧
      (∀ k, q < k → IsZero (K.X k)) ∧
      ∀ (B : Type u) [CommRing B] (φ : V →+* B) (i : ℕ),
        Nonempty (((baseChange φ).obj K).homology i ≅
          cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj F)
            (fun j => bcFst φ p ⁻¹ᵁ D.U j) (structureCoeff (bcSnd φ p)) i) :=
  D.exists_mumfordComplex_valuation F hF hflat q (D.isZero_cech_of_residue_valuation F hF hflat q hk)

attribute [local instance] MvPolynomial.gradedAlgebra in
include hF hflat in
/-- **The two-term Mumford complex of a projective curve over a valuation ring** (blueprint
`cor:sm-val-curve`): if `X` (with affine diagonal, universally closed over `V`) is a closed
subscheme of `ℙⁿ_V` and two homogeneous forms of positive degree have no common zero on the
closed fibre, then there is a two-term complex `K⁰ → K¹` of finite free `V`-modules with a
universal quasi-isomorphism to `Č(U, F)`, computing `Ȟⁱ(X_B, F_B)` for every `V → B`. -/
theorem exists_twoTerm_mumfordComplex_of_hypersurfaces
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] [UniversallyClosed p]
    {n : ℕ} (i : X ⟶ projectiveSpace V n) [IsClosedImmersion i]
    (f g : MvPolynomial (Fin (n + 1)) V) {d e : ℕ} (hf : f ∈ projectiveSpaceGrading V n d)
    (hd : 0 < d) (hg : g ∈ projectiveSpaceGrading V n e) (he : 0 < e)
    (hcov : ∀ x : X, p x = IsLocalRing.closedPoint V →
      x ∈ i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading V n) f ⊔
        i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading V n) g) :
    ∃ (K : CochainComplex (ModuleCat.{u} V) ℕ) (γ : K ⟶ cechComplex F D.U (structureCoeff p)),
      IsUnivQuasiIso γ ∧ (∀ k, Module.Finite V (K.X k)) ∧ (∀ k, Module.Free V (K.X k)) ∧
      (∀ k, 1 < k → IsZero (K.X k)) ∧
      ∀ (B : Type u) [CommRing B] (φ : V →+* B) (j : ℕ),
        Nonempty (((baseChange φ).obj K).homology j ≅
          cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj F)
            (fun l => bcFst φ p ⁻¹ᵁ D.U l) (structureCoeff (bcSnd φ p)) j) :=
  D.exists_mumfordComplex_valuation F hF hflat 1 fun k hk =>
    isZero_cechCohomology_of_hypersurfaces_closedFibre F (structureCoeff p) i p D.U D.iSup_eq_top
      D.isAffineOpen f g hf hd hg he hcov k hk

end ProjectiveCoordinates

end MumfordValuation

section CoverFree

variable {X : Scheme.{u}} {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **Finite presentation of the cohomology of projective schemes over a valuation ring**
(cover-free form of `ProjectiveCoordinates.finitePresentation_cechCohomology_valuation`): for
`p : X → Spec V` projective and `F` quasi-coherent with finite, `V`-flat sections on affine opens,
every `H^q(X, F)` is a finitely presented `V`-module. -/
theorem finitePresentation_cohomology_of_isProjectiveOver_valuation
    {p : X ⟶ Spec (CommRingCat.of V)} (hp : IsProjectiveOver p) [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (F : X.Modules) [F.IsQuasicoherent]
    (hF : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U))
    (hflat : ∀ U : X.Opens, IsAffineOpen U →
      Module.Flat V (sectionsModuleCat F (structureCoeff p) U le_top)) (q : ℕ) :
    Module.FinitePresentation V (cohomology F (structureCoeff p) q) := by
  obtain ⟨D⟩ := nonempty_projectiveCoordinates_of_isProjectiveOver hp
  have h : Module.FinitePresentation V
      (cechCohomology F D.toFiniteAffineCover.U (structureCoeff p) q) :=
    D.finitePresentation_cechCohomology_valuation F (fun j => hF _ (D.isAffineOpen j))
      (fun j => hflat _ (D.isAffineOpen j)) q
  exact Module.FinitePresentation.of_equiv
    (cohomologyIsoCech F (structureCoeff p) D.toFiniteAffineCover q).toLinearEquiv.symm

end CoverFree

end

end DeJongAlterations.StableModification.Cohomology
