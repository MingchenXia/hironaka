/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3B)
-/
import DeJongAlterations.StableModification.CurvesField.AmpleAffine
import DeJongAlterations.StableModification.Cohomology.FiniteProjective
import DeJongAlterations.StableModification.CurvesField.CohomologyP1

/-!
# A second section without common zero

Let `X` be projective over an infinite field `K` and `s` a global section of `𝓛^n` which does not
vanish at the non-closed points of `X`, so that its zero set `Z(s)` is a finite set of closed
points. Then some `𝓛^{n(m+1)}` has a global section `t` without zero on `Z(s)`
(`exists_section_sup_eq_top`): `s^{m+1}` and `t` have no common zero. Blueprint
`sm-curves-fields-ample.tex`, `lem:sm-ample-second-section`.

## The argument

Two linear forms (`Cohomology.exists_linearForm_mem_basicOpen`, `K` infinite) give an affine open
`V₁ = X ∩ D₊(ℓ₁)` containing `Z(s)` and the non-closed points, and an affine open `W₀ = X ∩ D₊(ℓ₀)`
containing the finitely many points outside `V₁` and the non-closed points. Then `U = W₀ ∩ D(s)` is
affine (`isAffineOpen_nonvanishingLocus_of_isAffineOpen`) and its complement is a finite set `S` of
closed points inside `V₁`. A section `σ` of `𝓛^n` over `V₁` without zero on `S` exists
(`exists_section_nonvanishing`: local generators made global by quasi-coherence, combined with
functions separating the points of `S`), and `V = D(σ)` is affine. On the cover `X = U ∪ V`,
`𝓛^{nk}` is the divisor twist `𝒪(kD)` by `f = s/σ` (`LineBundleData.twoChartIso`), and
`D = V(f) = Z(s)`. The first cohomology of the two-term complexes of `𝒪(kD)` is finite-dimensional
(`X` projective) and its dimension does not increase with `k`; once it is constant, the connecting
map `Γ(V, 𝒪) ⧸ f → H¹(𝒪(kD))` vanishes, so the class of `1` is the `V`-component of a global
section of `𝒪((k+1)D)` (`exists_forall_surjective_family_of_H1`, lane COH4's argument without the
non-zero-divisor hypothesis). Its `V`-component is `1` modulo `f`, a unit at the points of
`Z(s) = V(f)`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField.Ample

noncomputable section

/-! ### Global generation along the divisor over a field -/

section Algebra

variable {K : Type*} [Field K] {MU : Type*} {MV : Type*} {MW : Type*}
  [AddCommGroup MU] [Module K MU] [AddCommGroup MV] [Module K MV] [AddCommGroup MW]
  [Module K MW] (ρU : MU →ₗ[K] MW) (ρV : MV →ₗ[K] MW) (σ : MW ≃ₗ[K] MW) (φ : MV →ₗ[K] MV)
  (hφ : ρV ∘ₗ φ = σ.toLinearMap ∘ₗ ρV)
  (γ : ℤ → MW →ₗ[K] MW) (hγ : ∀ m, γ (m + 1) = σ.toLinearMap ∘ₗ γ m)

include hφ hγ in
lemma finiteDimensional_H1_nat [FiniteDimensional K (H1 ρU ρV (γ 0))] (m : ℕ) :
    FiniteDimensional K (H1 ρU ρV (γ m)) := by
  induction m with
  | zero => simpa using (inferInstance : FiniteDimensional K (H1 ρU ρV (γ 0)))
  | succ n ih =>
    rw [Nat.cast_succ, hγ]
    exact finiteDimensional_H1_step ρU ρV σ φ hφ (γ n)

include hφ hγ in
/-- **Global generation along `D` over a field, without a non-zero-divisor hypothesis**: if
`H¹(F)` is finite-dimensional, then for `m ≫ 0` every class of `MV ⧸ f MV` is the `V`-component
of a global section of `F((m+1)D)` (the dimension of `H¹(F(mD))` decreases and becomes constant;
then `H¹(F(mD)) → H¹(F((m+1)D))` is bijective, so the connecting map vanishes). -/
theorem exists_forall_surjective_family_of_H1 [FiniteDimensional K (H1 ρU ρV (γ 0))] :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ x : MV ⧸ LinearMap.range φ,
      ∃ p ∈ H0 ρU ρV (γ (m + 1)), (LinearMap.range φ).mkQ p.2 = x := by
  classical
  have hfd := finiteDimensional_H1_nat ρU ρV σ φ hφ γ hγ
  let c : ℕ → ℕ := fun m => Module.finrank K (H1 ρU ρV (γ m))
  have hc : Antitone c := antitone_nat_of_succ_le fun m => by
    have := hfd m
    have h := finrank_H1_step_le ρU ρV σ φ hφ (γ m)
    simp only [c]
    rw [Nat.cast_succ, hγ]
    exact h
  have hex : ∃ n, ∃ m, c m = n := ⟨c 0, 0, rfl⟩
  obtain ⟨m₀, hm₀⟩ := Nat.find_spec hex
  have hmin : ∀ m, Nat.find hex ≤ c m := fun m => Nat.find_min' hex ⟨m, rfl⟩
  refine ⟨m₀, fun m hm x => ?_⟩
  have hconst : c (m + 1) = c m := by
    have h1 : c (m + 1) ≤ c m₀ := hc (by omega)
    have h2 : c m ≤ c m₀ := hc hm
    have h3 := hmin (m + 1)
    have h4 := hmin m
    omega
  have := hfd m
  have : FiniteDimensional K (H1 ρU ρV (σ.toLinearMap ∘ₗ γ m)) :=
    finiteDimensional_H1_step ρU ρV σ φ hφ (γ m)
  have hrank : Module.finrank K (H1 ρU ρV (γ m)) =
      Module.finrank K (H1 ρU ρV (σ.toLinearMap ∘ₗ γ m)) := by
    have e : c (m + 1) = Module.finrank K (H1 ρU ρV (σ.toLinearMap ∘ₗ γ m)) := by
      simp only [c]
      rw [Nat.cast_succ, hγ]
    rw [← e, hconst]
  have hinj : Function.Injective (stepH1 ρU ρV σ φ hφ (γ m)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr
      (stepH1_surjective ρU ρV σ φ hφ (γ m))
  have hδ : stepδ ρU ρV σ φ hφ (γ m) x = 0 := by
    apply hinj
    rw [map_zero]
    exact (exact_stepδ_stepH1 ρU ρV σ φ hφ (γ m) _).mpr ⟨x, rfl⟩
  obtain ⟨p, hp⟩ := (exact_stepQ_stepδ ρU ρV σ φ hφ (γ m) x).mp hδ
  refine ⟨p.val, ?_, hp⟩
  rw [hγ]
  exact p.property

end Algebra

variable {X : Scheme.{u}}

/-! ### Non-vanishing loci over affine opens -/

open LineBundleData in
/-- **The non-vanishing locus of a section of a line bundle over an affine open is affine.** -/
theorem isAffineOpen_nonvanishingLocus_of_isAffineOpen {L : Projectivity.LineBundleData X}
    {m : ℤ} {W : X.Opens} (hW : IsAffineOpen W) (σ : L.Sections m W) :
    IsAffineOpen σ.nonvanishingLocus := by
  set V := σ.nonvanishingLocus
  have hVW : V ≤ W := σ.nonvanishingLocus_le
  let t : Set Γ(X, W) := {g | ∃ i, X.basicOpen g ≤ L.U i}
  have ht : Ideal.span t = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    obtain ⟨g, hgle, hxg⟩ := hW.exists_basicOpen_le ⟨x, hi⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨g, i, hgle⟩, hxg⟩
  let r : Γ(X, W) →+* Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom
  apply isAffineOpen_of_isAffineOpen_basicOpen V (r '' t)
  · rw [← Ideal.map_span, ht, Ideal.map_top]
  · rintro _ ⟨g, ⟨i, hgi⟩, rfl⟩
    have hgW : X.basicOpen g ≤ W ⊓ L.U i := le_inf (X.basicOpen_le g) hgi
    have e : X.basicOpen (r g) =
        X.basicOpen (X.presheaf.map (homOfLE hgW).op (σ.coeff i)) := by
      change X.basicOpen (X.presheaf.map (homOfLE hVW).op g) = _
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res, ← σ.nonvanishingLocus_inf i]
      apply le_antisymm
      · rintro x ⟨hxV, hxg⟩
        exact ⟨hxg, hxV, hgi hxg⟩
      · rintro x ⟨hxg, hxV, -⟩
        exact ⟨hxV, hxg⟩
    rw [e]
    exact (hW.basicOpen g).basicOpen _

/-! ### Sections without zero on a finite set of closed points -/

lemma isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : b ∈ IsLocalRing.maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have h' : a + b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have : a ∈ IsLocalRing.maximalIdeal R := by
    have := (IsLocalRing.maximalIdeal R).sub_mem h' hb
    rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp this ha

lemma isUnit_sum_of_eq {R : Type*} [CommRing R] [IsLocalRing R] {ι : Type*} (s : Finset ι)
    (f : ι → R) {i : ι} (hi : i ∈ s) (hfi : IsUnit (f i))
    (hf : ∀ j ∈ s, j ≠ i → f j ∈ IsLocalRing.maximalIdeal R) : IsUnit (∑ j ∈ s, f j) := by
  classical
  rw [← Finset.add_sum_erase s f hi]
  exact isUnit_add_of_mem_maximalIdeal hfi
    (Ideal.sum_mem _ fun j hj => hf j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj))

lemma mem_basicOpen_prod {U : X.Opens} {ι : Type*} (s : Finset ι) (f : ι → Γ(X, U)) {x : X}
    (hx : x ∈ U) (h : ∀ i ∈ s, x ∈ X.basicOpen (f i)) : x ∈ X.basicOpen (∏ i ∈ s, f i) := by
  rw [X.mem_basicOpen _ x hx, map_prod]
  exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
    (fun i hi => (X.mem_basicOpen _ x hx).mp (h i hi))

lemma not_mem_basicOpen_prod {U : X.Opens} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Γ(X, U)) {x : X} {j : ι} (hj : j ∈ s) (h : x ∉ X.basicOpen (f j)) :
    x ∉ X.basicOpen (∏ i ∈ s, f i) := by
  rw [← Finset.mul_prod_erase s f hj, X.basicOpen_mul]
  exact fun hx => h hx.1

lemma germ_mem_maximalIdeal {U : X.Opens} (f : Γ(X, U)) {x : X} (hx : x ∈ U)
    (h : x ∉ X.basicOpen f) :
    X.presheaf.germ U x hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  (IsLocalRing.mem_maximalIdeal _).mpr fun hu => h ((X.mem_basicOpen f x hx).mpr hu)

lemma Sections.coeff_sum {L : Projectivity.LineBundleData X} {m : ℤ} {W : X.Opens} {ι : Type*}
    (s : Finset ι) (a : ι → L.Sections m W) (i : L.ι) :
    (∑ j ∈ s, a j).coeff i = ∑ j ∈ s, (a j).coeff i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      Projectivity.LineBundleData.Sections.coeff_add, ih]

open LineBundleData in
/-- **A section without zero at finitely many closed points** of an affine open: for an affine
open `W` and a finite set `S ⊆ W` of closed points there is a section `σ` of `𝓛^m` over `W` with
`S ⊆ D(σ)` (semilocal triviality of line bundles). -/
theorem exists_section_nonvanishing (L : Projectivity.LineBundleData X) (m : ℤ) {W : X.Opens}
    (hW : IsAffineOpen W) {S : Set X} (hS : S.Finite) (hSW : S ⊆ W)
    (hcl : ∀ z ∈ S, IsClosed ({z} : Set X)) :
    ∃ σ : L.Sections m W, ∀ z ∈ S, z ∈ σ.nonvanishingLocus := by
  classical
  -- local generators made global
  have hloc : ∀ z ∈ S, ∃ τ : L.Sections m W, z ∈ τ.nonvanishingLocus := by
    intro z hz
    obtain ⟨i, hi⟩ := L.exists_mem_U z
    obtain ⟨g, hgle, hzg⟩ := hW.exists_basicOpen_le ⟨z, hi⟩ (hSW hz)
    let e : L.Sections m (X.basicOpen g) :=
      ofLocal (unitModule X) m hgle (1 : Γ(X, X.basicOpen g))
    have he : e.nonvanishingLocus = X.basicOpen g := by
      apply le_antisymm (Sections.nonvanishingLocus_le _)
      intro x hx
      rw [Sections.mem_nonvanishingLocus_iff _ (hgle hx)]
      have hc : e.coeff i = ((L.trans (le_inter_of_le hgle i) ^ m : Γ(X, X.basicOpen g ⊓ L.U i)ˣ) :
          Γ(X, X.basicOpen g ⊓ L.U i)) *
            X.presheaf.map (homOfLE (inf_le_left : X.basicOpen g ⊓ L.U i ≤ X.basicOpen g)).op 1 :=
        rfl
      rw [hc, map_one, mul_one, X.basicOpen_of_isUnit (Units.isUnit _)]
      exact ⟨hx, hgle hx⟩
    let M := L.twist (unitModule X) m
    let _ : Module Γ(X, W) Γ(M, X.basicOpen g) :=
      Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
    have hloc := isLocalizedModule_restrictLinearNative M hW g
    obtain ⟨⟨τ₀, ⟨_, k, rfl⟩⟩, hτ⟩ := hloc.surj (show Γ(M, X.basicOpen g) from e)
    let τ : L.Sections m W := τ₀
    change X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ k) • e =
      Sections.restrict (X.basicOpen_le g) τ at hτ
    refine ⟨τ, ?_⟩
    have hz : z ∈
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ k) • e).nonvanishingLocus := by
      rw [Sections.nonvanishingLocus_smul, he, Scheme.basicOpen_res]
      refine ⟨⟨hzg, ?_⟩, hzg⟩
      exact (X.mem_basicOpen (g ^ k) z (hSW hz)).mpr (by
        rw [map_pow]
        exact ((X.mem_basicOpen g z (hSW hz)).mp hzg).pow k)
    rw [hτ, Sections.nonvanishingLocus_restrict] at hz
    exact hz.2
  choose! τ hτ using hloc
  -- functions separating the points of `S`
  have hsep : ∀ z ∈ S, ∀ z' ∈ S, z' ≠ z →
      ∃ h : Γ(X, W), z ∈ X.basicOpen h ∧ z' ∉ X.basicOpen h := by
    intro z hz z' hz' hne
    let O : X.Opens := ⟨({z'} : Set X)ᶜ, (hcl z' hz').isOpen_compl⟩
    obtain ⟨h, hle, hzh⟩ := hW.exists_basicOpen_le (V := O) ⟨z, fun h => hne h.symm⟩ (hSW hz)
    exact ⟨h, hzh, fun hz'h => hle hz'h rfl⟩
  choose! hs hhs using hsep
  let F := hS.toFinset
  let hp : X → Γ(X, W) := fun z => ∏ z' ∈ F.erase z, hs z z'
  refine ⟨∑ z ∈ F, hp z • τ z, fun z hzS => ?_⟩
  have hzF : z ∈ F := hS.mem_toFinset.mpr hzS
  obtain ⟨i, hi⟩ := L.exists_mem_U z
  have hzWi : z ∈ W ⊓ L.U i := ⟨hSW hzS, hi⟩
  rw [Sections.mem_nonvanishingLocus_iff _ hi, Sections.coeff_sum, X.mem_basicOpen _ z hzWi,
    map_sum]
  apply isUnit_sum_of_eq F _ hzF
  · rw [← X.mem_basicOpen _ z hzWi, Sections.coeff_smul, X.basicOpen_mul, Scheme.basicOpen_res]
    refine ⟨⟨hzWi, ?_⟩, ?_⟩
    · exact mem_basicOpen_prod _ _ (hSW hzS) fun z' hz' =>
        (hhs z hzS z' (hS.mem_toFinset.mp (Finset.mem_of_mem_erase hz'))
          (Finset.ne_of_mem_erase hz')).1
    · exact (Sections.mem_nonvanishingLocus_iff _ hi).mp (hτ z hzS)
  · intro z'' hz'' hne
    apply germ_mem_maximalIdeal
    rw [Sections.coeff_smul, X.basicOpen_mul, Scheme.basicOpen_res]
    rintro ⟨⟨-, hzp⟩, -⟩
    have hz''S : z'' ∈ S := hS.mem_toFinset.mp hz''
    exact not_mem_basicOpen_prod (F.erase z'') (hs z'') (Finset.mem_erase.mpr ⟨Ne.symm hne, hzF⟩)
      (hhs z'' hz''S z hzS (Ne.symm hne)).2 hzp

/-! ### The second section -/

lemma infinite_residueField (K : Type*) [Field K] [Infinite K] :
    Infinite (IsLocalRing.ResidueField K) :=
  Infinite.of_injective (IsLocalRing.residue K) (IsLocalRing.residue K).injective

/-- A scheme separated over an affine scheme has affine diagonal. -/
lemma isAffineHom_diagonal_of_isSeparated {A : Type u} [CommRing A]
    (q : X ⟶ Spec (CommRingCat.of A)) [IsSeparated q] :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  have e : q ≫ terminal.from _ = terminal.from X := terminal.hom_ext _ _
  have : IsSeparated (terminal.from X) := by rw [← e]; infer_instance
  infer_instance

/-- A scheme quasi-compact over an affine scheme is quasi-compact. -/
lemma compactSpace_of_quasiCompact {A : Type u} [CommRing A] (q : X ⟶ Spec (CommRingCat.of A))
    [QuasiCompact q] : CompactSpace X :=
  ⟨by simpa using QuasiCompact.isCompact_preimage (f := q) Set.univ isOpen_univ isCompact_univ⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
open LineBundleData in
/-- **A second section** (blueprint `lem:sm-ample-second-section`): let `X` be projective over an
infinite field `K`, without chains of three distinct points, and `s` a global section of `𝓛^n`
which does not vanish at the non-closed points. Then for some `m` there is a global section `t` of
`𝓛^{n(m+1)}` without zero on the zero set of `s`. -/
theorem exists_section_sup_eq_top {K : Type u} [Field K] [Infinite K] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : ∀ x y z : X, x ⤳ y → y ⤳ z → x = y ∨ y = z)
    {L : Projectivity.LineBundleData X} {n : ℤ} (s : L.Sections n ⊤)
    (hgen : ∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) :
    ∃ (m : ℕ) (t : L.Sections (n * ((m + 1 : ℕ) : ℤ)) ⊤),
      s.nonvanishingLocus ⊔ t.nonvanishingLocus = ⊤ := by
  classical
  have : IsProper p := hp.isProper
  have : CompactSpace X := compactSpace_of_quasiCompact p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := ⟨⟩
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := isAffineHom_diagonal_of_isSeparated p
  have hp' := hp
  obtain ⟨N', i, hi, hcomp⟩ := hp'
  have : IsClosedImmersion i := hi
  have hiA : IsAffineHom i := inferInstance
  have : Infinite (IsLocalRing.ResidueField K) := infinite_residueField K
  -- the finitely many non-closed points and zeros of `s`
  set G : Set X := {x | ¬ IsClosed ({x} : Set X)}
  have hG : G.Finite := finite_setOf_not_isClosed hdim
  set S₀ : Set X := (s.nonvanishingLocus : Set X)ᶜ
  have hS₀ : S₀.Finite := finite_of_forall_isClosed_singleton
    s.nonvanishingLocus.isOpen.isClosed_compl fun z hz => by
      by_contra h
      exact hz (hgen z h)
  -- an affine open `V₁ = X ∩ D₊(ℓ₁)` containing `S₀` and `G`
  obtain ⟨ℓ₁, hℓ₁, hℓ₁S⟩ := exists_linearForm_mem_basicOpen (hS₀.union hG).toFinset
    (fun x => (i x : Proj (projectiveSpaceGrading K N')))
  set V₁ : X.Opens := i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading K N') ℓ₁
  have hV₁ : IsAffineOpen V₁ :=
    @IsAffineOpen.preimage _ _ _ (Proj.isAffineOpen_basicOpen _ ℓ₁ hℓ₁ one_pos) i hiA
  have hS₀V₁ : S₀ ⊆ V₁ := fun z hz =>
    hℓ₁S z ((hS₀.union hG).mem_toFinset.mpr (Or.inl hz))
  have hGV₁ : G ⊆ V₁ := fun z hz =>
    hℓ₁S z ((hS₀.union hG).mem_toFinset.mpr (Or.inr hz))
  -- an affine open `W₀ = X ∩ D₊(ℓ₀)` containing the complement of `V₁` and `G`
  set T₁ : Set X := (V₁ : Set X)ᶜ
  have hT₁ : T₁.Finite := finite_of_forall_isClosed_singleton V₁.isOpen.isClosed_compl
    fun z hz => by
      by_contra h
      exact hz (hGV₁ h)
  obtain ⟨ℓ₀, hℓ₀, hℓ₀S⟩ := exists_linearForm_mem_basicOpen (hT₁.union hG).toFinset
    (fun x => (i x : Proj (projectiveSpaceGrading K N')))
  set W₀ : X.Opens := i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading K N') ℓ₀
  have hW₀ : IsAffineOpen W₀ :=
    @IsAffineOpen.preimage _ _ _ (Proj.isAffineOpen_basicOpen _ ℓ₀ hℓ₀ one_pos) i hiA
  have hT₁W₀ : T₁ ⊆ W₀ := fun z hz =>
    hℓ₀S z ((hT₁.union hG).mem_toFinset.mpr (Or.inl hz))
  have hGW₀ : G ⊆ W₀ := fun z hz =>
    hℓ₀S z ((hT₁.union hG).mem_toFinset.mpr (Or.inr hz))
  -- the affine open `U = W₀ ∩ D(s)`
  set U : X.Opens := (s.restrict (le_top : W₀ ≤ ⊤)).nonvanishingLocus
  have hUdef : U = W₀ ⊓ s.nonvanishingLocus := Sections.nonvanishingLocus_restrict _ _
  have hUaff : IsAffineOpen U := isAffineOpen_nonvanishingLocus_of_isAffineOpen hW₀ _
  have hUs : U ≤ s.nonvanishingLocus := hUdef ▸ inf_le_right
  -- its complement `S` is a finite set of closed points of `V₁`
  set S : Set X := (U : Set X)ᶜ
  have hGU : G ⊆ U := fun z hz => by
    rw [hUdef]
    exact ⟨hGW₀ hz, hgen z hz⟩
  have hScl : ∀ z ∈ S, IsClosed ({z} : Set X) := fun z hz => by
    by_contra h
    exact hz (hGU h)
  have hSfin : S.Finite := finite_of_forall_isClosed_singleton U.isOpen.isClosed_compl hScl
  have hSV₁ : S ⊆ V₁ := by
    intro z hz
    by_cases hzs : z ∈ s.nonvanishingLocus
    · by_contra hzV
      apply hz
      rw [hUdef]
      exact ⟨hT₁W₀ hzV, hzs⟩
    · exact hS₀V₁ hzs
  -- a section `σ₁` of `𝓛^n` over `V₁` without zero on `S`, and `V = D(σ₁)`
  obtain ⟨σ₁, hσ₁⟩ := exists_section_nonvanishing L n hV₁ hSfin hSV₁ hScl
  set V : X.Opens := σ₁.nonvanishingLocus
  have hVaff : IsAffineOpen V := isAffineOpen_nonvanishingLocus_of_isAffineOpen hV₁ σ₁
  set σ : L.Sections n V := σ₁.restrict (Sections.nonvanishingLocus_le σ₁)
  have hσ : σ.nonvanishingLocus = V := by
    rw [Sections.nonvanishingLocus_restrict]
    exact inf_idem _
  have hcov : U ⊔ V = ⊤ := by
    apply top_unique
    intro z _
    by_cases hz : z ∈ U
    · exact Opens.mem_sup.mpr (Or.inl hz)
    · exact Opens.mem_sup.mpr (Or.inr (hσ₁ z hz))
  -- the two-chart setting: `𝓛^{nk} ≅ 𝒪(kD)`, `D = V(s/σ)`
  set c := structureCoeff p
  have hf := isUnit_ratio s hσ hUs
  have hUV : IsAffineOpen (U ⊓ V) := hUaff.inf hVaff
  have hfinO : Module.Finite K (cohomology (unitModule X) c 1) :=
    finite_cohomology_of_isProjectiveOver hp (unitModule X)
      (fun W _ => Module.Finite.self Γ(X, W)) 1
  have h1fd : FiniteDimensional K (H1 (resUV (unitModule X) U V c) (resVU (unitModule X) U V c)
      (twistFamily (unitModule X) U V c hf 0)) :=
    Module.Finite.equiv (cohomologyOneEquivTwistZero (unitModule X) U V c hf hcov hUaff hVaff hUV)
  obtain ⟨m₀, hm₀⟩ := exists_forall_surjective_family_of_H1 (resUV (unitModule X) U V c)
    (resVU (unitModule X) U V c) (fEquiv (unitModule X) U V c hf)
    (fMul (unitModule X) V c (ratio s hσ)) (resVU_fMul (unitModule X) U V c hf)
    (twistFamily (unitModule X) U V c hf) (twistFamily_succ (unitModule X) U V c hf)
  obtain ⟨p₀, hp₀, hp₀1⟩ := hm₀ m₀ le_rfl
    (Submodule.Quotient.mk (id (1 : Γ(X, V)) : sectionsModuleCat (unitModule X) c V le_top))
  set k : ℕ := m₀ + 1
  have hp₀' : p₀ ∈ H0 (resUV (unitModule X) U V c) (resVU (unitModule X) U V c)
      (twistFamily (unitModule X) U V c hf ((k : ℕ) : ℤ)) := by
    have e : ((m₀ : ℤ) + 1) = ((m₀ + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [← e]
    exact hp₀
  -- the global section of `𝒪(kD)` and the corresponding section `t` of `𝓛^{nk}`
  let glob := (divisorTwistGlobalEquiv (unitModule X) U V c hf k).symm ⟨p₀, hp₀'⟩
  let e := twoChartIso s hσ (unitModule X) hUs k hcov
  let T : Γ(L.twist (unitModule X) (n * k), ⊤) := e.inv.app ⊤ glob
  have hTp : e.hom.app ⊤ T = glob := by
    change (e.inv ≫ e.hom).app ⊤ glob = glob
    rw [e.inv_hom_id]
    rfl
  have h2 : (toPair s (unitModule X) hσ hUs k ⊤ T).2 =
      (unitModule X).presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op p₀.2 := by
    have e1 : toPair s (unitModule X) hσ hUs k ⊤ T =
        (show twistSubgroup (unitModule X) U V ((isUnit_ratio s hσ hUs).unit ^ (k : ℤ)) ⊤ from
          glob).1 := by
      rw [← twoChartHom_app s hσ (unitModule X) hUs k ⊤ T]
      exact congrArg (fun z => (show twistSubgroup (unitModule X) U V
        ((isUnit_ratio s hσ hUs).unit ^ (k : ℤ)) ⊤ from z).1) hTp
    rw [e1]
    rfl
  have hmul := mulSec_toPair_snd s hσ (unitModule X) hUs k ⊤ T
  rw [h2] at hmul
  let t : L.Sections (n * ((m₀ + 1 : ℕ) : ℤ)) ⊤ := T
  refine ⟨m₀, t, ?_⟩
  apply top_unique
  intro z _
  by_cases hz : z ∈ s.nonvanishingLocus
  · exact Opens.mem_sup.mpr (Or.inl hz)
  · refine Opens.mem_sup.mpr (Or.inr ?_)
    have hzV : z ∈ V := hσ₁ z (fun hzU => hz (hUs hzU))
    -- the `V`-component is `1` modulo `f = s/σ`
    obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).mp hp₀1
    let a : Γ(X, V) := p₀.2
    let b' : Γ(X, V) := b
    have hb' : a = 1 + ratio s hσ * b' := by
      have hb2 : ratio s hσ * b' = a - 1 := hb
      rw [hb2]
      ring
    have hz1 : z ∈ X.basicOpen a := by
      rw [X.mem_basicOpen _ z hzV, hb', map_add, map_one, map_mul]
      apply isUnit_add_of_mem_maximalIdeal isUnit_one
      apply Ideal.mul_mem_right
      apply germ_mem_maximalIdeal
      rw [basicOpen_ratio]
      exact fun h => hz h.2
    have hzT : z ∈ (t.restrict (le_top : ⊤ ⊓ V ≤ ⊤)).nonvanishingLocus := by
      have e2 : t.restrict (le_top : ⊤ ⊓ V ≤ ⊤) =
          X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op a • secV σ k ⊤ := by
        rw [← mulSec_unit]
        exact hmul.symm
      rw [e2, Sections.nonvanishingLocus_smul, Scheme.basicOpen_res,
        nonvanishingLocus_secV hσ k ⊤]
      exact ⟨⟨⟨trivial, hzV⟩, hz1⟩, ⟨trivial, hzV⟩⟩
    rw [Sections.nonvanishingLocus_restrict] at hzT
    exact hzT.2

end

end DeJongAlterations.StableModification.CurvesField.Ample
