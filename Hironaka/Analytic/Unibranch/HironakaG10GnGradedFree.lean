import Hironaka.Analytic.Unibranch.HironakaG10LfGradedFlat
import Hironaka.Resolution.HironakaRelativeNormalCoefficientAlgebraNearbyFreeness

/-!
# Free normal cone over a base quotient ⇒ free truncations ⇒ flat quotient (route N, item N3)

Lane G10GN, run 0081 (`work/hironaka-run0081-20261117/G10GN/hGF-route.md`, item G10GN-N3). Notation:
`R = 𝒪_{ℂᵈ,0}`, `B = 𝒪_{ℂ^{d+t},0}` (an `R`-algebra through the projection, `tangentAlgebra`), `N` the ideal of the
normal coordinates, `L` an ideal of `B` containing the extension of an ideal `K` of `R` (`K` = the vanishing ideal of
a parameter set). All the library's objects attached to `L` — the normal truncations `B ⧸ (L ⊔ Nᵠ)`, the normal graded
pieces, the polynomial quotient `R[x] ⧸ in(L)` — are killed by `K`, hence modules over `R̄ = R ⧸ K`.

* **`free_truncation_of_free_initial`**: if `R̄[x] ⧸ in(L)·R̄[x]` is free over `R̄` (`K` proper), then every normal
  truncation `B ⧸ (L ⊔ Nᵠ)` is free over `R̄` (degree pieces are direct summands of the free normal cone, hence
  projective and finite over the local ring `R̄`, hence free; then the exact filtration of the truncations).
* **`flat_quotient_of_free_initial`**: then `B ⧸ L` is flat over `R̄` (Frisch (II,1)(ii), lane G10LF's
  `HironakaG10LfGradedFlat.flat_of_forall_flat_quotient_pow`, Krull over the noetherian local ring `B ⧸ L`).

BP: hironaka-g10gn-graded-free.tex.
-/

set_option autoImplicit false

open Set Filter
open scoped DirectSum

namespace Hironaka.Analytic.Unibranch.HironakaG10GnGradedFree

noncomputable section

open Hironaka Hironaka
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalUniformTruncations
  HironakaRelativeNormalCoefficientAlgebraNearbyFreeness

attribute [local instance] tangentAlgebra

variable (d t : ℕ) (K : Ideal (HolGerm (ComplexModel d))) (L : Ideal (HolGerm (ComplexModel (d+t))))

/-- The constants of `K` lie in the normal initial ideal of `L` when `K·B ⊆ L`. -/
theorem C_mem_initialIdeal (hKL : ∀ k ∈ K, tangentPullback d t k ∈ L) {k : HolGerm (ComplexModel d)}
    (hk : k ∈ K) : MvPolynomial.C k ∈ originalNormalInitialIdeal d t L := by
  change normalAssociatedSymbolMap d t L (MvPolynomial.C k) = 0
  refine (normalAssociatedSymbolMap_eq_zero_iff d t L _).mpr ?_
  intro q
  rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_C (Fin t) k)]
  split_ifs with hq
  · subst hq
    have : normalPolynomialEval d t (MvPolynomial.C k) = tangentPullback d t k := MvPolynomial.aeval_C _ _
    rw [this]
    exact Ideal.mem_sup_left (hKL k hk)
  · rw [map_zero]
    exact Ideal.zero_mem _

/-- Normal truncations are killed by `K`. -/
theorem isTorsionBySet_truncation (hKL : ∀ k ∈ K, tangentPullback d t k ∈ L) (q : ℕ) :
    Module.IsTorsionBySet (HolGerm (ComplexModel d)) (originalNormalTruncation d t L q) K := by
  intro x k
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show Ideal.Quotient.mk (L ⊔ normalIdeal d t ^ q) b =
      Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (L ⊔ normalIdeal d t ^ q) b from rfl, ← map_smul,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]
  exact Ideal.mem_sup_left (L.mul_mem_right b (hKL k k.2))

/-- Normal graded pieces are killed by `K`. -/
theorem isTorsionBySet_piece (hKL : ∀ k ∈ K, tangentPullback d t k ∈ L) (q : ℕ) :
    Module.IsTorsionBySet (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t L q) K := by
  intro x k
  apply Subtype.ext
  exact isTorsionBySet_truncation d t K L hKL (q+1) (x := x.val) (a := k)

/-- The polynomial quotient by the normal initial ideal is killed by `K`. -/
theorem isTorsionBySet_initialQuotient (hKL : ∀ k ∈ K, tangentPullback d t k ∈ L) :
    Module.IsTorsionBySet (HolGerm (ComplexModel d))
      (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ originalNormalInitialIdeal d t L) K := by
  intro x k
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show Ideal.Quotient.mk (originalNormalInitialIdeal d t L) P =
      Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (originalNormalInitialIdeal d t L) P from rfl, ← map_smul,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.smul_eq_C_mul]
  exact Ideal.mul_mem_right _ _ (C_mem_initialIdeal d t K L hKL k.2)

/-! ### The base ring of the normal cone over `R̄ = R ⧸ K` -/

/-- The polynomial quotient over `R` maps onto the polynomial quotient over `R̄`. -/
def polyBaseHom :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)]
      MvPolynomial (Fin t) (HolGerm (ComplexModel d) ⧸ K) ⧸
        (originalNormalInitialIdeal d t L).map (MvPolynomial.map (Ideal.Quotient.mk K)) :=
  (Ideal.Quotient.mkₐ _ _).comp (MvPolynomial.mapAlgHom (Ideal.Quotient.mkₐ _ K))

theorem polyBaseHom_apply (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    polyBaseHom d t K L P = Ideal.Quotient.mk _ (MvPolynomial.map (Ideal.Quotient.mk K) P) := rfl

theorem polyBaseHom_surjective : Function.Surjective (polyBaseHom d t K L) := by
  intro y
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨P', rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective P
  exact ⟨P', rfl⟩

theorem ker_polyBaseHom (hKL : ∀ k ∈ K, tangentPullback d t k ∈ L) :
    RingHom.ker (polyBaseHom d t K L) = originalNormalInitialIdeal d t L := by
  ext P
  rw [RingHom.mem_ker, polyBaseHom_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective (MvPolynomial.map (Ideal.Quotient.mk K) :
      MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →+* MvPolynomial (Fin t) (HolGerm (ComplexModel d) ⧸ K))
      (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective),
    ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, Ideal.mk_ker]
  constructor
  · intro h
    have hle : Ideal.map (MvPolynomial.C : HolGerm (ComplexModel d) →+* _) K ≤
        originalNormalInitialIdeal d t L := by
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      exact C_mem_initialIdeal d t K L hKL hk
    exact (sup_le le_rfl hle) h
  · exact fun h => Ideal.mem_sup_left h

/-- `R[x] ⧸ in(L) ≅ R̄[x] ⧸ in(L)·R̄[x]` as `R`-algebras. -/
def initialQuotientAlgEquiv (hKL : ∀ k ∈ K, tangentPullback d t k ∈ L) :
    (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ originalNormalInitialIdeal d t L) ≃ₐ[HolGerm (ComplexModel d)]
      (MvPolynomial (Fin t) (HolGerm (ComplexModel d) ⧸ K) ⧸
        (originalNormalInitialIdeal d t L).map (MvPolynomial.map (Ideal.Quotient.mk K))) :=
  (Ideal.quotientEquivAlgOfEq _ (ker_polyBaseHom d t K L hKL).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (polyBaseHom_surjective d t K L))

/-! ### Type synonyms carrying the `R̄`-module structures of the `K`-torsion library objects -/

/-- The normal graded piece of degree `q`, as an `R̄`-module. -/
def PieceQ (_K : Ideal (HolGerm (ComplexModel d))) (q : ℕ) : Type :=
  originalNormalGradedPiece d t L q

/-- The normal truncation of order `q`, as an `R̄`-module. -/
def TruncQ (_K : Ideal (HolGerm (ComplexModel d))) (q : ℕ) : Type :=
  originalNormalTruncation d t L q

/-- The polynomial quotient by the normal initial ideal, as an `R̄`-module. -/
def InitQ (_K : Ideal (HolGerm (ComplexModel d))) : Type :=
  MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ originalNormalInitialIdeal d t L

instance (q : ℕ) : AddCommGroup (PieceQ d t L K q) :=
  inferInstanceAs (AddCommGroup (originalNormalGradedPiece d t L q))
instance (q : ℕ) : Module (HolGerm (ComplexModel d)) (PieceQ d t L K q) :=
  inferInstanceAs (Module (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t L q))
instance (q : ℕ) : AddCommGroup (TruncQ d t L K q) :=
  inferInstanceAs (AddCommGroup (originalNormalTruncation d t L q))
instance (q : ℕ) : Module (HolGerm (ComplexModel d)) (TruncQ d t L K q) :=
  inferInstanceAs (Module (HolGerm (ComplexModel d)) (originalNormalTruncation d t L q))
instance (q : ℕ) : Module (HolGerm (ComplexModel (d+t))) (TruncQ d t L K q) :=
  inferInstanceAs (Module (HolGerm (ComplexModel (d+t))) (originalNormalTruncation d t L q))
instance (q : ℕ) : IsScalarTower (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) (TruncQ d t L K q) :=
  inferInstanceAs (IsScalarTower (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)))
    (originalNormalTruncation d t L q))
instance : AddCommGroup (InitQ d t L K) :=
  inferInstanceAs (AddCommGroup (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ originalNormalInitialIdeal d t L))
instance : Module (HolGerm (ComplexModel d)) (InitQ d t L K) :=
  inferInstanceAs (Module (HolGerm (ComplexModel d))
    (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ originalNormalInitialIdeal d t L))

theorem isTorsionBySet_pieceQ (hKL : ∀ k ∈ K, tangentPullback d t k ∈ L) (q : ℕ) :
    Module.IsTorsionBySet (HolGerm (ComplexModel d)) (PieceQ d t L K q) K :=
  isTorsionBySet_piece d t K L hKL q

theorem isTorsionBySet_truncQ (hKL : ∀ k ∈ K, tangentPullback d t k ∈ L) (q : ℕ) :
    Module.IsTorsionBySet (HolGerm (ComplexModel d)) (TruncQ d t L K q) K :=
  isTorsionBySet_truncation d t K L hKL q

theorem isTorsionBySet_initQ (hKL : ∀ k ∈ K, tangentPullback d t k ∈ L) :
    Module.IsTorsionBySet (HolGerm (ComplexModel d)) (InitQ d t L K) K :=
  isTorsionBySet_initialQuotient d t K L hKL

variable [hKL : Fact (∀ k ∈ K, tangentPullback d t k ∈ L)]

instance (q : ℕ) : Module (HolGerm (ComplexModel d) ⧸ K) (PieceQ d t L K q) :=
  (isTorsionBySet_pieceQ d t K L hKL.out q).module
instance (q : ℕ) : IsScalarTower (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d) ⧸ K) (PieceQ d t L K q) :=
  (isTorsionBySet_pieceQ d t K L hKL.out q).isScalarTower
instance (q : ℕ) : Module (HolGerm (ComplexModel d) ⧸ K) (TruncQ d t L K q) :=
  (isTorsionBySet_truncQ d t K L hKL.out q).module
instance (q : ℕ) : IsScalarTower (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d) ⧸ K) (TruncQ d t L K q) :=
  (isTorsionBySet_truncQ d t K L hKL.out q).isScalarTower
instance : Module (HolGerm (ComplexModel d) ⧸ K) (InitQ d t L K) :=
  (isTorsionBySet_initQ d t K L hKL.out).module
instance : IsScalarTower (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d) ⧸ K) (InitQ d t L K) :=
  (isTorsionBySet_initQ d t K L hKL.out).isScalarTower

theorem free_initQ
    (hfree : Module.Free (HolGerm (ComplexModel d) ⧸ K)
      (MvPolynomial (Fin t) (HolGerm (ComplexModel d) ⧸ K) ⧸
        (originalNormalInitialIdeal d t L).map (MvPolynomial.map (Ideal.Quotient.mk K)))) :
    Module.Free (HolGerm (ComplexModel d) ⧸ K) (InitQ d t L K) := by
  let e : InitQ d t L K ≃ₗ[HolGerm (ComplexModel d)]
      (MvPolynomial (Fin t) (HolGerm (ComplexModel d) ⧸ K) ⧸
        (originalNormalInitialIdeal d t L).map (MvPolynomial.map (Ideal.Quotient.mk K))) :=
    (initialQuotientAlgEquiv d t K L hKL.out).toLinearEquiv
  exact Module.Free.of_equiv (e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective).symm

private theorem short_exact_middle_free {R L M N : Type} [CommRing R]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N] [Module.Free R L] [Module.Free R N]
    (g : L →ₗ[R] M) (h : M →ₗ[R] N) (hg : Function.Injective g)
    (hh : Function.Surjective h) (ex : Function.Exact g h) : Module.Free R M := by
  let S := ModuleCat.shortComplexOfCompEqZero g h ex.linearMap_comp_eq_zero
  have hs := ModuleCat.shortComplex_shortExact S ex hg hh
  exact ModuleCat.free_shortExact hs

theorem free_pieceQ (hK : K ≠ ⊤)
    (hfree : Module.Free (HolGerm (ComplexModel d) ⧸ K)
      (MvPolynomial (Fin t) (HolGerm (ComplexModel d) ⧸ K) ⧸
        (originalNormalInitialIdeal d t L).map (MvPolynomial.map (Ideal.Quotient.mk K)))) (q : ℕ) :
    Module.Free (HolGerm (ComplexModel d) ⧸ K) (PieceQ d t L K q) := by
  have : Nontrivial (HolGerm (ComplexModel d) ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK
  have : IsLocalRing (HolGerm (ComplexModel d) ⧸ K) :=
    .of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have := free_initQ d t K L hfree
  let e : InitQ d t L K ≃ₗ[HolGerm (ComplexModel d)] (⨁ q, PieceQ d t L K q) :=
    originalNormalAssociatedGradedQuotientEquiv d t L
  have hwhole : Module.Free (HolGerm (ComplexModel d) ⧸ K) (⨁ q, PieceQ d t L K q) :=
    Module.Free.of_equiv (e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
  have hproj : Module.Projective (HolGerm (ComplexModel d) ⧸ K) (PieceQ d t L K q) :=
    (Module.Projective.directSum_iff.mp
      (inferInstance : Module.Projective (HolGerm (ComplexModel d) ⧸ K) (⨁ q, PieceQ d t L K q))) q
  have hfinR : Module.Finite (HolGerm (ComplexModel d)) (PieceQ d t L K q) :=
    moduleFinite_originalNormalGradedPiece d t L q
  have hfin : Module.Finite (HolGerm (ComplexModel d) ⧸ K) (PieceQ d t L K q) :=
    Module.Finite.of_restrictScalars_finite (HolGerm (ComplexModel d)) _ _
  exact Module.free_of_flat_of_isLocalRing

/-- **Free normal cone over `R̄` ⇒ every normal truncation is free over `R̄`.** -/
theorem free_truncQ (hK : K ≠ ⊤)
    (hfree : Module.Free (HolGerm (ComplexModel d) ⧸ K)
      (MvPolynomial (Fin t) (HolGerm (ComplexModel d) ⧸ K) ⧸
        (originalNormalInitialIdeal d t L).map (MvPolynomial.map (Ideal.Quotient.mk K)))) (q : ℕ) :
    Module.Free (HolGerm (ComplexModel d) ⧸ K) (TruncQ d t L K q) := by
  induction q with
  | zero =>
    have : Subsingleton (TruncQ d t L K 0) := originalNormalTruncation_zero_subsingleton d t L
    exact Module.Free.of_subsingleton _ _
  | succ q ih =>
    have := free_pieceQ d t K L hK hfree q
    let g₀ : PieceQ d t L K q →ₗ[HolGerm (ComplexModel d)] TruncQ d t L K (q+1) :=
      originalNormalTruncationPieceInclusion d t L q
    let h₀ : TruncQ d t L K (q+1) →ₗ[HolGerm (ComplexModel d)] TruncQ d t L K q :=
      (originalNormalTruncationMap d t L q).toLinearMap
    let g := g₀.extendScalarsOfSurjective (S := HolGerm (ComplexModel d) ⧸ K) Ideal.Quotient.mk_surjective
    let h := h₀.extendScalarsOfSurjective (S := HolGerm (ComplexModel d) ⧸ K) Ideal.Quotient.mk_surjective
    exact short_exact_middle_free g h (originalNormalTruncationPieceInclusion_injective d t L q)
      (originalNormalTruncationMap_surjective d t L q) (originalNormalTruncation_exact d t L q)

/-! ### Flatness of `B ⧸ L` over `R̄` (Frisch (II,1)(ii)) -/

theorem normalIdeal_le_maximalIdeal :
    normalIdeal d t ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) := by
  rw [normalIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, HolGerm.isUnit_iff_eval_ne_zero, not_not]
  unfold normalCoordinate coordinateGerm
  rw [HolGerm.eval_mk]
  rfl

/-- The `R̄`-algebra structure of `B ⧸ L`. -/
abbrev quotAlgebra : Algebra (HolGerm (ComplexModel d) ⧸ K) (HolGerm (ComplexModel (d+t)) ⧸ L) :=
  Ideal.Quotient.algebraQuotientOfLEComap (fun k hk => hKL.out k hk)

/-- The image of the normal ideal in `B ⧸ L`. -/
abbrev normalQ : Ideal (HolGerm (ComplexModel (d+t)) ⧸ L) := (normalIdeal d t).map (Ideal.Quotient.mk L)

/-- The truncation `(B ⧸ L) ⧸ (N̄ⁿ · (B ⧸ L))`. -/
abbrev QTrunc (n : ℕ) : Type :=
  (HolGerm (ComplexModel (d+t)) ⧸ L) ⧸
    (normalQ d t L ^ n • (⊤ : Submodule (HolGerm (ComplexModel (d+t)) ⧸ L) (HolGerm (ComplexModel (d+t)) ⧸ L)))

theorem mk_mem_normalQ_smul_iff (n : ℕ) (b : HolGerm (ComplexModel (d+t))) :
    Ideal.Quotient.mk L b ∈ (normalQ d t L ^ n •
      (⊤ : Submodule (HolGerm (ComplexModel (d+t)) ⧸ L) (HolGerm (ComplexModel (d+t)) ⧸ L))) ↔
      b ∈ L ⊔ normalIdeal d t ^ n := by
  have hJn : (normalQ d t L ^ n •
      (⊤ : Submodule (HolGerm (ComplexModel (d+t)) ⧸ L) (HolGerm (ComplexModel (d+t)) ⧸ L))) =
      ((normalIdeal d t ^ n).map (Ideal.Quotient.mk L) : Ideal _) := by
    rw [smul_eq_mul, Ideal.mul_top, normalQ, Ideal.map_pow]
  rw [hJn, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]

/-- The `B`-linear map `B ⧸ (L ⊔ Nⁿ) → (B ⧸ L) ⧸ N̄ⁿ(B ⧸ L)`. -/
def truncLin (n : ℕ) : TruncQ d t L K n →ₗ[HolGerm (ComplexModel (d+t))] QTrunc d t L n :=
  (L ⊔ normalIdeal d t ^ n).liftQ
    (((normalQ d t L ^ n • (⊤ : Submodule (HolGerm (ComplexModel (d+t)) ⧸ L)
      (HolGerm (ComplexModel (d+t)) ⧸ L))).mkQ.restrictScalars (HolGerm (ComplexModel (d+t)))).comp
      (Algebra.linearMap (HolGerm (ComplexModel (d+t))) (HolGerm (ComplexModel (d+t)) ⧸ L)))
    (fun b hb => (Submodule.Quotient.mk_eq_zero _).mpr ((mk_mem_normalQ_smul_iff d t L n b).mpr hb))

omit hKL in
theorem truncLin_mk (n : ℕ) (b : HolGerm (ComplexModel (d+t))) :
    truncLin d t K L n (Submodule.Quotient.mk b) = Submodule.Quotient.mk (Ideal.Quotient.mk L b) := rfl

omit hKL in
theorem truncLin_bijective (n : ℕ) : Function.Bijective (truncLin d t K L n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [truncLin_mk, Submodule.Quotient.mk_eq_zero, mk_mem_normalQ_smul_iff] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  · intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨Submodule.Quotient.mk b, rfl⟩

theorem truncQ_smul (n : ℕ) (r : HolGerm (ComplexModel d)) (x : TruncQ d t L K n) :
    (Ideal.Quotient.mk K r) • x = (tangentPullback d t r) • x := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem qTrunc_smul (n : ℕ) (r : HolGerm (ComplexModel d)) (y : QTrunc d t L n) :
    letI := quotAlgebra d t K L
    (Ideal.Quotient.mk K r) • y = (tangentPullback d t r) • y := by
  letI := quotAlgebra d t K L
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  rfl

/-- The `R̄`-linear identification of the two truncations. -/
def truncEquiv (n : ℕ) :
    letI := quotAlgebra d t K L
    TruncQ d t L K n ≃ₗ[HolGerm (ComplexModel d) ⧸ K] QTrunc d t L n :=
  letI := quotAlgebra d t K L
  LinearEquiv.ofBijective
    { toFun := truncLin d t K L n
      map_add' := map_add _
      map_smul' := by
        intro r x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [RingHom.id_apply, truncQ_smul, qTrunc_smul, map_smul] }
    (truncLin_bijective d t K L n)

/-- **Free normal cone over `R̄` ⇒ `B ⧸ L` is flat over `R̄`.** -/
theorem flat_quotient_of_free_initial (hK : K ≠ ⊤)
    (hfree : Module.Free (HolGerm (ComplexModel d) ⧸ K)
      (MvPolynomial (Fin t) (HolGerm (ComplexModel d) ⧸ K) ⧸
        (originalNormalInitialIdeal d t L).map (MvPolynomial.map (Ideal.Quotient.mk K)))) :
    letI := quotAlgebra d t K L
    Module.Flat (HolGerm (ComplexModel d) ⧸ K) (HolGerm (ComplexModel (d+t)) ⧸ L) := by
  letI := quotAlgebra d t K L
  have := isNoetherianRing_holGerm_euclidean (d+t)
  have hJ : normalQ d t L ≤ Ideal.jacobson ⊥ := by
    have h1 : normalIdeal d t ≤ Ideal.jacobson L :=
      (normalIdeal_le_maximalIdeal d t).trans ((IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm.le.trans
        (Ideal.jacobson_mono bot_le))
    have h2 := Ideal.map_mono (f := Ideal.Quotient.mk L) h1
    rwa [Ideal.map_jacobson_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]),
      Ideal.map_quotient_self] at h2
  refine Hironaka.Analytic.Unibranch.HironakaG10LfGradedFlat.flat_of_forall_flat_quotient_pow
    (B := HolGerm (ComplexModel d) ⧸ K) (C := HolGerm (ComplexModel (d+t)) ⧸ L)
    (M := HolGerm (ComplexModel (d+t)) ⧸ L) (normalQ d t L) hJ (fun n => ?_)
  have := free_truncQ d t K L hK hfree n
  have : Module.Free (HolGerm (ComplexModel d) ⧸ K) (QTrunc d t L n) :=
    Module.Free.of_equiv (truncEquiv d t K L n)
  exact Module.Flat.of_free

end

end Hironaka.Analytic.Unibranch.HironakaG10GnGradedFree
