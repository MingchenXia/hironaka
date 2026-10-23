import DeJongAlterations.StableModification.Flattening.Torsion
import DeJongAlterations.StableModification.Limits.FlatDescent
import DeJongAlterations.StableModification.Limits.System
import DeJongAlterations.StableModification.ValuationRing.Nagata

/-!
# Strict transforms over valuation rings and their spreading out

Let `R₀` be a noetherian ring with a map to a field `K`, `V ⊆ K` a valuation ring containing the
image of `R₀`, and `B` an `R₀`-algebra of finite type. The strict transform of `Spec B` over
`Spec V` is `(V ⊗_{R₀} B) ⧸ torsion`. It is torsion free, hence flat over `V`, and of finite
type, hence of finite presentation (Temkin, *Stable modification of relative curves*,
Lemma 3.5.1 `valringlem`, after Raynaud–Gruson I 3.4.7: `ValuationRing.Nagata`); so the torsion
ideal of `V ⊗ B` is finitely generated (`fg_torsionIdeal`, blueprint
`lem:sm-strict-transform-valuation`).

Writing `V` as the directed union of its finitely generated `R₀`-subalgebras `F`, the generators
of the torsion ideal come from some `F₀ ⊗ B`, and descent of flatness
(`Limits.FlatDescent.flat_tensor_of_flat_tensor_union`, EGA IV₃ 11.2.6) gives a finitely
generated `F ⊇ F₀` in `V` such that `(F ⊗_{R₀} B) ⧸ torsion` is flat over `F`
(`exists_flat_quotient_torsion`, blueprint `lem:sm-strict-transform-spread`). This is the limit
step (v) of Temkin's `P`-modification method (§3.4, `semi-stable.tex` l.2486–2568) for
`P` = flatness; steps (ii)–(iv) are empty for flatness.
-/

open TensorProduct

universe u

namespace DeJongAlterations.StableModification.Flattening

open Limits Limits.FlatDescent

section Valuation

variable {V M : Type*} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing M] [Algebra V M]

/-- Over a valuation ring, the quotient of an algebra by its torsion is flat. -/
theorem flat_quotient_torsionIdeal : Module.Flat V (M ⧸ torsionIdeal V M) := by
  rw [ValuationRing.flat_iff_forall_smul_eq_zero]
  intro c hc q hq
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have h1 : c • x ∈ torsionIdeal V M := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk V, map_smul,
      Ideal.Quotient.mkₐ_eq_mk]
    exact hq
  obtain ⟨d, hd, hdx⟩ := (mem_torsion_iff_of_isDomain _).1 (mem_torsionIdeal.1 h1)
  refine mem_torsionIdeal.2 ((mem_torsion_iff_of_isDomain x).2 ⟨d * c, mul_ne_zero hd hc, ?_⟩)
  rw [mul_smul, hdx]

/-- **Lemma `lem:sm-strict-transform-valuation`.** Over a valuation ring `V`, the torsion ideal
of a finitely presented `V`-algebra is finitely generated: the quotient is flat and of finite
type, hence finitely presented (Temkin, Lemma 3.5.1). -/
theorem fg_torsionIdeal [Algebra.FinitePresentation V M] : (torsionIdeal V M).FG := by
  have : Module.Flat V (M ⧸ torsionIdeal V M) := flat_quotient_torsionIdeal
  have : Algebra.FinitePresentation V (M ⧸ torsionIdeal V M) :=
    ValuationRing.finitePresentation_of_finiteType_of_flat
  have h := Algebra.FinitePresentation.ker_fG_of_surjective
    (Ideal.Quotient.mkₐ V (torsionIdeal V M)) (Ideal.Quotient.mkₐ_surjective V _)
  change (RingHom.ker (Ideal.Quotient.mk (torsionIdeal V M))).FG at h
  rwa [Ideal.mk_ker] at h

end Valuation

section Spread

variable {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K]

/-- A valuation ring `V` of `K` containing the image of `R₀`, as an `R₀`-subalgebra. -/
def subalgebraOfValuationSubring (V : ValuationSubring K) (hV : ∀ r : R₀, algebraMap R₀ K r ∈ V) :
    Subalgebra R₀ K :=
  { V.toSubring with algebraMap_mem' := hV }

instance (V : ValuationSubring K) (hV : ∀ r : R₀, algebraMap R₀ K r ∈ V) :
    ValuationRing (subalgebraOfValuationSubring V hV) :=
  inferInstanceAs (ValuationRing V)

/-- The canonical map `G ⊗_{R₀} B → K ⊗_{R₀} B` for an intermediate algebra `R₀ → G → K`. -/
noncomputable def toFieldTensor (G : Type*) [CommRing G] [Algebra R₀ G] [Algebra G K]
    [IsScalarTower R₀ G K] (B : Type*) [AddCommGroup B] [Module R₀ B] :
    G ⊗[R₀] B →ₗ[G] K ⊗[R₀] B :=
  (AlgebraTensorModule.cancelBaseChange R₀ G K K B).toLinearMap.restrictScalars G ∘ₗ
    TensorProduct.mk G K (G ⊗[R₀] B) 1

/-- `toFieldTensor` on pure tensors. -/
lemma toFieldTensor_tmul (G : Type*) [CommRing G] [Algebra R₀ G] [Algebra G K]
    [IsScalarTower R₀ G K] (B : Type*) [AddCommGroup B] [Module R₀ B] (g : G) (b : B) :
    toFieldTensor (R₀ := R₀) (K := K) G B (g ⊗ₜ[R₀] b) = algebraMap G K g ⊗ₜ[R₀] b := by
  simp [toFieldTensor, Algebra.algebraMap_eq_smul_one]

/-- `K ⊗_{R₀} B` is the base change of `G ⊗_{R₀} B` along `G → K`. -/
lemma isBaseChange_toFieldTensor (G : Type*) [CommRing G] [Algebra R₀ G] [Algebra G K]
    [IsScalarTower R₀ G K] (B : Type*) [AddCommGroup B] [Module R₀ B] :
    IsBaseChange K (toFieldTensor (R₀ := R₀) (K := K) G B) :=
  IsBaseChange.of_equiv (AlgebraTensorModule.cancelBaseChange R₀ G K K B) fun _ => rfl

/-- For a domain `G` between `R₀` and `K` with `G → K` injective, an element of `G ⊗_{R₀} B` is
`G`-torsion iff it dies in `K ⊗_{R₀} B`. -/
lemma mem_torsion_iff_toFieldTensor (G : Type*) [CommRing G] [IsDomain G] [Algebra R₀ G]
    [Algebra G K] [IsScalarTower R₀ G K] (hG : Function.Injective (algebraMap G K))
    (B : Type*) [AddCommGroup B] [Module R₀ B] (x : G ⊗[R₀] B) :
    x ∈ Submodule.torsion G (G ⊗[R₀] B) ↔ toFieldTensor (R₀ := R₀) (K := K) G B x = 0 := by
  refine (eq_zero_iff_mem_torsion_of_isBaseChange (fun g hg => ?_)
    (isBaseChange_toFieldTensor (R₀ := R₀) (K := K) G B) x).symm
  refine IsUnit.mk0 _ ?_
  rw [Ne, ← map_zero (algebraMap G K)]
  exact fun h => hg (hG h)

/-- **The strict transform over a valuation ring `W` above `F₀`.** Let `R₀ → F₀ → W` with `W` a
valuation ring, `B` an `R₀`-algebra and `J ⊆ F₀ ⊗_{R₀} B` an ideal generating the `W`-torsion
ideal of `W ⊗_{R₀} B`. Then `W ⊗_{F₀} ((F₀ ⊗_{R₀} B) ⧸ J)` is flat over `W`: it is the
quotient of `W ⊗_{R₀} B` by its torsion. -/
theorem flat_tensor_quotient_of_map_eq {F₀ W B : Type*} [CommRing F₀] [Algebra R₀ F₀]
    [CommRing W] [IsDomain W] [ValuationRing W] [Algebra R₀ W] [Algebra F₀ W]
    [IsScalarTower R₀ F₀ W] [CommRing B] [Algebra R₀ B] (J : Ideal (F₀ ⊗[R₀] B))
    (hJ : J.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ F₀ W) (AlgHom.id R₀ B)) =
      torsionIdeal W (W ⊗[R₀] B)) :
    Module.Flat W (W ⊗[F₀] ((F₀ ⊗[R₀] B) ⧸ J)) := by
  let e₁ := Algebra.TensorProduct.tensorQuotientEquiv (R := F₀) W (F₀ ⊗[R₀] B) W J
  let e₂ := Algebra.TensorProduct.cancelBaseChange R₀ F₀ W W B
  have he₂ : (e₂ : W ⊗[F₀] (F₀ ⊗[R₀] B) →+* W ⊗[R₀] B).comp
      (Algebra.TensorProduct.includeRight : F₀ ⊗[R₀] B →ₐ[F₀] W ⊗[F₀] (F₀ ⊗[R₀] B)) =
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ F₀ W) (AlgHom.id R₀ B) :
        F₀ ⊗[R₀] B →+* W ⊗[R₀] B) := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [e₂, Algebra.smul_def]
    | add u v hu hv => simp only [map_add, hu, hv]
  have hJ' : torsionIdeal W (W ⊗[R₀] B) =
      Ideal.map e₂ (Ideal.map Algebra.TensorProduct.includeRight J) := by
    rw [← hJ, ← Ideal.map_coe e₂, ← Ideal.map_coe (Algebra.TensorProduct.includeRight :
      F₀ ⊗[R₀] B →ₐ[F₀] W ⊗[F₀] (F₀ ⊗[R₀] B)), Ideal.map_map, he₂, Ideal.map_coe]
  let e₃ := Ideal.quotientEquivAlg _ _ e₂ hJ'
  have : Module.Flat W ((W ⊗[R₀] B) ⧸ torsionIdeal W (W ⊗[R₀] B)) := flat_quotient_torsionIdeal
  exact Module.Flat.of_linearEquiv (e₁.trans e₃).toLinearEquiv

variable [IsNoetherianRing R₀]

/-- **Generators of the torsion over `V` come from a finitely generated subalgebra.** For a
valuation ring `V ⊇ R₀` of `K` and `R₀`-algebras `B l` of finite type, there are a finitely
generated `F₀ ⊆ V` and ideals `J l ⊆ F₀ ⊗_{R₀} B l` of `F₀`-torsion elements generating the
`V`-torsion ideal of `V ⊗_{R₀} B l`. -/
theorem exists_fg_torsion_generators (V : ValuationSubring K)
    (hV : ∀ r : R₀, algebraMap R₀ K r ∈ V) {ι : Type*} [Finite ι] (B : ι → Type u)
    [∀ l, CommRing (B l)] [∀ l, Algebra R₀ (B l)] [∀ l, Algebra.FiniteType R₀ (B l)] :
    ∃ (F₀ : Subalgebra R₀ K) (hF₀V : F₀ ≤ subalgebraOfValuationSubring V hV)
      (J : ∀ l, Ideal (F₀ ⊗[R₀] B l)), F₀.FG ∧
      (∀ l, J l ≤ torsionIdeal F₀ (F₀ ⊗[R₀] B l)) ∧
      ∀ l, (J l).map (tmap (P₀ := B l) hF₀V) =
        torsionIdeal (subalgebraOfValuationSubring V hV)
          (subalgebraOfValuationSubring V hV ⊗[R₀] B l) := by
  classical
  have := Fintype.ofFinite ι
  set Vs := subalgebraOfValuationSubring V hV
  -- the torsion ideals over `V` are finitely generated
  have hfg : ∀ l, (torsionIdeal Vs (Vs ⊗[R₀] B l)).FG := fun l => by
    have : Algebra.FinitePresentation R₀ (B l) :=
      Algebra.FinitePresentation.of_finiteType.1 inferInstance
    have : Algebra.FinitePresentation Vs (Vs ⊗[R₀] B l) :=
      Algebra.FinitePresentation.baseChange Vs
    exact fg_torsionIdeal
  choose s hs using hfg
  -- the generators come from a finitely generated subalgebra `F₀ ⊆ V`
  have hR : ∀ x ∈ Vs, ∃ i : FGSubalgebra R₀ Vs, x ∈ fgSubalgebraFamily Vs i :=
    fun _ hx => exists_mem hx
  have hlift : ∀ (p : Σ l, s l), ∃ i : FGSubalgebra R₀ Vs, ∃ y : (fgSubalgebraFamily Vs i) ⊗[R₀]
      B p.1, tmap (fgSubalgebraFamily_le i) y = p.2.1 := fun p =>
    exists_tmap_eq (fgSubalgebraFamily Vs) Vs fgSubalgebraFamily_le hR p.2.1
  choose idx y hy using hlift
  obtain ⟨i₀, hi₀⟩ := Finite.exists_le idx
  have hF₀V : i₀.1 ≤ Vs := i₀.2.2
  let t' : ∀ l, s l → i₀.1 ⊗[R₀] B l := fun l t =>
    tmap ((fgSubalgebraFamily Vs).monotone (hi₀ ⟨l, t⟩)) (y ⟨l, t⟩)
  have ht' : ∀ l (t : s l), tmap hF₀V (t' l t) = t := fun l t =>
    (tmap_tmap _ _ _).trans (hy ⟨l, t⟩)
  -- the lifted generators are `F₀`-torsion
  have htor : ∀ l (t : s l), t' l t ∈ torsionIdeal i₀.1 (i₀.1 ⊗[R₀] B l) := fun l t => by
    rw [mem_torsionIdeal, mem_torsion_iff_toFieldTensor i₀.1 Subtype.val_injective]
    have hcomp : ∀ z : i₀.1 ⊗[R₀] B l,
        toFieldTensor (R₀ := R₀) (K := K) Vs (B l) (tmap hF₀V z) =
          toFieldTensor (R₀ := R₀) (K := K) i₀.1 (B l) z := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, toFieldTensor_tmul, toFieldTensor_tmul]
        rfl
      | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
    rw [← hcomp, ht', ← mem_torsion_iff_toFieldTensor Vs Subtype.val_injective,
      ← mem_torsionIdeal, ← hs l]
    exact Ideal.subset_span t.2
  refine ⟨i₀.1, hF₀V, fun l => Ideal.span (Set.range (t' l)), i₀.2.1, fun l =>
    Ideal.span_le.2 (Set.range_subset_iff.2 (htor l)), fun l => ?_⟩
  rw [Ideal.map_span, ← Set.range_comp, ← hs l]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply, ht']
  constructor
  · rintro ⟨t, rfl⟩
    exact t.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Descent of flatness from a subalgebra `W ⊆ K` to one of its finitely generated
subalgebras (`Limits.FlatDescent.flat_tensor_of_flat_tensor_union` for the system of finitely
generated subalgebras). -/
theorem exists_flat_fgSubalgebra {F₀ L : Type u} [CommRing F₀] [IsNoetherianRing F₀] [CommRing L]
    [Algebra F₀ L] (W : Subalgebra F₀ L) (B₀ : Type*) [CommRing B₀] [Algebra F₀ B₀]
    [Algebra.FiniteType F₀ B₀] [Module.Flat W (W ⊗[F₀] B₀)] :
    ∃ i : FGSubalgebra F₀ W, ∀ j, fgSubalgebraFamily W i ≤ fgSubalgebraFamily W j →
      Module.Flat (fgSubalgebraFamily W j) (fgSubalgebraFamily W j ⊗[F₀] B₀) := by
  have hR : ∀ x ∈ W, ∃ i : FGSubalgebra F₀ W, x ∈ fgSubalgebraFamily W i :=
    fun _ hx => exists_mem hx
  have hnoeth : ∀ i : FGSubalgebra F₀ W, IsNoetherianRing (fgSubalgebraFamily W i) := fun i => by
    have : Algebra.FiniteType F₀ i.1 := (Subalgebra.fg_iff_finiteType _).1 i.2.1
    exact Algebra.FiniteType.isNoetherianRing F₀ i.1
  exact flat_tensor_of_flat_tensor_union (fgSubalgebraFamily W) W fgSubalgebraFamily_le hR
    hnoeth B₀

omit [IsNoetherianRing R₀] in
/-- The strict transform over `V`, written over a finitely generated `F₀ ⊆ V` whose tensor
product with `B` contains generators `J` of the torsion: `V ⊗_{F₀} ((F₀ ⊗_{R₀} B) ⧸ J)` is flat
over `V`. -/
theorem flat_tensor_quotient_of_valuationSubring (V : ValuationSubring K)
    (hV : ∀ r : R₀, algebraMap R₀ K r ∈ V) (B : Type u) [CommRing B] [Algebra R₀ B]
    (F₀ : Subalgebra R₀ K) (hF₀V : F₀ ≤ subalgebraOfValuationSubring V hV)
    (J : Ideal (F₀ ⊗[R₀] B))
    (hJ : J.map (tmap (P₀ := B) hF₀V) =
      torsionIdeal (subalgebraOfValuationSubring V hV)
        (subalgebraOfValuationSubring V hV ⊗[R₀] B)) :
    Module.Flat (subalgebraOfValuationSubring (R₀ := F₀) V fun x => hF₀V x.2)
      (subalgebraOfValuationSubring (R₀ := F₀) V (fun x => hF₀V x.2) ⊗[F₀]
        ((F₀ ⊗[R₀] B) ⧸ J)) := by
  have : ValuationRing (subalgebraOfValuationSubring (R₀ := F₀) V fun x => hF₀V x.2) :=
    inferInstanceAs (ValuationRing V)
  refine flat_tensor_quotient_of_map_eq J ?_
  have hfun : (⇑(Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ F₀
      (subalgebraOfValuationSubring (R₀ := F₀) V fun x => hF₀V x.2)) (AlgHom.id R₀ B)) :
        F₀ ⊗[R₀] B → (subalgebraOfValuationSubring (R₀ := F₀) V fun x => hF₀V x.2) ⊗[R₀] B) =
      ⇑(tmap (P₀ := B) hF₀V) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; rfl
    | tmul a b => rfl
    | add u v hu hv => rw [map_add, map_add, hu, hv]; rfl
  change Ideal.span (_ '' _) = _
  rw [hfun]
  exact hJ

omit [IsNoetherianRing R₀] in
/-- From the flat model over `F₀` to the strict transform: if `F₀ → G` is injective with `G` a
domain, `J ⊆ F₀ ⊗_{R₀} B` consists of `F₀`-torsion elements and `G ⊗_{F₀} ((F₀ ⊗ B) ⧸ J)` is
flat over `G`, then `(G ⊗_{R₀} B) ⧸ torsion` is flat over `G`. -/
theorem flat_quotient_torsion_of_flat_model {F₀ G B : Type*} [CommRing F₀] [Algebra R₀ F₀]
    [CommRing G] [IsDomain G] [Algebra F₀ G] [Algebra R₀ G] [IsScalarTower R₀ F₀ G]
    (hFG : Function.Injective (algebraMap F₀ G)) [CommRing B] [Algebra R₀ B]
    (J : Ideal (F₀ ⊗[R₀] B)) (hJtor : ∀ x ∈ J, ∃ a : F₀, a ≠ 0 ∧ a • x = 0)
    [Module.Flat G (G ⊗[F₀] ((F₀ ⊗[R₀] B) ⧸ J))] :
    Module.Flat G ((G ⊗[R₀] B) ⧸ Submodule.torsion G (G ⊗[R₀] B)) := by
  have h1 := flat_quotient_torsion_of_flat_quotient_ideal (R := F₀) (A := G) J
    (fun x hx => by
      obtain ⟨a, ha, hax⟩ := hJtor x hx
      refine (mem_torsion_iff_of_isDomain _).2 ⟨algebraMap F₀ G a, ?_, ?_⟩
      · rw [Ne, ← map_zero (algebraMap F₀ G)]
        exact fun h => ha (hFG h)
      · rw [algebraMap_smul, ← TensorProduct.tmul_smul, hax, TensorProduct.tmul_zero])
  exact flat_quotient_torsion_of_linearEquiv (AlgebraTensorModule.cancelBaseChange R₀ F₀ G G B)

/-- Descent of flatness for finitely many algebras at once: if `W ⊗_{F₀} B₀ l` is flat over `W`
for all `l`, then `G ⊗_{F₀} B₀ l` is flat over `G` for all `l`, for one finitely generated
`G ⊆ W`. -/
theorem exists_fgSubalgebra_flat {F₀ L : Type u} [CommRing F₀] [IsNoetherianRing F₀] [CommRing L]
    [Algebra F₀ L] (W : Subalgebra F₀ L) {ι : Type*} [Finite ι] (B₀ : ι → Type*)
    [∀ l, CommRing (B₀ l)] [∀ l, Algebra F₀ (B₀ l)] [∀ l, Algebra.FiniteType F₀ (B₀ l)]
    [∀ l, Module.Flat W (W ⊗[F₀] B₀ l)] :
    ∃ G : Subalgebra F₀ L, G.FG ∧ G ≤ W ∧ ∀ l, Module.Flat G (G ⊗[F₀] B₀ l) := by
  have hdesc : ∀ l, ∃ i : FGSubalgebra F₀ W, ∀ j, fgSubalgebraFamily W i ≤
      fgSubalgebraFamily W j → Module.Flat (fgSubalgebraFamily W j)
        (fgSubalgebraFamily W j ⊗[F₀] B₀ l) := fun l => exists_flat_fgSubalgebra W (B₀ l)
  choose jdx hjdx using hdesc
  obtain ⟨i, hi⟩ := Finite.exists_le jdx
  exact ⟨i.1, i.2.1, i.2.2, fun l => hjdx l i ((fgSubalgebraFamily W).monotone (hi l))⟩

omit [IsNoetherianRing R₀] in
/-- From a flat model over `F₀ ⊆ G` to the strict transform over `G`, viewed as an
`R₀`-subalgebra. -/
theorem flat_quotient_torsion_restrictScalars {B : Type u} [CommRing B] [Algebra R₀ B]
    (F₀ : Subalgebra R₀ K) (G : Subalgebra F₀ K) (J : Ideal (F₀ ⊗[R₀] B))
    (hJtor : J ≤ torsionIdeal F₀ (F₀ ⊗[R₀] B)) [Module.Flat G (G ⊗[F₀] ((F₀ ⊗[R₀] B) ⧸ J))] :
    Module.Flat (G.restrictScalars R₀) ((G.restrictScalars R₀ ⊗[R₀] B) ⧸
      Submodule.torsion (G.restrictScalars R₀) (G.restrictScalars R₀ ⊗[R₀] B)) := by
  set F : Subalgebra R₀ K := G.restrictScalars R₀
  have hF₀F : F₀ ≤ F := fun x hx => G.algebraMap_mem (⟨x, hx⟩ : F₀)
  let _ : Algebra F₀ F := (Subalgebra.inclusion hF₀F).toRingHom.toAlgebra
  have _ : IsScalarTower R₀ F₀ F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra G F := (RingHom.codRestrict (G.val : G →+* K) F fun x => x.2).toAlgebra
  have _ : IsScalarTower F₀ G F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat F (F ⊗[F₀] ((F₀ ⊗[R₀] B) ⧸ J)) :=
    Module.Flat.of_linearEquiv
      (AlgebraTensorModule.cancelBaseChange F₀ G F F ((F₀ ⊗[R₀] B) ⧸ J)).symm
  refine flat_quotient_torsion_of_flat_model (F₀ := F₀) (G := F) ?_ J fun x hx =>
    (mem_torsion_iff_of_isDomain x).1 (mem_torsionIdeal.1 (hJtor hx))
  intro a b h
  exact Subtype.val_injective (congrArg (fun z : F => (z : K)) h)

/-- The spreading step with the torsion generators given: for `F₀ ⊆ K` finitely generated, a
subalgebra `W ⊆ V` over `F₀` with `W ⊗_{F₀} ((F₀ ⊗ B l) ⧸ J l)` flat, and `J l` consisting of
`F₀`-torsion elements, some finitely generated `F ⊆ V` has flat strict transforms. -/
theorem exists_flat_quotient_torsion_of_generators (V : ValuationSubring K) {ι : Type*}
    [Finite ι] (B : ι → Type u) [∀ l, CommRing (B l)] [∀ l, Algebra R₀ (B l)]
    [∀ l, Algebra.FiniteType R₀ (B l)] (F₀ : Subalgebra R₀ K) (hF₀fg : F₀.FG)
    (W : Subalgebra F₀ K) (hWV : ∀ x ∈ W, x ∈ V) (J : ∀ l, Ideal (F₀ ⊗[R₀] B l))
    (hJtor : ∀ l, J l ≤ torsionIdeal F₀ (F₀ ⊗[R₀] B l))
    (hflat : ∀ l, Module.Flat W (W ⊗[F₀] ((F₀ ⊗[R₀] B l) ⧸ J l))) :
    ∃ F : Subalgebra R₀ K, F.FG ∧ (∀ x ∈ F, x ∈ V) ∧
      ∀ l, Module.Flat F ((F ⊗[R₀] B l) ⧸ Submodule.torsion F (F ⊗[R₀] B l)) := by
  have : Algebra.FiniteType R₀ F₀ := (Subalgebra.fg_iff_finiteType _).1 hF₀fg
  have : IsNoetherianRing F₀ := Algebra.FiniteType.isNoetherianRing R₀ F₀
  have : ∀ l, Module.Flat W (W ⊗[F₀] ((F₀ ⊗[R₀] B l) ⧸ J l)) := hflat
  obtain ⟨G, hGfg, hGW, hG⟩ := exists_fgSubalgebra_flat W (fun l => (F₀ ⊗[R₀] B l) ⧸ J l)
  refine ⟨G.restrictScalars R₀, ?_, fun x hx => hWV _ (hGW hx), fun l => ?_⟩
  · have : Algebra.FiniteType F₀ G := (Subalgebra.fg_iff_finiteType _).1 hGfg
    have : Algebra.FiniteType R₀ G := Algebra.FiniteType.trans (S := F₀) inferInstance
      inferInstance
    exact (Subalgebra.fg_iff_finiteType (G.restrictScalars R₀)).2 this
  · have := hG l
    exact flat_quotient_torsion_restrictScalars F₀ G (J l) (hJtor l)

/-- **Lemma `lem:sm-strict-transform-spread`.** Let `R₀` be noetherian, `V ⊆ K` a valuation ring
containing the image of `R₀`, and `B l` (`l` in a finite type) `R₀`-algebras of finite type.
There is a finitely generated `R₀`-subalgebra `F ⊆ V` of `K` such that every strict transform
`(F ⊗_{R₀} B l) ⧸ torsion` is flat over `F`. -/
theorem exists_flat_quotient_torsion (V : ValuationSubring K)
    (hV : ∀ r : R₀, algebraMap R₀ K r ∈ V) {ι : Type*} [Finite ι] (B : ι → Type u)
    [∀ l, CommRing (B l)] [∀ l, Algebra R₀ (B l)] [∀ l, Algebra.FiniteType R₀ (B l)] :
    ∃ F : Subalgebra R₀ K, F.FG ∧ (∀ x ∈ F, x ∈ V) ∧
      ∀ l, Module.Flat F ((F ⊗[R₀] B l) ⧸ Submodule.torsion F (F ⊗[R₀] B l)) := by
  obtain ⟨F₀, hF₀V, J, hF₀fg, hJtor, hJ⟩ := exists_fg_torsion_generators V hV B
  exact exists_flat_quotient_torsion_of_generators V B F₀ hF₀fg
    (subalgebraOfValuationSubring (R₀ := F₀) V fun x => hF₀V x.2) (fun _ hx => hx) J hJtor
    fun l => flat_tensor_quotient_of_valuationSubring V hV (B l) F₀ hF₀V (J l) (hJ l)

end Spread

end DeJongAlterations.StableModification.Flattening
