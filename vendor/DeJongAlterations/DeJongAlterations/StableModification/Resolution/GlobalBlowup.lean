import DeJongAlterations.StableModification.Resolution.GlobalStep
import DeJongAlterations.StableModification.Resolution.StrictifyStep

/-!
# The blowup steps of the resolution on schemes

Let `X` be an integral scheme of finite type over an algebraically closed field `k`, of dimension
`m + 1`, with a singular-locus ideal sheaf `N` and boundary ideal sheaves `E β`.
`GoodAt k m N E Q x` says that at `x` there is a formal node chart (`NodeChart`) whose
combinatorial data `(n, exp)` satisfy `Q`, or a formal regular chart (`RegChart`) at which `N` is
trivial.

For a closed subset `W ≠ X`, the blowup `π : X' → X` along the reduced structure of `W`
(Codex's `Geometry.BlowupGluing.blowup`) carries the transformed singular-locus ideal
`transformN W N = (N 𝒪' : I(W) 𝒪')` and the pulled back boundary ideals. At a closed point
`y ∈ X'`, the stalk map is a localization of a blowup chart (`hasChartData_blowupStructure`, lane
END-SNC) over `π y ∈ W`, and an isomorphism over `π y ∉ W`
(`isIso_stalkMap_blowupStructure`). Hence:

* `goodAt_blowup_branch` (de Jong 1996, 3.4): if the trace of `I(W)` at every closed point of `W`
  is a branch centre `(U, V, Z_a)` (`n_a ≥ 2`) of a node chart, the blowup has charts at all its
  closed points (`branch_step`, `NodeChart.transport`, `RegChart.transport`);
* `goodAt_blowup_crossing` (de Jong 1996, 4.27): the same for crossing centres
  `(U, V, Z_a, Z_b)` (`n_a = n_b = 1`, `crossing_step`);
* `exists_blowup_goodAt`: the blowup is an integral projective modification
  (`Geometry.BlowupModification.blowupStructure_isModification`,
  `Geometry.BlowupProjective.blowupStructure_comp_isProjective`).

Blueprint: `lem:sm-dj-blowup-chart-data`, `lem:sm-dj-chart-away`, `prop:sm-dj-stage-one`,
`prop:sm-dj-stage-two` (chapter `sm-dj-resolution-global.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Global

set_option backward.isDefEq.respectTransparency false

open Strictify Algebra.NodeFittingIdealSheaf Geometry.BlowupGluing
open Algebra.CompletionRegularityBasics

universe u

section Charts

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X] {ι : Type*}

variable (k) in
/-- **Formal charts at a point** for the singular-locus ideal sheaf `N` and the boundary ideal
sheaves `E`: a node chart whose combinatorial data satisfy `Q`, or a regular chart at which `N` is
trivial. -/
def GoodAt (m : ℕ) (N : X.IdealSheafData) (E : ι → X.IdealSheafData)
    (Q : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop) (x : X) : Prop :=
  (∃ c : NodeChart k (X.presheaf.stalk x) m (stalkIdeal N x) (fun β ↦ stalkIdeal (E β) x),
    Q c.n c.exp) ∨
  (Nonempty (RegChart (X.presheaf.stalk x) m (fun β ↦ stalkIdeal (E β) x)) ∧
    stalkIdeal N x = ⊤)

/-- The transformed singular-locus ideal sheaf `(N 𝒪' : I(W) 𝒪')` on the blowup along `W`. -/
def transformN (W : Closeds X) (N : X.IdealSheafData) :
    (blowup (Scheme.IdealSheafData.vanishingIdeal W)).IdealSheafData :=
  colonIdealSheaf (N.comap (blowupStructure (Scheme.IdealSheafData.vanishingIdeal W)))
    ((Scheme.IdealSheafData.vanishingIdeal W).comap
      (blowupStructure (Scheme.IdealSheafData.vanishingIdeal W)))

theorem stalkIdeal_transformN (W : Closeds X) (N : X.IdealSheafData)
    (y : blowup (Scheme.IdealSheafData.vanishingIdeal W)) :
    stalkIdeal (transformN W N) y =
      ((stalkIdeal N (blowupStructure (Scheme.IdealSheafData.vanishingIdeal W) y)).map
        ((blowupStructure (Scheme.IdealSheafData.vanishingIdeal W)).stalkMap y).hom).colon
        (((localIdeal W (blowupStructure (Scheme.IdealSheafData.vanishingIdeal W) y)).map
          ((blowupStructure (Scheme.IdealSheafData.vanishingIdeal W)).stalkMap y).hom :
            Ideal _) : Set _) := by
  rw [transformN, stalkIdeal_colonIdealSheaf, stalkIdeal_comap, stalkIdeal_comap]
  rfl

end Charts

section Step

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] {ι : Type*}

set_option hygiene false in
local notation "DW" => Scheme.IdealSheafData.vanishingIdeal W
set_option hygiene false in
local notation "πW" => blowupStructure (Scheme.IdealSheafData.vanishingIdeal W)

/-- **The blowup step along branches, at the closed points of the blowup** (de Jong 3.4). Let `W`
be a closed subset such that at every closed point `x ∈ W` there is a node chart with
`I(W) Ô = (U, V, Z_a)`, `n_a ≥ 2`, the transformed data `(n - 2 e_a, exp)` satisfying `Q`, and
`Q`-charts at the closed points outside `W`. Then the blowup along `W` has `Q`-charts at all its
closed points, for the transformed singular-locus ideal and the pulled back boundary ideals. -/
theorem goodAt_blowup_branch (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] {m : ℕ}
    (hdim : topologicalKrullDim X = (m + 1 : ℕ))
    (N : X.IdealSheafData) (E : ι → X.IdealSheafData) (W : Closeds X) (hW : W ≠ ⊤)
    (Q : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop)
    (hin : ∀ x : X, IsClosed ({x} : Set X) → x ∈ W →
      ∃ c : NodeChart k (X.presheaf.stalk x) m (stalkIdeal N x) (fun β ↦ stalkIdeal (E β) x),
        ∃ a, 2 ≤ c.n a ∧
          (localIdeal W x).map (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)) =
            Ideal.span {c.e (nodeU k c.n), c.e (nodeV k c.n), c.e (nodeZ k c.n a)} ∧
          Q (Function.update c.n a (c.n a - 2)) c.exp)
    (hout : ∀ x : X, IsClosed ({x} : Set X) → x ∉ W → GoodAt k m N E Q x)
    (y : blowup (Scheme.IdealSheafData.vanishingIdeal W)) (hy : IsClosed ({y} : Set _)) :
    GoodAt k m (transformN W N)
      (fun β ↦ (E β).comap (blowupStructure (Scheme.IdealSheafData.vanishingIdeal W))) Q y := by
  classical
  have hD : (DW).support ≠ ⊤ := by rwa [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
  have hmod : IsModification πW :=
    Geometry.BlowupModification.blowupStructure_isModification _ hD
  have : IsIntegral (blowup (DW)) := hmod.sourceIntegral
  have : LocallyOfFiniteType (πW ≫ p) := inferInstance
  have hx : IsClosed ({πW y} : Set X) := by
    have := (πW).isClosedMap _ hy
    rwa [Set.image_singleton] at this
  have hE' : (fun β ↦ stalkIdeal ((E β).comap πW) y) =
      fun β ↦ (stalkIdeal (E β) (πW y)).map ((πW).stalkMap y).hom := by
    funext β; exact stalkIdeal_comap _ _ _
  unfold GoodAt
  rw [hE', stalkIdeal_transformN]
  by_cases hxW : πW y ∈ W
  · obtain ⟨c, a, hna, htr, hQ⟩ := hin (πW y) hx hxW
    let : Algebra k (X.presheaf.stalk (πW y)) := (Scheme.baseToStalk p (πW y)).hom.toAlgebra
    let : Algebra k ((blowup (DW)).presheaf.stalk y) :=
      (Scheme.baseToStalk (πW ≫ p) y).hom.toAlgebra
    have hφk : ∀ a : k, ((πW).stalkMap y).hom (algebraMap k _ a) = algebraMap k _ a := by
      intro a
      have h := Scheme.baseToStalk_comp_stalkMap πW p y
      exact congrArg (fun f ↦ f.hom a) h
    have hresO : Function.Surjective (algebraMap k (ResidueField (X.presheaf.stalk (πW y)))) :=
      residue_comp_baseToStalk_surjective' p (πW y) hx
    have hresP : Function.Bijective
        (algebraMap k (ResidueField ((blowup (DW)).presheaf.stalk y))) :=
      ⟨(algebraMap k _).injective, residue_comp_baseToStalk_surjective' (πW ≫ p) y hy⟩
    have hdim' : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim ((blowup (DW)).presheaf.stalk y) := by
      rw [ringKrullDim_stalk_eq_of_isClosed (πW ≫ p) y hy,
        DeJong.topologicalKrullDim_eq_of_isModification p πW, hdim]
      simp
    obtain ⟨g, hg, hgen, hIg, hg0⟩ := hasChartData_blowupStructure W y
    rcases branch_step ((πW).stalkMap y).hom hφk hresO hresP c a hna _ htr g hg hIg hg0 hgen
      hdim' with ⟨c', hn', hexp'⟩ | ⟨hreg, htop⟩
    · exact Or.inl ⟨c', by rw [hn', hexp']; exact hQ⟩
    · refine Or.inr ⟨hreg, ?_⟩
      rw [← comap_map _ (((stalkIdeal N (πW y)).map _).colon _), htop, Ideal.comap_top]
  · have hyD : πW y ∉ (DW).support := by
      rwa [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
    have := isIso_stalkMap_blowupStructure _ y hyD
    let σ := (asIso ((πW).stalkMap y)).commRingCatIsoToRingEquiv
    have hσ : (σ : X.presheaf.stalk (πW y) →+* _) = ((πW).stalkMap y).hom := rfl
    have htop : localIdeal W (πW y) = ⊤ := by
      by_contra h
      exact hxW ((localIdeal_ne_top_iff W (πW y)).mp h)
    rw [htop, Ideal.map_top, Submodule.top_coe, Submodule.colon_univ, ← hσ]
    rcases hout (πW y) hx hxW with ⟨c, hQ⟩ | ⟨⟨r⟩, hN⟩
    · obtain ⟨c', hn', hexp'⟩ := c.transport σ
      exact Or.inl ⟨c', by rw [hn', hexp']; exact hQ⟩
    · refine Or.inr ⟨r.transport σ, ?_⟩
      rw [hN, Ideal.map_top]

open Classical in
/-- **The blowup step along crossings, at the closed points of the blowup** (de Jong 4.27). Let
`W` be a closed subset such that at every closed point `x ∈ W` there is a node chart with
`I(W) Ô = (U, V, Z_a, Z_b)`, `n_a = n_b = 1`, all possible transformed data of
`crossing_step` satisfying `Q`, and `Q`-charts at the closed points outside `W`. Then the blowup
along `W` has `Q`-charts at all its closed points. -/
theorem goodAt_blowup_crossing (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] {m : ℕ}
    (hdim : topologicalKrullDim X = (m + 1 : ℕ))
    (N : X.IdealSheafData) (E : ι → X.IdealSheafData) (W : Closeds X) (hW : W ≠ ⊤)
    (Q : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop)
    (hin : ∀ x : X, IsClosed ({x} : Set X) → x ∈ W →
      ∃ c : NodeChart k (X.presheaf.stalk x) m (stalkIdeal N x) (fun β ↦ stalkIdeal (E β) x),
        ∃ a b, a ≠ b ∧ c.n a = 1 ∧ c.n b = 1 ∧
          (localIdeal W x).map (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)) =
            Ideal.span {c.e (nodeU k c.n), c.e (nodeV k c.n), c.e (nodeZ k c.n a),
              c.e (nodeZ k c.n b)} ∧
          ∀ a' b' δ, ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) → δ ≤ 1 →
            Q (Function.update (Function.update c.n a' 0) b' δ) (fun β ↦ Function.update
              (Function.update (c.exp β) a' (c.exp β a' + c.exp β b')) b' (δ * c.exp β b')))
    (hout : ∀ x : X, IsClosed ({x} : Set X) → x ∉ W → GoodAt k m N E Q x)
    (y : blowup (Scheme.IdealSheafData.vanishingIdeal W)) (hy : IsClosed ({y} : Set _)) :
    GoodAt k m (transformN W N)
      (fun β ↦ (E β).comap (blowupStructure (Scheme.IdealSheafData.vanishingIdeal W))) Q y := by
  classical
  have hD : (DW).support ≠ ⊤ := by rwa [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
  have hmod : IsModification πW :=
    Geometry.BlowupModification.blowupStructure_isModification _ hD
  have : IsIntegral (blowup (DW)) := hmod.sourceIntegral
  have : LocallyOfFiniteType (πW ≫ p) := inferInstance
  have hx : IsClosed ({πW y} : Set X) := by
    have := (πW).isClosedMap _ hy
    rwa [Set.image_singleton] at this
  have hE' : (fun β ↦ stalkIdeal ((E β).comap πW) y) =
      fun β ↦ (stalkIdeal (E β) (πW y)).map ((πW).stalkMap y).hom := by
    funext β; exact stalkIdeal_comap _ _ _
  unfold GoodAt
  rw [hE', stalkIdeal_transformN]
  by_cases hxW : πW y ∈ W
  · obtain ⟨c, a, b, hab, hna, hnb, htr, hQ⟩ := hin (πW y) hx hxW
    let : Algebra k (X.presheaf.stalk (πW y)) := (Scheme.baseToStalk p (πW y)).hom.toAlgebra
    let : Algebra k ((blowup (DW)).presheaf.stalk y) :=
      (Scheme.baseToStalk (πW ≫ p) y).hom.toAlgebra
    have hφk : ∀ a : k, ((πW).stalkMap y).hom (algebraMap k _ a) = algebraMap k _ a := by
      intro a
      have h := Scheme.baseToStalk_comp_stalkMap πW p y
      exact congrArg (fun f ↦ f.hom a) h
    have hresO : Function.Surjective (algebraMap k (ResidueField (X.presheaf.stalk (πW y)))) :=
      residue_comp_baseToStalk_surjective' p (πW y) hx
    have hresP : Function.Bijective
        (algebraMap k (ResidueField ((blowup (DW)).presheaf.stalk y))) :=
      ⟨(algebraMap k _).injective, residue_comp_baseToStalk_surjective' (πW ≫ p) y hy⟩
    have hdim' : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim ((blowup (DW)).presheaf.stalk y) := by
      rw [ringKrullDim_stalk_eq_of_isClosed (πW ≫ p) y hy,
        DeJong.topologicalKrullDim_eq_of_isModification p πW, hdim]
      simp
    obtain ⟨g, hg, hgen, hIg, hg0⟩ := hasChartData_blowupStructure W y
    rcases crossing_step ((πW).stalkMap y).hom hφk hresO hresP c hab hna hnb _ htr g hg hIg hg0
      hgen hdim' with ⟨a', b', hab', δ, hδ, c', hn', hexp'⟩ | ⟨hreg, htop⟩
    · exact Or.inl ⟨c', by rw [hn', hexp']; exact hQ a' b' δ hab' hδ⟩
    · refine Or.inr ⟨hreg, ?_⟩
      rw [← comap_map _ (((stalkIdeal N (πW y)).map _).colon _), htop, Ideal.comap_top]
  · have hyD : πW y ∉ (DW).support := by
      rwa [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
    have := isIso_stalkMap_blowupStructure _ y hyD
    let σ := (asIso ((πW).stalkMap y)).commRingCatIsoToRingEquiv
    have hσ : (σ : X.presheaf.stalk (πW y) →+* _) = ((πW).stalkMap y).hom := rfl
    have htop : localIdeal W (πW y) = ⊤ := by
      by_contra h
      exact hxW ((localIdeal_ne_top_iff W (πW y)).mp h)
    rw [htop, Ideal.map_top, Submodule.top_coe, Submodule.colon_univ, ← hσ]
    rcases hout (πW y) hx hxW with ⟨c, hQ⟩ | ⟨⟨r⟩, hN⟩
    · obtain ⟨c', hn', hexp'⟩ := c.transport σ
      exact Or.inl ⟨c', by rw [hn', hexp']; exact hQ⟩
    · refine Or.inr ⟨r.transport σ, ?_⟩
      rw [hN, Ideal.map_top]

omit [IsAlgClosed k] in
/-- **Packaging one blowup.** If the blowup along `W ≠ X` has `Q`-charts at all its closed points,
it is an integral locally Noetherian projective modification carrying them. -/
theorem exists_blowup_goodAt (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hp : IsProjectiveOver p) {m : ℕ} (N : X.IdealSheafData) (E : ι → X.IdealSheafData)
    (W : Closeds X) (hW : W ≠ ⊤) (Q : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop)
    (h : ∀ y : blowup (Scheme.IdealSheafData.vanishingIdeal W), IsClosed ({y} : Set _) →
      GoodAt k m (transformN W N) (fun β ↦ (E β).comap πW) Q y) :
    ∃ (X' : Scheme.{u}) (_ : IsIntegral X') (_ : IsLocallyNoetherian X') (π : X' ⟶ X)
      (N' : X'.IdealSheafData), IsModification π ∧ IsProjectiveOver (π ≫ p) ∧
      ∀ y : X', IsClosed ({y} : Set X') → GoodAt k m N' (fun β ↦ (E β).comap π) Q y := by
  have hD : (DW).support ≠ ⊤ := by rwa [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
  have hmod : IsModification πW :=
    Geometry.BlowupModification.blowupStructure_isModification _ hD
  exact ⟨_, hmod.sourceIntegral, inferInstance, πW, transformN W N, hmod,
    Geometry.BlowupProjective.blowupStructure_comp_isProjective _ p hp, h⟩

end Step

end DeJongAlterations.StableModification.Resolution.Global
