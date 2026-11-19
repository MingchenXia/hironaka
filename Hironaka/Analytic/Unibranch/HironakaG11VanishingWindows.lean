import Hironaka.Analytic.Unibranch.HironakaG11InvLocalEmbeddingStabilize
import Hironaka.Analytic.Unibranch.HironakaG11CompatibleLevelSets
import Hironaka.Resolution.HironakaG11InvAmbientIso
import Hironaka.Resolution.HironakaEmbeddedReducible

/-!
# Compatible first-stage centres of the vanishing-ideal records (goal G11, vanishing route)

End-to-end wiring of lane G11B's embedding independence into the gluing of lane G11A, for the
vanishing-ideal records `(univ, [], 𝓘_C, 1)` of the carriers `C` of local embeddings (the route of
the human decision I-1296 C-0001 run in parallel with the Hilbert–Samuel records):

windows → stabilized common dimension → ambient biholomorphism `Φ` → agreement of the values on
overlaps → compatible level-set centres → glued centre (analytic) → glued blowup.

* `DimEmbedding X N`: local embeddings of the fixed ambient dimension `N` (so that the values of a
  route invariant on several windows lie in one type); `DimEmbedding.raise` stabilizes a local
  embedding of dimension `< N` to dimension `N` (`HironakaG11InvLocalEmbeddingStabilize.stabilizeN`)
  with the same image (`range_toPoint_raise`) and a thin carrier (`interior_carrier_raise`, from
  `interior_liftedCarrier_eq_empty`), so that its vanishing record lies in the domain of the
  invariants (`isInvDomain_windowRecord`, Cartan's coherence).
* **`vanishingValue_eq_of_toPoint_eq`**: the first-stage values of a route invariant on the
  vanishing records of two windows of dimension `N` agree at points with the same image in `X`
  (`HironakaG11InvLocalEmbeddingIso.exists_ambient_biholomorphism` +
  `HironakaG11InvTransport.inv_vanishingRecord_eq_on_overlap`).
* `levelSetCentres`: the `λ`-level sets of these values on the carriers, closed submanifolds by the
  admissibility of the route invariant, for any common bound `λ` (e.g. the global maximum);
  **`levelSetCentres_compatible`**, `preimage_support_levelSetCentres`,
  `isAnalyticSubset_support_levelSetCentres` (the glued centre is an analytic subset of `X` when the
  windows cover it), `exists_singularCentreBlowup_levelSetCentres` (the glued blowup when the glued
  centre is closed and singular);
* **`raisedWindows_levelSetCentres`**: for ANY family of local embeddings, raised to a common
  dimension above all of theirs, the level-set centres are compatible and glue to an analytic subset.

Only the FIRST stage (no tower) is wired here. The vanishing-record centres need not lie in the
singular locus (that is the hypothesis of the blowup step), and the Hilbert–Samuel route is not
touched. Nothing here proves or assumes G11. Blueprint: `hironaka-g11-resume-vanishing-windows.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11VanishingWindows

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaReducedComplexAnalyticSpaces
  HironakaG11InvLocalEmbeddingStabilize HironakaG11CompatibleAnalyticCover HironakaG11CompatibleLevelSets
  BlowupTowers MarkedIdeals ResolutionInvariantSeq OriginalAnalyticClosedSubspaceSmoothCentres
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain)
open _root_.Hironaka.HironakaG11InvTransport (vanishingRecord inv_vanishingRecord_eq_on_overlap)
open _root_.Hironaka.MaxLocusLocal (nestedOpens nestedOpensDiffeo)
open _root_.Hironaka.BlowupTowerIsomorphism (IsTowerIso)
open _root_.Hironaka.HironakaActualIntrinsicIsoPairedWindows (coordinateCarrier)

noncomputable section

variable {X : SourceReducedComplexSpace}

/-! ### Local embeddings of a fixed ambient dimension -/

/-- A local embedding of `X` whose ambient dimension is the fixed number `N` (so that invariants of
several windows take values in one type). -/
structure DimEmbedding (X : SourceReducedComplexSpace) (N : ℕ) where
  /-- The ambient open set `Ω ⊆ ℂ^N`. -/
  ambient : Opens (ComplexModel N)
  /-- The closed analytic subset carrying the model. -/
  carrier : Set ambient
  analytic : IsComplexAnalyticSubset (n := N) carrier
  /-- The open immersion of the model into `X`. -/
  map : (modelOver ambient carrier).left ⟶ X.obj.left
  isOpenImmersion : LocallyRingedSpace.IsOpenImmersion map
  overPoint : map ≫ X.obj.hom = (modelOver ambient carrier).hom

namespace DimEmbedding

variable {N M : ℕ}

/-- The underlying local embedding (of dimension `N`, definitionally). -/
abbrev toLocalEmbedding (w : DimEmbedding X N) : LocalEmbedding X :=
  ⟨N, w.ambient, w.carrier, w.analytic, w.map, w.isOpenImmersion, w.overPoint⟩

/-- A local embedding as an embedding of its own dimension. -/
def ofLocalEmbedding (e : LocalEmbedding X) : DimEmbedding X e.dim :=
  ⟨e.ambient, e.carrier, e.analytic, e.map, e.isOpenImmersion, e.overPoint⟩

theorem toLocalEmbedding_ofLocalEmbedding (e : LocalEmbedding X) :
    (ofLocalEmbedding e).toLocalEmbedding = e := rfl

/-- Transport along an equality of dimensions. -/
def cast (h : N = M) (w : DimEmbedding X N) : DimEmbedding X M := h ▸ w

theorem range_toPoint_cast (h : N = M) (w : DimEmbedding X N) :
    range (w.cast h).toLocalEmbedding.toPoint = range w.toLocalEmbedding.toPoint := by
  subst h
  rfl

/-- **Raising the ambient dimension**: a local embedding of dimension `≤ N`, stabilized to
dimension `N` (`stabilizeN`), with the same image in `X`. -/
def raise (e : LocalEmbedding X) (N : ℕ) (h : e.dim ≤ N) : DimEmbedding X N :=
  (ofLocalEmbedding (stabilizeN e (N - e.dim))).cast (by rw [stabilizeN_dim]; omega)

theorem range_toPoint_raise (e : LocalEmbedding X) (N : ℕ) (h : e.dim ≤ N) :
    range (raise e N h).toLocalEmbedding.toPoint = range e.toPoint := by
  rw [raise, range_toPoint_cast, toLocalEmbedding_ofLocalEmbedding]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact stabilizeN_toPoint_mem_range e _ z
  · rintro ⟨c, rfl⟩
    obtain ⟨c', hc'⟩ := exists_stabilizeN_point e c (N - e.dim)
    exact ⟨c', hc'⟩

theorem interior_carrier_cast (h : N = M) (w : DimEmbedding X N) :
    interior (w.cast h).carrier = ∅ ↔ interior w.carrier = ∅ := by
  subst h
  rfl

end DimEmbedding

/-- **Stabilized carriers are thin**: the carrier `C × 0 ⊆ Ω × ℂ` of a stabilization has empty
interior (it lies in the kernel of the last coordinate). -/
theorem interior_liftedCarrier_eq_empty {n : ℕ} {U : Opens (ComplexModel n)} (A : Set U) :
    interior (HironakaActualOpenZeroSectionDifferentials.liftedCarrier A) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  let L := HironakaActualCentreJointJets.actualJointNormalProjection n 1
  have hsub : (Subtype.val : HironakaActualOpenZeroSectionDifferentials.productOpen U →
      ComplexModel (n + 1)) '' interior (HironakaActualOpenZeroSectionDifferentials.liftedCarrier A) ⊆
        ((LinearMap.ker (L : ComplexModel (n + 1) →ₗ[ℂ] ComplexModel 1) : Submodule ℂ (ComplexModel (n + 1))) : Set (ComplexModel (n + 1))) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (interior_subset hy).2
  have hopen : IsOpen ((Subtype.val : HironakaActualOpenZeroSectionDifferentials.productOpen U →
      ComplexModel (n + 1)) '' interior (HironakaActualOpenZeroSectionDifferentials.liftedCarrier A)) :=
    (HironakaActualOpenZeroSectionDifferentials.productOpen U).isOpen.isOpenMap_subtype_val _
      isOpen_interior
  have hne : (interior ((LinearMap.ker (L : ComplexModel (n + 1) →ₗ[ℂ] ComplexModel 1) : Submodule ℂ (ComplexModel (n + 1))) : Set (ComplexModel (n + 1)))).Nonempty :=
    ⟨z.val, interior_maximal hsub hopen ⟨z, hz, rfl⟩⟩
  have htop := Submodule.eq_top_of_nonempty_interior' _ hne
  have hmem : (EuclideanSpace.single (Fin.natAdd n (0 : Fin 1)) (1 : ℂ) : ComplexModel (n + 1)) ∈
      LinearMap.ker (L : ComplexModel (n + 1) →ₗ[ℂ] ComplexModel 1) := by
    rw [htop]
    exact Submodule.mem_top
  have h0 := congrArg (fun v : ComplexModel 1 => v 0) (LinearMap.mem_ker.mp hmem)
  simp [L] at h0

theorem interior_carrier_stabilizeN (e : LocalEmbedding X) :
    ∀ r, 0 < r → interior (stabilizeN e r).carrier = ∅
  | r + 1, _ => interior_liftedCarrier_eq_empty (stabilizeN e r).carrier

namespace DimEmbedding

/-- A local embedding raised to a strictly larger dimension has a thin carrier. -/
theorem interior_carrier_raise (e : LocalEmbedding X) (N : ℕ) (h : e.dim < N) :
    interior (raise e N h.le).carrier = ∅ := by
  unfold raise
  rw [interior_carrier_cast]
  exact interior_carrier_stabilizeN e (N - e.dim) (by omega)

end DimEmbedding

/-! ### Agreement of the first-stage values on overlaps -/

variable {N k : ℕ} {Λ : Type*} [LinearOrder Λ]

/-- The vanishing-ideal record `(univ, [], 𝓘_C, 1)` of the carrier of a window. -/
abbrev windowRecord (w : DimEmbedding X N) : MarkedIdeals.MarkedIdeal N (CMfd.of (n := N) w.ambient) :=
  vanishingRecord N (M := CMfd.of (n := N) w.ambient) w.carrier

/-- The first-stage value of a route invariant on the vanishing-ideal record of a window. -/
def vanishingValue (R : ResolutionInvariant.{0} N k Λ) (w : DimEmbedding X N) (x : w.ambient) : Λ :=
  R.inv (X := CMfd.of (n := N) w.ambient) (windowRecord w) BlowupTower.refl x

/-- **The first-stage values of the vanishing-ideal records of two windows of the same ambient
dimension agree at points with the same image in `X`** (G11B's ambient biholomorphism of the two
local embeddings + `inv_vanishingRecord_eq_on_overlap`). -/
theorem vanishingValue_eq_of_toPoint_eq (R : ResolutionInvariant.{0} N k Λ)
    (w₁ w₂ : DimEmbedding X N) (hD₁ : IsInvDomain k (windowRecord w₁))
    (hD₂ : IsInvDomain k (windowRecord w₂)) (y : w₁.carrier) (z : w₂.carrier)
    (hyz : w₁.toLocalEmbedding.toPoint y = w₂.toLocalEmbedding.toPoint z) :
    vanishingValue R w₂ z.val = vanishingValue R w₁ y.val := by
  obtain ⟨A, B, hA, hB, Φ, hzA, hΦz, hcar, -⟩ :=
    HironakaG11InvLocalEmbeddingIso.exists_ambient_biholomorphism w₂.toLocalEmbedding
      w₁.toLocalEmbedding rfl z y hyz.symm
  let Ψ : CMfd.of (n := N) (nestedOpens w₂.ambient A) ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯
      CMfd.of (n := N) (nestedOpens w₁.ambient B) :=
    (nestedOpensDiffeo (n := N) hA).trans (Φ.trans (nestedOpensDiffeo (n := N) hB).symm)
  have hΨ : ∀ p : nestedOpens w₂.ambient A,
      (((Ψ p : nestedOpens w₁.ambient B) : w₁.ambient) : ComplexModel N) =
        (Φ ⟨((p : w₂.ambient) : ComplexModel N), p.property⟩ : ComplexModel N) := fun _ => rfl
  have hΨC : ∀ p : nestedOpens w₂.ambient A,
      ((Ψ p : nestedOpens w₁.ambient B) : w₁.ambient) ∈ w₁.carrier ↔
        (p : w₂.ambient) ∈ w₂.carrier := by
    intro p
    rw [← HironakaG11InvMinimalAmbient.val_mem_coordinateCarrier_iff w₁.carrier, hΨ,
      ← HironakaG11InvMinimalAmbient.val_mem_coordinateCarrier_iff w₂.carrier]
    exact (hcar ⟨((p : w₂.ambient) : ComplexModel N), p.property⟩).symm
  let p : nestedOpens w₂.ambient A := ⟨z.val, hzA⟩
  have hp : ((Ψ p : nestedOpens w₁.ambient B) : w₁.ambient) = y.val := by
    apply Subtype.ext
    rw [hΨ]
    exact hΦz
  have hcos : (windowRecord w₁).cosupp = w₁.carrier :=
    SmoothCentreLocus.cosupp_vanishingIdeal w₁.analytic.isClosed (subset_univ _)
  have hyC : ((Ψ p : nestedOpens w₁.ambient B) : w₁.ambient) ∈ (windowRecord w₁).cosupp := by
    rw [hcos, hp]
    exact y.property
  have h := (inv_vanishingRecord_eq_on_overlap R hD₁ hD₂ (nestedOpens w₁.ambient B)
    (nestedOpens w₂.ambient A) Ψ hΨC (T' := .refl) (T := .refl) trivial trivial (χ := Ψ)
    IsTowerIso.refl p hyC).2
  change R.inv (X := CMfd.of (n := N) w₂.ambient) (windowRecord w₂) BlowupTower.refl
    (p : w₂.ambient) = _
  rw [h]
  exact congrArg (fun x : w₁.ambient =>
    R.inv (X := CMfd.of (n := N) w₁.ambient) (windowRecord w₁) BlowupTower.refl x) hp

/-- A window record lies in the domain of the invariants in dimension `≤ k` (`N ≤ k`) as soon as
its carrier has empty interior in the ambient (Cartan's coherence). -/
theorem isInvDomain_windowRecord {k : ℕ} (hNk : N ≤ k) (w : DimEmbedding X N)
    (hint : interior w.carrier = ∅) : IsInvDomain k (windowRecord w) :=
  HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_interior_eq_empty
    (M := CMfd.of (n := N) w.ambient) hNk w.analytic hint

/-! ### The compatible level-set centres -/

section Family

variable {κ : Type*} (R : ResolutionInvariant.{0} N k Λ) (w : κ → DimEmbedding X N)

/-- The `λ`-level set of the first-stage value on the carrier of the `i`-th window (a subset of the
whole ambient window). -/
def levelCentre (lam : Λ) (i : κ) : Set (⊤ : Opens (w i).ambient) :=
  (Subtype.val : (⊤ : Opens (w i).ambient) → (w i).ambient) ⁻¹'
    {y | y ∈ (windowRecord (w i)).cosupp ∧ vanishingValue R (w i) y = lam}

theorem levelCentre_eq (lam : Λ) (i : κ) :
    levelCentre R w lam i =
      {x | x.val ∈ (w i).carrier} ∩ (fun x : (⊤ : Opens (w i).ambient) => vanishingValue R (w i) x.val) ⁻¹'
        {lam} := by
  have hcos : (windowRecord (w i)).cosupp = (w i).carrier :=
    SmoothCentreLocus.cosupp_vanishingIdeal (w i).analytic.isClosed (subset_univ _)
  ext x
  simp only [levelCentre, mem_preimage, Set.mem_ofPred_eq, mem_inter_iff, mem_singleton_iff, hcos]

/-- **The first-stage canonical centres of the vanishing-ideal records**, at a common bound `λ` of
the values (e.g. the global maximum over finitely many windows): the `λ`-level sets, closed
submanifolds of the ambient windows by the admissibility of the route invariant. -/
def levelSetCentres (hD : ∀ i, IsInvDomain k (windowRecord (w i))) (lam : Λ)
    (hlam : ∀ i, ∀ y ∈ (w i).carrier, vanishingValue R (w i) y ≤ lam) : LocalSmoothCentres X κ where
  emb i := (w i).toLocalEmbedding
  window _ := ⊤
  centre i := levelCentre R w lam i
  isClosedSubmanifold i := by
    have hcos : (windowRecord (w i)).cosupp = (w i).carrier :=
      SmoothCentreLocus.cosupp_vanishingIdeal (w i).analytic.isClosed (subset_univ _)
    have h := R.isInvValue.admissible (windowRecord (w i)) (hD i) BlowupTower.refl trivial ⊤ lam
      (fun y hy _ => hlam i y (hcos ▸ hy))
    exact h.1
  centre_subset i := by
    intro x hx
    have hcos : (windowRecord (w i)).cosupp = (w i).carrier :=
      SmoothCentreLocus.cosupp_vanishingIdeal (w i).analytic.isClosed (subset_univ _)
    have hx' : x.val ∈ (windowRecord (w i)).cosupp := hx.1
    rw [hcos] at hx'
    exact hx'

/-- **The first-stage centres of the vanishing-ideal records of windows of a common dimension agree
on overlaps** (the compatibility input of the gluing, for the vanishing-ideal route). -/
theorem levelSetCentres_compatible (hD : ∀ i, IsInvDomain k (windowRecord (w i))) (lam : Λ)
    (hlam : ∀ i, ∀ y ∈ (w i).carrier, vanishingValue R (w i) y ≤ lam) :
    (levelSetCentres R w hD lam hlam).Compatible := by
  apply (levelSetCentres R w hD lam hlam).compatible_of_levelSet_overlap
    (fun i => {x | x.val ∈ (w i).carrier})
    (fun i x => vanishingValue R (w i) x.val) lam (fun i => levelCentre_eq R w lam i)
  intro i k y z hyz _
  exact ⟨z.property, vanishingValue_eq_of_toPoint_eq R (w i) (w k) (hD i) (hD k)
    ⟨y.val.val, y.property⟩ ⟨z.val.val, z.property⟩ hyz⟩

/-- The trace of the glued centre on each window is its level set. -/
theorem preimage_support_levelSetCentres (hD : ∀ i, IsInvDomain k (windowRecord (w i))) (lam : Λ)
    (hlam : ∀ i, ∀ y ∈ (w i).carrier, vanishingValue R (w i) y ≤ lam) (i : κ) :
    ((levelSetCentres R w hD lam hlam).windowMap i).hom.left.base ⁻¹'
        (levelSetCentres R w hD lam hlam).support =
      (levelSetCentres R w hD lam hlam).trace i :=
  (levelSetCentres R w hD lam hlam).preimage_support (levelSetCentres_compatible R w hD lam hlam) i

/-- **The glued first-stage centre is an analytic subset of `X`** when the windows cover `X`: the
first canonical centre of the vanishing-ideal principalization is intrinsic to `X`. -/
theorem isAnalyticSubset_support_levelSetCentres (hD : ∀ i, IsInvDomain k (windowRecord (w i)))
    (lam : Λ) (hlam : ∀ i, ∀ y ∈ (w i).carrier, vanishingValue R (w i) y ≤ lam)
    (hcover : ∀ x : X.obj.left, ∃ i, x ∈ range (w i).toLocalEmbedding.toPoint) :
    X.IsAnalyticSubset (levelSetCentres R w hD lam hlam).support := by
  apply (levelSetCentres R w hD lam hlam).isAnalyticSubset_support_of_cover
    (levelSetCentres_compatible R w hD lam hlam)
  intro x
  obtain ⟨i, c, rfl⟩ := hcover x
  exact ⟨i, ⟨⟨c.val, trivial⟩, c.property⟩, rfl⟩

/-- **One glued blowup step along the first-stage vanishing-record centres**, when their glued
centre is closed and lies in the singular locus. -/
theorem exists_singularCentreBlowup_levelSetCentres (hD : ∀ i, IsInvDomain k (windowRecord (w i)))
    (lam : Λ) (hlam : ∀ i, ∀ y ∈ (w i).carrier, vanishingValue R (w i) y ≤ lam)
    (hcl : IsClosed (levelSetCentres R w hD lam hlam).support)
    (hsing : (levelSetCentres R w hD lam hlam).support ⊆
      HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus X.obj) :
    ∃ (hS : X.IsAnalyticSubset (levelSetCentres R w hD lam hlam).support)
      (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      SmoothCentreModification.IsSmoothCentreBlowup p
        (OriginalAnalyticClosedSubspace.inclusion X (levelSetCentres R w hD lam hlam).support hS) ∧
      HironakaG11SingularCentreModification.IsSingularCentreStep p ∧
      HironakaG11SingularCentreModification.IsSingularCentreModification p ∧
      Function.Surjective p.hom.left.base ∧
      SourceReducedComplexSpace.IsIsoOver p (levelSetCentres R w hD lam hlam).supportᶜ :=
  (levelSetCentres R w hD lam hlam).exists_singularCentreBlowup
    (levelSetCentres_compatible R w hD lam hlam) hcl hsing

end Family

/-! ### Any family of local embeddings, stabilized to a common dimension -/

section Stabilized

variable {κ : Type*} (R : ResolutionInvariant.{0} N k Λ) (hNk : N ≤ k) (e : κ → LocalEmbedding X)
  (hN : ∀ i, (e i).dim < N)

/-- The windows of a family of local embeddings, raised to a common dimension `N` above all of their
dimensions. -/
def raisedWindows : κ → DimEmbedding X N := fun i => DimEmbedding.raise (e i) N (hN i).le

include hNk in
theorem isInvDomain_raisedWindows (i : κ) : IsInvDomain k (windowRecord (raisedWindows e hN i)) :=
  isInvDomain_windowRecord hNk _ (DimEmbedding.interior_carrier_raise (e i) N (hN i))

/-- **The first-stage vanishing-record centres of ANY family of local embeddings, stabilized to a
common dimension, are compatible**, and (if the embeddings cover `X`) glue to an analytic subset of
`X`, whose trace on every window is that window's level set. -/
theorem raisedWindows_levelSetCentres (lam : Λ)
    (hlam : ∀ i, ∀ y ∈ (raisedWindows e hN i).carrier,
      vanishingValue R (raisedWindows e hN i) y ≤ lam) :
    (levelSetCentres R (raisedWindows e hN) (isInvDomain_raisedWindows hNk e hN) lam hlam).Compatible ∧
      ((∀ x : X.obj.left, ∃ i, x ∈ range (e i).toPoint) →
        X.IsAnalyticSubset
          (levelSetCentres R (raisedWindows e hN) (isInvDomain_raisedWindows hNk e hN) lam hlam).support) := by
  refine ⟨levelSetCentres_compatible R _ _ lam hlam, fun hcover => ?_⟩
  apply isAnalyticSubset_support_levelSetCentres
  intro x
  obtain ⟨i, hi⟩ := hcover x
  refine ⟨i, ?_⟩
  change x ∈ range (DimEmbedding.raise (e i) N (hN i).le).toLocalEmbedding.toPoint
  rw [DimEmbedding.range_toPoint_raise]
  exact hi

end Stabilized

end

end Hironaka.Analytic.Unibranch.HironakaG11VanishingWindows
