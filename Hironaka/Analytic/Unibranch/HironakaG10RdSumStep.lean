import Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex
import Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
import Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaCentre

/-!
# The `D_β` step of Theorem `I_n` as a permissible step (lane G10RD)

Plan item G10-03-07.c (re-split in `work/hironaka-run0081-20261117/G10RD/G10-03-03-sum-centre-globalization.md` §6).
Source: H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), choice of `D_β`
and Lemma 4.5.4, printed p. 542: "`π` is permissible for `R` … (clear by `D_β ⊆ Z` and by Lemma 3.2)".

* `PermStep.ofSumCentre` — an admissible sum centre (`IsSumCentreFor`), over which the family is flat and whose
  support lies in `s_1(f/B)`, together with transported flatteners whose supports are the germ-level transport
  (Lemma 4.4.5, plan item G10-03-09), is a permissible step;
* `exists_sumCentre_permStep` — **the library's `D_β` centre at Hironaka's index `i ≥ 1`**
  (`HironakaG10SourceLargeOmegaCentre.exists_source_large_omega_sumCentre`) gives such a step, for one exponent
  `β > 0`, with support exactly `C_i ∩ E_i`, given Lemma 4.4.5 for sum centres as the hypothesis `hT`.

`hT` is Hironaka's Lemma 4.4.5 (p. 537) for one step, not a statement about rounds; it is the open item G10-03-09.
No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10RdSumStep

open Hironaka HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10SourceLargeOmegaCentre
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

variable {s : Stage} {q : ℕ}

/-- **A sum-centre step is permissible**, given the transported flatteners (Lemma 4.4.5). -/
def PermStep.ofSumCentre (R : FDatum s q) (c : AdmissibleCentre s.f) (β : ℕ)
    (hβ : IsSumCentreFor c.B c.b s.f β)
    (hflat : ∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x))
    (hsub : nonunitLocus c.B c.b ⊆ relNonflat s.f R.B)
    (Z' : Fin q → LocalFlattener (nextWith s c).f)
    (hZ' : ∀ p, (Z' p).support = (R.trackedTransport c).Z p) : PermStep R where
  c := c
  flat := hflat
  sub := hsub
  perm := Or.inl ⟨β, hβ⟩
  next := ⟨strictSet s c R.B, isClosed_closure, Z'⟩
  next_B := rfl
  next_support := hZ'

/-- **The `D_β` step at Hironaka's index `i + 1`** (p. 542, Lemma 4.5.4): under the hypotheses of the library's
large-`ω` source centre, and Lemma 4.4.5 for sum centres (`hT`), there is a permissible step whose centre is a sum
centre for a positive exponent with support exactly `C_{i+1} ∩ E_{i+1}`. -/
theorem exists_sumCentre_permStep [CompactSpace s.X.obj.left] (R : FDatum s q)
    (Zaux : LocalFlattener s.f) (i : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn s.X (R.Z p).V (strata s.f R.B (i + 1)))
    (hSaux : IsLocallyAnalyticOn s.X Zaux.V (strata s.f R.B (i + 1)))
    (N : ℕ) (hN : strata s.f R.B N = ∅)
    (hcover : ∀ j x, x ∈ strata s.f R.B j → ∃ C, IsStratumComponent s.f R.B j C ∧ x ∈ C)
    (hfinite : (selectedHigherComponents s.f R.B (fun p => (R.Z p).support) (i + 1)).Finite)
    (hmax : ∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ i + 1)
    (hC : Cset s.f R.B (fun p => (R.Z p).support) (i + 1) ⊆ Zaux.support)
    (hdense : Dense (nonflatImage s.f)ᶜ)
    (K : Set s.X.obj.left) (hK : IsCompact K)
    (hKtracked : ∀ x ∈ K, ∃ p, x ∈ stratumBoundary s.f R.B (R.Z p).V (R.Z p).support i)
    (hT : ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
      ∃ Z' : Fin q → LocalFlattener (nextWith s c).f,
        ∀ p, (Z' p).support = (R.trackedTransport c).Z p) :
    ∃ st : PermStep R, (∃ β, β ≠ 0 ∧ IsSumCentreFor st.c.B st.c.b s.f β) ∧
      nonunitLocus st.c.B st.c.b = Cset s.f R.B (fun p => (R.Z p).support) (i + 1) ∩
        stratumBoundary s.f R.B Zaux.V Zaux.support i := by
  obtain ⟨_, ω₀, -, -, -, hω⟩ := exists_source_large_omega_sumCentre s.f R.B R.Z Zaux i hS hSaux N hN
    hcover hfinite hmax hC hdense K hK hKtracked
  obtain ⟨_, _, -, -, -, α, hα⟩ := hω ω₀ le_rfl
  obtain ⟨c, hcQ, hsum, hflat, -, -⟩ := hα (max α 1) (le_max_left _ _)
  obtain ⟨Z', hZ'⟩ := hT c _ hsum
  have hsub : nonunitLocus c.B c.b ⊆ relNonflat s.f R.B := by
    rw [hcQ]
    exact inter_subset_left.trans (cset_subset_relNonflat _)
  exact ⟨PermStep.ofSumCentre R c _ hsum hflat hsub Z' hZ',
    ⟨max α 1, by have := le_max_right α 1; omega, hsum⟩, hcQ⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10RdSumStep
