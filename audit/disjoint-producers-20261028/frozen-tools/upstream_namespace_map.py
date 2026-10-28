"""Single source of truth for the TN -> Hironaka renaming: module layout, namespace rename, private names.

Everything that renames (the shaker, the comparison tables for CompareLib.lean, the README generator) imports this file."""
import re

TN = 'TranscendentalNakamaye'

# ---------------------------------------------------------------- module layout
# Area of an original module (without the `TranscendentalNakamaye.` prefix).  First match wins.
API_RE = re.compile(r'^Pending\.HironakaAPI(\w*)$')
RULES = [
    (r'^FirstPass\.(ComplexManifold|HolomorphicMaps|HolomorphicContDiff|LocalHolomorphicInverse|HolomorphicVanishingDerivative|AnalyticPoleSet)$', 'Manifold'),
    (r'^FirstPass\.(BlowupSequences|ExceptionalLocus)$', 'Blowup'),
    (r'^FirstPass\.', 'Analytic'),
    (r'^Pending\.Hironaka\w*$', 'Resolution'),
    (r'^Pending\.(ExtSeqTransport|StepOne\w*|MaxOrderValue|MaximalOrderStepOneB|MaxLocusLocal|InvDomain\w*|Contact\w*|Companion\w*|Member\w*|General\w*|Monomial(Case|CaseAlong|Invariant\w*|Part\w*|Resolution|StepAlong)|Nonmonomial\w*|ResolutionInvariant\w*|ResolutionDriver|CanonicalCentres|CodimOne(PartCanonical|PartTowerAlong|AdmissibleAlong)|DropMembers|RestrictEmptyTower|SmoothCentre\w*|BoundaryCount\w*|DivisorExponent\w*|IdealOrderArithmetic|OrderMultiplicativity|OrderTaylor)$', 'Invariant'),
    (r'^Pending\.(CanonicalResolution|FactorizationFromResolution|FactorizationDomain|EmbeddedFromResolution|RelativePrincipalization\w*|EmbeddedResolution|StrictTransformSubvariety\w*|StrictTransformComposition)$', 'Resolution'),
    (r'^Pending\.(MarkedIdeal\w*|GermIdeal\w*|DerivativeIdeal\w*|CoefficientIdeal\w*|Coefficient\w*|Homogenized\w*|MaximalContact\w*|GiraudAlong|LocalGiraud\w*|IdealWeight\w*|RestrictedIdeal\w*|InvertibleIdealQuotient|NormalDerivative\w*|NormalTaylorOrder|TangentDirectionAlong|HadamardBridge\w*|RestrictLeCalculus|SubmanifoldRestrictLe|GeoTransformWellFormed|TransformOffCentre|MeteredDivisorOperations|DivisorMetric|CodimOne(Centre|CentreAlong|Support|SupportAlong))$', 'MarkedIdeal'),
    (r'^Pending\.(Blowup\w*|MonomialBlowup\w*|NormalCrossings\w*|SimultaneousNormalCrossings|Exceptional\w*|NestedFlattening|LiftedOpenModel|GlueingTrivialAction|RegularPatch\w*|BlanchardForm)$', 'Blowup'),
    (r'^Pending\.(Oka\w*|Cartan\w*|CoherentIdealColon|VanishingIdealCoherent|FiniteGeneratorIdealDescent)$', 'Coherence'),
    (r'^Pending\.', 'Analytic'),
]


# Explicit module paths for modules whose original name describes material that is not part of the library (only a few
# generic declarations of each are needed); their namespaces are kept.
MODULE_RENAMES = {
    'FirstPass.NonKahlerLocus': 'Hironaka.Analytic.SingularLocus',
    'FirstPass.AnalyticPoleSet': 'Hironaka.Manifold.ChartDifferentiable',
    'Pending.DivisorMetric': 'Hironaka.Analytic.InvertibleIdealCoherent',
    'Pending.MeteredDivisorOperations': 'Hironaka.Analytic.PullbackNonvanishing',
    'Pending.IdealWeightPowers': 'Hironaka.Analytic.IdealPowers',
    'Pending.IdealWeightProducts': 'Hironaka.Analytic.IdealProducts',
    'Pending.IdealWeightComparison': 'Hironaka.Analytic.IdealPresentation',
    'Pending.RestrictedIdealWeight': 'Hironaka.MarkedIdeal.RestrictLe',
    'Pending.RelativePrincipalizationSpan': 'Hironaka.Analytic.IdealSpanCalculus',
}
# Namespaces flattened into `Hironaka` (besides the API modules): the vocabulary of the public statements.
FLATTEN = ['TranscendentalNakamaye.FirstPass.NonKahlerLocus']


def is_api_module(m):
    return API_RE.match(m[len(TN) + 1:]) is not None


def area(m):
    s = m[len(TN) + 1:]
    for pat, a in RULES:
        if re.match(pat, s):
            return a
    raise ValueError(f'no layout rule for {m}')


def new_mod(m):
    """original module -> module of the library"""
    assert m.startswith(TN + '.'), m
    s = m[len(TN) + 1:]
    if s in MODULE_RENAMES:
        return MODULE_RENAMES[s]
    a = API_RE.match(s)
    if a:  # the public statements: Pending.HironakaAPI -> Hironaka.API, HironakaAPI2 -> Hironaka.API2, ...
        return 'Hironaka.API' + a.group(1)
    return 'Hironaka.' + area(m) + '.' + s.split('.')[-1]


# ---------------------------------------------------------------- namespace rename
# Ordered prefix rewrites on names (component-wise).  The namespaces of the public API modules are flattened into
# `Hironaka`, so that the public theorems are `Hironaka.exists_principalization`, ...
def ns_rules(api_modules):
    rules = []
    for m in sorted(list(api_modules) + FLATTEN, key=len, reverse=True):
        rules.append((m, 'Hironaka'))          # namespace TranscendentalNakamaye.Pending.HironakaAPI2 = module name
    rules += [(TN + '.Pending', 'Hironaka'), (TN + '.FirstPass', 'Hironaka'), (TN + '.Upstream', 'Hironaka'), (TN, 'Hironaka')]
    return rules


_RULES = None


def set_api_modules(api_modules):
    global _RULES
    _RULES = ns_rules(api_modules)


def _replace_prefix(n, a, b):
    if n == a:
        return b
    if n.startswith(a + '.'):
        return b + n[len(a):]
    return None


def flattened_short():
    """last components of the flattened namespaces (e.g. `HironakaAPI2`, `NonKahlerLocus`)"""
    return sorted({a.split('.')[-1] for a, b in _RULES if b == 'Hironaka' and a.count('.') >= 2}, key=len, reverse=True)


BASIC_RULES = [(TN + '.Pending', 'Hironaka'), (TN + '.FirstPass', 'Hironaka'), (TN + '.Upstream', 'Hironaka'), (TN, 'Hironaka')]


def rename_ns_naive(n):
    """the rename without flattening (the namespaces as they are written in the sources)"""
    for a, b in BASIC_RULES:
        r = _replace_prefix(n, a, b)
        if r is not None:
            return r
    return n


def rename_ns(n):
    """rename a (non-private) constant or namespace name"""
    for a, b in _RULES:
        r = _replace_prefix(n, a, b)
        if r is not None:
            return r
    return n


def rename_const(n, module_of_private=None):
    """rename a constant name, including private names `_private.<Module>.0.<decl>`"""
    if n.startswith('_private.'):
        head, sep, rest = n.partition('.0.')
        if not sep:
            return n
        mod = head[len('_private.'):]
        nm = new_mod(mod) if mod.startswith(TN + '.') else mod
        return '_private.' + nm + '.0.' + rename_ns(rest)
    return rename_ns(n)


def rename_text_names(s):
    """textual rename of fully qualified names inside source text (any position)"""
    for a, b in _RULES:
        s = re.sub(r'(?<![\w])' + re.escape(a) + r'(?![\w])', b, s)
    return s
