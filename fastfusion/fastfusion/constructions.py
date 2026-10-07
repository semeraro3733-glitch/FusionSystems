"""Explicit, verified constructions of symplectic-type p-groups (extraspecial
groups and direct products thereof), used as the test groups for the fast
fusion-system search.

An *extraspecial* p-group of order p^{1+2n} is a p-group S with
Z(S) = Phi(S) = S' of order p and S/Z(S) elementary abelian of rank 2n.
Choosing a symplectic basis x_1,y_1,...,x_n,y_n of V = S/Z(S) for the
(necessarily nondegenerate, since S/Z(S) is elementary abelian and this is a
standard fact about extraspecial groups) alternating commutator form

    B(x_1,y_1) = ... = B(x_n,y_n) = 1,   all other B(basis_i, basis_j) = 0,

gives the presentation used here: generators x_1,y_1,...,x_n,y_n,z (z = the
generator of Z(S) = S', placed *last*, matching the central-series
convention of pcgroup.py), relations [x_i,y_i] = z, all other pairs of basis
generators commute, and the pth-power map on generators is either trivial
throughout ("exponent-p type", the only kind used here for odd p -- see the
module docstring of autgroup.py for why Winter's theorem is cleanest in this
case) or, for p = 2, given by a quadratic refinement q of B (Aschbacher,
*Finite Group Theory*, 23.9-23.10): x_i^2 = z^{q(x_i)}, y_i^2 = z^{q(y_i)}.
The isomorphism type of S depends only on the Witt type of q (for p=2) --
"+"-type (q has maximal isotropic subspaces / Witt index n, central product
of n copies of D8) or "-"-type (Witt index n-1, one copy of Q8).  For p odd
there is only one isomorphism type of exponent-p extraspecial group of each
order p^{1+2n} up to choice of symplectic basis (any two are isomorphic via
a base change in Sp(2n,p), since the form is unique up to equivalence).

All constructions below are checked, in tests/test_constructions.py, against
GAP by independently building the identical presentation there and comparing
structural invariants (as in tests/test_pcgroup.py); for the smallest cases
(n small enough that GAP's small-group library applies) we also check the
IdGroup matches the expected library entry.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Tuple

from .pcgroup import PCPresentation, Word


def extraspecial(p: int, n: int, squares: Optional[Sequence[int]] = None) -> PCPresentation:
    """Extraspecial group of order p^{1+2n}.

    Generators (in order): x_1, y_1, x_2, y_2, ..., x_n, y_n, z.  [x_i, y_i] = z
    for every i; every other pair of the 2n basis generators commutes.

    `squares`, only meaningful for p = 2 (ignored -- and required to be all
    zero -- for odd p, since for odd p the pth-power map on a class-2 group is
    *additive* hence vanishes identically once it vanishes on a spanning set,
    and exponent-p type is the construction used throughout this project):
    a list of 2n bits, squares[2i] = q(x_{i+1}), squares[2i+1] = q(y_{i+1}),
    with x_{i+1}^2 = z^{squares[2i]}, y_{i+1}^2 = z^{squares[2i+1]}.  Default:
    all zero, which for n=1 gives D8; `witt_minus_squares(n)` gives a "-"-type
    presentation (one Q8 factor, n-1 D8 factors) for any n >= 1.
    """
    assert n >= 1
    N = 2 * n + 1
    z = N
    if squares is None:
        squares = [0] * (2 * n)
    else:
        squares = list(squares)
        assert len(squares) == 2 * n
    if p != 2:
        assert all(s == 0 for s in squares), "nontrivial pth powers only supported for p=2"
    power_words: List[Word] = [[]] * N
    power_words = [[z] if squares[i] else [] for i in range(2 * n)] + [[]]
    comm_words: Dict[Tuple[int, int], Word] = {}
    for i in range(n):
        xi, yi = 2 * i, 2 * i + 1
        comm_words[(xi, yi)] = [z]
    names = []
    for i in range(n):
        names += [f"x{i+1}", f"y{i+1}"]
    names += ["z"]
    return PCPresentation(n=N, p=p, power_words=power_words, comm_words=comm_words, names=names)


def witt_minus_squares(n: int) -> List[int]:
    """A choice of squares (see `extraspecial`) giving the "-"-type extraspecial
    2-group of order 2^{1+2n} (Witt index n-1): the first hyperbolic pair is a
    Q8 (both basis vectors square to z), the rest are D8 (square to 1)."""
    assert n >= 1
    sq = [0] * (2 * n)
    sq[0] = 1
    sq[1] = 1
    return sq


def direct_product(pres_list: Sequence[PCPresentation]) -> PCPresentation:
    """Direct product of several PC presentations, all for the same prime p.
    Generators are concatenated (factor 1's generators first, heaviest);
    cross-factor commutators are trivial (automatically consistent with the
    "later generators only" convention, since a trivial word references no
    generators at all)."""
    assert pres_list
    p = pres_list[0].p
    assert all(pr.p == p for pr in pres_list)
    offsets = []
    off = 0
    for pr in pres_list:
        offsets.append(off)
        off += pr.n
    N = off
    power_words: List[Word] = [[] for _ in range(N)]
    comm_words: Dict[Tuple[int, int], Word] = {}
    names: List[str] = []
    for pr, base in zip(pres_list, offsets):
        for i in range(pr.n):
            power_words[base + i] = [g + base for g in pr.power_words[i]]
        for (i, j), w in pr.comm_words.items():
            comm_words[(base + i, base + j)] = [g + base for g in w]
        names += [f"{nm}" for nm in pr.names]
    # disambiguate repeated names (e.g. two isomorphic factors) for printing
    seen: Dict[str, int] = {}
    uniq_names = []
    for nm in names:
        seen[nm] = seen.get(nm, 0) + 1
        uniq_names.append(nm if seen[nm] == 1 else f"{nm}#{seen[nm]}")
    return PCPresentation(n=N, p=p, power_words=power_words, comm_words=comm_words, names=uniq_names)


def extraspecial_plus(p: int, n: int) -> PCPresentation:
    """The exponent-p type for odd p; the "+"-type (Witt index n) for p=2."""
    return extraspecial(p, n)


def extraspecial_minus(n: int) -> PCPresentation:
    """The "-"-type extraspecial 2-group of order 2^{1+2n} (only defined for p=2)."""
    return extraspecial(2, n, squares=witt_minus_squares(n))
