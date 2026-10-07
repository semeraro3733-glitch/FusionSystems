# fastfusion

A pure-Python, from-scratch implementation of the fast proto-essential
subgroup search for fusion systems on finite $p$-groups, following

> P. Gautam, *Fusion systems on Sylow 3-subgroups of Fischer and Monster
> sporadic groups II*, Section 3, [arXiv:2607.24674](https://arxiv.org/abs/2607.24674)

as an improvement on the subgroup-lattice-based approach of

> C. Parker, J. Semeraro, *Algorithms for fusion systems with applications
> to p-groups of small order*, [arXiv:2003.01600](https://arxiv.org/abs/2003.01600)

(the MAGMA port of which, with the same fast method added, is the rest of
this repository). See [`paper/main.tex`](../paper/main.tex) (or
`main.pdf`) for the full writeup: the algorithm, the engine design, a
proof that extraspecial $p$-groups of rank $\geq 2$ have no
proto-essential subgroups at all, and the showcase results up to order
$5^7$ and $2^{10}$.

No external computer-algebra dependency is used anywhere in this package
(only `numpy`); GAP is used solely, in `tests/gap_oracle.py`, as an
*independent cross-check oracle* during testing, never at runtime.

## Layout

| file | purpose |
|---|---|
| `fastfusion/pcgroup.py` | The engine: `PCPresentation` (power-commutator presentation + collection from the left) and `CompiledPGroup` (compiled table-driven representation: multiplication, inversion, conjugation, centralizers, normalizers, closures, conjugacy classes). |
| `fastfusion/constructions.py` | Extraspecial $p$-groups of order $p^{1+2n}$ (exponent-$p$ for odd $p$; $+$/$-$ Witt type for $p=2$) and direct products. |
| `fastfusion/autgroup.py` | Explicit, individually verified automorphism generators via Winter's theorem (generate-and-verify, not hand-derived formulas). |
| `fastfusion/protoessential.py` | Gautam's Theorem 3.6 candidate search, the Parker–Semeraro cheap filters, the $\operatorname{Aut}(S)$-orbit reduction, and the radical test. |
| `tests/` | Correctness tests, including cross-validation against GAP (`gap_oracle.py`) and fixed expected outputs for every small case. |
| `scripts/showcase.py` | The showcase computations reported in the paper (small cases, $5^7$, $2^9$, $2^{10}$); writes JSON results to `results/`. |

## Running it

```bash
cd fastfusion
python3 tests/test_pcgroup.py          # engine correctness (+ GAP cross-check if gap is on PATH)
python3 tests/test_constructions.py
python3 tests/test_autgroup.py
python3 tests/test_protoessential.py   # fixed expected outputs for every small case

python3 scripts/showcase.py 5_7                 # order 5^7, the headline case
python3 scripts/showcase.py 2_9_plus 2_9_minus 2_10
python3 scripts/showcase.py 3_3 5_3 2_3_plus 2_3_minus 3_5 5_5 2_5_plus 2_5_minus   # all the small cases
```

Each run prints its progress and a summary, and writes
`results/<name>.json` with the full candidate/filter/orbit counts and the
proto-essential classes found (order, index in $S$, $|\operatorname{Out}_S(E)|$,
whether $E$ is normal in $S$).

GAP (with the `polycyclic` package) is only needed to re-run the
cross-validation in `tests/gap_oracle.py`; every other script and test
runs with just Python 3 and `numpy`.

## What this does *not* do

This package finds the **candidates for essential subgroups** -- the
previously infeasible stage. It does not implement the subsequent search
over compatible automizer assignments and the saturation test (done, for
a case with genuinely nontrivial essential subgroups, in GAP/MAGMA
elsewhere in this repository for $C_3 \wr C_3 \wr C_3$). For every group
in this package's showcase, the proto-essential search returns the empty
list, and the paper explains why that already determines every saturated
fusion system on these particular groups without needing that further
search. Porting that search engine to Python, for groups that do have
nontrivial essential subgroups, is noted as future work in the paper.
