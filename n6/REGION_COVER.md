# Exact regional coverage: morning results

9 September 2026. These are certificates for explicit parameter boxes, not a
proof covering every realization of a combinatorial type.

## Prism with one diagonal: complete nine-parameter box

Use the coordinates and original facets in [PRISM_DIAGONAL.md](PRISM_DIAGONAL.md).
The parameter order is `(x,y,u,v,w,A,B,C,D)`. The certified box has center

```
(-3, 1/10, -3, 0, 1, 4, 1/2, 1, 1)
```

and independent closed half-widths

```
(1/10, 1/100, 1/10, 1/100, 1/10, 1/10, 3/100, 3/100, 3/100).
```

The saved coordinate polynomials already include the center translation; its
`parameter_box` describes displacements from that center. The independent
checker uses the polynomials, not the informational `parameter_origin` field.

Independent replay returned `verified_complete_region_cover`: **443 leaves,
three distinct cut trees, maximum depth nine**. Every leaf verifies its original
facets and all 15 face pairs. Across the leaves, 3,991 pair checks use uncut
vertex fans and 2,654 use rigorously bounded separating edges. Every binary
split has two closed children whose union equals the parent, including their
shared boundary. Thus there is no omitted parameter tuple in this root box.

```
python3 -m n6.cover verify n6/results/prism-affine-cover.certificate.json.gz
```

The replay result is saved in
`results/prism-affine-cover.verification.json`. It is distinct from the
generator's preliminary counts. Verification uses Python's standard library
and exact rational arithmetic with outward bounds; numerical ranking is used
only to propose candidate trees during generation.

## Octahedron minus an edge: complete ten-parameter box

The chart is

```
P0=(0,0,0), P1=(x,y,0), P2=(1,0,0), P3=(u,v,0),
P4=(r,s,-h), P5=(t,k,-l).
```

The parameter order is `(x,y,u,v,r,s,h,t,k,l)`, center
`(1,1,0,1,3/4,1/4,1,1/4,3/4,1)`. The continuation expanded the verified box:

| Independent half-width in every parameter | Verified leaves | Trees |
|---|---:|---:|
| `1/100`, earlier box | 1 | 1 |
| `1/50` | 1 | 1 |
| `3/100` | 2 | 2 |
| `1/25` | 46 | 5 |
| `1/20` | 409 | 9 |

The `1/25` box is four times as wide in each of ten parameters. Independent
replay checks all 966 face pairs across its 46 leaves: 609 vertex-fan checks
and 357 separating-edge checks. Maximum depth is eight. Every leaf preserves
the original quadrilateral, with 20 strict supports and 22 coplanarity identities.

```
python3 -m n6.cover verify n6/results/minus-quadrupled-cover.certificate.json.gz
```

## Wider overnight searches remain incomplete

| Saved search | Generator-certified leaves | Unresolved leaves | Verdict |
|---|---:|---:|---|
| `prism-balanced-cover.partial.json.gz` | 1,649 | 94 | Partial; no complete-cover proof |
| `minus-expanded-cover.partial.json.gz` | 1,219 | 11 | Partial; no complete-cover proof |

These historical counts do not measure parameter volume. The continuation now
reports the exact fraction from each implied leaf box, explicitly separating
structural bookkeeping from independent geometric verification.

| New search on the half-width `1/20` root | Candidate-certified leaves | Unresolved | Candidate-covered parameter fraction |
|---|---:|---:|---:|
| Resumed overnight subdivision | 1,459 | 13 | `7185/16384` |
| Fresh search, 32 candidate trees per cell | 231 | 3 | `21/32` |
| Experimental affine-coefficient split heuristic | 191 | 10 | `7/32` |

The heuristic performed worse on this root and is not the default. These three
partial results complement one another. Their overlay covers `477/512` of the
root's parameter volume, with 400 candidate-certified cells and seven unresolved
cells. Resuming only those cells fills the remaining volume in about 29 seconds,
producing a **409-leaf cover that subsequently passed full independent replay**.
The verified half-width is `1/20` in every parameter, with nine trees and maximum
depth 13. The checker verified 5,498 vertex-fan pairs and 3,091 separating-edge
pairs: all 8,589 required face-pair checks. Its saved verdict is
`results/minus-merged-cover.verification.json`. This certifies every tuple in
the explicit closed root box, including all subdivision boundaries; it does
not cover the entire metric domain.

The merge routine overlays only covers with identical root geometry, uses a
certificate only on a contained cell, and retains every unresolved intersection.
Every split still has two closed children, so shared boundaries are included.
The independent checker reconstructs and verifies every resulting leaf.

```
python3 -m n6.cover summary n6/results/minus-merged-cover.certificate.json.gz
python3 -m n6.cover verify n6/results/minus-merged-cover.certificate.json.gz
```

An additional search tried all 224 original-edge trees on the unsplit wider
root. None was certified by the current bounds; this is inconclusive interval
arithmetic, not evidence that the trees overlap. Exact one-axis norm identities
now preserve planar projection correlations instead of unnecessarily estimating
`sqrt(q*q)` as a nonlinear expression.

Even successful verification of either larger box would still leave the rest
of the unbounded metric domain, near-degenerate limits, and any missing charts
to be covered. A universal certificate needs an exhaustive domain reduction
and certified handling of every resulting region.


## Progress measurement added to the overview

The partial prism search `prism-balanced-cover.partial.json.gz` has 1,649
cells labelled certified by the generator and 94 unresolved cells. Exact
structural volume accounting gives

```
candidate-covered fraction = 437/4194304  ≈ 0.0104198%
unresolved fraction        = 4193867/4194304 ≈ 99.9895802%.
```

Counting leaves equally would suggest about 94.6% coverage, which is incorrect:
the candidate-covered cells are much smaller. These fractions measure volume
in the nine chart parameters, not a fraction of all convex prism shapes.
A complete independent geometric replay of the partial cover has not finished;
the dashboard therefore labels this measurement **provisional**. The new
`n6.progress` command can perform that replay; it rejects any false certified
label and leaves unresolved cells explicit. A slow replay started during this
update was stopped without a proof conclusion.

This is **box B**, centered at `(0,1,0,0,1,5/2,1/2,9/10,9/10)` with half-widths
`(1/4,1/5,1/4,1/4,1/5,1/2,1/10,1/10,1/10)`. It is a different box from the
independently verified 443-leaf **box A** above; it is not a nested enlargement
of A. The two percentages must not be added. Future comparisons should keep
the same root box, coordinate chart, and verification status, or explicitly
start a new series.
