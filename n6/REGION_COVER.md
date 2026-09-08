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
`(1,1,0,1,3/4,1/4,1,1/4,3/4,1)`, and every parameter varies independently by
`1/100`. The original quadrilateral is retained. One tree verifies all 21 face
pairs throughout this box, with 20 strict facet supports and 22 coplanarity
identities checked.

```
python3 -m n6.polycert verify n6/results/minus-wide-affine.certificate.json
```

## Wider overnight searches remain incomplete

| Saved search | Generator-certified leaves | Unresolved leaves | Verdict |
|---|---:|---:|---|
| `prism-balanced-cover.partial.json.gz` | 1,649 | 94 | Partial; no complete-cover proof |
| `minus-expanded-cover.partial.json.gz` | 1,219 | 11 | Partial; no complete-cover proof |

These counts do not measure the fraction of parameter volume covered. Their
leaf certificates have not received an independent full replay. The saved
subdivisions can be resumed; unresolved leaves must never be counted as covered.

Even successful verification of either larger box would still leave the rest
of the unbounded metric domain, near-degenerate limits, and any missing charts
to be covered. A universal certificate needs an exhaustive domain reduction
and certified handling of every resulting region.
