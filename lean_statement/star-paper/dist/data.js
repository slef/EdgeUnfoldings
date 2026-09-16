window.PAPER_DATA = {
  "annotations": [
    {
      "id": "star-definition",
      "blocks": [
        "definition-1"
      ],
      "title": "What is the star unfolding in Lean?",
      "status": "restricted",
      "statement": "Definitions present for cofacial cuts",
      "proof": "Checked construction in restricted scope",
      "scope": "SixVertexGraph (the four nonuniversal six-vertex graph models), triangular/quadrilateral faces. The source is an original vertex and shares a face with every original vertex.",
      "note": "ConvexPolyhedron is the convex hull of its exact extreme vertices in ℝ³, with nonempty interior. The current starCuts removes straight source-to-vertex segments. These are shortest surface cuts when the source is cofacial with every vertex. This is not yet a definition of an arbitrary choice of shortest cuts for an arbitrary source.",
      "refs": [
        [
          "Definitions",
          "ConvexPolyhedron"
        ],
        [
          "Definitions",
          "ConvexPolyhedron.body"
        ],
        [
          "CofacialStarCuts",
          "starCuts"
        ],
        [
          "CofacialStarCuts",
          "UncutSurface"
        ],
        [
          "CofacialStarCuts",
          "original_route_subset_starCuts"
        ]
      ],
      "steps": [],
      "work": {
        "status": "complete",
        "reason": "The cofacial-cut definitions are sufficient for a universal-vertex source: every source-to-vertex edge lies on the surface. The development of that cut surface is a separate unfinished construction.",
        "remaining": [],
        "beyond": [
          "Chosen shortest cuts for arbitrary sources, and their general cut surface, remain an extension beyond this milestone."
        ],
        "depends_on": [
          "main"
        ]
      }
    },
    {
      "id": "boundary-images",
      "blocks": [
        "boundary"
      ],
      "title": "Boundary images and equal cut lengths",
      "status": "missing",
      "statement": "Polygonal-boundary statement present; 2n count absent",
      "proof": "Restricted boundary theorem checked",
      "scope": "SixVertexGraph (the four nonuniversal six-vertex graph models), triangular/quadrilateral faces. The source is an original vertex and shares a face with every original vertex.",
      "note": "The assembled development has an exact finite segment boundary. The paper’s alternating vertex/source images and its 2n (or 2(n−1)) boundary count have not been packaged as Lean statements. A finite polygonal boundary alone does not assert this combinatorial description.",
      "refs": [
        [
          "StarPolygonBoundary",
          "develop_frontier_eq_segments"
        ]
      ],
      "steps": [],
      "work": {
        "status": "beyond",
        "reason": "The exact alternating order and 2n boundary-image count are not needed by the current star-to-edge-unfolding construction. Their absence is not a remaining task for this milestone.",
        "remaining": [],
        "beyond": [
          "The paper’s boundary order and count have no matching complete statement/proof. A finite segment boundary does not establish them."
        ],
        "depends_on": []
      }
    },
    {
      "id": "tree",
      "blocks": [
        "cut-tree"
      ],
      "title": "The actual cut tree",
      "status": "restricted",
      "statement": "Definitions and tree statements present",
      "proof": "Checked in the stated small-polyhedron scope",
      "scope": "At most six vertices; every face triangular or quadrilateral. Arbitrary surface source.",
      "note": "The new theorem constructs an exact finite embedded tree, not a graph covering a superset. Its definition augments the multiple-route locus by the nonsource original vertices. Equality with the paper’s closure definition has a checked canonical-graph theorem; that equality is not yet exported in the broader small-polyhedron scope.",
      "refs": [
        [
          "MultipleShortestRoutes",
          "multipleRouteLocus"
        ],
        [
          "ClosedCutSet",
          "cutSet"
        ],
        [
          "EmbeddedCutGraph",
          "EmbeddedCutGraph"
        ],
        [
          "RegularCutTree",
          "CutLocusTree"
        ],
        [
          "SmallPolyhedronCutTree",
          "small_exists_regular_cut_tree"
        ],
        [
          "SmallPolyhedronCutTree",
          "small_cut_tree_open_edge_two_routes"
        ],
        [
          "CutSetVertexLimits",
          "cutSet_eq_closure_multiple"
        ]
      ],
      "steps": [
        "Exact local Voronoi descriptions → finite straight segments.",
        "Continuous retraction onto the cut set → contractibility → connectedness and acyclicity.",
        "Mark original cut vertices and all junctions → exactly two shortest routes on an open tree edge."
      ],
      "work": {
        "status": "complete",
        "reason": "The exact finite cut tree is constructed in the required small-polyhedron scope, including universal-vertex solids and arbitrary surface sources. No further tree-existence proof is needed for this milestone.",
        "remaining": [],
        "beyond": [
          "Exporting equality with the paper’s closure-based definition in the newer scope is an additional correspondence result, not an input required by the current assembly.",
          "Removing the vertex-count and face-size restrictions belongs to the unrestricted theorem."
        ],
        "depends_on": []
      }
    },
    {
      "id": "curve",
      "blocks": [
        "geodesic",
        "definition-2",
        "curve-sides",
        "lemma-1",
        "curve-images",
        "curve-tree",
        "curve-edges"
      ],
      "title": "§1.2 is included, but not formalized here",
      "status": "outside",
      "statement": "No matching curve-source declarations",
      "proof": "Outside the point-star subproject",
      "scope": "Geodesic or quasigeodesic curve sources.",
      "note": "This section is reproduced because it lies in the requested range. SurfacePath and shortest-route definitions elsewhere in the project do not amount to the paper’s geodesic-curve star unfolding. Lemma 1, point/segment images, and the straight/parabolic cut-locus classification are not being claimed as proved.",
      "refs": [],
      "steps": [],
      "work": {
        "status": "beyond",
        "reason": "Curve-source unfolding is deliberately outside this point-star subproject. This section is included only as part of the requested paper excerpt.",
        "remaining": [],
        "beyond": [
          "No curve-source proof work is planned here; none of these paper claims is being marked as proved."
        ],
        "depends_on": []
      }
    },
    {
      "id": "kite-partition",
      "blocks": [
        "kites"
      ],
      "title": "Build the actual radial triangles",
      "status": "restricted",
      "statement": "Route, metric-kite, and coverage statements present",
      "proof": "Checked; construction still uses canonical graphs",
      "scope": "SixVertexGraph (the four nonuniversal six-vertex graph models), triangular/quadrilateral faces.",
      "note": "The two basic shortest-route facts now hold without a canonical graph in the small-polyhedron scope. The complete two-triangle construction and its coverage theorem still use SixVertexGraph. Merely specifying equal distances in a metric model is not the whole surface partition.",
      "refs": [
        [
          "SmallPolyhedronShortestRoutes",
          "small_shortest_routes_agree_of_meeting"
        ],
        [
          "SmallPolyhedronTerminalRays",
          "small_geodesic_proper_prefix_outside_cutSet"
        ],
        [
          "CutEdgeMetricModel",
          "CutEdgeMetricModel"
        ],
        [
          "CutEdgeTriangles",
          "CutEdgeTriangles"
        ],
        [
          "CutEdgeTriangles",
          "exists_cut_edge_triangles"
        ],
        [
          "CutTreeTriangleCoverage",
          "cut_tree_triangles_cover"
        ]
      ],
      "steps": [
        "No branching/crossing of distinct shortest routes.",
        "Proper shortest prefixes stay outside the cut set.",
        "Construct both actual closed radial strips and develop them to metric triangles.",
        "Prove their union covers the surface; later separation handles overlap."
      ],
      "work": {
        "status": "todo",
        "reason": "The existing construction still depends on the canonical nonuniversal graphs. It must be extended before it can supply the universal-source development.",
        "remaining": [
          "Transfer the actual radial-triangle construction, flat-junction charts and surface coverage to the new small-polyhedron cut tree."
        ],
        "beyond": [],
        "depends_on": [
          "tree",
          "leaf"
        ]
      }
    },
    {
      "id": "budget",
      "blocks": [
        "source-budget"
      ],
      "title": "The source-angle budget is the integration gap",
      "status": "restricted",
      "statement": "Angle definitions and restricted budget statements present",
      "proof": "Local bound checked; global budget restricted",
      "scope": "SixVertexGraph (the four nonuniversal six-vertex graph models), triangular/quadrilateral faces. The global budget uses a source vertex.",
      "note": "The local bound “surface angle < 2π” is proved at every original vertex of a small polyhedron. That does not by itself prove that all the developed kite angles fit into that cone. The global source-angle sum is proved for canonical graphs, using actual cone coverage and curvature accounting.",
      "refs": [
        [
          "CutEdgeSourceAngles",
          "sourceAngle"
        ],
        [
          "VertexFanAngles",
          "totalAngle"
        ],
        [
          "VertexFanAngles",
          "totalAngle_lt_two_pi"
        ],
        [
          "CutTreeConeCoverage",
          "incident_model_angles_cover_cone"
        ],
        [
          "CutTreeCurvature",
          "sum_cutTreeCurvature"
        ],
        [
          "CutTreeSourceBudget",
          "source_angle_sum_le"
        ],
        [
          "CutTreeSourceBudget",
          "half_source_angle_sum_lt_pi"
        ]
      ],
      "steps": [
        "Local surface angle: checked for all small polyhedra.",
        "Incident radial triangles cover each cone: checked for canonical graphs.",
        "Total curvature accounting: checked for canonical graphs.",
        "Half the directed source-angle sum is < π: checked for canonical vertex sources."
      ],
      "work": {
        "status": "todo",
        "reason": "The local angle bound is complete, but the required global source-angle sum is not yet available for universal-vertex solids.",
        "remaining": [
          "Extend cone coverage and curvature accounting to the new local fans and derive the global budget for the universal vertex source."
        ],
        "beyond": [
          "An arbitrary nonvertex source permits equality in the half-angle budget. That case, and arbitrary vertex counts, belong to the broader theorem."
        ],
        "depends_on": []
      }
    },
    {
      "id": "main",
      "blocks": [
        "theorem-1"
      ],
      "title": "Theorem 1 — what has actually been proved",
      "status": "restricted",
      "statement": "Restricted theorem present; full paper statement absent",
      "proof": "Restricted theorem checked, no sorry",
      "scope": "SixVertexGraph (the four nonuniversal six-vertex graph models), triangular/quadrilateral faces. The source is an original vertex and shares a face with every original vertex.",
      "note": "cofacial_star_embedding constructs a continuous open embedding of the actual retained surface into the plane, with bounded connected image, finite straight-segment boundary, and exact local intrinsic isometry. This is a real proved checkpoint, but it is not Theorem 1 for every convex polyhedron and source. The cofacial hypothesis is impossible for the all-triangular octahedron, so this does not claim all four graph models admit such a source.",
      "refs": [
        [
          "CofacialStarEmbedding",
          "cofacial_star_embedding"
        ],
        [
          "SixVertexGraphs",
          "SixVertexGraph"
        ],
        [
          "CanonicalSixGraphs",
          "SixGraphKind"
        ],
        [
          "CutTreeCharts",
          "CutTreeCharts"
        ],
        [
          "GlobalKiteSeparation",
          "global_kites_nonoverlap"
        ],
        [
          "StarOpenEmbedding",
          "develop_isOpenEmbedding"
        ],
        [
          "StarLocalMetric",
          "develop_locally_isometric"
        ],
        [
          "RetainedCutConnectivity",
          "cofacial_uncut_surface_pathConnected"
        ]
      ],
      "steps": [
        "Construct the cut tree and coherent, covering radial charts.",
        "Prove the angle budget and separate every pair of kites.",
        "Glue the triangle maps and construct inverse neighborhoods.",
        "Prove local intrinsic isometry and retained-surface connectivity.",
        "Identify the exact finite-segment boundary."
      ],
      "work": {
        "status": "todo",
        "reason": "The proved cofacial checkpoint does not cover the universal-vertex family. Completing that family is the next star milestone, not merely an optional increase in paper coverage.",
        "remaining": [
          "Construct the universal-source charts and angle budget, then assemble the injective, locally isometric planar development."
        ],
        "beyond": [
          "The full paper theorem for arbitrary sources and unrestricted convex polyhedra remains unfinished. It is not declared complete by finishing this milestone."
        ],
        "depends_on": [
          "kite-partition",
          "budget",
          "leaf"
        ]
      }
    },
    {
      "id": "path",
      "blocks": [
        "path-reduction"
      ],
      "title": "Reduce any two kites to their tree path",
      "status": "proved",
      "statement": "Conditional chain and separation statements present",
      "proof": "Checked, from explicit geometric inputs",
      "scope": "Finite cut trees supplied with coherent CutTreeCharts and the source budget.",
      "note": "The combinatorial path argument is proved. The final canonical-graph theorem supplies its source budget; it still receives charts whose original_leaves field rules out internal original vertices.",
      "refs": [
        [
          "CutTreeCharts",
          "CutTreeCharts"
        ],
        [
          "CutTreeChainSeparation",
          "end_kites_nonoverlap"
        ],
        [
          "GlobalKiteSeparation",
          "global_kites_nonoverlap"
        ]
      ],
      "steps": [],
      "work": {
        "status": "complete",
        "reason": "The tree-path separation argument is checked under its displayed inputs. Constructing those inputs is tracked in the triangle, leaf and budget items; this component needs no new path argument.",
        "remaining": [],
        "beyond": [],
        "depends_on": [
          "kite-partition",
          "leaf",
          "budget"
        ]
      }
    },
    {
      "id": "wedge",
      "blocks": [
        "wedge-definition"
      ],
      "title": "W-wedges as actual planar sets",
      "status": "defined",
      "statement": "Definitions present",
      "proof": "Definitions; geometry proved in downstream lemmas",
      "scope": "Planar coordinates; no polyhedron classification is needed.",
      "note": "The implementation uses a circle-by-circle description (polarRegion) and a Cartesian region for root movement. Both bounded and unbounded cases are included. These are set definitions, not a structure assuming the desired separation.",
      "refs": [
        [
          "WedgeRotation",
          "polarRegion"
        ],
        [
          "WedgeRootMove",
          "region"
        ],
        [
          "GapKiteStep",
          "gapKite"
        ]
      ],
      "steps": [],
      "work": {
        "status": "complete",
        "reason": "The planar wedge definitions needed by the construction are present. This status records completion of definitions, not a claim that a definition is a proved theorem.",
        "remaining": [],
        "beyond": [],
        "depends_on": []
      }
    },
    {
      "id": "invariant",
      "blocks": [
        "induction-goal",
        "induction-step"
      ],
      "title": "The induction, decomposed",
      "status": "proved",
      "statement": "RegionStep and finite-chain statements present",
      "proof": "Checked, conditional on actual steps",
      "scope": "Sets in the plane and affine isometric changes of coordinates.",
      "note": "The Lean induction tracks three facts separately: the old wedge is contained in an enlarged wedge, the enlarged wedge avoids the next kite’s interior, and moving coordinates turns their union into the new wedge. It explicitly transports every kite into one common plane.",
      "refs": [
        [
          "ExpandingRegionChains",
          "RegionStep"
        ],
        [
          "ExpandingRegionChains",
          "finite_chain_separation"
        ],
        [
          "ExpandingRegionChains",
          "finite_chain_endpoint_separation"
        ]
      ],
      "steps": [
        "contains: Wᵢ₋₁ ⊆ W′ᵢ.",
        "avoids: W′ᵢ ∩ interior(kᵢ) = ∅.",
        "updated: Wᵢ is the transported union W′ᵢ ∪ kᵢ.",
        "Finite induction carries all earlier regions forward and separates the endpoints."
      ],
      "work": {
        "status": "complete",
        "reason": "The finite planar induction is checked. The surface construction must supply its step hypotheses; that work is tracked separately.",
        "remaining": [],
        "beyond": [],
        "depends_on": [
          "kite-partition",
          "budget"
        ]
      }
    },
    {
      "id": "containment",
      "blocks": [
        "lemma-2",
        "lemma-2-proof"
      ],
      "title": "Lemma 2 — a coordinate proof",
      "status": "proved",
      "statement": "Coordinate containment statements present",
      "proof": "Checked, under explicit outward-angle conditions",
      "scope": "Planar kites and wedges; coordinate formulations of the paper’s geometric step.",
      "note": "The code does not reproduce the circular-sector proof line by line. It proves kite containment and complementary exclusion by coordinate inequalities, then translates the angle budget to these inequalities in rotate_and_move. The full geometric step bundles rotation, exclusion and root movement.",
      "refs": [
        [
          "WedgeRootMove",
          "kite_subset_region"
        ],
        [
          "WedgeRootMove",
          "next_kite_outside"
        ],
        [
          "WedgeStep",
          "rotate_and_move"
        ],
        [
          "GapKiteStep",
          "gap_rotate_and_move_with_sources"
        ]
      ],
      "steps": [
        "Containment: a nonnegative dot product keeps the outer ray pointing outward.",
        "Exclusion: the outward condition at the new root keeps the next kite outside the old wedge.",
        "Angle-to-coordinate translation connects these conditions to the cumulative budget."
      ],
      "work": {
        "status": "complete",
        "reason": "The needed containment and exclusion are proved by coordinate inequalities. Reproducing the paper’s different circular-sector argument is not an additional task.",
        "remaining": [],
        "beyond": [],
        "depends_on": []
      }
    },
    {
      "id": "base",
      "blocks": [
        "base-case"
      ],
      "title": "Base case for an actual kite",
      "status": "proved",
      "statement": "Statement present",
      "proof": "Checked, given IncidentTriangles",
      "scope": "An actual first radial kite; its far endpoint may be an original vertex.",
      "note": "initial_kite_in_wedge encloses the complete first kite with exactly its own source-angle charge. The proof uses the already-checked planar move. Constructing IncidentTriangles in the broader polyhedral scope is still separate.",
      "refs": [
        [
          "InitialKiteWedge",
          "initial_kite_in_wedge"
        ],
        [
          "GapKiteStep",
          "gap_rotate_and_move_with_sources"
        ]
      ],
      "steps": [],
      "work": {
        "status": "complete",
        "reason": "The first-kite lemma is checked given its actual radial-triangle input. Supplying that input for the new family is tracked in the triangle-construction item.",
        "remaining": [],
        "beyond": [],
        "depends_on": [
          "kite-partition"
        ]
      }
    },
    {
      "id": "rotation",
      "blocks": [
        "rotate"
      ],
      "title": "Rotate the arms, then exclude the next kite",
      "status": "restricted",
      "statement": "Planar and flat-junction statements present",
      "proof": "Checked with a flat JunctionFan and angle budget",
      "scope": "Planar rotation is generic. The supplied surface junction fan is flat.",
      "note": "rotate_arms is a direct set-containment theorem. JunctionFan.wedge_step_with_parameters obtains the correct gap order and actual kite angles from the surface chart. The current global chart structure excludes internal original vertices; this is where the paper’s singular-vertex situation still needs additional construction. The journal says “surface area” here; the intended quantity is surface angle. Its pᵢ/pᵢ₋₁ wording is retained.",
      "refs": [
        [
          "WedgeRotation",
          "rotate_arms"
        ],
        [
          "JunctionWedgeStep",
          "wedge_step_with_parameters"
        ],
        [
          "CutTreeCharts",
          "CutTreeCharts"
        ]
      ],
      "steps": [
        "Get the circular order of the actual incoming and outgoing gaps.",
        "Rotate to an enlarged wedge without losing the old region.",
        "Use the complementary angle bound to exclude the outgoing kite."
      ],
      "work": {
        "status": "complete",
        "reason": "The planar rotation and flat-junction step are checked. The planned universal-source construction uses only flat internal junctions once the cofacial-leaf transfer is proved.",
        "remaining": [],
        "beyond": [
          "Singular junctions at original vertices require more work for arbitrary sources; they are not required by this milestone."
        ],
        "depends_on": [
          "kite-partition",
          "leaf",
          "budget"
        ]
      }
    },
    {
      "id": "center",
      "blocks": [
        "move-center"
      ],
      "title": "Move the root and add exactly one kite",
      "status": "proved",
      "statement": "Statements present",
      "proof": "Checked, with explicit angle budget",
      "scope": "Planar region movement and actual flat-junction data.",
      "note": "move_root proves an exact set equality, stronger than the needed containment. The geometric step identifies the next source radius, corner angle and source-angle increment. Editorial note: the paper’s phrase “to αᵢ” omits the fixed π/2 offset used in its wedge definition; the Lean formula retains ω + sourceAngle.",
      "refs": [
        [
          "WedgeRootMove",
          "move_root"
        ],
        [
          "GapKiteStep",
          "gap_rotate_and_move_with_sources"
        ],
        [
          "JunctionWedgeStep",
          "wedge_step_with_parameters"
        ]
      ],
      "steps": [],
      "work": {
        "status": "complete",
        "reason": "The root-movement identity and its flat-junction step are checked. Constructing the needed surface data and budget is tracked separately.",
        "remaining": [],
        "beyond": [],
        "depends_on": [
          "kite-partition",
          "budget"
        ]
      }
    },
    {
      "id": "exterior",
      "blocks": [
        "empty-regions",
        "lemma-3"
      ],
      "title": "Lemma 3 has no complete matching theorem yet",
      "status": "missing",
      "statement": "Full geometric statement not yet declared",
      "proof": "Unfinished; no literal sorry declaration",
      "scope": "Exterior W-region at an arbitrary original vertex image.",
      "note": "The finite-chain theorem preserves an initial empty region, which is useful infrastructure. There is not yet a theorem identifying that region with the paper’s exterior W for every vertex image and all possible incident cut edges.",
      "refs": [
        [
          "ExpandingRegionChains",
          "finite_chain_separation"
        ]
      ],
      "steps": [],
      "work": {
        "status": "beyond",
        "reason": "The current star-embedding route uses direct pairwise kite separation. It does not require a separate theorem with the full exterior-W conclusion of Lemma 3.",
        "remaining": [],
        "beyond": [
          "The exact exterior-W definition, its identification at all vertex images and the closed-boundary avoidance conclusion remain unformalized. This paper result is not being claimed as proved."
        ],
        "depends_on": []
      }
    },
    {
      "id": "leaf",
      "blocks": [
        "lemma-3-leaf"
      ],
      "title": "Lemma 3 — the leaf case",
      "status": "restricted",
      "statement": "Leaf and abstract empty-region statements present",
      "proof": "Components checked; paper-level corollary not assembled",
      "scope": "SixVertexGraph (the four nonuniversal six-vertex graph models), triangular/quadrilateral faces. The source is an original vertex and shares a face with every original vertex.",
      "note": "The leaf classification is proved for cofacial sources in canonical graphs. Finite-chain separation also keeps every later kite interior out of its initial region. These components have not been assembled into the exact closed-unfolding-versus-interior(W) assertion of Lemma 3.",
      "refs": [
        [
          "UniqueRouteLeaves",
          "cofacial_source_leaf_iff_original"
        ],
        [
          "ExpandingRegionChains",
          "finite_chain_separation"
        ]
      ],
      "steps": [],
      "work": {
        "status": "todo",
        "reason": "The cofacial-leaf classification must be extended to universal-vertex solids. This is required to justify using flat internal junctions, even though the full exterior-W assertion is not required.",
        "remaining": [
          "Prove that every nonsource original vertex is a leaf of the new small-polyhedron cut tree for a universal vertex source."
        ],
        "beyond": [
          "Assembling the exact closed-unfolding-versus-interior(W) assertion of Lemma 3 is additional paper coverage."
        ],
        "depends_on": [
          "tree"
        ]
      }
    },
    {
      "id": "singular",
      "blocks": [
        "lemma-3-internal"
      ],
      "title": "Lemma 3 — an internal original vertex",
      "status": "missing",
      "statement": "General cone-junction / exterior-W bridge absent",
      "proof": "Unfinished; no literal sorry declaration",
      "scope": "Original polyhedron vertices with several incident cut-locus edges.",
      "note": "The paper selects a tree path and uses W ⊆ W₀ for its chosen first edge. Our current CutTreeCharts instead requires every original cut vertex to be a leaf. Thus the existing global assembly cannot express this case merely by supplying another fan.",
      "refs": [
        [
          "CutTreeCharts",
          "CutTreeCharts"
        ]
      ],
      "steps": [],
      "work": {
        "status": "beyond",
        "reason": "Internal original-vertex junctions are outside the universal-source milestone. Their exclusion there still depends on the leaf proof, which is explicitly marked “Still to do”.",
        "remaining": [],
        "beyond": [
          "For the arbitrary-source theorem, construct singular-cone junctions, prove the paper’s W ⊆ W₀ comparison and extend the global assembly. This remains unfinished."
        ],
        "depends_on": [
          "leaf"
        ]
      }
    }
  ],
  "declarations": {
    "CanonicalSixGraphs:SixGraphKind": {
      "name": "SixGraphKind",
      "qualified": "SixVertexUnfolding.SmallGraphs.SixGraphKind",
      "kind": "inductive",
      "module": "CanonicalSixGraphs",
      "line": 8,
      "signature": "inductive SixGraphKind where\n  | octahedron\n  | minusEdge\n  | prismDiagonal\n  | prism\n  deriving DecidableEq, Fintype",
      "context": "",
      "namespace": "SixVertexUnfolding.SmallGraphs",
      "proofHole": false
    },
    "ClosedCutSet:cutSet": {
      "name": "cutSet",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.cutSet",
      "kind": "def",
      "module": "ClosedCutSet",
      "line": 12,
      "signature": "def cutSet (P : ConvexPolyhedron) (a : frontier P.body) : Set (frontier P.body) :=\n  {b | (b : Space) ∈ P.multipleRouteLocus a ∨ ((b : Space) ∈ P.vertices ∧ b ≠ a)}",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "CofacialStarCuts:UncutSurface": {
      "name": "UncutSurface",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.UncutSurface",
      "kind": "abbrev",
      "module": "CofacialStarCuts",
      "line": 16,
      "signature": "abbrev UncutSurface (P : ConvexPolyhedron) (a : frontier P.body) :=\n  {b : frontier P.body // b ∉ P.starCuts a}",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "CofacialStarCuts:original_route_subset_starCuts": {
      "name": "original_route_subset_starCuts",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.original_route_subset_starCuts",
      "kind": "theorem",
      "module": "CofacialStarCuts",
      "line": 38,
      "signature": "theorem original_route_subset_starCuts (P : ConvexPolyhedron) (a b : frontier P.body)\n    (original : (b : Space) ∈ P.vertices) (F : P.Face) (source : (a : Space) ∈ F.val)\n    (target : (b : Space) ∈ F.val) (route : P.BoundaryCurve) (member : route ∈ P.geodesicFiber a b) :\n    range route ⊆ P.starCuts a",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "CofacialStarCuts:starCuts": {
      "name": "starCuts",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.starCuts",
      "kind": "def",
      "module": "CofacialStarCuts",
      "line": 12,
      "signature": "def starCuts (P : ConvexPolyhedron) (a : frontier P.body) : Set (frontier P.body) :=\n  {b | ∃ v : P.Vertex, (b : Space) ∈ segment ℝ (a : Space) (v : Space)}",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "CofacialStarEmbedding:cofacial_star_embedding": {
      "name": "cofacial_star_embedding",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.cofacial_star_embedding",
      "kind": "theorem",
      "module": "CofacialStarEmbedding",
      "line": 19,
      "signature": "theorem cofacial_star_embedding {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n      (F.val ∩ (P.vertices : Set Space)).ncard = 4)\n    (a : frontier P.body) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))\n    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :\n    ∃ develop : C(P.UncutSurface a, Plane),\n      Topology.IsOpenEmbedding develop ∧ Bornology.IsBounded (range develop) ∧\n      IsPathConnected (range develop) ∧\n      (∃ edges : Finset (Plane × Plane), frontier (range develop) =\n        ⋃ e ∈ edges, segment ℝ e.1 e.2) ∧\n      ∀ b : P.UncutSurface a, ∃ radius > 0, ∀ c d : P.UncutSurface a,\n        dist (c.val : Space) (b.val : Space) < radius →\n        dist (d.val : Space) (b.val : Space) < radius →\n        dist (develop c) (develop d) = P.surfaceDist c.val d.val",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "CutEdgeMetricModel:CutEdgeMetricModel": {
      "name": "CutEdgeMetricModel",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel",
      "kind": "structure",
      "module": "CutEdgeMetricModel",
      "line": 15,
      "signature": "structure CutEdgeMetricModel {P : ConvexPolyhedron} {a : frontier P.body}\n    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v) where\n  left : Plane\n  right : Plane\n  first : Plane\n  second : Plane\n  base_length : dist left right = dist (u : Space) (v : Space)\n  distinct_sources : first ≠ second\n  first_distances : ∀ t : unitInterval,\n    dist first (AffineMap.lineMap left right (t : ℝ)) = P.surfaceDist a (T.closedEdgeTarget edge t)\n  second_distances : ∀ t : unitInterval,\n    dist second (AffineMap.lineMap left right (t : ℝ)) = P.surfaceDist a (T.closedEdgeTarget edge t)",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "CutEdgeSourceAngles:sourceAngle": {
      "name": "sourceAngle",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel.sourceAngle",
      "kind": "def",
      "module": "CutEdgeSourceAngles",
      "line": 15,
      "signature": "noncomputable def sourceAngle : ℝ := angle M.left M.first M.right",
      "context": "open Set EuclideanGeometry\nvariable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}\n  {u v : T.vertices} {edge : T.graph.Adj u v} (M : CutEdgeMetricModel T edge)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.CutEdgeMetricModel",
      "proofHole": false
    },
    "CutEdgeTriangles:CutEdgeTriangles": {
      "name": "CutEdgeTriangles",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.CutEdgeTriangles",
      "kind": "structure",
      "module": "CutEdgeTriangles",
      "line": 11,
      "signature": "structure CutEdgeTriangles {P : ConvexPolyhedron} {a : frontier P.body}\n    (T : P.CutLocusTree a) {u v : T.vertices} (edge : T.graph.Adj u v) where\n  strips : CutEdgeStrips T edge\n  model : CutEdgeMetricModel T edge\n  first : C(unitInterval, P.BoundaryCurve)\n  second : C(unitInterval, P.BoundaryCurve)\n  agrees : ∀ t, first (interiorTime t) = strips.first t ∧ second (interiorTime t) = strips.second t\n  member : ∀ t, first t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t) ∧\n    second t ∈ P.geodesicFiber a (T.closedEdgeTarget edge t)\n  first_triangle : RadialStripTriangle first model.first model.left model.right\n  second_triangle : RadialStripTriangle second model.second model.left model.right",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "CutEdgeTriangles:exists_cut_edge_triangles": {
      "name": "exists_cut_edge_triangles",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.exists_cut_edge_triangles",
      "kind": "theorem",
      "module": "CutEdgeTriangles",
      "line": 51,
      "signature": "theorem exists_cut_edge_triangles (a : frontier P.body) (T : P.CutLocusTree a)\n    {u v : T.vertices} (edge : T.graph.Adj u v) : Nonempty (CutEdgeTriangles T edge)",
      "context": "open Set\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)\ninclude graph small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "CutSetVertexLimits:cutSet_eq_closure_multiple": {
      "name": "cutSet_eq_closure_multiple",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.cutSet_eq_closure_multiple",
      "kind": "theorem",
      "module": "CutSetVertexLimits",
      "line": 75,
      "signature": "theorem cutSet_eq_closure_multiple (a : frontier P.body) :\n    P.cutSet a = closure {b : frontier P.body | (b : Space) ∈ P.multipleRouteLocus a}",
      "context": "open Set Filter\nopen scoped Topology\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)\ninclude graph small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "CutTreeChainSeparation:end_kites_nonoverlap": {
      "name": "end_kites_nonoverlap",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.CutTreeChain.end_kites_nonoverlap",
      "kind": "theorem",
      "module": "CutTreeChainSeparation",
      "line": 30,
      "signature": "theorem end_kites_nonoverlap (total : (∑ i, chain.sourceAngle charts i) < π) :\n    Disjoint (charts.kite (chain.edge 0))\n      (interior (charts.kite (chain.edge (Fin.last n).succ)))",
      "context": "open Set Real Wedge\nvariable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a} {n : ℕ}\n    (chain : CutTreeChain T n) (charts : CutTreeCharts T)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.CutTreeChain",
      "proofHole": false
    },
    "CutTreeCharts:CutTreeCharts": {
      "name": "CutTreeCharts",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.CutTreeCharts",
      "kind": "structure",
      "module": "CutTreeCharts",
      "line": 16,
      "signature": "structure CutTreeCharts {P : ConvexPolyhedron} {a : frontier P.body} (T : P.CutLocusTree a) where\n  fan : ∀ u : T.vertices, (u : Space) ∉ P.vertices → JunctionFan T u\n  triangles : ∀ {u v : T.vertices} (edge : T.graph.Adj u v), PlacedCutEdgeTriangles T edge\n  at_fan : ∀ {u v : T.vertices} (edge : T.graph.Adj u v) (nonvertex : (u : Space) ∉ P.vertices),\n    triangles edge = ((fan u nonvertex).edgeTriangles edge).placed\n  original_leaves : ∀ u : T.vertices, (u : Space) ∈ P.vertices → ∃! v, T.graph.Adj u v\n  frames : CutTreeFrames T triangles\n  covers : ∀ b : frontier P.body, ∃ u v : T.vertices, ∃ edge : T.graph.Adj u v,\n    b ∈ (triangles edge).region",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "CutTreeConeCoverage:incident_model_angles_cover_cone": {
      "name": "incident_model_angles_cover_cone",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.incident_model_angles_cover_cone",
      "kind": "theorem",
      "module": "CutTreeConeCoverage",
      "line": 75,
      "signature": "theorem incident_model_angles_cover_cone (a : frontier P.body) (T : P.CutLocusTree a)\n    [Fintype T.vertices] [DecidableRel T.graph.Adj]\n    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)\n    (u : T.vertices) (pole : Fin 6) (at_vertex : (u : Space) = (graph.vertex pole : Space)) :\n    graph.totalAngleAt pole ≤ T.incidentAngleSum models u",
      "context": "open Set EuclideanGeometry\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n      (F.val ∩ (P.vertices : Set Space)).ncard = 4)\ninclude small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "CutTreeCurvature:sum_cutTreeCurvature": {
      "name": "sum_cutTreeCurvature",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.sum_cutTreeCurvature",
      "kind": "theorem",
      "module": "CutTreeCurvature",
      "line": 39,
      "signature": "theorem sum_cutTreeCurvature [Fintype T.vertices] (source : Fin 6)\n    (at_source : (a : Space) = (graph.vertex source : Space)) :\n    ∑ u, graph.cutTreeCurvature T u = 4 * π - graph.curvature source",
      "context": "open Real Set\nopen scoped BigOperators\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  {a : frontier P.body} (T : P.CutLocusTree a)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "CutTreeSourceBudget:half_source_angle_sum_lt_pi": {
      "name": "half_source_angle_sum_lt_pi",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.half_source_angle_sum_lt_pi",
      "kind": "theorem",
      "module": "CutTreeSourceBudget",
      "line": 28,
      "signature": "theorem half_source_angle_sum_lt_pi (source : Fin 6)\n    (at_source : (a : Space) = (graph.vertex source : Space)) :\n    (∑ d, (models d).sourceAngle) / 2 < π",
      "context": "open Set Real\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n      (F.val ∩ (P.vertices : Set Space)).ncard = 4)\n    {a : frontier P.body} (T : P.CutLocusTree a)\n    [Fintype T.vertices] [DecidableRel T.graph.Adj]\n    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)\ninclude small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "CutTreeSourceBudget:source_angle_sum_le": {
      "name": "source_angle_sum_le",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.source_angle_sum_le",
      "kind": "theorem",
      "module": "CutTreeSourceBudget",
      "line": 20,
      "signature": "theorem source_angle_sum_le (source : Fin 6)\n    (at_source : (a : Space) = (graph.vertex source : Space)) :\n    ∑ d, (models d).sourceAngle ≤ graph.totalAngleAt source",
      "context": "open Set Real\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n      (F.val ∩ (P.vertices : Set Space)).ncard = 4)\n    {a : frontier P.body} (T : P.CutLocusTree a)\n    [Fintype T.vertices] [DecidableRel T.graph.Adj]\n    (models : (d : T.graph.Dart) → CutEdgeMetricModel T d.adj)\ninclude small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "CutTreeTriangleCoverage:cut_tree_triangles_cover": {
      "name": "cut_tree_triangles_cover",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.cut_tree_triangles_cover",
      "kind": "theorem",
      "module": "CutTreeTriangleCoverage",
      "line": 19,
      "signature": "theorem cut_tree_triangles_cover (a : frontier P.body) (T : P.CutLocusTree a)\n    (triangles : (d : T.graph.Dart) → CutEdgeTriangles T d.adj) (b : frontier P.body) :\n    ∃ d, b ∈ range (closedRouteStripMap (triangles d).first) ∪\n      range (closedRouteStripMap (triangles d).second)",
      "context": "open Set\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)\ninclude graph small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "Definitions:ConvexPolyhedron": {
      "name": "ConvexPolyhedron",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron",
      "kind": "structure",
      "module": "Definitions",
      "line": 13,
      "signature": "structure ConvexPolyhedron where\n  vertices : Finset Space\n  solid : (interior (convexHull ℝ (vertices : Set Space))).Nonempty\n  vertices_exact :\n    (vertices : Set Space) =\n      (convexHull ℝ (vertices : Set Space)).extremePoints ℝ",
      "context": "",
      "namespace": "SixVertexUnfolding",
      "proofHole": false
    },
    "Definitions:ConvexPolyhedron.body": {
      "name": "ConvexPolyhedron.body",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.body",
      "kind": "def",
      "module": "Definitions",
      "line": 20,
      "signature": "def ConvexPolyhedron.body (P : ConvexPolyhedron) : Set Space :=\n  convexHull ℝ (P.vertices : Set Space)",
      "context": "",
      "namespace": "SixVertexUnfolding",
      "proofHole": false
    },
    "EmbeddedCutGraph:EmbeddedCutGraph": {
      "name": "EmbeddedCutGraph",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.EmbeddedCutGraph",
      "kind": "structure",
      "module": "EmbeddedCutGraph",
      "line": 12,
      "signature": "structure EmbeddedCutGraph (P : ConvexPolyhedron) (a : frontier P.body) where\n  vertices : Set Space\n  finite_vertices : vertices.Finite\n  graph : SimpleGraph vertices\n  trace : ∀ x, x ∈ P.cutSetInSpace a ↔ x ∈ vertices ∨\n    ∃ u v : vertices, graph.Adj u v ∧ x ∈ openSegment ℝ (u : Space) (v : Space)\n  cofacial_edges : ∀ u v : vertices, graph.Adj u v →\n    ∃ F : P.Face, segment ℝ (u : Space) (v : Space) ⊆ F.val\n  no_vertex_inside : ∀ u v : vertices, graph.Adj u v →\n    Disjoint (openSegment ℝ (u : Space) (v : Space)) vertices\n  open_edges_meet : ∀ u v w z : vertices, graph.Adj u v → graph.Adj w z →\n    ∀ x ∈ openSegment ℝ (u : Space) (v : Space), x ∈ openSegment ℝ (w : Space) (z : Space) →\n      (u = w ∧ v = z) ∨ (u = z ∧ v = w)",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "ExpandingRegionChains:RegionStep": {
      "name": "RegionStep",
      "qualified": "SixVertexUnfolding.Wedge.RegionStep",
      "kind": "structure",
      "module": "ExpandingRegionChains",
      "line": 12,
      "signature": "structure RegionStep (before after kite : Set Plane) where\n  enlarged : Set Plane\n  motion : Plane ≃ᵃⁱ[ℝ] Plane\n  contains : before ⊆ enlarged\n  avoids : Disjoint enlarged (interior kite)\n  updated : motion '' (enlarged ∪ kite) = after",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "ExpandingRegionChains:finite_chain_endpoint_separation": {
      "name": "finite_chain_endpoint_separation",
      "qualified": "SixVertexUnfolding.Wedge.finite_chain_endpoint_separation",
      "kind": "theorem",
      "module": "ExpandingRegionChains",
      "line": 97,
      "signature": "theorem finite_chain_endpoint_separation (n : ℕ) (regions kites : ℕ → Set Plane)\n    (steps : ∀ i : Fin n, RegionStep (regions i) (regions (i + 1)) (kites i))\n    (first last : Set Plane) (initial : first ⊆ regions 0)\n    (terminal : Disjoint (regions n) (interior last)) :\n    ∃ frames : ℕ → Plane ≃ᵃⁱ[ℝ] Plane,\n      frames 0 = AffineIsometryEquiv.refl ℝ Plane ∧\n      (∀ i : Fin n, ∀ x, frames (i + 1) ((steps i).motion x) = frames i x) ∧\n      Disjoint first (interior (frames n '' last))",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "ExpandingRegionChains:finite_chain_separation": {
      "name": "finite_chain_separation",
      "qualified": "SixVertexUnfolding.Wedge.finite_chain_separation",
      "kind": "theorem",
      "module": "ExpandingRegionChains",
      "line": 47,
      "signature": "theorem finite_chain_separation (n : ℕ) (regions kites : ℕ → Set Plane)\n    (steps : ∀ i : Fin n, RegionStep (regions i) (regions (i + 1)) (kites i)) :\n    ∃ frames : ℕ → Plane ≃ᵃⁱ[ℝ] Plane,\n      frames 0 = AffineIsometryEquiv.refl ℝ Plane ∧\n      (∀ i : Fin n, ∀ x, frames (i + 1) ((steps i).motion x) = frames i x) ∧\n      (∀ i j : ℕ, i < j → j < n →\n        Disjoint (frames i '' kites i) (interior (frames j '' kites j))) ∧\n      (∀ j : ℕ, j < n → Disjoint (regions 0) (interior (frames j '' kites j))) ∧\n      (∀ i j : ℕ, i ≤ j → j ≤ n → frames i '' regions i ⊆ frames j '' regions j)",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "GapKiteStep:gapKite": {
      "name": "gapKite",
      "qualified": "SixVertexUnfolding.Wedge.gapKite",
      "kind": "def",
      "module": "GapKiteStep",
      "line": 14,
      "signature": "def gapKite (z : Plane) (d L γ δ : ℝ) : Set Plane :=\n  convexHull ℝ ({z, z + L • direction ((γ + δ) / 2), z + d • direction δ} : Set Plane) ∪\n  convexHull ℝ ({z + L • direction ((γ + δ) / 2), z, z + d • direction γ} : Set Plane)",
      "context": "open Real Set EuclideanGeometry",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "GapKiteStep:gap_rotate_and_move_with_sources": {
      "name": "gap_rotate_and_move_with_sources",
      "qualified": "SixVertexUnfolding.Wedge.gap_rotate_and_move_with_sources",
      "kind": "theorem",
      "module": "GapKiteStep",
      "line": 31,
      "signature": "theorem gap_rotate_and_move_with_sources (z : Plane) {d L α β γ δ ω : ℝ}\n    (source_positive : 0 < d) (length_positive : 0 < L)\n    (gap_ordered : γ < δ) (gap_width : δ < γ + 2 * π)\n    (separated : (β ≤ γ ∧ δ ≤ α + 2 * π) ∨ (δ ≤ α ∧ β ≤ γ + 2 * π))\n    (outer_lower : π / 2 ≤ ω)\n    (budget : ω + angle z (z + d • direction δ) (z + L • direction ((γ + δ) / 2)) ≤ 3 * π / 2) :\n    let y := z + L • direction ((γ + δ) / 2)\n    let apex := angle z (z + d • direction δ) y\n    let W := {x | x - z ∈ polarRegion d ω α β}\n    let V := {x | x - z ∈ polarRegion d ω δ (γ + 2 * π)}\n    ∃ D Θ : ℝ, 0 < D ∧ 0 < Θ ∧ Θ < π ∧\n      z + d • direction δ = y + D • direction (Θ + (γ + δ) / 2) ∧\n      z + d • direction γ = y + D • direction (2 * π - Θ + (γ + δ) / 2) ∧\n      let W' := {x | x - y ∈ polarRegion D (ω + apex)\n        (Θ + (γ + δ) / 2) (2 * π - Θ + (γ + δ) / 2)}\n      W ⊆ V ∧ Disjoint V (interior (gapKite z d L γ δ)) ∧ W' = V ∪ gapKite z d L γ δ",
      "context": "open Real Set EuclideanGeometry",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "GlobalKiteSeparation:global_kites_nonoverlap": {
      "name": "global_kites_nonoverlap",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.global_kites_nonoverlap",
      "kind": "theorem",
      "module": "GlobalKiteSeparation",
      "line": 17,
      "signature": "theorem global_kites_nonoverlap {a : frontier P.body} (T : P.CutLocusTree a)\n    (charts : CutTreeCharts T) (source : Fin 6)\n    (at_source : (a : Space) = (graph.vertex source : Space))\n    {u v w z : T.vertices} (first : T.graph.Adj u v) (last : T.graph.Adj w z)\n    (different : s(u, v) ≠ s(w, z)) :\n    Disjoint (charts.kite first) (interior (charts.kite last))",
      "context": "open Set\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)\ninclude small_faces",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "InitialKiteWedge:initial_kite_in_wedge": {
      "name": "initial_kite_in_wedge",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles.initial_kite_in_wedge",
      "kind": "theorem",
      "module": "InitialKiteWedge",
      "line": 18,
      "signature": "theorem initial_kite_in_wedge :\n    D.developedKite ⊆ D.incomingWedge (π / 2 + D.model.sourceAngle)",
      "context": "open Real Set EuclideanGeometry Wedge\nvariable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}\n    {u v : T.vertices} {edge : T.graph.Adj u v}\n    {chart : P.CutVoronoiChart a (T.vertexTarget u)} {φ : ℝ}\n    (D : IncidentTriangles T edge chart φ)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.IncidentTriangles",
      "proofHole": false
    },
    "JunctionWedgeStep:wedge_step_with_parameters": {
      "name": "wedge_step_with_parameters",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.JunctionFan.wedge_step_with_parameters",
      "kind": "theorem",
      "module": "JunctionWedgeStep",
      "line": 20,
      "signature": "theorem wedge_step_with_parameters\n    (incoming outgoing : circularGapMidpoints fan.order.angles fan.order.first fan.order.last)\n    (distinct : incoming ≠ outgoing) (ω : ℝ) (outer_lower : π / 2 ≤ ω)\n    (budget : ω + (fan.triangles outgoing).model.sourceAngle ≤ 3 * π / 2) :\n    let z := fan.order.chart.origin\n    let d := P.surfaceDist a (T.vertexTarget u)\n    let L := dist (u : Space) ((fan.order.neighbors outgoing).val : Space)\n    let y := z + L • direction outgoing\n    ∃ α β γ δ : ℝ,\n      IsCircularGap fan.order.angles fan.order.first fan.order.last α β ∧\n      IsCircularGap fan.order.angles fan.order.first fan.order.last γ δ ∧\n      (incoming : ℝ) = (α + β) / 2 ∧ (outgoing : ℝ) = (γ + δ) / 2 ∧\n      ∃ D Θ : ℝ, 0 < D ∧ 0 < Θ ∧ Θ < π ∧\n        D = P.surfaceDist a (T.vertexTarget (fan.order.neighbors outgoing).val) ∧\n        π - Θ = angle (fan.triangles outgoing).model.first\n          (fan.triangles outgoing).model.right (fan.triangles outgoing).model.left ∧\n        let W := {x | x - z ∈ polarRegion d ω α β}\n        let V := {x | x - z ∈ polarRegion d ω δ (γ + 2 * π)}\n        let W' := {x | x - y ∈ polarRegion D (ω + (fan.triangles outgoing).model.sourceAngle)\n          (Θ + (γ + δ) / 2) (2 * π - Θ + (γ + δ) / 2)}\n        W ⊆ V ∧ Disjoint V (interior (gapKite z d L γ δ)) ∧ W' = V ∪ gapKite z d L γ δ",
      "context": "open Real Set EuclideanGeometry Wedge\nvariable {P : ConvexPolyhedron} {a : frontier P.body} {T : P.CutLocusTree a}\n  {u : T.vertices} (fan : JunctionFan T u)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.JunctionFan",
      "proofHole": false
    },
    "MultipleShortestRoutes:multipleRouteLocus": {
      "name": "multipleRouteLocus",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.multipleRouteLocus",
      "kind": "def",
      "module": "MultipleShortestRoutes",
      "line": 12,
      "signature": "def multipleRouteLocus (P : ConvexPolyhedron) (a : Space) : Set Space :=\n  {b | a ≠ b ∧ ∃ first second : P.SurfacePath a b,\n    first.IsShortest ∧ second.IsShortest ∧ first.length ≠ ⊤ ∧ second.length ≠ ⊤ ∧\n    LipschitzWith first.length.toNNReal first.curve ∧ LipschitzWith second.length.toNNReal second.curve ∧\n    ¬ ∀ t, first.curve t = second.curve t}",
      "context": "open face, in the finite source-bisector arrangement. Tree structure remains open. -/\nopen Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "RegularCutTree:CutLocusTree": {
      "name": "CutLocusTree",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.CutLocusTree",
      "kind": "structure",
      "module": "RegularCutTree",
      "line": 25,
      "signature": "structure CutLocusTree (P : ConvexPolyhedron) (a : frontier P.body) extends P.EmbeddedCutGraph a where\n  tree : graph.IsTree\n  exceptional_vertices : ∀ b ∈ P.cutExceptions a, (b : Space) ∈ vertices",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "RetainedCutConnectivity:cofacial_uncut_surface_pathConnected": {
      "name": "cofacial_uncut_surface_pathConnected",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.cofacial_uncut_surface_pathConnected",
      "kind": "theorem",
      "module": "RetainedCutConnectivity",
      "line": 53,
      "signature": "theorem cofacial_uncut_surface_pathConnected (a : frontier P.body)\n    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :\n    IsPathConnected (P.starCuts a)ᶜ",
      "context": "open Set\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "SixVertexGraphs:SixVertexGraph": {
      "name": "SixVertexGraph",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "kind": "structure",
      "module": "SixVertexGraphs",
      "line": 10,
      "signature": "structure SixVertexGraph (P : ConvexPolyhedron) where\n  kind : SmallGraphs.SixGraphKind\n  vertex : Fin 6 ≃ P.Vertex\n  edges : ∀ i j : Fin 6, P.edgeGraph.Adj (vertex i) (vertex j) ↔\n    i ≠ j ∧ s(i, j) ∉ kind.missingEdges",
      "context": "",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "SmallPolyhedronCutTree:small_cut_tree_open_edge_two_routes": {
      "name": "small_cut_tree_open_edge_two_routes",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.small_cut_tree_open_edge_two_routes",
      "kind": "theorem",
      "module": "SmallPolyhedronCutTree",
      "line": 43,
      "signature": "theorem small_cut_tree_open_edge_two_routes (a : frontier P.body) (T : P.CutLocusTree a)\n    {u v : T.vertices} (edge : T.graph.Adj u v) (b : frontier P.body)\n    (inside : (b : Space) ∈ openSegment ℝ (u : Space) (v : Space)) :\n    Nat.card (P.geodesicFiber a b) = 2",
      "context": "open tree edge contains exactly two shortest routes to each of its points. -/\nopen Set\nvariable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)\ninclude size small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "SmallPolyhedronCutTree:small_exists_regular_cut_tree": {
      "name": "small_exists_regular_cut_tree",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.small_exists_regular_cut_tree",
      "kind": "theorem",
      "module": "SmallPolyhedronCutTree",
      "line": 29,
      "signature": "theorem small_exists_regular_cut_tree (a : frontier P.body) : Nonempty (P.CutLocusTree a)",
      "context": "open tree edge contains exactly two shortest routes to each of its points. -/\nopen Set\nvariable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)\ninclude size small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "SmallPolyhedronShortestRoutes:small_shortest_routes_agree_of_meeting": {
      "name": "small_shortest_routes_agree_of_meeting",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.small_shortest_routes_agree_of_meeting",
      "kind": "theorem",
      "module": "SmallPolyhedronShortestRoutes",
      "line": 62,
      "signature": "theorem small_shortest_routes_agree_of_meeting\n    (first second : P.SurfacePath a b) (different : a ≠ b)\n    (first_shortest : first.IsShortest) (second_shortest : second.IsShortest)\n    (first_finite : first.length ≠ ⊤) (second_finite : second.length ≠ ⊤)\n    (first_speed : LipschitzWith first.length.toNNReal first.curve)\n    (second_speed : LipschitzWith second.length.toNNReal second.curve)\n    (m : unitInterval) (after_start : 0 < m) (before_end : m < 1)\n    (meet : first.curve m = second.curve m) : ∀ t, first.curve t = second.curve t",
      "context": "open Set\nvariable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)\n  {a b : Space}\ninclude size small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "SmallPolyhedronTerminalRays:small_geodesic_proper_prefix_outside_cutSet": {
      "name": "small_geodesic_proper_prefix_outside_cutSet",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.small_geodesic_proper_prefix_outside_cutSet",
      "kind": "theorem",
      "module": "SmallPolyhedronTerminalRays",
      "line": 64,
      "signature": "theorem small_geodesic_proper_prefix_outside_cutSet (f : P.BoundaryCurve) (geodesic : f ∈ P.geodesicCurves)\n    (different : f 0 ≠ f 1) (t : unitInterval) (before : t < 1) : f t ∉ P.cutSet (f 0)",
      "context": "open Set Filter BoundedContinuousFunction\nopen scoped Topology ENNReal\nvariable {P : ConvexPolyhedron} (size : P.vertices.card ≤ 6)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)\ninclude size small_faces in",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron",
      "proofHole": false
    },
    "StarLocalMetric:develop_locally_isometric": {
      "name": "develop_locally_isometric",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.develop_locally_isometric",
      "kind": "theorem",
      "module": "StarLocalMetric",
      "line": 18,
      "signature": "theorem develop_locally_isometric {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)\n    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))\n    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)\n    (b : P.UncutSurface a) :\n    ∃ radius > 0, ∀ c d : P.UncutSurface a,\n      dist (c.val : Space) (b.val : Space) < radius →\n      dist (d.val : Space) (b.val : Space) < radius →\n      dist (charts.develop c.val) (charts.develop d.val) = P.surfaceDist c.val d.val",
      "context": "open Set\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)\ninclude graph small_faces",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "StarOpenEmbedding:develop_isOpenEmbedding": {
      "name": "develop_isOpenEmbedding",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.develop_isOpenEmbedding",
      "kind": "theorem",
      "module": "StarOpenEmbedding",
      "line": 56,
      "signature": "theorem develop_isOpenEmbedding {a : frontier P.body} {T : P.CutLocusTree a} (charts : CutTreeCharts T)\n    (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))\n    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :\n    Topology.IsOpenEmbedding (fun b : P.UncutSurface a => charts.develop b.val)",
      "context": "open Set Filter Topology\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "StarPolygonBoundary:develop_frontier_eq_segments": {
      "name": "develop_frontier_eq_segments",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.develop_frontier_eq_segments",
      "kind": "theorem",
      "module": "StarPolygonBoundary",
      "line": 60,
      "signature": "theorem develop_frontier_eq_segments {a : frontier P.body} {T : P.CutLocusTree a}\n    (charts : CutTreeCharts T) (source : Fin 6) (at_source : (a : Space) = (graph.vertex source : Space))\n    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val) :\n    frontier (range (fun c : P.UncutSurface a => charts.develop c.val)) =\n      ⋃ e ∈ charts.boundarySegments, segment ℝ e.1 e.2",
      "context": "open Set\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "UniqueRouteLeaves:cofacial_source_leaf_iff_original": {
      "name": "cofacial_source_leaf_iff_original",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph.cofacial_source_leaf_iff_original",
      "kind": "theorem",
      "module": "UniqueRouteLeaves",
      "line": 48,
      "signature": "theorem cofacial_source_leaf_iff_original (a : frontier P.body) (T : P.CutLocusTree a)\n    (cofacial : ∀ v : P.Vertex, ∃ F : P.Face, (a : Space) ∈ F.val ∧ (v : Space) ∈ F.val)\n    (u : T.vertices) : (∃! v, T.graph.Adj u v) ↔ (u : Space) ∈ P.vertices",
      "context": "open Set\nvariable {P : ConvexPolyhedron} (graph : P.SixVertexGraph)\n  (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n    (F.val ∩ (P.vertices : Set Space)).ncard = 4)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.SixVertexGraph",
      "proofHole": false
    },
    "VertexFanAngles:totalAngle": {
      "name": "totalAngle",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan.totalAngle",
      "kind": "def",
      "module": "VertexFanAngles",
      "line": 18,
      "signature": "noncomputable def totalAngle : ℝ := ∑ i : Fin n, fan.sectorAngle i",
      "context": "open Set Real InnerProductGeometry\nvariable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]\n  (fan : P.VertexFaceFan pole n)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan",
      "proofHole": false
    },
    "VertexFanAngles:totalAngle_lt_two_pi": {
      "name": "totalAngle_lt_two_pi",
      "qualified": "SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan.totalAngle_lt_two_pi",
      "kind": "theorem",
      "module": "VertexFanAngles",
      "line": 44,
      "signature": "theorem totalAngle_lt_two_pi (size : P.vertices.card ≤ 6)\n    (small_faces : ∀ F : P.Face, (F.val ∩ (P.vertices : Set Space)).ncard = 3 ∨\n      (F.val ∩ (P.vertices : Set Space)).ncard = 4) : fan.totalAngle < 2 * π",
      "context": "open Set Real InnerProductGeometry\nvariable {P : ConvexPolyhedron} {pole : P.Vertex} {n : ℕ} [NeZero n]\n  (fan : P.VertexFaceFan pole n)",
      "namespace": "SixVertexUnfolding.ConvexPolyhedron.VertexFaceFan",
      "proofHole": false
    },
    "WedgeRootMove:kite_subset_region": {
      "name": "kite_subset_region",
      "qualified": "SixVertexUnfolding.Wedge.kite_subset_region",
      "kind": "theorem",
      "module": "WedgeRootMove",
      "line": 184,
      "signature": "theorem kite_subset_region {h r q a b : ℝ} (height_pos : 0 < h)\n    (outward : 0 ≤ h * b - r * a) : kite h r q ⊆ region h q a b",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "WedgeRootMove:move_root": {
      "name": "move_root",
      "qualified": "SixVertexUnfolding.Wedge.move_root",
      "kind": "theorem",
      "module": "WedgeRootMove",
      "line": 206,
      "signature": "theorem move_root {h r q a b : ℝ} (height_pos : 0 < h) (order : r ≤ q)\n    (outward : 0 ≤ h * b - r * a) :\n    region h q a b = region h r a b ∪ kite h r q",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "WedgeRootMove:next_kite_outside": {
      "name": "next_kite_outside",
      "qualified": "SixVertexUnfolding.Wedge.next_kite_outside",
      "kind": "theorem",
      "module": "WedgeRootMove",
      "line": 214,
      "signature": "theorem next_kite_outside {h r q a b : ℝ} (height_pos : 0 < h)\n    (outward : 0 ≤ h * b - q * a) :\n    Disjoint (region h r a b) (openKite h r q)",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "WedgeRootMove:region": {
      "name": "region",
      "qualified": "SixVertexUnfolding.Wedge.region",
      "kind": "def",
      "module": "WedgeRootMove",
      "line": 18,
      "signature": "def region (h r a b : ℝ) : Set Plane := {z |\n  (h ≤ |z 1| ∧ (if 0 < b then b * z 0 ≤ a * (|z 1| - h) else 0 < a)) ∨\n  (|z 1| ≤ h ∧\n    (if 0 ≤ b then h * z 0 ≤ r * (h - |z 1|)\n     else if a < 0 then\n       h * z 0 ≤ r * (h - |z 1|) ∧ b * z 0 ≤ a * (|z 1| - h)\n     else h * z 0 ≤ r * (h - |z 1|) ∨ b * z 0 ≤ a * (|z 1| - h)))}",
      "context": "open Set",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "WedgeRotation:polarRegion": {
      "name": "polarRegion",
      "qualified": "SixVertexUnfolding.Wedge.polarRegion",
      "kind": "def",
      "module": "WedgeRotation",
      "line": 130,
      "signature": "noncomputable def polarRegion (d γ lower upper : ℝ) : Set Plane := {z |\n  z = 0 ∨ ∃ ρ θ : ℝ, 0 < ρ ∧ z = ρ • direction θ ∧\n    lower + offset d γ ρ ≤ θ ∧ θ ≤ upper - offset d γ ρ}",
      "context": "open Real Set",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "WedgeRotation:rotate_arms": {
      "name": "rotate_arms",
      "qualified": "SixVertexUnfolding.Wedge.rotate_arms",
      "kind": "theorem",
      "module": "WedgeRotation",
      "line": 136,
      "signature": "theorem rotate_arms {d γ lower₁ upper₁ lower₂ upper₂ : ℝ}\n    (lower_moves : lower₂ ≤ lower₁) (upper_moves : upper₁ ≤ upper₂) :\n    polarRegion d γ lower₁ upper₁ ⊆ polarRegion d γ lower₂ upper₂",
      "context": "open Real Set",
      "namespace": "SixVertexUnfolding.Wedge",
      "proofHole": false
    },
    "WedgeStep:rotate_and_move": {
      "name": "rotate_and_move",
      "qualified": "SixVertexUnfolding.Wedge.ArmCoordinates.rotate_and_move",
      "kind": "theorem",
      "module": "WedgeStep",
      "line": 94,
      "signature": "theorem rotate_and_move {q D Θ lower upper : ℝ}\n    (order : r ≤ q) (radius : 0 < D) (angle_pos : 0 < Θ) (angle_lt_pi : Θ < π)\n    (source_x : -q = D * cos Θ) (source_y : h = D * sin Θ)\n    (lower_moves : θ ≤ lower) (upper_moves : upper ≤ 2 * π - θ)\n    (budget : γ + EuclideanGeometry.angle (point r 0) (point 0 h) (point q 0) ≤ 3 * π / 2) :\n    let α := EuclideanGeometry.angle (point r 0) (point 0 h) (point q 0)\n    let W : Set Plane := {z | z - point r 0 ∈ polarRegion d γ lower upper}\n    let V : Set Plane := {z | z - point r 0 ∈ polarRegion d γ θ (2 * π - θ)}\n    let W' : Set Plane := {z | z - point q 0 ∈\n      polarRegion D (γ + α) Θ (2 * π - Θ)}\n    W ⊆ V ∧ Disjoint V (interior (kite h r q)) ∧ W' = V ∪ kite h r q",
      "context": "open Real Set\nvariable {h r a b d θ γ : ℝ} (C : ArmCoordinates h r a b d θ γ)",
      "namespace": "SixVertexUnfolding.Wedge.ArmCoordinates",
      "proofHole": false
    }
  },
  "sources": {
    "CanonicalSixGraphs": {
      "path": "SixVertexUnfolding/CanonicalSixGraphs.lean",
      "sha256": "0cdbbf33dee6f6aaa5411cd0ab5a38807cc57627a0748e9be99c6562101c6da1"
    },
    "ClosedCutSet": {
      "path": "SixVertexUnfolding/Geometry/ClosedCutSet.lean",
      "sha256": "aa5004ee116f1b60b868629f6b5518e1cdb9d77d46de6821d43e9340d3e43664"
    },
    "CofacialStarCuts": {
      "path": "SixVertexUnfolding/Geometry/CofacialStarCuts.lean",
      "sha256": "0c7b8aee498bd8445fef847c78a7e5242e9ffcbe55896439f2cecdd8ef998053"
    },
    "CofacialStarEmbedding": {
      "path": "SixVertexUnfolding/Geometry/CofacialStarEmbedding.lean",
      "sha256": "86defbc1d1d91e26c0545a79f399c28fad39be3b9660a9407bffacb0c253e1d0"
    },
    "CutEdgeMetricModel": {
      "path": "SixVertexUnfolding/Geometry/CutEdgeMetricModel.lean",
      "sha256": "f08889cf37aefbbeb1533fb1bcf454896e8d306a9dc5aec86cd02d12a4c00f91"
    },
    "CutEdgeSourceAngles": {
      "path": "SixVertexUnfolding/Geometry/CutEdgeSourceAngles.lean",
      "sha256": "3a4479da675c30fc30c64f17895f7c30c16de8c80084d83a631baa07e1a6b7e0"
    },
    "CutEdgeTriangles": {
      "path": "SixVertexUnfolding/Geometry/CutEdgeTriangles.lean",
      "sha256": "eda1afeabcd2e58c2ec89e8a62544e04cc0b09a554fc474a65cf8705a9fb00dc"
    },
    "CutSetVertexLimits": {
      "path": "SixVertexUnfolding/Geometry/CutSetVertexLimits.lean",
      "sha256": "21cb01adfb8193f2802c519aad0326faeebc5218d4ece756d59040ff4e842f9a"
    },
    "CutTreeChainSeparation": {
      "path": "SixVertexUnfolding/Geometry/CutTreeChainSeparation.lean",
      "sha256": "06879b165e6d39d48d18322ac68f139a7ee347ed3f0bdf5e0f21ac936ddcfa1b"
    },
    "CutTreeCharts": {
      "path": "SixVertexUnfolding/Geometry/CutTreeCharts.lean",
      "sha256": "7c728b898e9ad96fdd8070119bb0666832d5c9c12913932635f816a402853c21"
    },
    "CutTreeConeCoverage": {
      "path": "SixVertexUnfolding/Geometry/CutTreeConeCoverage.lean",
      "sha256": "dbb52070a2da4aa5507b8e9948a9cc3c0ffbd79a04238912a31a9ed7320de2b2"
    },
    "CutTreeCurvature": {
      "path": "SixVertexUnfolding/Geometry/CutTreeCurvature.lean",
      "sha256": "38e833e92a552193e07ba85efa912dc04151827c48f4e8de1b355b820dfdacb9"
    },
    "CutTreeSourceBudget": {
      "path": "SixVertexUnfolding/Geometry/CutTreeSourceBudget.lean",
      "sha256": "8600f499f4e9d9f100f5ec073c0c09e336304430da3c4a2fdd929951d30bd37a"
    },
    "CutTreeTriangleCoverage": {
      "path": "SixVertexUnfolding/Geometry/CutTreeTriangleCoverage.lean",
      "sha256": "ef8da9ddfc98d5b50f0c4a3639872406d627b71268609fc9c026f6c1408798ca"
    },
    "Definitions": {
      "path": "SixVertexUnfolding/Definitions.lean",
      "sha256": "68c780075a74cbe7fa8f51dcc3831d2ef1b7da9ee5f39d204f122cbd9dac35ef"
    },
    "EmbeddedCutGraph": {
      "path": "SixVertexUnfolding/Geometry/EmbeddedCutGraph.lean",
      "sha256": "e162026d13a73fafa07b92ba1283e580152988d89724f543c274e03d90dfdd51"
    },
    "ExpandingRegionChains": {
      "path": "SixVertexUnfolding/Geometry/ExpandingRegionChains.lean",
      "sha256": "a0fb9481f8ddb4393b3da9663fb54b920e6ad716e77a7138a60c84e9e2daf144"
    },
    "GapKiteStep": {
      "path": "SixVertexUnfolding/Geometry/GapKiteStep.lean",
      "sha256": "8c8b12e4ad334446b14e24a5102657e14aa556bcf88232bd5697bc58c0cd20ed"
    },
    "GlobalKiteSeparation": {
      "path": "SixVertexUnfolding/Geometry/GlobalKiteSeparation.lean",
      "sha256": "08904ad739fa15bb906812c5869f3035642f4ec49e67908058aaf018e5f59387"
    },
    "InitialKiteWedge": {
      "path": "SixVertexUnfolding/Geometry/InitialKiteWedge.lean",
      "sha256": "6dce3b434fbc7e3a199856db5c28e7e75bb99e4b38c8d6aed3a0019082afef0b"
    },
    "JunctionWedgeStep": {
      "path": "SixVertexUnfolding/Geometry/JunctionWedgeStep.lean",
      "sha256": "ab06578dbf02f0f46866e885ed5caa228717f54ae098b6830c1711bc4d40df9c"
    },
    "MultipleShortestRoutes": {
      "path": "SixVertexUnfolding/Geometry/MultipleShortestRoutes.lean",
      "sha256": "23050b33c9b46baff6b494af80c1c4921bfcd48b7d8e4774f510e00abbaf8df4"
    },
    "RegularCutTree": {
      "path": "SixVertexUnfolding/Geometry/RegularCutTree.lean",
      "sha256": "324af0598e1fd9e027fdd0518f2c88ab6646df179592ae1e10dcc781f0464907"
    },
    "RetainedCutConnectivity": {
      "path": "SixVertexUnfolding/Geometry/RetainedCutConnectivity.lean",
      "sha256": "bc5e4bd9c751d098ed5e52887d311686752664379f5b8851972c6db7b1912aed"
    },
    "SixVertexGraphs": {
      "path": "SixVertexUnfolding/Geometry/SixVertexGraphs.lean",
      "sha256": "4317cd118b6c798490cbc45ae5024eefcf56c15dc90dbf6fe39f8f8c228e2f8f"
    },
    "SmallPolyhedronCutTree": {
      "path": "SixVertexUnfolding/Geometry/SmallPolyhedronCutTree.lean",
      "sha256": "d8c3d2512ab189fac07db833e31bdf7690a8598a26fdd08e1b483c9322d8e32c"
    },
    "SmallPolyhedronShortestRoutes": {
      "path": "SixVertexUnfolding/Geometry/SmallPolyhedronShortestRoutes.lean",
      "sha256": "525363d66dc540d7799f8732de4571e32d42d42ad990622a940adf16793d0b03"
    },
    "SmallPolyhedronTerminalRays": {
      "path": "SixVertexUnfolding/Geometry/SmallPolyhedronTerminalRays.lean",
      "sha256": "3837ed6d3adabf542527cef30fd4888d370d6c5481a8193eb2c790f0012e124f"
    },
    "StarLocalMetric": {
      "path": "SixVertexUnfolding/Geometry/StarLocalMetric.lean",
      "sha256": "f467ab8b728c44c72e8c8bb32b79fd4a83e544ae0e297f738bfed5fa4f7c3a83"
    },
    "StarOpenEmbedding": {
      "path": "SixVertexUnfolding/Geometry/StarOpenEmbedding.lean",
      "sha256": "bcc8d5c0403a1bdf12694a7ba1eb788735f72623186c8b219f42477fca390a6b"
    },
    "StarPolygonBoundary": {
      "path": "SixVertexUnfolding/Geometry/StarPolygonBoundary.lean",
      "sha256": "a9812afdb15149d90c87c8d7753eb8a63732a89efbc0c948fa94810683e3784c"
    },
    "UniqueRouteLeaves": {
      "path": "SixVertexUnfolding/Geometry/UniqueRouteLeaves.lean",
      "sha256": "a702c124af5c10aa8c490b9a722ee2c4dc0405b24ca2dcc8ab0efb132d00c4e0"
    },
    "VertexFanAngles": {
      "path": "SixVertexUnfolding/Geometry/VertexFanAngles.lean",
      "sha256": "2aed7155134da4f8fa7687f5caf7607f5f6ff074c44d8754b208ef89b8b6affb"
    },
    "WedgeRootMove": {
      "path": "SixVertexUnfolding/Geometry/WedgeRootMove.lean",
      "sha256": "be2cd9937923e6c7a5d24cef66bf9c9ae4d1dbe47c3ab095f23978153fb33c01"
    },
    "WedgeRotation": {
      "path": "SixVertexUnfolding/Geometry/WedgeRotation.lean",
      "sha256": "f8c7cc7380371f59e00b78db8e520905418fe9c8783eca85f8563165c7d8e4b0"
    },
    "WedgeStep": {
      "path": "SixVertexUnfolding/Geometry/WedgeStep.lean",
      "sha256": "4a9a85a9e647c5b636b2749ecae1bc25782a875beec34d85c3fbd04052dd24ce"
    }
  },
  "revision": "99e7591f252351d873bb51676f1294899fceecfe",
  "date": "2026-09-16",
  "paper": [
    {
      "id": "definition-1",
      "section": "1.1",
      "title": "Definition 1 · The point star",
      "text": "Definition 1 Let P be a convex polyhedron, and let x be a point on P. The star unfolding, Sₓ, is a 2-dimensional polygon formed by cutting P along a shortest path from every vertex of P to x, and flattening the result into the plane. See Fig. 2. Note that there is a choice of cuts if a vertex has more than one shortest path to x.",
      "kind": "claim"
    },
    {
      "id": "boundary",
      "section": "1.1",
      "title": "Boundary images",
      "text": "If P has n vertices, then the polygon Sₓ will have 2n vertices in general, and 2(n − 1) vertices if x is located at a vertex of P. The vertices of Sₓ alternate around the boundary between vertex images, denoted vᵢ , that correspond to the vertices of P, and n ‘copies’ of x, called source images and denoted by xᵢ . See Fig. 2. The edges of Sₓ correspond to the shortest path cuts made from each vertex to x. Therefore, the two edges incident to any vertex image vᵢ are always the same length.",
      "kind": "paragraph"
    },
    {
      "id": "cut-tree",
      "section": "1.1",
      "title": "The cut locus is a tree",
      "text": "The cut locus (or “ridge tree”), Tₓ, is the closure of the set of all points on the surface of P that have more than one shortest path to x. It is known that the cut locus is a tree [12], and that its edges are shortest paths [1] and thus correspond to straight-line segments in Sₓ. See Fig. 2b. As a corollary to their proof of non-overlap [3, Thm. 10.2], Aronov and O’Rourke proved that the cut locus is a subset of the Voronoi diagram of the images of x, but we will not use this result.",
      "kind": "paragraph"
    },
    {
      "id": "point-only",
      "section": "1.1",
      "title": "Reading the point case",
      "text": "Readers interested only in the point case may proceed directly to Sect. 2. In the next subsection we give definitions for the star unfolding from a geodesic curve.",
      "kind": "paragraph"
    },
    {
      "id": "geodesic",
      "section": "1.2",
      "title": "Geodesic and quasigeodesic curves",
      "text": "Given a polyhedron P, a geodesic curve λ on P is a curve on the surface of P, such that at every interior point p of λ, the surface angle to either side of p is exactly π . If the surface angle to either side of p is at most π then the curve is called a quasigeodesic. We will only consider [quasi]geodesic curves that are simple, meaning there is no point of self-intersection between any two interior (i.e., non-endpoint) points of the curve.",
      "kind": "paragraph"
    },
    {
      "id": "definition-2",
      "section": "1.2",
      "title": "Definition 2 · A curve source",
      "text": "Definition 2 Let P be a convex polyhedron, and let λ be a simple geodesic curve on the surface of P. The geodesic star unfolding Sλ is a 2-dimensional polygon formed by cutting λ, and cutting a shortest path along the surface of P from every vertex vᵢ of P to λ, and flattening the result into the plane. See ahead to Fig. 6.",
      "kind": "claim"
    },
    {
      "id": "curve-sides",
      "section": "1.2",
      "title": "Endpoints and sides",
      "text": "The endpoints of λ are labelled a and b and the two sides of λ are labelled s and t, with the convention that the clockwise order around λ on the outside surface of P is a, s, b, t. We distinguish shortest paths to λ that arrive at (or “report to”) a or b, and shortest paths that arrive at interior points of λ on side s or t. Any shortest path that arrives at an interior point of λ forms a right angle with λ, as shown by the following lemma, which is a special case of [9, Lem. 1].",
      "kind": "paragraph"
    },
    {
      "id": "lemma-1",
      "section": "1.2",
      "title": "Lemma 1 · Arrival angles",
      "text": "Lemma 1 Let λ be a [quasi]geodesic curve on a convex polyhedron P, with points x₀ on λ and x not on λ such that xx₀ is a shortest path from x to λ. The angles formed between xx₀ and λ are at least π/2 to each side.",
      "kind": "claim"
    },
    {
      "id": "curve-images",
      "section": "1.2",
      "title": "Point and segment images",
      "text": "In the unfolding Sλ, a source image is either a copy of an endpoint (a or b), called a point image, or a sub-segment of λ corresponding to side s or t, called a segment image. (Note that a segment image might include one of the endpoints of λ.) Around a clockwise traversal of the boundary of Sλ we encounter source images in order a, s, b, t—this is because our convention is to draw the inside of the polyhedron’s surface facing up. Each consecutive pair of source images is separated by two edges of equal length joined at a vertex image, such that the edges correspond to the shortest path cut at the vertex.",
      "kind": "paragraph"
    },
    {
      "id": "curve-tree",
      "section": "1.2",
      "title": "The geodesic cut locus",
      "text": "The cut locus of a geodesic λ, denoted Tλ, is the closure of the set of all points on the surface of P that have more than one shortest path to λ. The cut locus of a geodesic is a tree [13]. (An alternate proof can be found in [4, Lem. 4]. The lemma applies to the outside of any closed convex curve on the surface of P—in the present situation, the closed convex curve is the set of points at some fixed distance ε from λ.) See ahead to Fig. 6.",
      "kind": "paragraph"
    },
    {
      "id": "curve-edges",
      "section": "1.2",
      "title": "Straight and parabolic edges",
      "text": "A key difference from the point case is that the edges of the geodesic cut locus are not necessarily straight-line segments. Every edge of the cut locus is the locus of points that are equidistant from two source images. Thus, when the two sources to either side of an edge are a point image and a segment image respectively, a parabolic cut locus edge will result. The cut locus edges between pairs of point images or pairs of segment images will still be straight.",
      "kind": "paragraph"
    },
    {
      "id": "section-2-intro",
      "section": "2",
      "title": "A new non-overlap proof",
      "text": "In this section we give a new proof of non-overlap for the point star unfolding that is simpler than the original proof of Aronov and O’Rourke [3].",
      "kind": "paragraph"
    },
    {
      "id": "kites",
      "section": "2",
      "title": "Partition into congruent triangle pairs",
      "text": "The most important idea of our proof is to partition the star unfolding into pairs of congruent triangles. Each vertex of the cut locus has three or more shortest paths to x on the surface of P. Add all these shortest paths as line segments in the star unfolding. We use the following basic properties of shortest paths: (1) no two shortest paths to x (or more generally, to a geodesic curve) cross each other [9, Lem. 2] (their lemma is stated for vertices of the polyhedron, but applies more generally); and (2) no shortest path crosses the cut locus [12, Lem. 4.2]. These properties imply that when we add the line segments corresponding to shortest paths between x and cut locus vertices, each edge of the cut locus will have a triangle to each side. Because all shortest paths from a cut locus vertex to the nearest source images have the same length, the two triangles to either side of a cut locus edge have corresponding sides of equal length, and therefore are congruent. We call each such pair of triangles a kite. The kite associated with cut locus edge e is denoted kite(e). The two images of x to each side of e are called the apex vertices of the kite. Observe that the kites form a partition of Sₓ. See Fig. 2b.",
      "kind": "paragraph"
    },
    {
      "id": "source-budget",
      "section": "2",
      "title": "The source-angle budget",
      "text": "We define the source angle of e, α(e), to be the interior angle at either apex of kite(e). See Fig. 2b. We extend this definition to paths as follows. For a path σ of cut locus edges, where σ = e₁, …, eₜ, the source angle of σ is α(σ) = ∑ᵢ₌₁ᵗ α(eᵢ). Observe that α(σ) ≤ π because 2α(σ) measures the total source angle at both apex vertices of every kite on the path, so this is bounded by the total surface angle at the source point x, which is bounded by 2π.",
      "kind": "paragraph"
    },
    {
      "id": "theorem-1",
      "section": "2",
      "title": "Theorem 1 · Non-overlap",
      "text": "Theorem 1 [3, Thm. 9.1] The star unfolding Sₓ does not overlap.",
      "kind": "claim"
    },
    {
      "id": "path-reduction",
      "section": "2",
      "title": "Reduce to a path of kites",
      "text": "Proof We will show that no two kites overlap. Consider two kites, and the path in the cut locus between them. Let e₁ , . . . , eₜ be the edges of the path in the cut locus with eᵢ joining cut locus vertices pᵢ₋₁ and pᵢ . Let kᵢ = kite(eᵢ ). We will show that k₁ and kₜ have disjoint interiors. We will define a sequence of regions W₁ , . . . , Wₜ₋₁ , called W-wedges, so that Wᵢ includes k₁ , . . . , kᵢ and excludes kᵢ₊₁ . Then Wₜ₋₁ includes k₁ and excludes kₜ , which will complete the proof.",
      "kind": "paragraph"
    },
    {
      "id": "wedge-definition",
      "section": "2",
      "title": "Define the W-wedges",
      "text": "The boundary of the W-wedge Wᵢ consists of four edges, generally shaped like a ‘W’ and defined as follows. The center point of Wᵢ is the point pᵢ, where eᵢ and eᵢ₊₁ intersect; the inner legs are the edges of kᵢ that are incident to pᵢ; and the outer legs form an angle with the inner legs (on the side of kᵢ) of π/2 + αᵢ, where αᵢ = ∑ⱼ₌₁ⁱ α(eⱼ). The outer legs extend either to their point of intersection, or as infinite rays if they do not intersect. This boundary divides the plane into two regions and we define Wᵢ to be the region containing kᵢ in a neighbourhood of pᵢ. We also define W₀ to have center point p₀, with inner legs along the edges of k₁ and outer legs rotated outward (on the opposite side from k₁) by π/2. See Fig. 4. Note that αᵢ is in the range [0, π] as observed above.",
      "kind": "paragraph"
    },
    {
      "id": "induction-goal",
      "section": "2",
      "title": "The induction invariant",
      "text": "We will prove by induction that kᵢ is outside Wᵢ₋₁ and that Wᵢ contains kᵢ ∪ Wᵢ₋₁ . At each step, including the base case, we will need the following:",
      "kind": "paragraph"
    },
    {
      "id": "lemma-2",
      "section": "2",
      "title": "Lemma 2 · Enclose one kite",
      "text": "Lemma 2 Let p be an endpoint of cut locus edge e, and let W be a W-wedge centered at p such that the inner legs of W are edges of kite(e), and the outer legs are rotated out (on the side of kite(e)) by an angle θ in the range [π/2 + α(e), 3π/2]. Then kite(e) ⊆ W.",
      "kind": "claim"
    },
    {
      "id": "lemma-2-proof",
      "section": "2",
      "title": "Proof of Lemma 2",
      "text": "Proof Consider the two circular sectors aₚ and a_q centered at the endpoints p and q of e and bounded by the two incident kite edges as radii (see Fig. 3). At each apex of kite(e) the angles between the outer leg of W and the two sides of kite(e) are at least π/2. Thus the circular sector a_q is inside W, and the circular sector aₚ is outside W. This implies that kite(e) ⊆ W. □",
      "kind": "paragraph"
    },
    {
      "id": "base-case",
      "section": "2",
      "title": "Base case",
      "text": "We are now ready to prove by induction that kᵢ is outside Wᵢ₋₁ and that Wᵢ contains kᵢ ∪ Wᵢ₋₁ . For the base case i = 1, k₁ is outside W₀ by the lemma above (applied to the outside of W₀ ), and W₁ contains k₁ ∪ W₀ by the same lemma.",
      "kind": "paragraph"
    },
    {
      "id": "induction-step",
      "section": "2",
      "title": "Induction step",
      "text": "For the induction step we consider i > 1. Suppose by induction that Wᵢ₋₁ contains kᵢ₋₁ ∪ Wᵢ₋₂ . We will show how to transform Wᵢ₋₁ into Wᵢ in a way that makes it clear that kᵢ is outside Wᵢ₋₁ and Wᵢ contains kᵢ ∪ Wᵢ₋₁ .",
      "kind": "paragraph"
    },
    {
      "id": "rotate",
      "section": "2",
      "title": "First move · Rotate the arms",
      "text": "Note that the unfolding does not overlap in the neighbourhood of point pᵢ—this is true whether pᵢ is a point with 2π surface area, or a vertex, which will be incident to a single cut. Thus the kites kᵢ and kᵢ₋₁, which are both incident to pᵢ, do not overlap. Rotate each of the inner legs of Wᵢ₋₁ about point pᵢ₋₁, away from kᵢ₋₁ to the edge of kᵢ. This is a rotation by 0° when an edge of kᵢ₋₁ is coincident with an edge of kᵢ. Keep the angle between inner and outer legs fixed throughout the rotation. Observe that all the kite edges incident to pᵢ₋₁ have the same length, so we really perform a rigid transformation on each half of the W. Call the resulting W-wedge W′ᵢ (shown as a dashed poly-line in Fig. 4). Notice that W′ᵢ contains Wᵢ₋₁, because the angle αᵢ₋₁ + π/2 is in the range [π/2, 3π/2] so the outer legs remain outside the rotation sector of the inner legs. (Here it is crucial that we added the extra π/2 to the initial angle.) That kᵢ is outside W′ᵢ follows from applying Lemma 2 to the outside of W′ᵢ, noting that αᵢ₋₁ + α(eᵢ) ≤ π so the angle αᵢ₋₁ + π/2 is in the range [π/2, 3π/2 − α(eᵢ)] and therefore the complementary angle is in the range [α(eᵢ) + π/2, 3π/2].",
      "kind": "paragraph"
    },
    {
      "id": "move-center",
      "section": "2",
      "title": "Second move · Move the center",
      "text": "The second step of the transformation is to move the center point of W′ᵢ from pᵢ₋₁ to pᵢ, while keeping the outer legs fixed. The W-wedge increases until it contains kᵢ. The angle between inner and outer legs increases by α(eᵢ), to αᵢ. Thus the result is precisely Wᵢ, and therefore Wᵢ contains kᵢ ∪ Wᵢ₋₁.",
      "kind": "paragraph"
    },
    {
      "id": "empty-regions",
      "section": "2",
      "title": "A stronger empty-region result",
      "text": "Our proof, like Aronov and O’Rourke’s, shows a stronger result that certain regions outside the star unfolding are empty. Aronov and O’Rourke [3] showed that at any vertex vᵢ adjacent to source images xᵢ and xᵢ₊₁ in the unfolding, no part of the unfolding enters the circular sector centered at vᵢ exterior to the unfolding near vᵢ and bounded by the radii vᵢ xᵢ and vᵢ xᵢ₊₁ . See Fig. 5. Our proof shows that larger regions are empty, as formalized in the following lemma.",
      "kind": "paragraph"
    },
    {
      "id": "lemma-3",
      "section": "2",
      "title": "Lemma 3 · Exterior empty region",
      "text": "Lemma 3 Let vᵢ be a vertex image adjacent to source images xᵢ and xᵢ₊₁ on the boundary of a star unfolding Sₓ, and let W be the region bounded by vᵢ xᵢ , vᵢ xᵢ₊₁ , and the rays extending from xᵢ and xᵢ₊₁ at right angles from these segments on the exterior side of vᵢ . Then no part of the unfolding intersects the interior of W .",
      "kind": "claim"
    },
    {
      "id": "lemma-3-leaf",
      "section": "2",
      "title": "Lemma 3 · Leaf case",
      "text": "Proof In non-degenerate situations, vᵢ is a leaf of the cut locus. Let e be the cut locus edge incident to vᵢ . For any kite k = kite( f ) of the unfolding, consider the path in the cut locus starting with e and ending with f , and apply the above proof to this path. Wedge W in the statement of the lemma is wedge W₀ in the proof, and the proof shows that kite k does not enter wedge W₀ .",
      "kind": "paragraph"
    },
    {
      "id": "lemma-3-internal",
      "section": "2",
      "title": "Lemma 3 · Internal original vertex",
      "text": "More generally, vᵢ may be an internal vertex of the cut locus with more than one incident cut locus edge, and we need a slight generalization of this argument. Consider any kite k = kite( f ) of the unfolding, and consider the path in the cut locus starting with vᵢ and ending with f . Apply the above proof to this path. The path will use one of the cut locus edges incident to vᵢ . The crucial observation is that wedge W in the statement of the lemma is a subset of wedge W₀ in the proof for this path. The proof shows that kite k does not enter wedge W₀ , and therefore k does not enter W . □",
      "kind": "paragraph"
    }
  ],
  "figures": {
    "2": "The star unfolding from a point. a The polyhedron, the source point x, and the shortest paths from vertices to the source point. b The corresponding star unfolding. The cut locus is the internal tree drawn with solid grey edges. The kites are shown with dashed lines. The kite on cut locus edge e is shaded, and its source angle α(e) is indicated. Note that the unfolding shows the inside surface of the polyhedron.",
    "3": "Illustration for the proof of Lemma 2. Angle θ is in the range [π/2 + α(e), 3π/2] and thus the outer leg of W lies between the tangents (dashed) to the circular arcs aₚ and a_q.",
    "4": "Kite kᵢ₋₁ (shaded) and the corresponding W-wedge Wᵢ₋₁ (lightly shaded). In the base case, kite k₁ is outside the W-wedge W₀ (very lightly shaded), and W₁ contains k₁ ∪ W₀. To prove by induction that Wᵢ contains all previous kites, we expand Wᵢ₋₁, first rotating the legs about pᵢ₋₁ to the W-wedge W′ᵢ (dashed line), and then moving the center point to pᵢ to obtain Wᵢ. Note that although the figure shows kites kᵢ₋₁ and kᵢ sharing only a vertex, in non-degenerate situations cut locus vertices have degree 3, and two consecutive kites will share an edge as well.",
    "5": "Old sectors of emptiness (light grey) established by Aronov and O’Rourke and new empty regions (light grey + dark grey) established by Lemma 3."
  }
};
