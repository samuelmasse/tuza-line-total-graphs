# Separate informal orientation refinement

This result was Proposition 5.1 of the 7 September 2026 manuscript. It is
preserved here as a separate informal note because it has not been formalized
in Lean. It is not part of the revised paper's formal-verification claim or
the four Palomar targets. Its removal from the main paper does not retract
the argument; it separates the extra result from the proof-aligned release.

For a finite simple triangle-free graph F, put m = |E(F)|, d_v = deg_F(v),
o = the number of odd-degree vertices, and
t(d) = binomial(d, 2) - floor(d²/4). Then

\[
\tau_\triangle(\operatorname{Tot}(F))
\leq \sum_v t(d_v+1)+o/2
=m+\sum_v t(d_v).
\]

Add a dummy vertex adjacent to every odd-degree vertex, orient Euler tours
cyclically in each augmented component, and delete the dummy edges. This
gives an orientation in which indegree and outdegree differ by at most one.

Let Q_v consist of original vertex v and its incident edge-vertices. At an
even-degree vertex, put v and the incoming edge-vertices in one part of a
balanced bipartition of Q_v. Do the same at an odd-degree vertex of indegree
(d_v-1)/2. At an odd-degree vertex of indegree (d_v+1)/2, move one incoming
edge-vertex to the other part. Select all within-part edges. Each packet
contributes exactly t(d_v+1) edges and all packet triangles are covered.

For a root edge e directed toward v, its bridge triangle is hit by incidence
edge ve unless e was moved to the other part at v. In that case select the
original edge e instead. These added original edges are distinct because
every directed edge has a unique head. Exactly o/2 odd-degree vertices have
the larger indegree: the sum of the lower permitted indegrees is m-o/2,
whereas the actual sum is m. There are no other triangle types because F is
triangle-free. The cover has the stated size. Finally,
t(d+1)-t(d)=floor(d/2) and the degree sum give the displayed identity.

The cubic specialization follows because d_v=3 and m=3|V(F)|/2. The revised
paper instead proves that specialization by the Hall assignment used in
`Tuza/CubicTotal.lean`.

Historical source: [the frozen manuscript](https://github.com/samuelmasse/tuza-line-total-graphs/blob/82f6bb5195653b60ee05ad5c662faf4d3bae7667/paper/main.tex),
Section 5. Internal informal verification is recorded in the vmath paper
audit dated 7 September 2026; it is not a Lean proof of this general bound.
