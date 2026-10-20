---
title: 'Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean'
---

**Paper I of the series:** *Triangle decompositions I: Formalizing the Nash–Williams theorem in Lean* (this article).

**Paper II of the series:** *Triangle decompositions II: Robust absorption for typed triangles* [1].

**Preprint 1.0 — 20 October 2026.**

DOI: https://doi.org/10.5281/zenodo.23428173.

© 2026 Juan Pablo Traverso Gianini. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Abstract

Delcourt and Postle gave a proof that every sufficiently large triangle-divisible graph of minimum degree at least three quarters of its order has a triangle decomposition; their decomposition step invokes the manuscript listed as reference 17 in [2]. We give a Lean formalization that follows their extremal and non-extremal case division, together with the fractional threshold and stability results used in the proof. The decomposition inputs are supplied by typed absorption results developed in Paper II and by a protected covering construction presented here. This replaces the applications of their Theorem 13.16 without using it as an assumption. The protected construction combines simultaneous local packing, a sparse reserve, and matchings that control the resources needed by later rounds. We give its proof, including the bounded signed certificates used at the terminal step. We also state the typed inputs and check their application to the extremal residual graphs. The theorem, its attribution and its degree threshold are unchanged; the contribution is the formal proof and the explicit replacement constructions and interfaces.

**Keywords:** Nash–Williams theorem; triangle decomposition; formal verification; Lean; absorption.

## 1. The theorem and the contribution

Nash-Williams posed the triangle-decomposition conjecture in 1970 [16]. Delcourt and Postle gave a proof of the Nash–Williams theorem for sufficiently large graphs in *A Proof of Nash-Williams' Conjecture* [2, Theorem 1.8]; its decomposition step invokes their manuscript listed as reference 17 in [2]. The present formalization supplies the replacement constructions described below, without assuming their Theorem 13.16. We formalize that result and the fractional theorems on which its proof rests. A graph is *triangle-divisible* if its number of edges is divisible by three and every vertex has even degree. A triangle decomposition partitions its edges into triangles.

### Main theorem — Delcourt–Postle [2, Theorem 1.8]

There is an integer $N$ such that every finite simple graph $G$ of order $n\ge N$ satisfying
$$
3\mid |E(G)|,\qquad d_G(v)\equiv0\pmod2\quad(v\in V(G)),\qquad
3n\le4\delta(G)
\tag{1.1}
$$
has a triangle decomposition.

The degree threshold in (1.1) is exactly $3n/4$; only the order is required to be sufficiently large. The theorem is due to Delcourt and Postle [2]. Their fractional threshold theorem and two stability theorems are stated in Section 2, with the original numbering.

The proof divides graphs into extremal and non-extremal cases. In the extremal cases, a preliminary triangle packing covers exceptional vertices and leaves a partitioned residual graph. Its remaining triangles must have prescribed types. In the non-extremal case, a sequence of coverings moves the uncovered edges into progressively smaller vertex sets while preserving a reserve for the next step.

We follow this division and make the decomposition inputs explicit. The original argument applies [2, Theorem 13.16], whose proof is assigned to the manuscript [3], listed as reference 17 in [2]. No public version of [3] was located in preparing the source development. Paper II [1] supplies the typed results needed for the extremal residuals. For the non-extremal case, we give a protected covering round and use Paper II's conversion of signed certificates into terminal absorbers. These replacements do not identify our results with an unexamined statement from [3].

Two checks recur throughout the argument. A typed residual must satisfy both the global edge-count lattice and the local degree-profile lattices. A covering round must also leave enough unused edges inside the next reserve. Counting the total number of uncovered edges does not establish either condition. Sections 3 and 4 state the results used for these tasks and explain how their hypotheses are verified.

Section 5 records the integer relations and rounding conventions needed at the interfaces. Appendix A gives the signed-certificate argument, the protected round, and its iteration. The full case analysis inherited from Delcourt and Postle remains in [2]; the proofs here concentrate on the replacement steps used by this development.

## 2. Fractional inputs and proof strategy

### 2.1. Fractional decomposition, stability and regularity

A fractional triangle decomposition assigns a nonnegative real weight to every triangle so that the weights of the triangles containing any fixed edge sum to one. We state the three formalized fractional results using Delcourt and Postle's original numbering.

#### Fractional theorem — Delcourt–Postle [2, Theorem 1.4]

Every finite simple graph $G$ of order $n$ with $3n\le4\delta(G)$ has a fractional triangle decomposition.

Unlike the main theorem, this result requires neither integral divisibility nor a sufficiently large order. Its formal proof follows the dual discharging argument and then passes to fractional weights through a finite-dimensional alternative theorem.

To state stability, call $G$ $\sigma$-extremal if at least $(1-\sigma)n$ vertices have degree at most $(3/4+\sigma)n$ and some cut has at least $(1-\sigma)n^2/4$ edges. Both conditions are required; this is [2, Definition 12.2].

#### Fractional stability — Delcourt–Postle [2, Theorem 1.6]

We use the formalized form with an order threshold; the original statement in [2] does not impose this additional threshold.

There is $\sigma_0>0$ such that, for every $0<\sigma\le\sigma_0$, there are $\varepsilon>0$ and an integer $n_0$ with the following property: every simple graph $G$ of order $n\ge n_0$ with $\delta(G)\ge(3/4-\varepsilon)n$ either has a fractional triangle decomposition or is $\sigma$-extremal.

#### Regular fractional stability — Delcourt–Postle [2, Theorem 2.6]

There is $\sigma_0>0$ such that, for every $0<\sigma\le\sigma_0$, there are $\varepsilon>0$, $C\ge1$ and an integer $n_0$ with the following property: every simple graph $G$ of order $n\ge n_0$ that is not $\sigma$-extremal and satisfies $\delta(G)\ge(3/4-\varepsilon)n$ has a fractional triangle decomposition whose weight on each triangle belongs to $[1/(Cn),C/n]$.

The constants are chosen before the graph. Both exact edge coverage and the bounds on all triangle weights are part of the regular conclusion. This is the input needed for the random selection in Proposition 4.1.

These three fractional results do not use the integral conclusion of the main theorem. Appendix A also uses the maximum-cut sampling theorem [2, Theorem 11.4] to preserve non-extremality through nested sets, and the hinge supply [2, Lemma 14.4] to realize terminal absorbers. The companion [7] gives the source correspondence for these inputs. The sampling result is due to Arora–Karger–Karpinski [14] and Goldreich–Goldwasser–Ron [15], as attributed in [2]. Here its formalized use is a one-sided bound for uniformly sampled ordered tuples, with repetition allowed.

### 2.2. How the fractional and integral arguments fit together

Regular fractional stability gives bounded weights on the actual triangles of a non-extremal graph. Proposition 4.1 turns these weights into a single packing that controls all prescribed large edge sets simultaneously. Its application to vertex stars bounds the residual degree at each vertex.

That packing alone does not close the integral proof. Proposition 4.2 first reserves edges into a smaller set, applies the packing outside the protected edges, and then covers the remaining exterior and radial edges. Its conclusion bounds the use of edges inside the smaller set and leaves the next interior untouched. Corollary 4.3 iterates this operation and uses a fixed terminal absorber.

The extremal branches instead use the typed decomposition results of Section 3. The preliminary packing removes the exceptional vertices; the residual is checked at its own order, with its global and local divisibility conditions. The typed decomposition and the preliminary packing then partition the original edge set.

The fractional results are proved before these constructions and do not use the integral conclusion. All tolerances and order thresholds are chosen before the graph. Equation (1.1) expresses the degree bound without a rounding convention. The final result is an existence theorem; it gives neither an efficient decomposition algorithm nor an explicit numerical value of $N$.

## 3. Replacing the four applications

### 3.1. Replacement inputs

The case division in [2] has five branches but four kinds of decomposition input. Two extremal branches use different instances of the same nearly complete typed theorem. Table 1 records the replacements; it is not an inventory of the inherited lemmas.

**Table 1.** Decomposition results used by the formal assembly. Numbers refer to [2].

| Branch | Hypotheses checked for the replacement | Result used |
|---|---|---|
| 12.4: non-extremal | Near-threshold degree, non-extremality and bounds on protected reserves | Proposition 4.2 and Corollary 4.3 |
| 12.5 via 14.6 | Semidense $\mathcal F_0$ host, integral divisibility and one part away from balanced templates | Paper II; Theorem 3.3 |
| 12.6 and 12.7 via 14.7 | Nearly complete, nearly balanced $\mathcal F_1$ or $\mathcal F_2$ host with integral divisibility | Paper II; Theorem 3.2 |
| 12.8 | Proper four-colouring, degree margin, even degrees and equal opposite-pair edge sums | Paper II, $\mathcal F_3$; Proposition 3.1 |

Each row replaces an application of [2, Theorem 13.16], not the hypotheses of the corresponding branch theorem. The conditions in the middle column are proved from those branch hypotheses. We do not assume a further decomposition criterion on the original graph.

The semidense result has internal degrees near a quarter of the full order, while the graph between the two parts is nearly complete. Its density assumptions differ from those of the nearly complete result: the internal graphs need not be nearly complete.

For the four-colour branch, the nearly complete $\mathcal F_3$ theorem of Paper II gives the following corollary. Its proof checks balance, missing degrees and both integer lattice conditions directly; no separate fractional-packing construction is needed. Write $e_{ij}$ for the number of edges between colour classes $i$ and $j$.

### Proposition 3.1 (four-colour input)

There exist $0<\varepsilon\le1/16$ and an integer $N$ such that every graph $G$ of order $n\ge N$ with a proper four-colouring, even degrees, and
$$
\delta(G)\ge(3/4-\varepsilon)n,
\qquad
e_{01}+e_{23}=e_{02}+e_{13}=e_{03}+e_{12}
\tag{3.1}
$$
admits a triangle decomposition. Every triangle uses three different colours.

Each such triangle contributes one edge to each of the three opposite-pair sums in (3.1). For a properly four-coloured graph, even degrees together with those equalities are exactly integral divisibility for the family $\mathcal F_3=\{012,013,023,123\}$.

*Proof.* Use the nearly complete theorem of Paper II [1] for $\mathcal F_3$. It gives constants $\eta,\delta>0$ and $N_{\mathrm{II}}$ such that an integrally $\mathcal F_3$-divisible graph has an $\mathcal F_3$-decomposition if its four classes have sizes in $[(1/4-\eta)n,(1/4+\eta)n]$, all its edges join distinct classes, and every vertex misses at most $\delta n$ of the vertices in other classes. Choose
$$
\varepsilon=\min\{1/16,\eta/3,\delta/4\},\qquad
N=\max\{N_{\mathrm{II}},1\}.
$$
Write $n_i$ for the class sizes. A vertex in a nonempty class has degree at most $n-n_i$, so $n_i\le(1/4+\varepsilon)n$; the same upper bound holds for an empty class. Subtracting the upper bounds for the other three classes gives
$$
(1/4-3\varepsilon)n\le n_i\le(1/4+\varepsilon)n.
$$
These bounds imply the required balance. At a vertex of class $i$, the number of missing allowed neighbours is
$$
n-n_i-d_G(v)\le4\varepsilon n\le\delta n.
$$
The integer bound supplied to the formal theorem is $d=\lfloor4\varepsilon n\rfloor$: an integer missing degree bounded by $4\varepsilon n$ is bounded by $d$, and $d\le\delta n$. Proper colouring gives exactly the allowed-pair condition.

We check the integer lattice conditions separately. At a vertex, the allowed profiles are the three vectors with two coordinates equal to one; their integer span consists exactly of triples with even sum. Even degrees supply this condition. Globally, set
$$
a_{012}=\frac{e_{01}+e_{02}-e_{03}}2,\quad
a_{013}=e_{01}-a_{012},\quad
a_{023}=e_{02}-a_{012},\quad
a_{123}=e_{12}-a_{012}.
$$
The first coefficient is an integer because the sum of degrees in class zero is even. The equalities in (3.1) show that these four integers reproduce all six edge counts. Conversely, every rainbow triangle has even degrees and contributes one edge to each opposite-pair sum. This is precisely integral $\mathcal F_3$-divisibility. Paper II now gives the required decomposition. $\square$

The cleanup in branch 12.8 covers the exceptional vertices and the remaining internal edges. The residual graph therefore has no edges within its four classes: the inherited partition is a proper colouring, as Proposition 3.1 requires.

### 3.2. The typed inputs from Paper II

Let $V(G)=V_0\sqcup\cdots\sqcup V_{t-1}$, with part map $p$. A triangle type is the multiset of its three part labels. For a family $\mathcal F$ of permitted types, a pair of labels is allowed if it occurs in a permitted type. An $\mathcal F$-decomposition uses only triangles of those types. The general lattice framework for decompositions with prescribed label data is due to Keevash [19]. Paper II [1, Section 2.3] distinguishes that framework from the explicit typed hypotheses used here. We use
$$
\begin{aligned}
\mathcal F_0&=\{001,011\},\\
\mathcal F_1&=\{002,003,112,113,022,122,033,133\},\\
\mathcal F_2&=\{002,003,112,113,023,123\}.
\end{aligned}
\tag{3.2}
$$

Integral $\mathcal F$-divisibility has a global and a local condition. The vector counting edges by unordered pairs of parts must lie in the integer lattice generated by the edge-count vectors of the permitted triangles. At each vertex $v$, the vector $(|N_G(v)\cap V_j|)_{j=0}^{t-1}$ must lie in the integer lattice generated by the vectors counting the other two labels when a corner of label $p(v)$ is fixed in a permitted triangle. All edges must have allowed types.

An idealized $\mathcal F$-host with tolerance $\varepsilon>0$ has only allowed edges and satisfies
$$
|V_i|\ge(1-\varepsilon)n/t\quad(0\le i<t),\qquad
|N_G(v)\cap V_j|\ge|V_j|-\varepsilon n
\quad\text{whenever }p(v)j\text{ is allowed}.
\tag{3.3}
$$
Neighbourhoods are open, including when the allowed pair is internal.

### Theorem 3.2 (Paper II, Corollary 4.2, idealized form)

For each $\mathcal F\in\{\mathcal F_1,\mathcal F_2\}$ there exist $\varepsilon>0$ and an integer $N_{\mathrm{II}}$ such that every integrally $\mathcal F$-divisible idealized $\mathcal F$-host with tolerance $\varepsilon$ and order $n\ge N_{\mathrm{II}}$ has an $\mathcal F$-decomposition.

This idealized form of Paper II [1, Corollary 4.2] is the input used in branches 12.6 and 12.7.

The two-part input has different density assumptions. For a vertex set $D$, say that $G[D]$ is $\alpha$-close to a balanced template if at most $\alpha|D|^2$ edge edits turn it into either the complete bipartite graph on a split of sizes $\lfloor|D|/2\rfloor,\lceil|D|/2\rceil$, or the disjoint union of the two cliques on such a split.

### Theorem 3.3 (Paper II, Theorem C)

For every $\alpha>0$ there are $\varepsilon_0>0$ and an integer $n_0$ with the following property. Let $G$ have order $n\ge n_0$, a partition $V_0\sqcup V_1$, and integral $\mathcal F_0$-divisibility. Suppose that
$$
|V_i|\ge(1-\varepsilon_0)n/2\quad(i=0,1),
\tag{3.4}
$$
and, for every $v\in V_i$,
$$
(1/4-\varepsilon_0)n\le|N_G(v)\cap V_i|\le(1/4+\varepsilon_0)n,\qquad
|N_G(v)\cap V_{1-i}|\ge(1/2-\varepsilon_0)n.
\tag{3.5}
$$
If at least one of $G[V_0],G[V_1]$ is not $\alpha$-close to a balanced template, then $G$ has an $\mathcal F_0$-decomposition.

For $\mathcal F_0$, integral divisibility is equivalent to even degrees and the identity $e_{01}=2(e_{00}+e_{11})$. Theorem 3.3 is a separate theorem of Paper II; it is not an instance of Theorem 3.2.

### 3.3. Checking the extremal residual graphs

The applications for $\mathcal F_1$ and $\mathcal F_2$ have a common structure. First choose the tolerance and order threshold from Paper II. Then choose the cleanup parameters in terms of that tolerance. The cleanup constructs a triangle packing $\mathcal T$ covering all edges incident with an exceptional vertex set $A$. The residual graph is
$$
H=(G-E(\mathcal T))[V(G)\setminus A],\qquad m=|V(H)|.
\tag{3.6}
$$
Three checks are required before applying the typed theorem.

First, the classes of $H$ must be nearly balanced and the allowed pairs nearly complete **at scale $m$**. Estimates at scale $n$ have to be transported through the bound on $|A|$. Second, the order bound must give $m\ge N_{\mathrm{II}}$, not merely $n\ge N_{\mathrm{II}}$. Third, the residual edge counts and every residual vertex profile must lie in their required integer lattices. Even degrees alone do not express typed divisibility.

The formal reductions perform these checks on the same residual graph. Paper II then supplies a typed decomposition $\mathcal D$ of $H$. Since all edges incident with $A$ were covered, and the residual edges avoid the packing,
$$
E(G)=E(\mathcal T)\,\dot\cup\,E(H).
\tag{3.7}
$$
Consequently $\mathcal T\cup\mathcal D$ is a decomposition of $G$. This application uses only the specified families, not a classification of all families studied in Paper II.

For the semidense branch 12.5, there is an additional issue: the part that is far from the balanced templates must remain so after cleanup. The branch reduction first finds such a part in the original graph. If its residual part were close to a balanced template at the smaller tolerance, that split could be extended to the deleted vertices and rebalanced. Write $k$ for the number of deleted vertices in the original part $D$, $d=|D|$, and $C_{\mathrm{out}}$ for the packing edges avoiding $A$. In unordered edge edits, restoring the vertices costs at most $kd$ and rebalancing the split at most $d(k+1)$. Together with the removed edges the extra cost is at most
$$
|C_{\mathrm{out}}|+(2k+1)d
\le 3\sqrt\beta\,n^2+4\sqrt\beta\,nd+d\le39\sqrt\beta\,d^2+d.
$$
The formal reduction in `Case125/Residual.lean` uses the sufficient bounds $160\sqrt\beta\le\theta$, $n\ge12/\theta$, $|A|\le2\sqrt\beta\,n$, $|C_{\mathrm{out}}|\le3\sqrt\beta\,n^2$ and $d\ge n/3$ to transfer non-closeness from $\theta$ to $\theta/2$. Since $d\ge4/\theta$, the last expression is at most $(39/160+1/4)\theta d^2=79\theta d^2/160<\theta d^2/2$. Adding the hypothesized residual edit cost, at most $\theta d^2/2$, contradicts the original non-closeness. Thus the displayed estimate uses exactly the stated order threshold. The reduction also checks (3.4)–(3.5) at order $m$, even degrees and the exact internal–crossing edge balance. It then applies Theorem 3.3 to that residual graph.

For branch 12.8, the cleanup does more than produce a proper colouring: it enforces the two independent equalities in (3.1). Subtracting a triangle packing preserves even degrees, and its incidence bound limits the degree lost at each surviving vertex. The size and degree estimates then give the order threshold and degree margin of Proposition 3.1 at order $m$. These checks justify the four-colour application without invoking the nearly complete theorem for $\mathcal F_1$ or $\mathcal F_2$. The decomposition is reassembled with the cleanup packing as in (3.7).

### 3.4. Combining the branches

Let $\alpha_1,\alpha_2,\alpha_3$ be the tolerances for the three template-near cases, with thresholds $n_1,n_2,n_3$, and put $\alpha=\min\{\alpha_1,\alpha_2,\alpha_3\}$. The remaining extremal case supplies $\beta>0$ and $n_4$ for this $\alpha$. If $\beta_0$ is the range allowed by the non-extremal branch, choose $\beta'=\min\{\beta,\beta_0\}$ and its threshold $n_5$. Then
$$
N=\max\{n_1,n_2,n_3,n_4,n_5\}
\tag{3.8}
$$
works for the assembly. A graph close to one of the three templates uses its corresponding branch. A graph close to none is either $\beta'$-extremal, hence $\beta$-extremal, or is not $\beta'$-extremal. These are the remaining two branches. All choices precede the graph.

## 4. Local packing and protected covering

The nested sets, cover-down rounds and fixed terminal absorber follow the iterative-absorption scheme of Barber, Kühn, Lo and Osthus [17]. The certificate-to-absorber viewpoint is related to the refined-absorption framework of Delcourt and Postle [18]. Here we give the bounded signed certificate of Lemma A.1 and the reserve and matching controls that protect the resources required by subsequent rounds.

We give two constructions used in the non-extremal argument. The first applies the pseudorandom matching theorem of Ehard, Glock and Joos [4] to actual triangles while controlling prescribed sets of edges. The second adds protected reserves and an exact covering step. Neither construction uses the full Nash–Williams conclusion.

### 4.1. From fractional weights to actual triangles

Let $K_3(J)$ denote the set of triangles of a graph $J$ of order $n$. A $C$-regular fractional decomposition assigns weights $w(T)$ to its triangles such that
$$
\sum_{T\ni e}w(T)=1\quad(e\in E(J)),\qquad
\frac1{Cn}\le w(T)\le\frac Cn\quad(T\in K_3(J)).
\tag{4.1}
$$

### Proposition 4.1 (simultaneous local packing)

For every $C\ge1$, $\eta>0$ and integer $B\ge0$, there is an integer $N$ with the following property. Suppose $J$ has order $n\ge N$ and a $C$-regular fractional decomposition. Given a family $\mathscr S$ of at most $n^B$ subsets of $E(J)$, there is one triangle packing $\mathcal P$ in $J$ such that
$$
|S\setminus E(\mathcal P)|\le\eta|S|
\quad\text{for every }S\in\mathscr S\text{ with }|S|\ge6n^{1/4}.
\tag{4.2}
$$

*Proof.* Put $\zeta=\min\{\eta/4,1/4\}$ and $d=n/(2C)$. Select each triangle $T$ independently with probability $dw(T)\le1/2$. For every edge $e$, the expected number of selected triangles containing it is $d$. There are at most $n$ candidate triangles containing $e$. Hoeffding's inequality and a union bound show that the probability of a deviation of at least $\zeta d$ at any edge is at most
$$
2n^2\exp\left(-\frac{\zeta^2 n}{2C^2}\right)<1
\tag{4.3}
$$
for sufficiently large $n$. Fix a selected triangle family with all these degree bounds.

Its triangle hypergraph has the edges of $J$ as vertices. It is simple, and two distinct graph edges belong together to at most one triangle, so its codegrees are at most one. Set $\Delta=(1+\zeta)d$. Every hypergraph vertex corresponding to an edge of $J$ has degree between $(1-2\zeta)\Delta$ and $\Delta$.

For $S\in\mathscr S$, give a hyperedge the weight equal to the number of its graph edges in $S$. The total weight is at least $(1-2\zeta)\Delta|S|$. Since $\Delta\le n$ and $2\zeta\le1/2$, the size condition in (4.2) implies that this weight is at least $3\Delta^{5/4}$. Thus it meets the weight threshold in [4, Theorem 1.2], with $\delta_{\mathrm{EGJ}}=1/4$ and $r=3$, hence $\epsilon_{\mathrm{EGJ}}=\delta_{\mathrm{EGJ}}/(50r^2)=1/1800$. The number of hyperedges and monitors is polynomial in $n$. Since $\Delta$ is a positive constant multiple of $n$, both are at most $\exp(\Delta^{1/1800^2})$ for sufficiently large $n$, as the theorem requires.

One matching therefore leaves at most $(2\zeta+\Delta^{-1/1800})|S|$ uncovered edges in each such $S$. Enlarge $N$ so that $\Delta^{-1/1800}\le\eta/2$. Since $2\zeta\le\eta/2$, this gives (4.2). A hypergraph matching is a packing of the selected actual triangles, as required.

The selection step is necessary for this application: applying the weighted matching theorem to all triangles would normalize the monitor by the triangle degrees of its edges, which need not be nearly equal. This construction selects actual triangles and controls all the prescribed edge sets simultaneously. It is a reusable consequence of [4], rather than a new matching theorem.

### 4.2. A round that preserves the next reserve

For $\beta>0$, call $G$ *$\beta$-extremal* when at least $(1-\beta)n$ vertices have degree at most $(3/4+\beta)n$ and some cut has at least $(1-\beta)n^2/4$ edges. This is the same definition [2, Definition 12.2]. Write $E_G(W)=E(G[W])$.

### Proposition 4.2 (protected covering round)

For every $\beta>0$ there exist $0<\theta\le1$ and $q_0>0$ such that, for each $0<q\le q_0$, there are $\kappa>0$ and an integer $N_0$ with the following property. Let $G$ have order $n\ge N_0$, let $Z\subseteq W\subseteq V(G)$, and let $F\subseteq E(G)$ satisfy
$$
\frac{7q}{8}n\le|W|\le\frac{9q}{8}n,\qquad |Z|\le\frac{9q}{8}|W|,
\tag{4.4}
$$
$$
\delta(G)\ge(3/4-\theta)n,\qquad
G\text{ is not }(\beta/4)\text{-extremal},\qquad
|N_G(v)\cap W|\ge(3/4-\theta)|W|\quad(v\in V(G)),
\tag{4.5}
$$
$$
F\cap E_G(W)=\varnothing,\qquad\Delta(F)\le\kappa n,\qquad
d_{G-F}(x)\equiv0\pmod2\quad(x\notin W).
\tag{4.6}
$$
Then there is a triangle-decomposable edge set $Q\subseteq E(G)\setminus F$ such that
$$
(E(G)\setminus F)\setminus E_G(W)\subseteq Q,\qquad
Q\cap E_G(Z)=\varnothing,\qquad
\Delta(Q\cap E_G(W))\le\kappa|W|.
\tag{4.7}
$$

The round first packs the graph with all reserves removed, then covers the exterior edges with reserve apices, and finally covers the remaining radial edges using disjoint matchings inside the reserve. The matching selection controls use inside each future link, not just total degree. The order of choices is $\beta$, then $\theta,q_0$, then $q$, then $\kappa,N_0$. The complete proof, including the integer budgets, is in Appendix A.3.

### 4.3. From one round to the non-extremal branch

### Corollary 4.3 (non-extremal decomposition)

There is $\beta_0>0$ such that, for every $0<\beta\le\beta_0$, there is an integer $N_\beta$ with the following property. Every triangle-divisible graph $G$ of order $n\ge N_\beta$ with $\delta(G)\ge3n/4$ that is not $\beta$-extremal has a triangle decomposition.

Construct nested vertex sets while preserving the degree and non-extremality conditions. Before choosing any covering round, build a fixed absorber for every possible divisible residue in the terminal set. Lemma A.1 supplies its signed certificates, and Lemma SC of Paper II [1] converts them into absorbers. Each round protects the next interior and leaves only a small degree of used edges there. The resulting iteration ends with a residue handled by the fixed absorber. Appendix A.4 proves these assertions and records the order of the thresholds.

## 5. Divisibility and rounding at the interfaces

### 5.1. Integer lattices and index corrections

Typed divisibility requires more information than even degrees and a total edge count. In this subsection we use the labels $1,2,3,4$ of [2], and $e_{ii}$ counts unordered internal edges. For the family $\mathcal F_1$ of Lemma 13.19, every allowed triangle has one internal edge and two crossing edges. Hence the edge-count relation is
$$
e_{13}+e_{14}+e_{23}+e_{24}
=2(e_{11}+e_{22}+e_{33}+e_{44}),
\tag{5.1}
$$
and its four crossing counts are even in the integer type lattice. For $\mathcal F_2$ in Lemma 13.20, the corresponding conditions include
$$
e_{13}+e_{14}+e_{23}+e_{24}=2(e_{11}+e_{22}+e_{34}),\qquad
2e_{11}+e_{13}-e_{14}\equiv0\pmod4.
\tag{5.2}
$$

The displayed statements in [2, v1, pp.80 and 82] contain typographical index errors: their crossing sums end in $e_{34}$ instead of $e_{24}$; Lemma 13.19 also has the wrong internal sum and lists $e_{34}$ instead of $e_{14}$ among the even crossing counts. The relations used in the formal reductions are (5.1)–(5.2), obtained by counting the permitted triangle types. Local vertex-profile conditions remain part of typed divisibility.

The calculation for $\mathcal F_2$ left by analogy in [2, Claim 14.7.2] is also developed separately, including its vertex-profile inequalities. That supplementary result should be distinguished from the near-complete decomposition input used in Table 1.

### 5.2. Rounding and the correct scale

Remark 12.3 of [2] suppresses floors and ceilings in the extremal templates. The formal definitions retain them. In the associated four-class partition, each class $C$ satisfies $n\le4|C|+3$, including odd orders. The additive error is absorbed by the size threshold. Deleting the exceptional vertices also changes the denominator in the density estimates: the application in (3.6) must use the order of the residual graph.

The construction gives explicit compatible choices for some intermediate parameters, but we do not obtain a new value for the Nash–Williams degree threshold or an explicit numerical value of $N$. Their role is to make the successive existence arguments composable.

## Formalization and reproducibility

The theorem and the inputs described here have been checked in Lean 4 with Mathlib [5,6]. The fixed Paper I validation reports only propositional extensionality, classical choice and quotient soundness in its six final axiom queries, with no unfinished proof or additional mathematical axiom in those queries. The companion [7], preprint 1.0, records the exact source snapshot, build scope, declaration correspondence, dependency audit and reproduction procedure. It also distinguishes the separate EGJ registration [13] from its use in this development. Earlier formalization accounts [8–10] provide context; the contribution and attribution of the mathematical results here remain as stated above. The selected freeze preserves the complete local clean-build evidence for the aligned 1,070-module closure, using pinned Mathlib build products, before the author-header correction. Its current sources differ only in ordinary header comments naming Juan Pablo Traverso Gianini; a reversible hash record binds them to the compiled sources, without asserting a new Lean build. Its typed inputs use the aligned Paper II sources and are checked within the Paper I target. This is not an independent reproduction and does not certify the complete Paper II development. The companion records the alignment, receipt chain and exact audit scope.

## Acknowledgments

The author is deeply grateful to his wife María Paz and his children Lucas, Juan Cristóbal, Francisca, Raimundo and Benjamín for their love, patience and support. The author thanks Delcourt and Postle for the mathematical work on which this formalization is based, and the Lean and Mathlib communities for the infrastructure used in the development.

## Use of artificial intelligence and computational tools

Claude, by Anthropic, and ChatGPT/Codex, by OpenAI, were used to explore and check arguments and to prepare the manuscript. Aristotle, by Harmonic, contributed to exploring approaches, searching for counterexamples, developing proofs, and formalizing and reviewing them in Lean. Its role was not limited to translating finished proofs.

Certo [11] and Jacobian [12] were used to explore finite instances, check identities and assess candidate constructions. These computations informed the development of the arguments; finite checks were not treated as proofs of universal statements.

The author remains responsible for the arguments, citations, code and presentation. No AI system is listed as an author.

## Appendix A. Proofs for the non-extremal branch

We give the signed-certificate construction first, then the protected round and its iteration. The general conversion of a signed certificate into a positive absorber is Lemma SC of Paper II [1]. Its proof uses occurrence gadgets and edge-preserving slot matchings; no non-extremal hypothesis enters that conversion.

### A.1. A bounded signed certificate

For an integer vector $w$ on $E(G)$, write $\|w\|_1=\sum_e|w_e|$, $d_w(v)=\sum_{e\ni v}w_e$, and $s(w)=\sum_e w_e$. Denote the edge vector of a triangle $T$ by $[T]$. The cost of a signed triangle representation is the sum of the absolute values of its coefficients.

### Lemma A.1 (signed certificates in a non-extremal host)

Let $\beta>0$. Suppose $G$ is a nonempty graph of order $n$, with $\delta(G)\ge3n/4$, that is not $\beta$-extremal. If $w\in\mathbb Z^{E(G)}$ satisfies
$$
d_w(v)\equiv0\pmod2\quad(v\in V(G)),\qquad 3\mid s(w),
$$
then $w$ has a representation by actual triangles of cost at most $16741\|w\|_1$.

*Proof.* All equalities in this proof concern integer edge vectors. Walks may repeat an edge; its multiplicity is retained. No positive decomposition is used as a premise.

**Removing parity.** For any two vertices $a,c$, their common-neighbour set $S$ has size at least $n/2$. The graph induced on $S$ has minimum degree at least $|S|-n/4\ge|S|/2$, and is therefore connected. A shortest path in it has length at most 14: closed neighbourhoods at positions $0,3,6,\ldots$ are disjoint, and each has more than $|S|/5$ vertices. Six such neighbourhoods are impossible.

Consider a closed four-edge walk $abcd a$. If $a=c$ or $b=d$, its edge vector is twice an integer vector. Otherwise choose a path of length at most 14 from $b$ to $d$ in $G[N(a)\cap N(c)]$. For each path edge $xy$, take the two triangles $axy,cxy$. Modulo two, their sum over the path is exactly the four-edge walk: the path edges occur twice and all intermediate spokes cancel. Thus every such walk is $g+2h$, where $g$ has a triangle representation of cost at most 28.

For a closed five-edge walk $v_0v_1v_2v_3v_4v_0$, choose a common neighbour $y$ of $v_0,v_2,v_3$. Such a vertex exists, since their common neighbourhood has size at least $n/4>0$. Its edge vector is the sum of the four-edge walks $v_0v_1v_2yv_0$ and $v_0yv_3v_4v_0$ and the triangle $v_2v_3y$, minus twice the three edges $v_0y,v_2y,v_3y$. The preceding argument therefore represents it modulo two at cost at most $28+1+28=57$.

Fix a vertex $r$ and, for each $v$, a common neighbour $m(v)$ of $r,v$. Let $\pi_v$ be the two-edge walk $r m(v)v$. For every edge $uv$, use the closed walk obtained by following $\pi_u$, then $uv$, then $\pi_v$ backwards. Summing with coefficients $w_{uv}$ gives
$$
w+\sum_v d_w(v)\pi_v.
$$
The second term is even. Applying the five-walk construction to each summand gives an integer triangle combination $g$ and an integer vector $U$ such that
$$
w=g+2U,\qquad \operatorname{cost}(g)\le57\|w\|_1,
\qquad \|U\|_1\le86\|w\|_1.
\tag{A.1}
$$
Indeed $\|g\|_1\le3\operatorname{cost}(g)$, so $2\|U\|_1\le\|w\|_1+\|g\|_1\le172\|w\|_1$. Since every triangle has three edges and $3\mid s(w)$, also $3\mid s(U)$.

**Transporting twice an edge.** Form a graph $O$ whose vertices are the edges of $G$, joining two when they are opposite edges of a copy of $K_4$. If $ab,cd$ are such a pair, then
$$
[abc]+[abd]-[acd]-[bcd]=2([ab]-[cd]).
\tag{A.2}
$$
We show that $O$ is connected. First suppose every common-neighbour graph of two distinct vertices contains a triangle. Each such graph is connected by the degree estimate above. For an edge $uv$ and a triangle $abc$ in its common-neighbour graph, the two-step paths $uv,bc,ua$ and $uv,bc,va$ lie in $O$. If $a,b$ are adjacent in that common-neighbour graph, the opposite pairs $ua,vb$ and $va,ub$ propagate this conclusion from the spokes at $a$ to those at $b$. Thus $uv$ is connected in $O$ to every spoke $ux,vx$ with $x\in N(u)\cap N(v)$.

Any two incident edges $uv,uw$ have a common neighbour $x$ of their three endpoints; both are connected in $O$ to $ux$. Since $G$ is connected, this connects all its edges in $O$.

It remains to treat a triangle-free common-neighbour graph on a set $S$. Put $q=n/4$. We have $|S|\ge2q$ and $\delta(G[S])\ge|S|-q$. For an edge $xy$ of $G[S]$, its two internal neighbourhoods are disjoint, so $2(|S|-q)\le|S|$. Hence $|S|=2q$. In particular, the degree equality below forces $q$ to be an integer, so $4\mid n$. Every vertex of $S$ has internal degree exactly $q$: its degree is at least $q$, and the disjoint-neighbourhood inequality with any neighbour gives the reverse bound. Its degree in $G$ is consequently exactly $3q$, and every edge from $S$ to $R=V(G)\setminus S$ is present. The graph $G[R]$ has order $2q$ and minimum degree at least $q$, so it is connected and contains an edge.

If $G[R]$ were also triangle-free, the same argument would give degree $3q$ at every vertex of $G$, with a complete balanced cut between $S$ and $R$. This makes $G$ $\beta$-extremal, a contradiction. This is the only use of non-extremality in the certificate construction. Thus $G[R]$ contains a triangle. For each edge $ab$ in $G[S]$, its common-neighbour graph is exactly $G[R]$. The spoke argument already proved connects $ab$ to every edge from $a$ or $b$ to $R$. All edges in $G[S]$ are opposite one fixed edge of $G[R]$, and every edge of $G[R]$ is opposite one fixed edge of $G[S]$. Every vertex of $S$ has a neighbour there. These observations connect every edge of $G$ in $O$.

For every edge $uv$, put $S=N(u)\cap N(v)$. Every edge in $G[S]$ is a neighbour of $uv$ in $O$, and
$$
d_O(uv)=e(G[S])\ge\frac{|S|(|S|-n/4)}2\ge\frac{n^2}{16}\ge\frac{n^2}{20}.
$$
Also $|V(O)|=e(G)\le n^2/2$. On a geodesic of length 30, the eleven closed neighbourhoods at positions $0,3,\ldots,30$ would be disjoint and together exceed $n^2/2$ vertices. Hence the diameter of $O$ is at most 29. Summing (A.2) along a path shows that $2([e]-[f])$ has a triangle representation of cost at most $4\cdot29=116$ for any two edges $e,f$.

**The remaining multiple of three.** Fix a triangle with edges $f_0,f_1,f_2$; such a triangle exists by the degree condition. The identity
$$
6[f_0]=2[T]-2([f_1]-[f_0])-2([f_2]-[f_0])
$$
has cost at most $2+2\cdot116=234$. Write $s(U)=3k$. Then
$$
2U=\sum_e U_e\,2([e]-[f_0])+6k[f_0].
$$
Since $3|k|\le\|U\|_1$, this representation has cost at most $(116+234/3)\|U\|_1=194\|U\|_1$. Combining it with (A.1) gives
$$
57\|w\|_1+194\cdot86\|w\|_1=16741\|w\|_1.
$$
This proves the lemma. The constants are convenient uniform bounds, not optimized ones. $\square$

The formal result also allows a small loss below $3n/4$, coupled to the non-extremality parameter. We have stated and proved the exact-threshold specialization used for the terminal absorber here; the stronger formal statement is not needed for this application.

### A.2. The signed-certificate absorption input

We use Lemma SC of Paper II [1] in the following exact form. Suppose every pair has at least $\alpha n$ common neighbours and every pair of triangles sharing an edge has, for some $6\le i\le C_0$, at least $cn^{i-4}$ physical hinges of order $i$. A signed certificate for $\mathbf1_L$ of cost at most $K$, with $V(L)\subseteq Z_0$ and $|Z_0|\le z$, gives an absorber avoiding $E_G(Z_0)$ whenever
$$
z+3K+4KC_0+1<\alpha n,\qquad
2^{\binom{C_0+1}{2}}(z+3K+4KC_0+1)<cn.
\tag{A.3}
$$
The absorber and its union with $L$ are triangle-decomposable, and it has at most $4K(\binom{C_0+1}{2}+2)$ edges. The lemma constructs these two decompositions by matching positive and negative edge occurrences; it does not assume an absorber. For $C_0=8$, the bounds become $z+35K+1$, $2^{36}$ and $152K$. The exponent $i-4$ counts the free hinge vertices after fixing its four roots, as explained in Paper II.

This is the appropriate division between the articles: Lemma A.1 produces certificates using the non-extremal degree hypothesis, whereas Lemma SC converts supplied certificates using only common-neighbour and hinge supplies.

### A.3. Proof of Proposition 4.2

*Proof.* We separate the protected fractional step, the coverage of exterior edges, and the final coverage of radial edges. Put $u=|W|$, $z=|Z|$ and $X=V(G)\setminus W$.

**Choice of constants.** Regular fractional stability remains applicable after a sufficiently small maximum-degree deletion. Indeed, use Theorem 2.6 with extremality parameter $b/2$, where $0<b\le\beta/4$ is chosen in its permitted range, in particular with $b/2\le\sigma_0$ for the constant in Theorem 2.6. If $H$ is deleted from a graph that is not $b$-extremal, then a $(b/2)$-extremal graph $G-H$ would make $G$ $b$-extremal: the cut only gains edges, and every degree increases by at most $\Delta(H)$. If $\varepsilon_{2.6}$ is the degree margin in Theorem 2.6, choose $0<\theta_{\mathrm n}\le\min\{\varepsilon_{2.6}/2,b/4\}$. Since $\theta\le\theta_{\mathrm n}$, the original margin and the deletion together cost at most $\theta+\theta_{\mathrm n}\le\varepsilon_{2.6}$. This produces constants $\theta_{\mathrm n}>0$ and $C\ge1$ for the protected fractional step. They are chosen before $q$ and before the graph.

The following choices suffice; they are the ones used in the formal construction:
$$
\begin{aligned}
\theta&=\min\{\theta_{\mathrm n},1/100\},&
q_0&=\min\{\theta_{\mathrm n}/8,1/100\},\\
\kappa&=q/1000,&
\rho&=q^2/4000,&
\sigma&=\rho^4q^2/10^4.
\end{aligned}
$$
Increase $N_0$ to meet the sampling and packing thresholds below and to ensure
$$
4\log n+8\le\rho qn/20,\qquad
1\le\sigma n,\qquad 6n^{1/4}\le\sigma n.
$$
All these requirements depend only on the constants already fixed.

**The reserve and the protected packing.** For each $x\in X$, put $C_x=N_{G-F}(x)\cap(W\setminus Z)$. Select every available edge from $X$ to $W\setminus Z$ independently with probability $\rho$, forming $R$. Write $R_x=N_R(x)$. We may choose a sample for which each of the following quantities differs from its expectation by at most $\sigma n$: $|R_x|$, $|R_x\cap N_G(y)|$ for all $x,y$, $|R_x\cap R_{x'}|$ for distinct exterior vertices, and the number of reserve edges at each interior vertex. For each fixed quantity the summands indexed by vertices on the opposite side of the bipartition are independent; for the overlap their expectation is $\rho^2|C_x\cap C_{x'}|$. Hoeffding's inequality and a union bound over at most a constant times $n^2$ quantities give such a sample for large $n$.

In particular, $\Delta(R)\le(\rho+\sigma)n$. The total maximum-degree loss from deleting $F$, $R$ and all edges inside $W$ is at most
$$
\kappa n+(\rho+\sigma)n+u\le\theta_{\mathrm n}n.
$$
Obtain the regular fractional decomposition directly on
$$
J=G-(F\cup R\cup E_G(W)),
\tag{A.4}
$$
using the protected stability step. Apply Proposition 4.1 to its vertex stars. A star of size at least $6n^{1/4}$ has leftover at most $\sigma n$; a smaller star already has that bound. We obtain a packing with edge set $Q_{\mathrm p}$ and residual maximum degree at most $D=\lfloor\sigma n\rfloor$. No triangle of this packing uses a protected edge.

**Covering exterior edges.** Let $L$ be the residual edges with both endpoints in $X$. Then $\Delta(L)\le D$ and $2|L|\le nD$. For each $xy\in L$, the sampling estimates and (4.5) give at least $M$ common reserve neighbours, where
$$
M=\left\lfloor
\rho^2\bigl((1/2-2\theta)u-2z-2\kappa n\bigr)-\sigma n
\right\rfloor,\qquad
K_{\mathrm g}=\lfloor\rho^2u/40\rfloor.
$$
The parameter choices, with $N_0$ enlarged, give
$$
M\ge0.44\rho^2u-1,\qquad
3nD+12K_{\mathrm g}(K_{\mathrm g}+D)<2K_{\mathrm g}M.
$$
Process the edges of $L$ one by one. Call a reserve vertex saturated when it has served as the apex of $K_{\mathrm g}$ previously chosen triangles. There are at most $|L|/K_{\mathrm g}$ such vertices, hence fewer than $3|L|/K_{\mathrm g}$ when a demand edge remains. Each vertex lies in at most $K_{\mathrm g}$ triangles as an apex and at most $D$ as an endpoint of a demand edge. Previously chosen triangles meeting $x$ or $y$ exclude at most $6(K_{\mathrm g}+D)$ further candidates. The strict inequality above leaves an available common reserve neighbour. Add the corresponding triangle. This constructs an edge-disjoint family with edge set $Q_{\mathrm a}$, using one edge of $L$ and two edges of $R$ per triangle.

**The remaining radial edges.** For $x\in X$, let $T_x\subseteq W$ be its neighbours in the graph still uncovered after these two packings. Every exterior edge has been covered, and parity in (4.6) implies that $|T_x|$ is even. At most $D$ reserve edges were spent at $x$ by apex coverage, and at most $D$ non-reserve edges at $x$ survived the first packing. Hence
$$
|R_x\setminus T_x|\le D,\qquad |T_x\setminus R_x|\le D.
$$
Let $K$ now denote the graph of available interior edges $E_G(W)\setminus E_G(Z)$. The first two packings have used no interior edge. The sampling bounds imply the following four estimates:
$$
\begin{aligned}
|T_x|&\ge t_*:=\rho\bigl((3/4-\theta)u-z-\kappa n\bigr)-\sigma n-D,\\
|T_x\setminus N_K(y)|&\le
g:=\left\lceil\rho(1/4+\theta)u+2\sigma n+D+1\right\rceil
&& (y\in T_x),\\
|T_x\cap T_{x'}|&\le
\omega:=\left\lceil\rho^2u+\sigma n+2D\right\rceil
&& (x\ne x'),\\
|\{x:v\in T_x\}|&\le
v_*:=\left\lceil\rho n+\sigma n+D\right\rceil
&& (v\in W).
\end{aligned}
$$
For the second estimate, a vertex of $Z$ can belong to $T_x$ only through one of the at most $D$ residual non-reserve edges; this also pays for the deletion of $E_G(Z)$. The last estimate counts the demands left at an interior vertex; it does not incorrectly charge all previous apex use as $D$.

We need perfect matchings in the sets $T_x$ whose edges are disjoint across roots. Put
$$
k_*=\lceil800\rho^2n\rceil,\qquad
B_*=\left\lceil\frac{(\mathrm e-1)\omega v_*}{k_*}+2\log n\right\rceil.
$$
The same constant choices give
$$
\omega\le2\rho^2u,\quad v_*\le2\rho n\le\kappa u,\quad
B_*\le\rho u/100+2\log n+1,\quad
2(g+B_*+k_*)\le t_*.
$$
Here are the finite estimates behind these bounds. Put $t=\rho^2u$. The parameter choices give $\sigma\le\rho q/10^4$ and $4\sigma n\le t/100$. Since $1\le\sigma n$, we have $t\ge400$. In particular, floors and ceilings are included in the following calculations.

| Bound used | Verification |
|---|---|
| Common apices | $(1/2-2\theta)u-2z-2\kappa n\ge(45/100)u$, so $M\ge(45/100)t-\sigma n-1\ge(44/100)t-1$. |
| Greedy budget | $t/80\le K_{\mathrm g}\le t/40$ and $2M-12K_{\mathrm g}-12D\ge t/2$. Also $3nD\le3\rho^4q^2n^2/10^4<\rho^4u^2/160\le K_{\mathrm g}t/2$. Rearranging gives the required strict inequality. |
| Future-set counts | $\omega\le t+3\sigma n+1\le2t$ and $v_*\le\rho n+2\sigma n+1\le2\rho n\le\kappa u$. |
| Exponential potential | Using $\mathrm e-1\le2$ and $k_*\ge800\rho^2n$, we obtain $(\mathrm e-1)\omega v_*/k_*\le\rho u/100$. Taking the ceiling adds at most one. |

For the matching margin, write $r=\rho u$. The same bounds imply
$$
\begin{aligned}
t_*&\ge\left(\frac34-\frac1{100}-\frac9{800}-\frac8{7000}-\frac{16}{70000}\right)r
\ge\frac{72}{100}r,\\
2(g+B_*+k_*)&\le\frac{54}{100}r+6\sigma n+1600\rho^2n+4\log n+8\\
&\le\left(\frac{54}{100}+\frac{48}{70000}+\frac{12800}{2800000}+\frac2{35}\right)r
\le\frac{61}{100}r<t_*.
\end{aligned}
$$
For the second line, $g\le\rho(1/4+\theta)u+2\sigma n+D+2$, $k_*\le800\rho^2n+1$ and the bound on $B_*$ pay for all three ceilings. These are deliberately conservative estimates of the formal round's scalar budgets.

Here is the selection argument, including the control inside future sets. Process the roots in an arbitrary order. If previously selected matching edges remove at most $B_*$ neighbours of each vertex inside every future $T_x$, then the current even-order graph has $k_*$ edge-disjoint candidate perfect matchings: after each candidate is removed, minimum degree is still at least $|T_x|/2$. An even graph with this minimum degree has a perfect matching. To see this, take a maximum matching; two unmatched vertices cannot be adjacent, and if they cannot be joined by an augmenting path through a matched edge, their combined degree is at most the number of matched vertices, which is at most $|T_x|-2$, a contradiction.

Choose one of the candidate matchings while preserving the asserted future bound. For a future set $T_j$ and a vertex $v\in T_j$, let $c(v,j)$ count already selected neighbours of $v$ in $T_j$. One stage changes this count by zero or one. Averaged over the $k_*$ candidates, its increment is at most $\omega/k_*$ when $v$ belongs to the current set, and zero otherwise: the candidates share no edge and the two sets overlap in at most $\omega$ vertices. Set $\mu=(\mathrm e-1)\omega/k_*$. The sum, over future pairs $(v,j)$, of
$$
\exp\bigl(c(v,j)-\mu a(v)\bigr)
$$
can be kept nonincreasing, where $a(v)$ counts the processed sets containing $v$. Indeed, the average multiplicative factor is at most $\exp(-\mu)(1+\mu)\le1$; removing the current monitors can only decrease the sum. Initially there are at most $n^2$ monitors, and $a(v)\le v_*$. Thus every future count is at most $\mu v_*+2\log n\le B_*$. This proves the induction and the existence of the disjoint perfect matchings.

For every matched edge $yy'$ in $T_x$, take the triangle $xyy'$. These triangles cover precisely the remaining radial demands and their matching edges. Their bases have maximum degree at most $v_*$, since each vertex occurs in at most that many sets $T_x$. Together with the first two packings they give $Q$. Only the matching bases lie inside $W$; they avoid $E_G(Z)$ and have maximum degree at most $\kappa u$. This proves all three conclusions in (4.7). $\square$

### A.4. Proof of Corollary 4.3

*Proof.* We give the construction of the nested sets, the fixed terminal absorber, and the iteration. The same $q$ and $\kappa$ will be used at every scale.

**Nested sets.** Fix $0<\beta\le\beta_0=1/8$, and take $\theta,q_0$ from Proposition 4.2. For a sufficiently small fixed $q\le\min\{q_0,1/32\}$ we construct
$$
V(G)=U_0\supseteq U_1\supseteq\cdots\supseteq U_\ell,
\tag{A.5}
$$
with each child between $7q/8$ and $9q/8$ times the size of its parent. Every original induced graph $G[U_i]$ is not $(\beta/4)$-extremal and has minimum degree at least $(3/4-\theta)|U_i|$. Every vertex of $U_i$ has at least $(3/4-\theta)|U_{i+1}|$ neighbours in the next set. We stop when the order is below a constant $m$, chosen large enough that even the last child meets the auxiliary sampling thresholds.

There are two ways for the original graph to fail extremality. Either at least $\beta n$ vertices have degree greater than $(3/4+\beta)n$, or every cut has fewer than $(1-\beta)n^2/4$ edges. In the first case, sample so as to preserve both the proportion of these vertices and their degree advantage. An error at most $\beta/16$ in each quantity leaves more than a $\beta/4$ proportion with degree greater than $(3/4+\beta/4)$ times the current order.

In the second case use the maximum-cut sampling theorem [2, Theorem 11.4]. Set $\eta=\beta/16$ and fix a sufficiently large integer $k$, also satisfying $3\le\beta(k-1)$. Call an ordered $k$-tuple bad if its pullback graph has a cut whose doubled size is at least $t k^2$, where $t=(1-\beta)/2+\eta$. The theorem makes the proportion of bad tuples at most $\eta$ in the original graph. Preserve that proportion with cumulative error at most
$$
\epsilon_1=\min\{\theta/2,\beta/16\}.
$$
For a cut of any later graph, averaging its doubled pullback size over all ordered tuples gives $k(k-1)$ times its doubled cut density. Good tuples contribute less than $t k^2$ and the others at most $k^2$. Hence its doubled cut density is at most
$$
(t+\eta+\epsilon_1)\frac{k}{k-1}<\frac{1-\beta/4}{2}.
$$
The later graph therefore also fails the cut condition for $(\beta/4)$-extremality. We have used the disjunction expressing non-extremality, not assumed that both its defining conditions fail.

For completeness, the errors can be controlled uniformly through an arbitrarily long sequence of scales. In a parent of order $a$, select vertices independently with probability $q$ and use error scale $a^{-1/4}$. Hoeffding's inequality controls its size, the high-degree set when needed, and the non-neighbourhood of every parent vertex. The total failure probability is at most $2(a+2)\exp(-2\sqrt a)$. For the bad-tuple count, only intersecting tuples contribute covariance. Their number is at most $k^2a^{2k-1}$; tuples with repeated coordinates cause bias at most $k^2a^{k-1}$. Chebyshev's inequality adds a failure probability of at most $k^2/(q^{2k}\sqrt a)$, after enlarging the threshold. The sum is less than one.

Normalizing by the sampled order changes each tracked density by at most $D_{\mathrm v}a^{-1/4}$, where $D_{\mathrm v}=4k/q+4$ suffices. Maintain cumulative error at most $2D_{\mathrm v}a^{-1/4}$ at order $a$. Since the child has order at most $a/16$, its permitted error is at least $4D_{\mathrm v}a^{-1/4}$, which pays for the previous error and the new step. Choose the stopping threshold so that the error at the smallest child is at most $\epsilon_1$. The same neighbourhood estimates give the required parent-to-child degree bounds. This constructs (A.5) with constants chosen before $G$.

**A fixed absorber for the terminal set.** We spell out the finite-library construction, and identify its absorption inputs. In a host of minimum degree at least $3n/4$, every two vertices have at least $n/2$ common neighbours. Non-extremality and [2, Lemma 14.4] supply a constant $c>0$ and at least $cn^4$ root-clean eight-vertex hinges for every two triangles sharing exactly one edge. A hinge provides the two alternative triangle decompositions needed to exchange the two rooted wedges; its edges avoid those of the root triangles. We use the configuration-count form with normalization $n^{i-4}$ for four fixed roots, as in Paper II, rather than the $n^{i-2}$ normalization printed in [2, Definition 13.15]. The separation hypothesis follows quantitatively from non-extremality. Choose $0<\gamma\le\min\{\alpha_0,\beta^2/8,\beta/8\}$ and $n\ge\lceil2/\beta\rceil$. If $G$ were $\gamma$-close to a template, at most $4\gamma n/\beta\le\beta n/2$ vertices could meet more than $\beta n/2$ edited edges. All remaining degrees would be at most $3n/4+1+\beta n/2\le(3/4+\beta)n$, and the balanced template cut would retain at least $\lfloor n^2/4\rfloor-\gamma n^2\ge(1-\beta)n^2/4$ edges. Thus $G$ would be $\beta$-extremal, a contradiction. Lemma 14.4 therefore applies with this separation parameter.

Apply Lemma A.1 to $\mathbf1_L$ for each possible triangle-divisible residue $L$. It gives a certificate of cost at most $K=16741|L|$. Lemma SC of Paper II [1], in the form recorded in Appendix A.2, then gives $A_L$, avoiding all edges inside a prescribed set $Z_0\supseteq V(L)$, with $A_L$ and $A_L\cup L$ decomposable. Its bounds are
$$
|Z_0|+35K+1<n/2,\qquad
2^{36}(|Z_0|+35K+1)<cn,\qquad |A_L|\le152K.
$$
The factor $2^{36}$ counts possible hinge edge sets; it is unrelated to a fractional regularity parameter. Both constructions precede the covering rounds.

Apply this construction to every possible divisible residue in the terminal set $U_\ell$, whose order is at most $m$. Put
$$
b_m=\binom{m+1}{2},\qquad
s_m=2^{b_m},\qquad
K_m=16741b_m,\qquad a_m=152K_m.
$$
There are at most $s_m$ residues. Construct their absorbers successively, forbidding $U_1$ and all vertices incident with earlier absorber edges. At any step the forbidden set has size at most $|U_1|+2s_ma_m$. Define
$$
D_m=2s_ma_m+35K_m+1,\qquad
\zeta=\min\{1/8,c/2^{37}\}.
$$
Choose $q$ above also to satisfy $q\le\zeta/2$, so that $|U_1|\le\zeta n$. After $m$ is fixed, enlarge the host threshold so that
$$
n>8D_m,\qquad
n>4\cdot2^{36}D_m/c,\qquad
s_ma_m\le\kappa n.
$$
These inequalities give both fresh-choice budgets for every residue. The resulting absorbers are edge-disjoint. Their union $A$ is triangle-decomposable, has maximum degree at most $|A|\le s_ma_m\le\kappa n$, and absorbs every divisible residue inside $U_\ell$: use the absorbing decomposition for that residue's member and the ordinary decompositions of all others. Moreover $A\cap E_G(U_1)=\varnothing$. This is edge disjointness, not vertex disjointness; $A$ may contain edges joining $U_\ell$ to vertices outside $U_1$.

The order of choices is important. The hinge supply determines $\zeta$; we then fix $q$, and Proposition 4.2 fixes $\kappa,N_0$. Choose the stopping bound $m$ to exceed the sampling and round thresholds. Only then choose the final host threshold to pay for the finite absorber library. Nothing depends on the residue that the rounds will produce.

**Iteration.** Let $Q_{<i}$ be the union of earlier round edge sets and set
$$
F_i=(A\cup Q_{<i})\cap E_G(U_i).
\tag{A.6}
$$
At step zero this is $A$, which has the forbidden-degree bound and avoids $E_G(U_1)$. For $i\ge1$, the absorber avoids all edges inside $U_i$. Every round $j\le i-2$ protected $E_G(U_{j+2})$, which contains $E_G(U_i)$. Therefore
$$
F_i=Q_{i-1}\cap E_G(U_i),\qquad
\Delta(F_i)\le\kappa|U_i|,\qquad
F_i\cap E_G(U_{i+1})=\varnothing.
$$
Apply Proposition 4.2 to the original graph $G[U_i]$, with $W=U_{i+1}$ and $Z=U_{i+2}$, taking $Z=\varnothing$ in the last round. The nested-set construction supplies (4.4)–(4.5), with the same $q,\kappa$. Outside the current set, all remaining edges have already been covered. Thus the even degrees of the original graph, after subtracting $A$ and the earlier triangle packings, give the local parity required in (4.6). This proves the induction.

At termination the remaining edge set $L$ lies inside $U_\ell$. Subtracting the decomposable edge sets preserves both even degrees and divisibility of the edge count by three. Thus $L$ is triangle-divisible. Use the fixed decomposition of $A\cup L$ and the disjoint round packings. They partition $E(G)$, proving the corollary. $\square$

## References

[1] J. P. Traverso Gianini, *Triangle decompositions II: Robust absorption for typed triangles*, preprint 1.0 (2026). [Document](https://github.com/jtraverso/nash-williams-triangle-decompositions-release/blob/main/preprints/PAPER_II/01_manuscript/PAPER_II_preprint_v1.0_en.md). https://doi.org/10.5281/zenodo.23502224.

[2] M. Delcourt and L. Postle, *A Proof of Nash-Williams' Conjecture*, arXiv:2606.11178v1 (2026). https://doi.org/10.48550/arXiv.2606.11178.

[3] M. Delcourt and L. Postle, *Refined absorption for partitioned hypergraphs and beyond*, unpublished manuscript (2026), cited as reference 17 in [2]. No public version was located during preparation; no unexamined statement from this manuscript is used as an assumption.

[4] S. Ehard, S. Glock and F. Joos, *Pseudorandom hypergraph matchings*, Combinatorics, Probability and Computing 29 (2020), 868–885. https://doi.org/10.1017/S0963548320000280.

[5] L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 28 (2021), 625–635. https://doi.org/10.1007/978-3-030-79876-5_37.

[6] The mathlib Community, *The Lean Mathematical Library*, CPP 2020, 367–381. https://doi.org/10.1145/3372885.3373824.

[7] J. P. Traverso Gianini, *Triangle decompositions I: Formalization and reproducibility companion*, preprint 1.0 (2026), accompanying source freeze `PAPER_I_LEAN_20261020_ALIGNED_v3`. Accompanying technical document. [Document](https://github.com/jtraverso/nash-williams-triangle-decompositions-release/blob/main/preprints/PAPER_I/05_formalization/FORMALIZATION_COMPANION_preprint_v1.0_en.md). https://doi.org/10.5281/zenodo.23428173.

[8] T. Hales et al., *A formal proof of the Kepler conjecture*, Forum of Mathematics, Pi 5 (2017), e2. https://doi.org/10.1017/fmp.2017.1.

[9] C. Edmonds, A. Koutsoukou-Argyraki and L. C. Paulson, *Formalising Szemerédi's Regularity Lemma and Roth's Theorem on Arithmetic Progressions in Isabelle/HOL*, Journal of Automated Reasoning 67 (2023), article 2. https://doi.org/10.1007/s10817-022-09650-2. Preprint: https://arxiv.org/abs/2207.07499v3.

[10] Y. Dillies and B. Mehta, *Formalising Szemerédi's Regularity Lemma in Lean*, ITP 2022. https://doi.org/10.4230/LIPIcs.ITP.2022.9.

[11] J. P. Traverso Gianini, *Certo*, software repository. https://github.com/jtraverso/certo-math.

[12] *Jacobian*, software repository. https://github.com/morluto/jacobian.

[13] J. P. Traverso Gianini, *Pseudorandom hypergraph matchings (Ehard–Glock–Joos)*, Lean formalization, Palomar, PALOMAR-2026-10-17-000004, version 1 (2026). [Registered version](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000004&version=1).

[14] S. Arora, D. Karger and M. Karpinski, *Polynomial Time Approximation Schemes for Dense Instances of NP-Hard Problems*, Journal of Computer and System Sciences 58 (1999), 193–210. https://doi.org/10.1006/jcss.1998.1605.

[15] O. Goldreich, S. Goldwasser and D. Ron, *Property Testing and Its Connection to Learning and Approximation*, Journal of the ACM 45 (1998), 653–750. https://doi.org/10.1145/285055.285060.

[16] C. St. J. A. Nash-Williams, *An unsolved problem concerning decomposition of graphs into triangles*, in *Combinatorial Theory and its Applications III*, North-Holland, Amsterdam (1970), 1179–1183.

[17] B. Barber, D. Kühn, A. Lo and D. Osthus, *Edge-decompositions of graphs with high minimum degree*, Advances in Mathematics 288 (2016), 337–385. https://doi.org/10.1016/j.aim.2015.09.032.

[18] M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*, arXiv:2402.17855v1 (2024). https://doi.org/10.48550/arXiv.2402.17855.

[19] P. Keevash, *The existence of designs II*, arXiv:1802.05900v1 (2018). https://doi.org/10.48550/arXiv.1802.05900.
