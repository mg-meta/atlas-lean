# Switching reconstruction of oriented graphs — natural-language proof and audit

Paper: `Switching_Reconstruction.pdf`, source `Latex/main.tex` (Milana Golich,
with Muse Spark and Watermelon, October 2026). Background: `McKayPaper_Digraphs.pdf`
(McKay–Schweitzer, *Switching reconstruction of digraphs*, J. Graph Theory 76
(2014)) and Bondy–Mercier (2011), cited in `Latex/bib.bib`.

This file is the complete natural-language proof, in dependency order, written
before the Lean formalization (per `AGENTS.md`). Every computational claim was
checked independently of the paper's text with a separate Python computation
(script kept outside the deliverable, at `/tmp/audit_switching.py`); all checks
passed. The Lean formalization re-checks the same finite computations with the
Lean kernel (`of_decide_eq_true rfl`), never with `native_decide`.

## Definitions (paper, Problem Statement)

For a digraph $D$ and a vertex $v$, $\mathrm{switch}(D,v)$ reverses every edge
incident with $v$ and fixes all other edges. Digraphs $D,H$ have the *same
switching deck* if there is a bijection $\pi:V(D)\to V(H)$ with
$\mathrm{switch}(D,v)\cong\mathrm{switch}(H,\pi(v))$ for every $v$. $D$ is
*switching non-reconstructible* if some $H\not\cong D$ has the same switching
deck as $D$.

An *oriented graph* is a digraph with no loops and no 2-cycles; equivalently
its signed adjacency matrix $A$ satisfies $A^T=-A$, $A_{ii}=0$ and
$A_{ij}\in\{-1,0,1\}$, where $A_{ij}=1$ iff $i\to j$.

## The example (paper, Solution)

Let $D$ be the oriented graph on $V=\{0,\dots,11\}$ with the signed adjacency
matrix $A$ printed in the paper. Direct check: $A$ is skew-symmetric with
entries in $\{-1,0,1\}$ and zero diagonal (so $D$ is oriented); the only
non-adjacent distinct pairs are
$(0,3),(1,4),(2,5),(6,9),(7,10),(8,11)$; the out-neighbour lists printed in
the paper agree with $A$.

Let $H$ be obtained from $D$ by switching at $0$ and at $1$ successively; its
signed adjacency matrix is $C_{ij}=-A_{ij}$ if exactly one of $i,j$ lies in
$\{0,1\}$, and $C_{ij}=A_{ij}$ otherwise. Direct check: this $C$ equals the
matrix printed in the paper, and $C$ is again skew-symmetric with entries in
$\{-1,0,1\}$ (switching preserves oriented graphs: in matrix form switching
at $v$ is conjugation $S_vAS_v$ by the diagonal sign matrix $S_v$, and two
such conjugations give $C=S_{01}AS_{01}$).

## Same switching deck

Let $\pi=(0\,1)(2\,5)(3\,4)(6\,7)(8\,11)(9\,10)$, i.e.
$\pi=[1,0,5,4,3,2,7,6,11,10,9,8]$. For each $v$, let $\psi_v$ be the
permutation tabulated in the paper (the identity for $v=0$; the table was
reproduced in the audit). Claim: for every $v$ and all $i,j$,
$[\mathrm{switch}(D,v)]_{ij}
=[\mathrm{switch}(H,\pi(v))]_{\psi_v(i),\psi_v(j)}$.
This is a finite check of $12\cdot12\cdot12$ signed entries; it was verified
in Python for all $12$ values of $v$, and each $\psi_v$ is a bijection.
Hence $\psi_v$ is an isomorphism
$\mathrm{switch}(D,v)\cong\mathrm{switch}(H,\pi(v))$ for every $v$, so $D$ and
$H$ have the same switching deck (witnessed by $\pi$). The paper's sample
identity $D_0=S_1CS_1=H_1=H_{\pi(0)}$ is the case $v=0$.

## $D$ is not isomorphic to $H$

For a vertex $v$ let $\mathrm{outdeg}(v)$ be the number of $+1$'s in row $v$
(equivalently $|\{w:v\to w\}|$) and let
$P_G(v)=(\mathrm{outdeg}(v), \text{sorted out-degrees over }N^+(v),
\text{sorted out-degrees over }N^-(v))$.
An isomorphism preserves out-degree of every vertex, hence preserves
$P_G(v)$ (it maps $N^+(v),N^-(v)$ bijectively onto the corresponding
neighbourhoods of the image, preserving the out-degree of each neighbour);
so $P$ is an isomorphism invariant.

Computation: $P_D(0)=(4,(3,6,6,6),(4,4,4,5,5,7))$, since
$0\to\{5,7,8,10\}$ with out-degrees $(6,6,3,6)$ and
$N^-(0)=\{1,2,4,6,9,11\}$ with out-degrees $(5,4,5,4,4,7)$.
In $H$ the vertices of out-degree $4$ are exactly $2,4,6,9$, with
$P_H(2)=(4,(4,4,6,7),(3,4,5,5,6,6))$,
$P_H(4)=(4,(3,4,6,6),(4,4,5,5,6,7))$,
$P_H(6)=P_H(9)=(4,(3,4,5,6),(4,5,6,6,6,7))$,
none equal to $P_D(0)$. If $\varphi:D\to H$ were an isomorphism, $\varphi(0)$
would have out-degree $4$ in $H$, so $\varphi(0)\in\{2,4,6,9\}$, but then
$P_H(\varphi(0))=P_D(0)$, contradiction. Hence $D\not\cong H$. (Python also
confirms the full multisets $\{P_D(v)\}$ and $\{P_H(v)\}$ already differ.)

## Conclusion

$D$ and $H$ are oriented graphs on $12$ vertices with the same switching deck
and $D\not\cong H$; therefore $D$ is switching non-reconstructible. In
particular there exists a switching non-reconstructible oriented graph on
some $n\ge 12$ vertices (take $n=12$), answering the Bondy–Mercier question
as posed in the paper. The paper proves no construction for every $n\ge12$;
see `GAPS.md`.

## External results used

None are needed for the proof itself: all steps are elementary definitions
or finite computations. Kelly–Ulam (1957/1960), Stanley (1985),
Bondy–Mercier (2011) and McKay–Schweitzer (2014) are cited background and
motivation only. Edge cases checked: vertex $v$ itself under switching
($A_{vv}=0$ is fixed by sign conjugation); non-adjacent pairs stay
non-adjacent under switching ($0$ entries are fixed); $P_H(6)=P_H(9)$ does
not affect the argument, which only needs $P_H(v)\ne P_D(0)$ at the four
out-degree-$4$ vertices.
