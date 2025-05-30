# Compiling the development

We depend on the following external libraries:

```
  "coq"                      { = "8.18.0"           }
  "coq-core"                 { = "8.18.0"           }
  "coq-elpi"                 { = "2.0.0"            }
  "dune"                     {>= "3.2" & <= "3.13.0"}
  "dune-configurator"        { = "3.12.1"           }
  "coq-hierarchy-builder"    { = "1.7.0"            }
  "coq-mathcomp-ssreflect"   { = "2.2.0"            }
  "coq-mathcomp-algebra"     { = "2.2.0"            }
  "coq-mathcomp-fingroup"    { = "2.2.0"            }
  "coq-mathcomp-analysis"    { = "1.3.1"            }
  "coq-mathcomp-real-closed" { = "2.0.0"            }
  "coq-mathcomp-finmap"      { = "2.1.0"            }
```

The easiest way to install the above libraries is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```bash
opam switch create \
    --yes \
    --deps-only \
    --repositories=default=https://opam.ocaml.org,coq-released=https://coq.inria.fr/opam/released \
    .
```

Then, you can compile the development by just typing `make` (or `opam
config exec -- make` if you used a local opam switch to install the
dependencies).

Remark I: if any unexpected error occurs, please follow the exact version of the 
above libraries. It's known that dune-configurator >= 3.13.0 will kill the 
compilation (incompatible with coq.8.18.0 if use `-(notation)` attribute 
for importing files).

Remark II: suppose that you already have opam and basic ocaml packages installed, the time expected to install all the dependencies is approximately 43.5 minutes, while compiling the projects using make takes roughly 22.5 minutes.

<br>

# Axioms present in the develoment

Our development is made assuming the informative excluded middle and
functional extensionality. The axioms are not explicitly stated in our
development but inherited from mathcomp analysis.

<br>

# Development of veriQEC

The development is displayed in ./src/example/veri_QEC:

### cqwhile.v
Formalization of classical-quantum (hybrid) primitive language follows from [FY21].
We formalize both the operational semantics and denotational semantics, and show their equivalence.

### preliminary.v
Formalization of preliminaries. It includes: basic properties of Pauli gate and Clifford group;
1-eigenspace of linear operators and related properties; definition of projective measurement.

### logic.v
Formalization of main results (Section 3 and 4, as well as related results in appendix).

### repetition.v
We formally prove the correctness of repetition code (for the case of X errors).

<br>

# File lists of CoqQ project

## Extra files to MathComp and MathComp Analysis

### mcextra.v
Extra of mathcomp and mathcomp-real-closed

### mcaextra.v
Extra of mathcomp-analysis

### xvector.v
Extra of mathcomp/algebra/vector.v

### notation.v
Collecting common notations of CoqQ

## Matrix and Topology

### mxpred.v
Predicate for matrix and their hierarchy theory; 
  modules for vector norm, vector order;
  Define Lowner order of matrices.

### svd.v
Singular value decomposition; Courant-Fischer theorem for svd decomposition;
prove basic inequality of singular values: 
$$\prod_{i < k} \sigma_i (AB) <= \prod_{i < k} \sigma_i (A)\sigma_i (B).$$

### extnum.v
Define $\small\texttt{extNumType}$ as the common parent type of 
  $\small\mathbb{R}$ and $\small\mathbb{C}$ 
  to prove the topological properties of $\small\mathbb{R}^n$ and $\small\mathbb{C}^n$ 
  under the same framework. Modules for 
  finite-dimensional normed module type $\small\texttt{finNormedModType}$
  (equipped with a vector order) and finite-dimensional ordered topological 
  vector space $\small\texttt{vorderFinNormedModType}$. 
  Prove the Bolzano-Weierstrass theorem, the equivalence of vector norms,
  the monotone convergence theorem for vector space w.r.t. arbitrary
  vector order with closed condition.

### ctopology.v
Instantiate extnum.v to complex number. 

### convex.v [merged from [YZB24])
Simple implementation of convex hull with proof of basic properties.

### majorization.v
Theory of majorization, including Hall's perfect-matching theorem, 
Konig Frobenius theorem, Birkhoff's theorem, etc.
Prove basic inequalies of singular values.

### mxnorm.v
define matrix norm includes lpnorm (entry-wise lp-norm), ipqnorm (induced p,q-norm), 
schattern norm (lp-norm over singular values); prove basic properties such as
hoelder's inequality, cauchy's inequality.
Instance of norms: i2norm (induced 2-norm), trnorm (trace/nuclear norm/schatten 1
  norm), fbnorm (Frobenius norm/schatten 2 norm).
Show density matrices form a cpo w.r.t. Lowner order.

### summable.v
Bounded and Summable functions (discrete function maps to normed topological space over real or complex number).

## Order and Hilbert subspace

### cpo.v
Module for complete partial order.

### orthomodular.v
Module for orthomodular lattice (inherited from CoqQ); 
 establish foundational theories of orthomodular lattices following
 from [Beran 1985; Gabriëls et al . 2017], prove extensive properties 
 and tactics for determining the equivalence and order relations of 
 free bivariate formulas [Beran 1985].

### hspace.v
Hilbert subspace theory based on projection representation; i.e., the theory
  of projection lattice.

### hspace_extra.v (merged from [FZX23])
Extra of hspace.v, formalizing infinite caps and cups of Hilbert subspaces 
and related theories.

## Quantum Frame

### hermitian.v
Define the Hermitian space and its instance chsType -- hermitian
  type with a orthonormal canonical basis. Define and prove correct
  the Gram–Schmidt process that allows the orthonormalization a set of
  vectors w.r.t. an inner product. Define outer product and
  basic operators such as adjoint, transpose, conjugate of linear functions.

### quantum.v
Define most of the basic concept of quantum mechanics based on
  linear function representation (lfun). Concepts includes:
  normal/hermitian/positive-semidefinite/density/observable/projection/bounded/isometry/unitary
  linear operators, super-operators and its norms and topology,
  (partial) orthonormal basis, normalized state, trace-nonincreasing /
  trace-preserving (quantum measurement) maps, completely-positive
  super-operators (CP, via choi matrix theory), quantum operation
  (QO), quantum channel (QC), unital channel (QU). Basic constructs of super-operator
  (initialization, unitary transformation, if and while, dual
  super-operator) and their canonical structure to CP/QO/QC/QU.

### inhabited.v
Define inhabited finite type (ihbFinType), Hilbert space associated
  to a ihbFinType, tensor product of state/operator in/on associated
  Hilbert space (for pair, tuple, finite function and dependent finite
  function)

### qtype.v
Utility of quantum data type; includes common 1/2-qubit gates,
  multiplexer, quantum Fourier bases/transformation, (phase) oracle
  (i.e., quantum access to a classical function) etc.

## (Labeled) Dirac Notation

### prodvect.v
Variant of dependent finite function.

### tensor.v
Define the tensor product over a family of Hermitian space based on
  their bases. define multi-linear maps. Prove that the tensor produce
  of Hermitian/chsType is still a Hermitian/chsType with inner product
  consistent with each components. 

### dirac/hstensor.v
For a given $\small L$ and $\small{\mathcal{H}_i}$ for $\small{i\in L}$, 
define Hilbert space $\bigotimes_{i \in S}\mathcal{H}_i$ for any subsystem $\small{S \subseteq L}$.
  Define the tensor product of vectors and linear functions, 
  and general composition of linear functions.
  Define the cylindrical extension of linear functions (lifting to a larger space).

### dirac/dirac.v
Labelled Dirac notation, defined as a non-dependent type and have
  linear algebraic structure. Using canonical structures to trace the
  domain and codomain of a labelled Dirac notation.

## Automation

### dirac/setdec.v
A prove-by-reflection tactic for efficient automated reasoning about
  set theory goals based on the tableau decision procedure in
  [Anisimov 2015].

### autonat.v (merged from [FZX23])
Light-weight tactic for mathcomp nat based on standard Lia/Nia: dealing with 
ordinal numbers, divn, modn, half/uphalf and bump. It served as the automated 
checking for the disjointness of quantum registers (of array variables with 
indexes).

## Quantum Register

### qreg.v (merged from [FZX23])
Formalization of quantum registers. define $\small\texttt{qType}$, 
$\small\texttt{cType}$ and classical/quantum variables. define quantum 
registers as an inductive type that reflects the manipulation of 
quantum variables (e.g., merging and splitting). An automated type-checker 
for the disjointness condition is implemented to enhance usability.

### qmem.v (merged from [FZX23])
Formalization of quantum memory model: mapping each quantum variable/register 
to a tensor Hilbert system (as its semantics). It is consistent with the 
merging and splitting of quantum registers. A default memory model is established. 
Related theories that facilitate the use of Dirac notation are re-proved.

## Quantum Information Theory (in processing)

### commutator.v
Implementation of commutator and its related theories, including Jacobi's
  identity, Parallelogram inequality, Heisenberg uncertainty, Maccone-Pati
  uncertainty, CHSH inequality and its violation.

### series.v
Formalization of generalized series for R[i] and chsf. Currently, only the
  natural exponential function has been implemented, as well as its convergence
  and several properties.

## Files copy from Mathcomp

### complex.v (copy from mathcomp-real-closed)
Fixing canonical problem (unexpected coercion from 
$\small\mathbb{C}$ to $\small{\texttt{lmodType R}}$ without alias).

### spectral.v (copy from mathcomp-algebra 'experiment/forms' branch)
Make it compatible with mathcomp-analysis/forms.v.
