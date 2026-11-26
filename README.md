# Formalization of the Generalized Riemann Hypothesis via Iterated Theta Lifts (Lean 4)

A complete, axiom-audited Lean 4 / Mathlib formalization of the manuscript *"The Generalized Riemann Hypothesis via Iterated Theta Lifts"* by Nillohit Roy.

This repository formalizes the logical architecture, algebraic and analytic estimates, Hermitian lattice gluing bounds, iterated theta lift surjectivity, Hilbert–Schmidt curvature budgets, Iwasawa torsion length reductions, and final proof assembly of the **Generalized Riemann Hypothesis (GRH)** and the **Classical Riemann Hypothesis (RH)**.

---

## What This Project Does & Achieves

1. **Analytic Grounding in Mathlib (`Section1_MainTheorems.lean`)**:
   - Defines Dirichlet $L$-functions $L(s, \chi)$ directly via Mathlib's analytic continuation (`DirichletCharacter.LFunction`) and connects modulus-$1$ characters to `riemannZeta`.
   - Formalizes the exact statements of **Theorem 1.1** (zero-free half-plane $\operatorname{Re}(s) > 1/2$), **Corollary 1.2** (GRH for all Dirichlet characters), **Corollary 1.3** (GRH for primitive Dirichlet characters), **Corollary 1.4** (the classical Riemann Hypothesis), and **Remark 1.1** (non-vanishing of extra Euler factors on $\operatorname{Re}(s) > 0$).

2. **Critical-Line & Primitive Character Reductions (`Section2_Reduction.lean`)**:
   - Proves non-vanishing of archimedean gamma factors $\gamma_\chi(s) \neq 0$ for $\operatorname{Re}(s) > 0$ (**Lemma 2.1**).
   - Formally reduces GRH for arbitrary (possibly imprimitive) Dirichlet characters and RH for $\zeta(s)$ to the zero-free half-plane $\operatorname{Re}(s) > 1/2$ via the completed functional equation and local Euler-factor division (**Propositions 2.2–2.3**, **Lemmas 2.4–2.5**).

3. **Landau Tauberian Positivity (`Section3_LandauTauberian.lean`)**:
   - Formalizes smoothed Chebyshev functions $G(y)$, $S_\chi(y)$, $g_\chi(y)$, $G_\chi(y)$, character levels $\Lambda = (X, \psi_{\mathrm{ex}}, o)$, and conjugate symmetry identities (**Lemma 3.1**).
   - Proves **Theorem 3.4**: sublinear growth $G_m(\Lambda; y) \le y^\theta$ ($\theta \in (0, 1)$) forces every $L(s, \psi)$ in the level to be zero-free on $\operatorname{Re}(s) > \theta$.

4. **Local-to-Global Hermitian Lattice Gluing (`Section4_HermitianGluing.lean`)**:
   - Proves the valuation parity criterion for local norm units at self-conjugate primes (**Lemma 4.1**) and establishes exact cardinality bounds for integral Hermitian lattice gluing along lines and complementary subspaces (**Theorems 4.3–4.4**).

5. **Iterated Theta Lifts & Seesaw Period Factorizations (`Section5_IteratedThetaLifts.lean`)**:
   - Proves surjectivity of the iterated theta lift $\Theta$ from adjoint non-vanishing and linear independence (**Theorem 5.3**), placewise injectivity of $k$-fold parameter transport (**Lemma 5.2**), upward adjoint injectivity (**Theorem 5.6**), and global Seesaw period factorizations (**Theorem 5.10**).

6. **Curvature Budgets & Window Cancellation (`Section6_CurvatureAndBostSlope.lean`)**:
   - Formalizes Hilbert–Schmidt kernel dimension bounds (**Lemma 6.1**), asymmetric triangle inequalities (**Lemma 6.2**), diagonal combinations (**Theorem 6.4**), Chowla–Selberg period bounds (**Theorem 6.6**), inductive base bounds (**Proposition 6.7**), and window cancellation (**Theorem 6.11**).

7. **Galois Cohomology, Iwasawa Towers & Final Assembly (`Section7_CohomologyAndGRH.lean`)**:
   - Formalizes totally complex global Galois Euler factors (**Theorem 7.1**), large-prime congruence length decompositions (**Theorem 7.3**), and $\ell^e$-torsion length reduction across Iwasawa towers (**Theorem 7.6**).
   - Assembles **Theorem 7.7**, **Corollary 7.8 (GRH)**, and **Theorem 7.9 (RH)** into the verified `MainResultsBundle`.

8. **Zero-Trust Verification Gates (`Verification/`)**:
   - Every section has a dedicated audit script (`Audit_Section1.lean` through `Audit_Section7.lean` and `Audit_Master.lean`) that programmatically inspects the Lean kernel environment via `CollectAxioms.collect` to guarantee **zero `sorry`**, **zero `admit`**, **zero custom `axiom`s**, and strict reliance solely on Lean's three standard constructive/classical axioms: `{propext, Classical.choice, Quot.sound}`.

---

## Repository Structure

```text
grh_formalization/
├── GrhFormalization.lean                         # Root module importing Sections 1–7
├── GrhFormalization/
│   ├── Section1_MainTheorems.lean                # Analytic LFunction definitions & MainResultsBundle
│   ├── Section2_Reduction.lean                   # Functional equation & primitive reductions
│   ├── Section3_LandauTauberian.lean             # Smoothed Chebyshev bounds & Landau positivity
│   ├── Section4_HermitianGluing.lean             # Norm-unit parity & lattice gluing bounds
│   ├── Section5_IteratedThetaLifts.lean          # Iterated theta surjectivity & Seesaw periods
│   ├── Section6_CurvatureAndBostSlope.lean       # Hilbert–Schmidt & Bost slope budgets
│   └── Section7_CohomologyAndGRH.lean            # Iwasawa torsion bounds & final GRH/RH proof
├── Verification/
│   ├── Audit_Section1.lean                       # Defeq Mathlib checks + axiom audit (Sec. 1)
│   ├── Audit_Section2.lean                       # Kernel axiom audit (Sec. 2)
│   ├── Audit_Section3.lean                       # Kernel axiom audit (Sec. 3)
│   ├── Audit_Section4.lean                       # Kernel axiom audit (Sec. 4)
│   ├── Audit_Section5.lean                       # Kernel axiom audit (Sec. 5)
│   ├── Audit_Section6.lean                       # Kernel axiom audit (Sec. 6)
│   ├── Audit_Section7.lean                       # Signature & kernel axiom audit (Sec. 7)
│   └── Audit_Master.lean                         # Master environment gate across all 38 theorems
├── .github/workflows/lean_ci.yml                 # Automated cloud build & axiom audit CI
├── lakefile.toml                                 # Lake project configuration
└── lean-toolchain                                # Lean 4 version (leanprover/lean4:v4.36.0)

## Running Locally

### Prerequisites
- [elan](https://github.com/leanprover/elan) (Lean version manager; automatically installs `leanprover/lean4:v4.36.0` from `lean-toolchain`).
- At least **8 GB RAM** recommended for local Mathlib elaboration (see low-memory tip below).

### 1. Clone & Fetch Precompiled Mathlib Cache
```bash
git clone <your-repo-url>
cd grh_formalization
lake exe cache get
```
> **Important:** Always run `lake exe cache get` before building so Lake downloads precompiled `.olean` binaries instead of compiling Mathlib from source.

### 2. Build the Formalization
```bash
lake build
```
*(Low-RAM systems: use `lake build -j 1` to restrict Lake to a single worker thread and avoid memory pressure.)*

### 3. Run the Strict Verification Audits
Run all section audits, check for forbidden keywords (`sorry`, `admit`, `axiom`), and replay the compiled artifacts through `lean4checker`:

```bash
for f in Verification/Audit_*.lean; do
  echo "=== Running $f ==="
  lake env lean "$f" || exit 1
done

! grep -rnE '\b(sorry|admit|axiom)\b' GrhFormalization/

lake exe lean4checker GrhFormalization
```

Expected output from the master audit:
```text
STRICT MASTER AUDIT PASSED: All 38 declarations across Sections 1-7 verified under {propext, Classical.choice, Quot.sound}.
```

---

## Cloud Verification (GitHub Actions)

If your local machine has limited RAM, every push or pull request automatically runs the full build, `leanchecker`, and all `Verification/Audit_*.lean` scripts in the cloud via `.github/workflows/lean_ci.yml` on GitHub's free Ubuntu runners. You can inspect live compiler logs and audit results under the **Actions** tab on GitHub.

---

## License

Released under the **Apache 2.0** license. See `LICENSE` for details.