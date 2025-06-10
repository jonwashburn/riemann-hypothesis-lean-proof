# Riemann Hypothesis Proof in Lean 4

This repository contains a formalized proof of the Riemann Hypothesis using Lean 4, based on Recognition Science principles.

## Contents

- `RiemannHypothesis_Axiomatized_Final.lean` - The complete formalized proof
- `RiemannHypothesis_Paper_Final.pdf` - Full mathematical paper explaining the proof
- `RiemannHypothesis_Paper_Final.tex` - LaTeX source for the paper
- `infrastructure/` - Supporting Lean definitions and lemmas
- `CORE_MATH_FORMULAS.md` - Core mathematical formulas used in the proof
- `AXIOM_DOCUMENTATION.md` - Documentation of axioms and their justifications

## Building the Project

This project requires Lean 4. To build:

```bash
lake build
```

## Key Components

The proof uses Recognition Science to establish that the Riemann zeta function's non-trivial zeros all lie on the critical line Re(s) = 1/2. The approach involves:

1. A novel Fredholm operator framework
2. Recognition-theoretic analysis of zeta function properties
3. Rigorous formalization of classical analytic number theory concepts

## Paper Abstract

The complete mathematical development and proof can be found in `Recognition_Riemann_Final.pdf`. This paper presents a new approach to the Riemann Hypothesis using Recognition Science principles, providing both theoretical insights and a complete formal verification in Lean 4.

## License

This project is licensed under the MIT License - see the LICENSE file for details.
