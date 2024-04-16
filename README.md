
# Quantum Computing Final Project

Group members:
- McKinley Keys
- Zhihao Xie
- Aarabhi Achanta


# Overview

This project has three parts:
- `Lean Proofs`: proofs of quantum computing theorems written in the Lean theorem prover.
- TODO: MATLAB stuff
- `Shor's Algorithm`: a Python program that verifies the accuracy of Shor's algorithm for reasonably small `N`.


# Lean Proofs

- [Lemmas.lean](Lean Proofs/Quantum/Lemmas.lean): Lemmas unrelated to quantum computing.
- [Probability.lean](Lean Proofs/Quantum/Probability.lean): A foundation for randomized algorithms.
- [Definitions.lean](Lean Proofs/Quantum/Definitions.lean): Quantum computing definitions.
- [Basic.lean](Lean Proofs/Quantum/Basic.lean): Assorted lemmas.
- [Adjoint.lean](Lean Proofs/Quantum/Adjoint.lean): Lemmas about matrix adjoints.
- [TensorProduct.lean](Lean Proofs/Quantum/Adjoint.lean): Lemmas about the tensor product.
- [Congruence.lean](Lean Proofs/Quantum/Congruence.lean): Lemmas about the "congruence" relation (equality up to a global phase), including a proof that congruence is decidable.
- [Measurement.lean](Lean Proofs/Quantum/Measurement.lean): Proof that if we measure `α|0⟩ + β|1⟩` in the computational basis, the probability of getting `|0⟩` is `‖α‖`. This is the only proof that uses the definitions of measurement based on the `Random` monad.
- [NoCloning.lean](Lean Proofs/Quantum/NoCloning.lean): Proof of the no-cloning theorem.
- [Teleportation.lean](Lean Proofs/Quantum/Teleportation.lean): Proof of correctness of the quantum teleportation algorithm.
