
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

- [Lemmas.lean](Lean%20Proofs/Quantum/Lemmas.lean): General lemmas not specific to quantum computing.
- [Probability.lean](Lean%20Proofs/Quantum/Probability.lean): A foundation for randomized algorithms.
- [Definitions.lean](Lean%20Proofs/Quantum/Definitions.lean): Quantum computing definitions.
- [Basic.lean](Lean%20Proofs/Quantum/Basic.lean): Assorted quantum computing lemmas.
- [Adjoint.lean](Lean%20Proofs/Quantum/Adjoint.lean): Lemmas about matrix adjoints.
- [TensorProduct.lean](Lean%20Proofs/Quantum/Adjoint.lean): Lemmas about the tensor product.
- [Congruence.lean](Lean%20Proofs/Quantum/Congruence.lean): Lemmas about the "congruence" relation (equality up to a global phase), including a proof that congruence is decidable.
- [Measurement.lean](Lean%20Proofs/Quantum/Measurement.lean): Proof that if we measure `α|0⟩ + β|1⟩` in the computational basis, the probability of getting `|0⟩` is `‖α‖`. This is the only proof that uses the `Random`-monad-based definitions of quantum measurement.
- [NoCloning.lean](Lean%20Proofs/Quantum/NoCloning.lean): Proof of the no-cloning theorem.
- [Teleportation.lean](Lean%20Proofs/Quantum/Teleportation.lean): Proof of correctness of the quantum teleportation algorithm.
