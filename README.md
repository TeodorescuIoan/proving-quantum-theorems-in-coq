# Proving Quantum Theorems in Coq

## Building instructions

These proofs rely on [QuantumLib](https://github.com/inQWIRE/QuantumLib).

TODO

## Documentation

* Heisenberg's Uncertainty Principle

   Proving the hermitian version of Heisenberg's uncertainty principle [[1]](#1):

   $$Var_x(A) Var_x(B) \ge \frac{1}{4} \mid \langle x \mid \[A,B\]x\rangle \mid^2$$

* No-Cloning Theorem

   A quantum state cloning operator $U$ applied to an arbitrary state $\mid \phi \rangle$
   is specified by:

   $$U (\mid \phi \rangle \otimes 0) = \mid \phi \rangle \otimes \mid \phi \rangle $$

   The proof shows such an operator does not exist.

* Phase Kickback on CNOT gate

   The proof is trivial thanks to [QuantumLib](https://github.com/inQWIRE/QuantumLib) automation tactics.

## References

<a id="1">[1]</a> Hirvensalo, N. (2001) Quantum computing. Springer-Verlag, Berlin, Heidelberg.

<a id="2">[2]</a> Yanofsky, N.S. and Mannucci, M.A. (2008) Quantum Computing for Computer Scientists. Cambridge: Cambridge University Press. 
