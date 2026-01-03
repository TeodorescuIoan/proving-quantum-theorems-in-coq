# Proving Quantum Theorems in Coq

Proving interesting theorems from [[1]](#1) and [[2]](#2) in Rocq (previously Coq).

## Building instructions

Install the [opam](https://opam.ocaml.org/) package manager.

Create an opam switch (recommended when working with Rocq).

```shell
opam switch create 5.4.0
eval $(opam env)
```

The argument given to create is the OCaml compiler version.

The proofs rely on [QuantumLib](https://github.com/inQWIRE/QuantumLib).

To install it and the other dependencies on your system navigate to the root of the project and run:

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install . --deps-only
```

Finally, to build the project run:

```shell
make all
```

## Documentation

### Heisenberg's Uncertainty Principle

   Proving the hermitian version of the uncertainty principle [[1]](#1):

   Let $A$, $B$ two hermitian operators and $| x \rangle$ a quantum state.

   ```math
   Var_x(A) Var_x(B) \ge \frac{1}{4} | \langle x | [A,B]x\rangle |^2
   ```

### No-Cloning Theorem

   A quantum state cloning operator $U$ applied to an arbitrary state $| \phi \rangle$
   is specified by:

   ```math
   U (| \phi \rangle \otimes 0) = | \phi \rangle \otimes | \phi \rangle
   ```

   The proof shows such an operator does not exist.

### Phase Kickback on CNOT gate

   Surrounding a CNOT gate by Hadamard gates at each end reverses the control bit.

## References

<a id="1">[1]</a> Hirvensalo, N. (2001) Quantum computing. Springer-Verlag, Berlin, Heidelberg.

<a id="2">[2]</a> Yanofsky, N.S. and Mannucci, M.A. (2008) Quantum Computing for Computer Scientists. Cambridge: Cambridge University Press. 
