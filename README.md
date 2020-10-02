# Flow

## Session

### Dependencies

- [Isabelle 2020](https://isabelle.in.tum.de/)
- [AFP](https://www.isa-afp.org/) (tested 2020-08-15)

### Usage

Interactively explore/work on session in Isabelle:

```text
isabelle -d <path-to-flow> jedit
```

Check/build session:

```text
isabelle -d <path-to-flow> build Flow
```

### Project Structure

We annotate the theory names with the definitions and lemmas from [1] that are contained in there.
The ordering of theories in this enumeration provides a reasonable order to examine the project.

Preliminary development is contained in theories
- `Auxiliary`: arbitrary/common/auxiliary lemmas on lists/sets/functions
- `Alternating`: alternating list predicates
- `Endomorphism`[1, defs. 9,10,12]: formalization of endomorphisms
- `Chain`[1, def. 10]: a special kind of function concatenation induced by lists on binary functions
- `Pigeonhole`: the generalized pigeonhole principle and some auxiliary lemmas for the simple pigeonhole principle

The basic abstractions, flow graphs and flow interfaces are defined in theories
- `Flow_Graph`[1, defs. 3,4, lem. 1]
- `Flow_Interface`[1, defs. 5,6]

Their relationship is formalized in theory (for further development,
do not use `Flow_Graph` or `Flow_Interface` directly, use this one)
- `Flow_Base`[1, lem. 2]

Theoretical results on flow graphs and flow interfaces are provided in
- `Flow_Footprint`: a node is in footprint of some operation iff. it is changed
- `Flow_Graph_Separation_Algebra`: valid flow graphs form a separation algebra
- `Flow_Interface_Separation_Algebra`[1, th. 1]: valid flow interfaces form a separation algebra

Two notions of extensions of flow graphs are provided in:
- `Flow_Extension`[1, defs. 7,13, th. 2]

Approximations of flow terms are developed in:
- `Approximations`

The development on nilpotent flow graphs is provided in:
- `Nilpotent`[1, lem. 4]

The development on effectively acyclic flow graphs is provided in:
- `Effectively_Acyclic`[1, def. 11]: general definitions regarding effective acyclicity
- `Effectively_Acyclic_Approximations`: extends `Approximations` in context of effective acyclicity
- `Effectively_Acyclic_Switch_Worlds`: auxiliary result for `Effectively_Acyclic_Maintain`
- `Effectively_Acyclic_Sourced_Path`: auxiliary result for `Effectively_Acyclic_Maintain`
- `Effectively_Acyclic_Equal_Capacity`: auxiliary result for `Effectively_Acyclic_Maintain`
- `Effectively_Acyclic_Uniqueness`[1, lem. 5]: proves uniqueness of flows of effectively acyclic flow graphs
- `Effectively_Acyclic_Maintain`[1, th. 3]: proves existence of flow of effectively acyclic flow graphs
- `Effectively_Acyclic_Maintain_Counter_Example`: provides counter example for [1, th. 3]

"Encoding flow-based proofs in SL"[1, sec. 3.1]:
- `FF.thy`

The PIP example[1, sec. 3.2] is split into:
- `Pip_Shared`: shared development for acquire and release cases
- `Pip_Acquire`: proof of acquire operation
- `Pip_Release`: proof of release operation
- `Pip_Example`: small example demonstrating the application of the PIP operations

All development is summarized in `Flow.thy`.

## References

* [1] Siddharth Krishna, Alexander J. Summers, and Thomas Wies: Local Reasoning for Global Graph Properties, ESOP 2020, [https://cs.nyu.edu/~siddharth/](https://cs.nyu.edu/~siddharth/)
* [2] Siddharth Krishna: Compositional Abstractions for Verifying Concurrent Data Structures, [https://cs.nyu.edu/~siddharth/](https://cs.nyu.edu/~siddharth/)