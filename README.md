Covert channels allow malicious applications to circumvent information flow
control systems by encoding and transferring information indirectly, and they
are often subtle and difficult to spot.

Nickel is a framework that helps developers systematically eliminate covert
channels inherent in their system designs, through automated verification of
noninterference. It allows developers to express a high-level information flow
policy in Python. It extends the Hyperkernel infrastructure to verify that both
an interface specification and an implementation satisfy noninterference with
respect to the policy, ruling out covert channels. If verification fails,
Nickel generates informative counterexamples for debugging and revising the
design.

See more information at:

https://unsat.cs.washington.edu/projects/nickel/

# How to run the Nistar OS kernel

We have tested it on both Linux and macOS.

    $ make qemu-kernel

The syscall interface is defined in `include/uapi/nistar/syscall.h` and most of
the implementation is under `nistar/`.

# How to run the Nistar proofs

We have tested it only on Linux using Z3 version 4.6.0.

## Refinement proofs

    $ make verify-nistar-par-refinement

and

    $ make verify-nistar-assumptions

## Noninterference proofs

    $ make verify-nistar-par-ni

## Other invariants/lemmas required by the NI proofs

    $ make verify-nistar-par-spec-lemmas

