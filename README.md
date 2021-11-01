# synth

## A Z3Py program synthesizer

This is a Python-based implementation of the oracle-guided inductive synthesis system introduced in [Jha et al. (2010)](https://dl.acm.org/doi/pdf/10.1145/1806799.1806833). This system allows the programmer to automatically generate
minimal, efficient programs that satisfy some set of input-output examples. Such a system could potentially be used for
simple program deobfuscation as well as program optimization.

In its current state, `synth` can be used anywhere the satisfiability modulo theories solver package `z3` is available.
This is a hard dependency and no other SMT backends are currently supported. A web app is currently in development for
those who cannot install `z3` as a dependency for this project but would still like access to a simple program synthesis
application.

## Getting started

To get started, first import both `synth` and `z3`. From there, you can declare the inputs and outputs of your reference
program, provide some input-output examples, and begin your synthesis:

```
import synth
import z3


# Declare inputs and output
inputs = (z3.Int, z3.Int)
output = z3.Int


# Provide some input-output examples
examples = {
    (3, 2): 5,
    (1, 4): -15,
}


# Provide a reference implementation
def oracle(a: int, b: int) -> int:
    return a * a - b * b


synthesizer = synth.Synthesizer()
synthesizer(oracle, inputs, output, examples)
```

Once run, the synthesizer will perform a breadth-first search across the set of possible programs, looking for a
candidate that satisfies all of the provided input-output examples with as few base components as possible. Currently
only boolean and integer operations are fully supported; support for real number operations is only experimental. The
user can configure the base components that the system has available to it in ops.py (or add their own if so desired).

## Upcoming

1. Finish docstrings in engine.py and synthesizer.py
2. Add support for real number operations
3. Export the ops.py component dictionary to a JSON file for easier configuration by the user
