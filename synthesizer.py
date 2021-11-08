# Rory Linerud
# rlinerud@u.rochester.edu
#
# synthesizer.py

from synth.engine import SynthesisEngine, SynthesisError
from synth.ops import ops
from synth.program import Program
from synth.types import Instantiator, Library, Oracle, Value
from typing import Optional


class Synthesizer:

    """
    An automatic program synthesizer.

    Generates a program that satisfies a set of given input-output
    examples from an invisible but accessible reference program. The
    base component library may or may not be known ahead of time. When
    it is, just a single attempt at synthesis should be made;
    otherwise, the synthesizer should search over the library space
    until it finds a suitable set of components.

    Public methods:

    - `__call__`: run the synthesizer to generate a program consistent
      with the provided oracle, input-output pairs, and (if present)
      base component library.
    """

    @staticmethod
    def _next_libs(library: Library) -> list[Library]:
        """
        Get the next several libraries that should be searched after
        the given library is already exhausted.

        Libraries should be generated in a breadth-first fashion. That
        is, a library with one AND gate and one OR gate should be
        considered before a library with three AND gates.

        Parameters:

        - `library`: a dictionary that maps each available base
          component to its frequency of occurrence in any synthesized
          programs.
        """
        libs = []
        for component in library:
            libs.append(library | {component: library[component] + 1})

        return libs

    def __call__(self, oracle: Oracle,
                 input_types: tuple[Instantiator],
                 output_type: Instantiator,
                 examples: dict[tuple[Value, ...], Value],
                 library: Optional[Library] = None,
                 verbose: bool = True) -> Optional[Program]:
        """
        Either use the specified library to synthesize a program that
        satisfies the given reference `oracle` and input-output
        `examples`; or perform an iterative search over the component
        library space, looking for a feasible set of components if no
        predetermined library is provided.

        Parameters:

        - `oracle`: the reference program to be synthesized.
        - `input_types`: a tuple of Z3 variable instantiators that
          represent the input types of the synthesized program.
        - `output_type`: a Z3 variable instantiator that represents the
          output type of the synthesized program.
        - `examples`: a collection of input-output pairs from the
          reference program.
        - `library`: an optional, predetermined library of base
          components that the synthesizer should use to perform program
          synthesis.
        - `verbose`: a boolean indicating whether or not informative
          print statements should be run during the execution of this
          function.
        """
        if library is None:
            init_lib = {op: 0 for op in ops}
            cache = {tuple(init_lib.items())}
            queue = [init_lib]
            while True:
                library = queue.pop(0)
                if verbose:
                    print(f'Current library: {library}')

                synth = SynthesisEngine(input_types, output_type, library)
                try:
                    program = synth.synthesize(oracle, examples, verbose)
                    return program

                except SynthesisError:
                    if verbose:
                        print('    Trying with another library...')

                for lib in self._next_libs(library):
                    hashable = tuple(lib.items())
                    if hashable not in cache:
                        queue.append(lib)
                        cache.add(hashable)

        else:
            synth = SynthesisEngine(input_types, output_type, library)
            try:
                program = synth.synthesize(oracle, examples, verbose)
                return program

            except SynthesisError:
                return None
