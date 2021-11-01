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
    """

    @staticmethod
    def _next_libs(library: Library) -> list[Library]:
        """
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
                 verbose: bool = True) -> Program:
        """
        
        """
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
