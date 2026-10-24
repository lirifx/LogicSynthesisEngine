"""Tests for lse.py.   Run:  python -m unittest discover -s tests -v"""
import itertools
import os
import random
import sys
import tempfile
import unittest

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
sys.path.insert(0, ROOT)

from lse import Cube, HazardAnalyzer, LogicEngine, Minimizer, Parser  # noqa: E402

EXAMPLES = os.path.join(ROOT, "examples")


def covered(cubes):
    """All minterms inside a list of cubes."""
    return {m for cube in cubes for m in Cube.minterms(cube)}


def random_function(rng, n):
    """Random ON set and don't-care set for n inputs."""
    on = {m for m in range(2 ** n) if rng.random() < 0.4}
    dc = {m for m in range(2 ** n) if m not in on and rng.random() < 0.15}
    return on, dc


class TestMinimizer(unittest.TestCase):
    def test_cover_is_correct(self):
        rng = random.Random(1)
        for n in range(1, 7):
            for _ in range(30):
                on, dc = random_function(rng, n)
                off = set(range(2 ** n)) - on - dc
                result = Minimizer(n, on, dc)
                self.assertTrue(on <= covered(result.cover))           # every 1 is covered
                self.assertFalse(covered(result.cover) & off)          # no 0 is covered
                self.assertTrue(set(result.essentials) <= set(result.cover))
                for prime in result.primes:                            # primes cannot grow
                    for k, bit in enumerate(prime):
                        if bit != "-":
                            bigger = prime[:k] + "-" + prime[k + 1:]
                            self.assertTrue(covered([bigger]) & off)

    def test_cover_is_minimal(self):
        rng = random.Random(7)
        for n in (2, 3, 4):
            for _ in range(40):
                on, dc = random_function(rng, n)
                result = Minimizer(n, on, dc)
                if len(result.primes) > 12:
                    continue
                best = min(sum(Cube.literals(c) for c in combo)
                           for size in range(len(result.primes) + 1)
                           for combo in itertools.combinations(result.primes, size)
                           if on <= covered(combo))
                self.assertEqual(result.literals, best)

    def test_textbook_example(self):
        engine = LogicEngine(Parser.parse_equations("F(A,B,C,D) = m(0,2,5,7,8,10,13,15) + d(1,9)"))
        result = engine.minimize(engine.design.functions[0])
        self.assertEqual((len(result.primes), len(result.essentials), result.literals), (4, 2, 4))
        self.assertIn("F = BD + B'D'", engine.minimized_sop())


class TestHazards(unittest.TestCase):
    def test_fix_removes_all_hazards(self):
        rng = random.Random(3)
        for _ in range(100):
            n = rng.randint(2, 5)
            on, _ = random_function(rng, n)
            result = Minimizer(n, on)
            fixed = HazardAnalyzer.fix(n, on, result.cover, result.primes)
            self.assertEqual(HazardAnalyzer.find(n, on, fixed), [])
            self.assertEqual(covered(fixed), covered(result.cover))   # same function

    def test_known_hazard(self):
        engine = LogicEngine(Parser.parse_equations("F = A'B + AC"))
        self.assertIn("Static-1 hazards in AND-OR realization: 1", engine.hazards())


class TestParser(unittest.TestCase):
    def test_same_function_written_differently(self):
        expected = Parser.parse_equations("F = A'B + AC").functions[0].on
        for text in ["F = ~A*B + A*C", "F = !A & B | A & C", "F = (A' B) + (A C)",
                     "F(A,B,C) = m(2,3,5,7)", "F(A,B,C) = M(0,1,4,6)", "F = (A + B)(A' + C)",
                     "INORDER = A B C; F = !A*B + A*C;"]:
            self.assertEqual(Parser.parse_equations(text).functions[0].on, expected, text)

    def test_full_adder(self):
        design = Parser.load_file(os.path.join(EXAMPLES, "full_adder.eqn"))
        self.assertEqual([sorted(f.on) for f in design.functions], [[1, 2, 4, 7], [3, 5, 6, 7]])

    def test_bcd_decoder(self):
        design = Parser.load_file(os.path.join(EXAMPLES, "bcd7seg.pla"))
        segment_a = design.functions[0]
        self.assertEqual(sorted(segment_a.on), [0, 2, 3, 5, 6, 7, 8, 9])
        self.assertEqual(sorted(segment_a.dc), [10, 11, 12, 13, 14, 15])

    def test_constants(self):
        for text, on in [("F = A + A'", [0, 1]), ("F = A A'", []), ("F = 1 + A", [0, 1])]:
            self.assertEqual(sorted(Parser.parse_equations(text).functions[0].on), on)


class TestNetlist(unittest.TestCase):
    def test_every_circuit_style(self):
        for name in os.listdir(EXAMPLES):
            engine = LogicEngine(Parser.load_file(os.path.join(EXAMPLES, name)))
            for kind in ("canonical", "sop", "pos", "hazard_free"):
                for universal in (False, True):
                    self.assertTrue(engine.check_netlist(engine.build_netlist(kind, universal)),
                                    (name, kind, universal))

    def test_constant_outputs(self):
        engine = LogicEngine(Parser.parse_equations("INORDER = a b; one = a + a'; zero = a a'; f = a;"))
        for kind in ("sop", "pos"):
            for universal in (False, True):
                self.assertTrue(engine.check_netlist(engine.build_netlist(kind, universal)))

    def test_files_are_written(self):
        with tempfile.TemporaryDirectory() as folder:
            engine = LogicEngine(Parser.load_file(os.path.join(EXAMPLES, "bcd7seg.pla")), folder)
            self.assertIn("PASS", engine.write_verilog())
            engine.write_fpga_files()
            for filename in ("bcd7seg.v", "tb_bcd7seg.v", "bcd7seg_hdlboard.v", "bcd7seg_nexysa7.v", "bcd7seg_nexysa7.xdc"):
                self.assertTrue(os.path.exists(os.path.join(folder, filename)))
            self.assertNotIn("Unknown", engine.run_all())


if __name__ == "__main__":
    unittest.main()
