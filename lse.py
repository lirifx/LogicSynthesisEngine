#!/usr/bin/env python3
"""
LSE - Logic Synthesis Engine
============================

Name: Francis Liri
EC551: Advanced Digital Design with Verilog and FPGAs (Fall 2026)


This  code implements a custom Logic Synthesis Engine

It reads a Boolean function input via file or command line, minimizes and analyzes it, and writes 3 structural
Verilog files as described below
 - a logic module only 
 - a logic module and a top module wrapper to run the file o the online fpga simulator HDLBoard
 - a logic module and a top module wrapper to run the file on a Nexys A7 FPGA board 

Usage
    python lse.py examples/bcd7seg.pla -a                  run operations 1-12
    python lse.py examples/full_adder.eqn -c "1;5;9"       run selected operations
    python lse.py -e "F = A'B + AC" -a                     equation typed on the command line
    python lse.py examples/bcd7seg.pla --verilog --fpga    write Verilog and the FPGA files
    python lse.py examples/bcd7seg.pla -a -o report.txt    also save the results to a file

Input formats
    .pla  Espresso truth table:  .i .o .ilb .ob, rows like "0011 1111001", '-' = don't care
    .eqn  equations, one per line or separated by ';'
            F = A'B + AC                  sum of products
            F = (A + B')(C + D)           product of sums
            F(A,B,C) = m(1,3,5) + d(7)    minterm list with don't-cares
            F(A,B,C) = M(0,2)             maxterm list
            INORDER = a b cin;  OUTORDER = sum cout;
            p = a ^ b;  sum = p ^ cin;    multi-level circuit: each equation is a gate
                                          (node) and each signal name is a wire (edge)
          operators: NOT ' ~ !   AND * &  (or AB written together)   XOR ^   OR + |

The following operations can be performed to minimize and analyze the circuit:
1. csop - Canonical SOP
2. cpos - Canonical POS
3. icsop - Canonical SOP of the inverse F'
4. icpos - Canonical POS of the inverse F'
5. minsop - Literal-minimized SOP and literals saved
6. minpos -Literal-minimized POS and literals saved
7. pi - Number of prime implicants
8. epi - Number of essential prime implicants
9. on - Number of ON-set minterms
10. off - Number of OFF-set maxterms
11. hazard - Custom 1: static hazard detection and hazard-free covers
12. cost - Custom 2: gate/transistor cost and delay of implementations


How functions are stored
    A function is kept as Python sets of minterm numbers: the ON set (output 1),
    the DC set (don't care) and the OFF set (output 0). The first input is the most
    significant bit, so for inputs (A, B, C) minterm 6 = 110 means A=1, B=1, C=0.

    A product term ("cube") is a string of '0', '1' and '-' in input order:
    '1-0' means A C' ('-' = that input does not appear in the term).


"""
import argparse
import itertools
import os
import re
import sys

MAX_INPUTS = 16
sys.setrecursionlimit(10000)


def to_bits(m, n):
    """Minterm number -> n-character bit string, e.g. to_bits(6, 3) == '110'."""
    return format(m, f"0{n}b")


# ============================================================================
#  Product terms (cubes)
# ============================================================================
class Cube:
    """Helper functions for product terms written as strings of '0', '1', '-'."""

    @staticmethod
    def literals(cube):
        """Number of variables in the term, e.g. '1-0' (A C') has 2."""
        return len(cube) - cube.count("-")

    @staticmethod
    def minterms(cube):
        """All minterm numbers inside the cube, e.g. '1-0' -> [4, 6]."""
        choices = [("0", "1") if c == "-" else (c,) for c in cube]
        return [int("".join(bits), 2) for bits in itertools.product(*choices)]

    @staticmethod
    def contains(cube, m):
        """True if minterm m lies inside the cube."""
        return all(c == "-" or c == b for c, b in zip(cube, to_bits(m, len(cube))))

    @staticmethod
    def sort_key(cube):
        """Sort fewer literals first, then '1' before '0' before '-' (gives A before A')."""
        order = {"1": 0, "0": 1, "-": 2}
        return Cube.literals(cube), [order[c] for c in cube]


# ============================================================================
#  Functions and designs
# ============================================================================
class BoolFunction:
    """One output: the sets of minterms where it is 1 (on), don't care (dc) and 0 (off)."""

    def __init__(self, name, inputs, on, dc=()):
        self.name = name
        self.inputs = list(inputs)
        self.n = len(self.inputs)
        self.on = set(on)
        self.dc = set(dc) - self.on                    # a minterm listed as both counts as ON
        self.off = set(range(2 ** self.n)) - self.on - self.dc


class Design:
    """A complete input file: the input names and one BoolFunction per output."""

    def __init__(self, name, inputs, functions):
        self.name = name
        self.inputs = list(inputs)
        self.functions = functions


# ============================================================================
#  Reading input files
# ============================================================================
class ParseError(Exception):
    pass


class ExprParser:
    """Turns a list of tokens into an expression tree.

    "A'B + C" becomes ('or', [('and', [('not', ('var', 'A')), ('var', 'B')]), ('var', 'C')])

    Precedence, lowest first:  OR (+ |)  ->  XOR (^)  ->  AND (* & or juxtaposition)  ->  NOT
    """

    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        """The next token without consuming it (None at the end)."""
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def next(self):
        """Consume and return the next token."""
        token = self.peek()
        self.pos += 1
        return token

    def parse(self):
        tree = self.parse_or()
        if self.peek() is not None:
            raise ParseError(f"unexpected '{self.peek()}'")
        return tree

    def parse_or(self):
        terms = [self.parse_xor()]
        while self.peek() in ("+", "|"):
            self.next()
            terms.append(self.parse_xor())
        return terms[0] if len(terms) == 1 else ("or", terms)

    def parse_xor(self):
        terms = [self.parse_and()]
        while self.peek() == "^":
            self.next()
            terms.append(self.parse_and())
        return terms[0] if len(terms) == 1 else ("xor", terms)

    def parse_and(self):
        terms = [self.parse_not()]
        while True:
            token = self.peek()
            if token in ("*", "&", "."):
                self.next()
            elif token is None or token in ("+", "|", "^", ")"):
                break
            # anything else (a name, '(' or '~') right after a factor is an implicit AND
            terms.append(self.parse_not())
        return terms[0] if len(terms) == 1 else ("and", terms)

    def parse_not(self):
        token = self.next()
        if token in ("~", "!"):                               # prefix NOT
            node = ("not", self.parse_not())
        elif token == "(":
            node = self.parse_or()
            if self.next() != ")":
                raise ParseError("missing ')'")
        elif token in ("0", "1"):
            node = ("const", token == "1")
        elif token and (token[0].isalpha() or token[0] == "_"):
            node = ("var", token)
        else:
            raise ParseError(f"unexpected '{token}'" if token else "expression ends too early")
        while self.peek() == "'":                             # postfix NOT, e.g. A'
            self.next()
            node = ("not", node)
        return node

    @staticmethod
    def variables(node):
        """Names used in a tree, in order of first appearance."""
        kind = node[0]
        if kind == "var":
            return [node[1]]
        if kind == "const":
            return []
        if kind == "not":
            return ExprParser.variables(node[1])
        names = []
        for child in node[1]:
            names += [x for x in ExprParser.variables(child) if x not in names]
        return names

    @staticmethod
    def evaluate(node, lookup):
        """True/False value of a tree. lookup(name) returns the value of a signal."""
        kind = node[0]
        if kind == "var":
            return lookup(node[1])
        if kind == "const":
            return node[1]
        if kind == "not":
            return not ExprParser.evaluate(node[1], lookup)
        values = [ExprParser.evaluate(child, lookup) for child in node[1]]
        if kind == "and":
            return all(values)
        if kind == "or":
            return any(values)
        return sum(values) % 2 == 1                          # XOR: odd number of 1s


class Parser:
    """Reads .pla and equation files into a Design."""

    @staticmethod
    def load_file(path):
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        name = os.path.splitext(os.path.basename(path))[0]
        if path.lower().endswith(".pla"):
            return Parser.parse_pla(text, name)
        return Parser.parse_equations(text, name)

    @staticmethod
    def default_names(n):
        """A, B, C ... for up to 26 inputs, otherwise x0, x1, ..."""
        return [chr(ord("A") + i) for i in range(n)] if n <= 26 else [f"x{i}" for i in range(n)]

    # ------------------------------------------------------------------ PLA
    @staticmethod
    def parse_pla(text, name):
        n = None
        n_out = 1
        inputs = outputs = None
        rows = []
        for line in text.splitlines():
            words = line.split("#")[0].split()          # drop comments, split on spaces
            if not words:
                continue
            if words[0] == ".i":
                n = int(words[1])
            elif words[0] == ".o":
                n_out = int(words[1])
            elif words[0] == ".ilb":
                inputs = words[1:]
            elif words[0] == ".ob":
                outputs = words[1:]
            elif words[0] == ".e":
                break
            elif not words[0].startswith("."):            # a truth-table row
                rows.append(words)
        if n is None:
            raise ParseError("the PLA file has no .i line")
        if n > MAX_INPUTS:
            raise ParseError(f"{n} inputs: at most {MAX_INPUTS} are supported")
        inputs = inputs or Parser.default_names(n)
        outputs = outputs or (["F"] if n_out == 1 else [f"F{j}" for j in range(n_out)])

        on = [set() for _ in range(n_out)]
        dc = [set() for _ in range(n_out)]
        for row in rows:
            if len(row) != 2 or len(row[0]) != n or len(row[1]) != n_out:
                raise ParseError(f"bad PLA row: {' '.join(row)}")
            in_pattern, out_pattern = row
            minterms = Cube.minterms(in_pattern)           # e.g. '11--' -> 12, 13, 14, 15
            for j, value in enumerate(out_pattern):
                if value == "1":
                    on[j].update(minterms)
                elif value == "-":
                    dc[j].update(minterms)
        functions = [BoolFunction(outputs[j], inputs, on[j], dc[j]) for j in range(n_out)]
        return Design(name, inputs, functions)

    # ------------------------------------------------------------------ equations
    @staticmethod
    def parse_equations(text, name="design"):
        text = text.replace("’", "'")
        text = re.sub(r"#.*", "", text)                     # remove comments
        statements = [s.strip() for s in re.split(r"[;\n]", text) if s.strip()]

        inputs = outputs = None
        equations = []                                      # (signal name, right-hand side)
        for statement in statements:
            # INORDER / OUTORDER declare the input and output order
            declaration = re.match(r"(INORDER|OUTORDER)\s*=\s*(.*)", statement, re.I)
            if declaration:
                names = declaration.group(2).replace(",", " ").split()
                if declaration.group(1).upper() == "INORDER":
                    inputs = names
                else:
                    outputs = names
                continue
            if "=" not in statement:                        # a bare expression is named F
                statement = "F = " + statement
            left, right = [part.strip() for part in statement.split("=", 1)]
            # left side is "F" or "F(A,B,C)", the brackets list the inputs
            match = re.fullmatch(r"(\w+)\s*(?:\((.*)\))?", left)
            if not match:
                raise ParseError(f"bad left-hand side '{left}'")
            if match.group(2) and inputs is None:
                inputs = [x.strip() for x in match.group(2).split(",")]
            equations.append((match.group(1), right))
        if not equations:
            raise ParseError("no equations found")

        # Without an explicit AND operator, "AB" means A AND B (single-letter names)
        all_text = " ".join(right for _, right in equations)
        split_letters = not re.search(r"[*&.]", all_text)
        known_names = set(inputs or []) | {signal for signal, _ in equations}

        # Each signal is either a minterm/maxterm list or an expression tree
        definitions = {}
        largest_index = 0
        for signal, right in equations:
            term_list = re.fullmatch(r"([mM])\s*\(([\d,\s]*)\)\s*(?:\+\s*d\s*\(([\d,\s]*)\))?", right)
            if term_list:
                numbers = [int(x) for x in re.findall(r"\d+", term_list.group(2))]
                dont_cares = [int(x) for x in re.findall(r"\d+", term_list.group(3) or "")]
                largest_index = max([largest_index] + numbers + dont_cares)
                definitions[signal] = ("list", term_list.group(1), set(numbers), set(dont_cares))
            else:
                tokens = []
                for token in re.findall(r"\w+|\S", right):
                    if split_letters and token not in known_names and token[0].isalpha():
                        tokens += re.findall(r"[A-Za-z_]\d*", token)   # "AB" -> "A", "B"
                    else:
                        tokens.append(token)
                definitions[signal] = ("expr", ExprParser(tokens).parse())

        # Inputs = names used in expressions that are not defined by an equation
        used = []
        for definition in definitions.values():
            if definition[0] == "expr":
                used += [x for x in ExprParser.variables(definition[1]) if x not in used]
        if inputs is None:
            inputs = sorted(x for x in used if x not in definitions)
            if not inputs:                                  # only minterm lists were given
                inputs = Parser.default_names(max(1, largest_index.bit_length()))
        n = len(inputs)
        if n > MAX_INPUTS:
            raise ParseError(f"{n} inputs: at most {MAX_INPUTS} are supported")
        if largest_index >= 2 ** n:
            raise ParseError(f"term {largest_index} does not fit in {n} inputs")

        # Outputs = signals that no other equation uses (unless OUTORDER lists them)
        if outputs is None:
            outputs = [s for s, _ in equations if s not in used] or [s for s, _ in equations]

        def signal_value(signal, m, cache, path=()):
            """Value of any signal when the inputs equal minterm m."""
            if signal in inputs:
                return to_bits(m, n)[inputs.index(signal)] == "1"
            if signal in cache:
                return cache[signal]
            if signal not in definitions:
                raise ParseError(f"undefined signal '{signal}'")
            if signal in path:
                raise ParseError(f"combinational loop through '{signal}'")
            definition = definitions[signal]
            if definition[0] == "list":                     # m(...) lists 1s, M(...) lists 0s
                value = (m in definition[2]) == (definition[1] == "m")
            else:
                value = ExprParser.evaluate(
                    definition[1], lambda s: signal_value(s, m, cache, path + (signal,)))
            cache[signal] = value
            return value

        # Build each output's truth table by evaluating it for every minterm
        functions = []
        for output in outputs:
            on = set()
            for m in range(2 ** n):
                if signal_value(output, m, {}):
                    on.add(m)
            definition = definitions.get(output)
            dc = definition[3] if definition and definition[0] == "list" else set()
            functions.append(BoolFunction(output, inputs, on, dc))
        return Design(name, inputs, functions)


# ============================================================================
#  Minimization (operations 5-8)
# ============================================================================
class Minimizer:
    """Quine-McCluskey minimization of one function.

    1. Find all prime implicants: the largest cubes containing only ON and
       don't-care minterms.
    2. Find the essential primes: the only prime covering some ON minterm.
    3. Cover the remaining ON minterms with the fewest literals using a
       branch-and-bound search. If the search gets too big it stops early and
       `exact` is set to False (the result is still correct, maybe not minimal).
    """
    SEARCH_LIMIT = 100_000

    def __init__(self, n, on, dc=()):
        self.n = n
        self.on = set(on)

        # Keep only primes that cover at least one ON minterm
        self.covers = {}                                    # prime -> ON minterms it covers
        for prime in self.find_primes(self.on | set(dc)):
            covered = self.on & set(Cube.minterms(prime))
            if covered:
                self.covers[prime] = covered
        self.primes = sorted(self.covers, key=Cube.sort_key)

        # For every ON minterm, the list of primes that cover it
        self.primes_for = {m: [p for p in self.primes if m in self.covers[p]] for m in self.on}

        self.essentials = sorted({ps[0] for ps in self.primes_for.values() if len(ps) == 1},
                                 key=Cube.sort_key)
        remaining = set(self.on)
        for prime in self.essentials:
            remaining -= self.covers[prime]

        self.exact = True
        self.cover = sorted(self.essentials + self.cheapest_cover(remaining), key=Cube.sort_key)
        self.literals = sum(Cube.literals(c) for c in self.cover)

    def find_primes(self, minterms):
        """Merge cubes that differ in one position ('0' and '1' -> '-') until nothing merges.
        Cubes that never merge with another are the prime implicants."""
        current = {to_bits(m, self.n) for m in minterms}
        primes = set()
        while current:
            merged, used = set(), set()
            for cube in current:
                for i, bit in enumerate(cube):
                    if bit == "0":
                        partner = cube[:i] + "1" + cube[i + 1:]
                        if partner in current:
                            merged.add(cube[:i] + "-" + cube[i + 1:])
                            used.update([cube, partner])
            primes |= current - used
            current = merged
        return primes

    @staticmethod
    def cost(prime):
        """Literals count most; the +1 prefers fewer terms when literals are equal."""
        return 1000 * Cube.literals(prime) + 1

    def cheapest_cover(self, remaining):
        self.best_cost = float("inf")
        self.best_cover = []
        self.steps = 0
        self.search(frozenset(remaining), [], 0)
        return self.best_cover

    def search(self, remaining, chosen, cost):
        """Depth-first search: pick the uncovered minterm with the fewest primes,
        try each of those primes, and drop any branch that costs more than the best so far."""
        if not remaining:
            if cost < self.best_cost:
                self.best_cost, self.best_cover = cost, list(chosen)
            return
        self.steps += 1
        if self.steps > self.SEARCH_LIMIT:
            self.exact = False
            return
        minterm = min(remaining, key=lambda m: len(self.primes_for[m]))
        # try the primes that cover the most for their cost first
        options = sorted(self.primes_for[minterm],
                         key=lambda p: self.cost(p) / len(self.covers[p] & remaining))
        for prime in options:
            if cost + self.cost(prime) < self.best_cost:
                chosen.append(prime)
                self.search(remaining - self.covers[prime], chosen, cost + self.cost(prime))
                chosen.pop()


# ============================================================================
#  Hazard analysis (operation 11)
# ============================================================================
class HazardAnalyzer:
    """Static hazards in two-level circuits.

    If two ON minterms differ in only one input but no single product term
    covers both, then while that input changes one AND gate can switch off just
    before the other switches on, so the output glitches 1 -> 0 -> 1
    (a static-1 hazard). Running the same check on the OFF set and the POS
    cover finds static-0 hazards (0 -> 1 -> 0) in OR-AND circuits.
    Adding a prime that covers each such pair removes the hazard.
    """

    @staticmethod
    def find(n, minterms, cover):
        """List of (m1, m2, k): neighbouring minterms that differ in input k and share no cube."""
        minterms = set(minterms)
        hazards = []
        for m1 in sorted(minterms):
            for k in range(n):
                bit = 1 << (n - 1 - k)                      # the bit of input k
                m2 = m1 | bit
                if m1 & bit or m2 not in minterms:
                    continue
                if not any(Cube.contains(c, m1) and Cube.contains(c, m2) for c in cover):
                    hazards.append((m1, m2, k))
        return hazards

    @staticmethod
    def fix(n, minterms, cover, primes):
        """Return the cover plus one extra prime for every hazardous pair."""
        cover = list(cover)
        for m1, m2, _ in HazardAnalyzer.find(n, minterms, cover):
            if any(Cube.contains(c, m1) and Cube.contains(c, m2) for c in cover):
                continue                                    # already fixed by an earlier addition
            candidates = [p for p in primes if Cube.contains(p, m1) and Cube.contains(p, m2)]
            cover.append(min(candidates, key=Cube.sort_key))
        return cover


# ============================================================================
#  Gate netlist, cost/delay and Verilog (operation 12 and Verilog output)
# ============================================================================
class Netlist:
    """A two-level circuit made of Verilog primitive gates.

    Each gate is stored as (kind, output_wire, [input_wires]). Inverters for
    complemented inputs and identical gates are shared between outputs.
    """
    KEYWORDS = {"and", "or", "not", "nand", "nor", "xor", "xnor", "buf", "module", "endmodule",
                "input", "output", "wire", "reg", "assign", "begin", "end", "if", "else", "case"}

    # How each primitive gate computes its output from a list of input values
    LOGIC = {"and": all, "or": any,
             "nand": lambda x: not all(x), "nor": lambda x: not any(x),
             "not": lambda x: not x[0], "buf": lambda x: x[0]}

    def __init__(self, module, inputs, outputs):
        self.used_names = set()
        self.module = self.make_name(module)
        self.input_names = list(inputs)                     # original names
        self.output_names = list(outputs)
        self.inputs = [self.make_name(x) for x in inputs]   # Verilog-safe port names
        self.outputs = [self.make_name(x) for x in outputs]
        self.wires = []
        self.gates = []
        self.inverters = {}                                 # input index -> inverted wire
        self.built = {}                                     # (kind, inputs) -> existing wire

    def make_name(self, name):
        """A unique, Verilog-safe identifier."""
        name = re.sub(r"\W", "_", name)
        if not name or name[0].isdigit() or name in self.KEYWORDS:
            name = "n_" + name
        while name in self.used_names:
            name += "_"
        self.used_names.add(name)
        return name

    def new_wire(self, base):
        wire = self.make_name(base)
        self.wires.append(wire)
        return wire

    def literal(self, k, positive):
        """Wire carrying input k (positive) or its complement (adds one shared NOT gate)."""
        if positive:
            return self.inputs[k]
        if k not in self.inverters:
            wire = self.new_wire(self.inputs[k] + "_n")
            self.gates.append(("not", wire, [self.inputs[k]]))
            self.inverters[k] = wire
        return self.inverters[k]

    def add_gate(self, kind, ins, out=None):
        """Add a gate, or reuse an identical one. Without `out` a new wire is created."""
        key = (kind, tuple(sorted(ins)))
        if key in self.built:
            if out is None:
                return self.built[key]
            self.gates.append(("buf", out, [self.built[key]]))   # output copies the shared gate
            return out
        if out is None:
            out = self.new_wire(f"w{len(self.wires)}")
        self.gates.append((kind, out, list(ins)))
        self.built[key] = out
        return out

    def add_output(self, j, cubes, form="sop", universal=False):
        """Build output j from a two-level cover.

        form 'sop': cubes are the product terms of f   -> AND-OR   (NAND-NAND if universal)
        form 'pos': cubes are the product terms of f'  -> OR-AND   (NOR-NOR if universal);
                    by De Morgan each cube of f' becomes one OR clause of f.
        """
        out = self.outputs[j]
        if not cubes:                                       # no terms: constant output
            self.gates.append(("buf", out, ["1'b0" if form == "sop" else "1'b1"]))
            return
        if any(Cube.literals(c) == 0 for c in cubes):       # a term covering everything
            self.gates.append(("buf", out, ["1'b1" if form == "sop" else "1'b0"]))
            return

        # Each term becomes a list of (input index, positive?) literals.
        # In POS form the polarity flips: cube bit '0' becomes the plain input in the clause.
        terms = []
        for cube in cubes:
            term = [(k, (bit == "1") == (form == "sop")) for k, bit in enumerate(cube) if bit != "-"]
            terms.append(term)

        if len(terms) == 1 and len(terms[0]) == 1:          # output is a single literal
            self.gates.append(("buf", out, [self.literal(*terms[0][0])]))
            return

        if universal:
            # NAND-NAND (SOP) or NOR-NOR (POS): both levels use the same gate type.
            # A one-literal term feeds the second level inverted instead of through a gate.
            kind = "nand" if form == "sop" else "nor"
            first_level = []
            for term in terms:
                if len(term) == 1:
                    k, positive = term[0]
                    first_level.append(self.literal(k, not positive))
                else:
                    first_level.append(self.add_gate(kind, [self.literal(k, p) for k, p in term]))
            if len(first_level) == 1:
                self.gates.append(("not", out, first_level))
            else:
                self.add_gate(kind, first_level, out)
        else:
            # AND-OR (SOP) or OR-AND (POS)
            inner, outer = ("and", "or") if form == "sop" else ("or", "and")
            first_level = []
            for term in terms:
                if len(term) == 1:
                    first_level.append(self.literal(*term[0]))
                else:
                    first_level.append(self.add_gate(inner, [self.literal(k, p) for k, p in term]))
            if len(first_level) == 1:
                self.gates.append(("buf", out, first_level))
            else:
                self.add_gate(outer, first_level, out)

    def simulate(self, m, n):
        """Output values (True/False) of the circuit when the inputs equal minterm m."""
        values = {"1'b0": False, "1'b1": True}
        for k, port in enumerate(self.inputs):
            values[port] = to_bits(m, n)[k] == "1"
        for kind, out, ins in self.gates:                   # gates are stored in signal order
            values[out] = self.LOGIC[kind]([values[i] for i in ins])
        return [values[o] for o in self.outputs]

    def metrics(self):
        """Gate count, gate inputs, CMOS transistors, logic levels and delay.

        Model (k = number of gate inputs, delay in units of one inverter delay, tau):
            NOT           2 transistors        delay 1
            NAND / NOR    2k transistors       delay 1 + 0.25(k-1)
            AND / OR      2k + 2 transistors   delay 2 + 0.25(k-1)   (NAND/NOR + inverter)
            BUF           a plain wire         delay 0
        """
        delay = {wire: 0.0 for wire in self.inputs + ["1'b0", "1'b1"]}   # arrival time per wire
        level = {wire: 0 for wire in delay}                              # gates passed per wire
        gates = gate_inputs = transistors = 0
        for kind, out, ins in self.gates:
            k = len(ins)
            if kind == "buf":
                gate_delay, gate_transistors = 0, 0
            elif kind == "not":
                gate_delay, gate_transistors = 1, 2
            elif kind in ("nand", "nor"):
                gate_delay, gate_transistors = 1 + 0.25 * (k - 1), 2 * k
            else:
                gate_delay, gate_transistors = 2 + 0.25 * (k - 1), 2 * k + 2
            if kind != "buf":
                gates += 1
                gate_inputs += k
            transistors += gate_transistors
            delay[out] = max(delay[i] for i in ins) + gate_delay
            level[out] = max(level[i] for i in ins) + (0 if kind == "buf" else 1)
        return {"gates": gates, "gate_inputs": gate_inputs, "transistors": transistors,
                "levels": max(level[o] for o in self.outputs),
                "delay": max(delay[o] for o in self.outputs)}

    def verilog(self, comments=()):
        """Structural Verilog: one primitive gate instance per line."""
        lines = [f"// {c}" for c in comments]
        lines += ["`timescale 1ns / 1ps", "", f"module {self.module} ("]
        ports = [f"    input  wire {p}" for p in self.inputs] + [f"    output wire {p}" for p in self.outputs]
        lines += [",\n".join(ports), ");", ""]
        for i in range(0, len(self.wires), 8):              # declare internal wires, 8 per line
            lines.append("    wire " + ", ".join(self.wires[i:i + 8]) + ";")
        lines.append("")
        for i, (kind, out, ins) in enumerate(self.gates):
            lines.append(f"    {kind:<4} g{i} ({out}, {', '.join(ins)});")
        lines += ["", "endmodule", ""]
        return "\n".join(lines)

    def testbench(self, functions, n):
        """Testbench that applies every input combination and checks each output."""
        name, n_out = "tb_" + self.module, len(self.outputs)
        connections = [f".{p}(x[{n - 1 - k}])" for k, p in enumerate(self.inputs)]
        connections += [f".{p}(y[{j}])" for j, p in enumerate(self.outputs)]
        lines = ["// Exhaustive self-checking testbench (generated by LSE)",
                 f"// Run: iverilog -o sim {name}.v {self.module}.v && vvp sim",
                 "`timescale 1ns / 1ps", f"module {name};",
                 f"    reg  [{n - 1}:0] x;", f"    wire [{n_out - 1}:0] y;", "    integer errors = 0;",
                 f"    {self.module} dut ({', '.join(connections)});", "",
                 "    // compare y with the expected value, ignoring don't-care bits (care = 0)",
                 f"    task check(input [{n_out - 1}:0] expected, input [{n_out - 1}:0] care);",
                 "        if (((y ^ expected) & care) !== 0) begin",
                 '            $display("MISMATCH x=%b y=%b expected=%b", x, y, expected);',
                 "            errors = errors + 1;", "        end", "    endtask", "", "    initial begin"]
        for m in range(2 ** n):
            expected = "".join("1" if m in f.on else "0" for f in reversed(functions))
            care = "".join("0" if m in f.dc else "1" for f in reversed(functions))
            lines.append(f"        x = {n}'d{m}; #1 check({n_out}'b{expected}, {n_out}'b{care});")
        lines += [f'        if (errors == 0) $display("PASS: all {2 ** n} input combinations match");',
                  '        else $display("FAIL: %0d mismatches", errors);',
                  "        $finish;", "    end", "endmodule", ""]
        return "\n".join(lines)


# ============================================================================
#  FPGA top levels
# ============================================================================
class FpgaTop:
    """Top-level Verilog that connects the generated logic to a board's switches,
    LEDs and 7-segment display. Two boards are supported:

      DE1-SoC style  (<name>_hdlboard.v)  ports SW[9:0], KEY_N, LEDR[9:0], HEX0_N..HEX5_N
      Nexys A7       (<name>_nexysa7.v)   ports SW[15:0], LED[15:0], CA..CG, DP, AN[7:0]
                                          (+ <name>_nexysa7.xdc with the pin numbers)

    Mapping on both boards: the inputs go to the switches (last input on SW[0],
    so the switch value is the minterm number) and output j lights LED j.
    If the outputs are named a..g they also drive the right-most 7-segment digit,
    so a 7-segment decoder shows the digit. The logic module is appended to the file.
    """

    # Nexys A7-100T package pins (from Digilent's master constraints file)
    NEXYS_PINS = {
        "SW": "J15 L16 M13 R15 R17 T18 U18 R13 T8 U8 R16 T13 H6 U12 U11 V10".split(),
        "LED": "H17 K15 J13 N14 R18 V17 U17 U16 V16 T15 U14 T16 V15 V14 V12 V11".split(),
        "SEG": {"CA": "T10", "CB": "R10", "CC": "K16", "CD": "K13", "CE": "P15", "CF": "T11", "CG": "L18"},
        "DP": "H15",
        "AN": "J17 J18 T9 J14 P14 T14 K2 U13".split(),
    }

    def __init__(self, netlist):
        self.netlist = netlist
        names = [name.lower() for name in netlist.output_names]
        self.seven_segment = names == list("abcdefg")       # outputs drive a 7-segment digit

    def core_instance(self, switches):
        """Instance of the logic module: input k on a switch, output j on y[j].
        Returns (instance text, description of the input mapping)."""
        nl = self.netlist
        n = len(nl.inputs)
        connections, input_map = [], []
        for k, port in enumerate(nl.inputs):
            switch = n - 1 - k                              # last input on SW[0]
            source = f"SW[{switch}]" if switch < switches else "1'b0"   # no switch left: tie to 0
            connections.append(f"        .{port}({source})")
            input_map.append(f"{nl.input_names[k]}={source}")
        for j, port in enumerate(nl.outputs):
            connections.append(f"        .{port}(y[{j}])")
        text = f"    {nl.module} core (\n" + ",\n".join(connections) + "\n    );"
        return text, ", ".join(input_map)

    def led_bus(self, width):
        """Expression for a LED bus of `width` bits: y padded with zeros (or cut to width)."""
        n_out = len(self.netlist.outputs)
        return f"y[{width - 1}:0]" if n_out >= width else f"{{{width - n_out}'b0, y}}"

    def output_map(self, led_name, width):
        return ", ".join(f"{name}={led_name}[{j}]" for j, name in enumerate(self.netlist.output_names[:width]))

    # ------------------------------------------------------------------ DE1-SoC style board
    def hdlboard_verilog(self, core_verilog):
        instance, input_map = self.core_instance(switches=10)
        hex0 = "~y[6:0]" if self.seven_segment else "7'h7F"
        hex0_note = "decoder outputs a-g drive the segments" if self.seven_segment else "off"
        return f"""// FPGA top level for the SW / LEDR / HEX board (generated by LSE)
//   inputs  -> switches  ({input_map})
//   outputs -> LEDs      ({self.output_map("LEDR", 10)})
//   HEX0    -> {hex0_note}
`timescale 1ns / 1ps

module top (
    input  wire        CLOCK_50,
    input  wire [9:0]  SW,
    input  wire [3:0]  KEY_N,
    output wire [9:0]  LEDR,
    output wire [6:0]  HEX0_N,
    output wire [6:0]  HEX1_N,
    output wire [6:0]  HEX2_N,
    output wire [6:0]  HEX3_N,
    output wire [6:0]  HEX4_N,
    output wire [6:0]  HEX5_N
);
    wire [{len(self.netlist.outputs) - 1}:0] y;   // outputs of the generated logic

{instance}

    assign LEDR   = {self.led_bus(10)};
    assign HEX0_N = {hex0};   // segments are active low (0 = on)
    assign HEX1_N = 7'h7F;     // unused displays off
    assign HEX2_N = 7'h7F;
    assign HEX3_N = 7'h7F;
    assign HEX4_N = 7'h7F;
    assign HEX5_N = 7'h7F;
    // CLOCK_50 and KEY_N are not used
endmodule

{core_verilog}"""

    # ------------------------------------------------------------------ Nexys A7
    def nexys_a7_verilog(self, core_verilog):
        instance, input_map = self.core_instance(switches=16)
        # Only the right-most digit is used, so no multiplexing (and no clock) is needed.
        # Segments CA..CG and digit enables AN are active low (0 = on).
        if self.seven_segment:
            segments = "    assign {CG, CF, CE, CD, CC, CB, CA} = ~y[6:0];   // a = CA ... g = CG"
            digits = "    assign AN = 8'b1111_1110;                         // only digit 0 on"
            note = "right-most digit, segments a-g driven by the outputs"
        else:
            segments = "    assign {CG, CF, CE, CD, CC, CB, CA} = 7'h7F;     // segments off"
            digits = "    assign AN = 8'hFF;                                // all digits off"
            note = "off"
        return f"""// FPGA top level for the Digilent Nexys A7 (generated by LSE)
// Use together with the matching .xdc file (pin numbers).
//   inputs  -> switches  ({input_map})
//   outputs -> LEDs      ({self.output_map("LED", 16)})
//   7-seg   -> {note}
`timescale 1ns / 1ps

module top (
    input  wire [15:0] SW,
    output wire [15:0] LED,
    output wire        CA, CB, CC, CD, CE, CF, CG,   // segment cathodes, active low
    output wire        DP,                           // decimal point, active low
    output wire [7:0]  AN                            // digit enables, active low
);
    wire [{len(self.netlist.outputs) - 1}:0] y;   // outputs of the generated logic

{instance}

    assign LED = {self.led_bus(16)};
{segments}
{digits}
    assign DP = 1'b1;                                  // decimal point off
endmodule

{core_verilog}"""

    def nexys_a7_xdc(self):
        """Pin constraints for the Nexys A7 top level."""
        pins = self.NEXYS_PINS
        ports = [(f"SW[{i}]", pin) for i, pin in enumerate(pins["SW"])]
        ports += [(f"LED[{i}]", pin) for i, pin in enumerate(pins["LED"])]
        ports += list(pins["SEG"].items()) + [("DP", pins["DP"])]
        ports += [(f"AN[{i}]", pin) for i, pin in enumerate(pins["AN"])]
        lines = ["## Nexys A7-100T pin constraints (generated by LSE)",
                 "## SW[8] and SW[9] are on a 1.8 V bank, everything else is 3.3 V"]
        for port, pin in ports:
            standard = "LVCMOS18" if port in ("SW[8]", "SW[9]") else "LVCMOS33"
            lines.append(f"set_property -dict {{ PACKAGE_PIN {pin} IOSTANDARD {standard} }} [get_ports {{{port}}}]")
        lines += ["set_property CFGBVS VCCO [current_design]",
                  "set_property CONFIG_VOLTAGE 3.3 [current_design]"]
        return "\n".join(lines) + "\n"


# ============================================================================
#  The engine: operations 1-12
# ============================================================================
class LogicEngine:
    """Runs the 12 operations on a Design and returns the results as text."""

    # number, short name, method name, description
    OPERATIONS = [
        ("1", "csop", "canonical_sop", "Canonical SOP"),
        ("2", "cpos", "canonical_pos", "Canonical POS"),
        ("3", "icsop", "inverse_canonical_sop", "Canonical SOP of the inverse F'"),
        ("4", "icpos", "inverse_canonical_pos", "Canonical POS of the inverse F'"),
        ("5", "minsop", "minimized_sop", "Literal-minimized SOP and literals saved"),
        ("6", "minpos", "minimized_pos", "Literal-minimized POS and literals saved"),
        ("7", "pi", "prime_implicants", "Number of prime implicants"),
        ("8", "epi", "essential_prime_implicants", "Number of essential prime implicants"),
        ("9", "on", "on_set_minterms", "Number of ON-set minterms"),
        ("10", "off", "off_set_maxterms", "Number of OFF-set maxterms"),
        ("11", "hazard", "hazards", "Custom 1: static hazard detection and hazard-free covers"),
        ("12", "cost", "cost_and_delay", "Custom 2: gate/transistor cost and delay of implementations"),
    ]

    def __init__(self, design, outdir="build"):
        self.design = design
        self.outdir = outdir
        self.inputs = design.inputs
        self.n = len(design.inputs)
        self.selected = None             # name of the only output to report (None = all)
        self.minimizers = {}             # cache: (output name, inverse?) -> Minimizer
        # single-letter names can be written next to each other (AB); longer ones need '*'
        self.and_symbol = "" if all(len(x) == 1 for x in self.inputs) else "*"

    def run(self, command):
        """Run an operation given by number (5) or short name (minsop)."""
        command = command.strip().lower()
        for number, short, method, _ in self.OPERATIONS:
            if command in (number, short, method):
                return getattr(self, method)()
        if command == "all":
            return self.run_all()
        if command == "info":
            return self.info()
        return f"Unknown command '{command}'. Use 1-12, all or info."

    def run_all(self):
        results = [self.info()] + [getattr(self, op[2])() for op in self.OPERATIONS]
        return ("\n" + "-" * 72 + "\n").join(results)

    # ------------------------------------------------------------------ helpers
    def functions(self):
        """The outputs to report on (all, or only the one chosen with --output)."""
        return [f for f in self.design.functions if self.selected in (None, f.name)]

    def minimize(self, f, inverse=False):
        """Minimizer of f, or of f' when inverse=True (used for the POS forms)."""
        key = (f.name, inverse)
        if key not in self.minimizers:
            self.minimizers[key] = Minimizer(self.n, f.off if inverse else f.on, f.dc)
        return self.minimizers[key]

    def product(self, cube):
        """Product term as text, e.g. '1-0' -> AC'."""
        literals = [name + ("" if bit == "1" else "'")
                    for name, bit in zip(self.inputs, cube) if bit != "-"]
        return self.and_symbol.join(literals) or "1"

    def clause(self, cube):
        """OR clause that is the complement of a cube (De Morgan), e.g. '1-0' -> (A' + C)."""
        literals = [name + ("'" if bit == "1" else "")
                    for name, bit in zip(self.inputs, cube) if bit != "-"]
        if not literals:
            return "0"
        return literals[0] if len(literals) == 1 else "(" + " + ".join(literals) + ")"

    def sop(self, cubes):
        """Sum of products, e.g. AC + A'B."""
        return " + ".join(self.product(c) for c in cubes) or "0"

    def pos(self, cubes_of_inverse):
        """Product of sums of f, built from the cubes of f'."""
        clauses = [self.clause(c) for c in cubes_of_inverse]
        if "0" in clauses:
            return "0"
        separator = " * " if self.and_symbol else ""
        return separator.join(clauses) or "1"

    def header(self, number, title, f):
        return f"[{number}] {title} -- {f.name}({', '.join(self.inputs)})"

    @staticmethod
    def numbers(values):
        return ", ".join(str(v) for v in sorted(values))

    def dont_care_text(self, f):
        return f" + d({self.numbers(f.dc)})" if f.dc else ""

    def prime_lines(self, primes):
        return [f"    {p}   {self.product(p):<24} ({Cube.literals(p)} literals)" for p in primes]

    # ------------------------------------------------------------------ operations 1-4
    def canonical(self, number, title, f, terms, form, inverse):
        """Canonical SOP (sum of minterms) or POS (product of maxterms)."""
        name = f.name + ("'" if inverse else "")
        terms = sorted(terms)
        if form == "sop":
            listing = f"Σm({self.numbers(terms)})"
            expression = " + ".join(self.product(to_bits(m, self.n)) for m in terms) or "0"
            kind = "minterms"
        else:
            listing = f"ΠM({self.numbers(terms)})"
            separator = " * " if self.and_symbol else ""
            expression = separator.join(self.clause(to_bits(m, self.n)) for m in terms) or "1"
            kind = "maxterms"
        return "\n".join([self.header(number, title, f),
                          f"  {name} = {listing}{self.dont_care_text(f)}",
                          f"  {name} = {expression}",
                          f"  {kind}: {len(terms)}   literals: {len(terms) * self.n}", ""])

    def canonical_sop(self):
        # f = sum of the minterms where f is 1
        return "\n".join(self.canonical(1, "Canonical SOP", f, f.on, "sop", False) for f in self.functions())

    def canonical_pos(self):
        # f = product of the maxterms where f is 0
        return "\n".join(self.canonical(2, "Canonical POS", f, f.off, "pos", False) for f in self.functions())

    def inverse_canonical_sop(self):
        # f' is 1 exactly where f is 0
        return "\n".join(self.canonical(3, "Inverse canonical SOP", f, f.off, "sop", True)
                         for f in self.functions())

    def inverse_canonical_pos(self):
        # f' is 0 exactly where f is 1
        return "\n".join(self.canonical(4, "Inverse canonical POS", f, f.on, "pos", True)
                         for f in self.functions())

    # ------------------------------------------------------------------ operations 5-6
    def minimized(self, number, f, inverse):
        """Minimized SOP (from f) or POS (from f', then De Morgan) and literals saved."""
        result = self.minimize(f, inverse)
        canonical_literals = len(f.off if inverse else f.on) * self.n
        saved = canonical_literals - result.literals
        percent = 100 * saved / canonical_literals if canonical_literals else 0
        form, unit = ("POS", "clauses") if inverse else ("SOP", "terms")
        expression = self.pos(result.cover) if inverse else self.sop(result.cover)
        lines = [self.header(number, f"Literal-minimized {form}", f),
                 f"  {f.name} = {expression}",
                 f"  {unit}: {len(result.cover)}   literals: {result.literals}"
                 + ("" if result.exact else "   (search stopped early: may not be minimal)"),
                 f"  canonical {form} literals: {canonical_literals}  ->  "
                 f"saved {saved} literals ({percent:.1f}%)"]
        if inverse:
            lines.append(f"  (from minimizing {f.name}' = {self.sop(result.cover)} and applying De Morgan)")
        return "\n".join(lines + [""])

    def minimized_sop(self):
        return "\n".join(self.minimized(5, f, False) for f in self.functions())

    def minimized_pos(self):
        return "\n".join(self.minimized(6, f, True) for f in self.functions())

    # ------------------------------------------------------------------ operations 7-10
    def prime_implicants(self):
        blocks = []
        for f in self.functions():
            primes = self.minimize(f).primes
            blocks.append("\n".join([self.header(7, "Prime implicants", f),
                                     f"  Number of prime implicants: {len(primes)}"]
                                    + self.prime_lines(primes) + [""]))
        return "\n".join(blocks)

    def essential_prime_implicants(self):
        blocks = []
        for f in self.functions():
            result = self.minimize(f)
            others = len(result.cover) - len(result.essentials)
            blocks.append("\n".join([self.header(8, "Essential prime implicants", f),
                                     f"  Number of essential prime implicants: {len(result.essentials)}"]
                                    + self.prime_lines(result.essentials)
                                    + [f"  minimum cover = {len(result.essentials)} essential + "
                                       f"{others} other prime(s)", ""]))
        return "\n".join(blocks)

    def on_set_minterms(self):
        return "\n".join("\n".join([
            self.header(9, "ON-set minterms", f),
            f"  Number of ON-set minterms: {len(f.on)}   (of {2 ** self.n}; don't-cares: {len(f.dc)})",
            f"  Σm({self.numbers(f.on)})", ""]) for f in self.functions())

    def off_set_maxterms(self):
        return "\n".join("\n".join([
            self.header(10, "OFF-set maxterms", f),
            f"  Number of OFF-set maxterms: {len(f.off)}   (of {2 ** self.n}; don't-cares: {len(f.dc)})",
            f"  ΠM({self.numbers(f.off)})", ""]) for f in self.functions())

    # ------------------------------------------------------------------ operation 11
    def hazard_free_cover(self, f, inverse=False):
        result = self.minimize(f, inverse)
        return HazardAnalyzer.fix(self.n, f.off if inverse else f.on, result.cover, result.primes)

    def describe_hazard(self, m1, m2, k):
        others = [f"{name}={bit}" for i, (name, bit) in enumerate(zip(self.inputs, to_bits(m1, self.n)))
                  if i != k]
        return (f"    m{m1} ({to_bits(m1, self.n)}) <-> m{m2} ({to_bits(m2, self.n)}): "
                f"{self.inputs[k]} toggles with {', '.join(others) or '-'}")

    def hazards(self):
        blocks = []
        for f in self.functions():
            lines = [self.header(11, "Static hazard analysis (custom #1)", f)]
            # SOP side uses the ON set (static-1), POS side the OFF set (static-0)
            for inverse in (False, True):
                result = self.minimize(f, inverse)
                show = self.pos if inverse else self.sop
                form, kind, circuit = ("POS", "0", "OR-AND") if inverse else ("SOP", "1", "AND-OR")
                found = HazardAnalyzer.find(self.n, f.off if inverse else f.on, result.cover)
                lines.append(f"  Minimized {form}: {f.name} = {show(result.cover)}")
                lines.append(f"  Static-{kind} hazards in {circuit} realization: {len(found)}")
                lines += [self.describe_hazard(*h) for h in found]
                if found:
                    fixed = self.hazard_free_cover(f, inverse)
                    extra = sum(Cube.literals(c) for c in fixed) - result.literals
                    lines.append(f"  Hazard-free {form}: {f.name} = {show(fixed)}")
                    lines.append(f"    (+{len(fixed) - len(result.cover)} consensus term(s), "
                                 f"+{extra} literals)")
            blocks.append("\n".join(lines + [""]))
        return "\n".join(blocks)

    # ------------------------------------------------------------------ operation 12
    def build_netlist(self, kind, universal=False, functions=None):
        """Gate netlist for all outputs. kind: 'canonical', 'sop', 'pos' or 'hazard_free'."""
        functions = functions or self.design.functions
        netlist = Netlist(self.design.name, self.inputs, [f.name for f in functions])
        for j, f in enumerate(functions):
            if kind == "canonical":
                netlist.add_output(j, [to_bits(m, self.n) for m in sorted(f.on)], "sop", universal)
            elif kind == "hazard_free":
                netlist.add_output(j, self.hazard_free_cover(f), "sop", universal)
            elif kind == "pos":
                netlist.add_output(j, self.minimize(f, True).cover, "pos", universal)
            else:
                netlist.add_output(j, self.minimize(f).cover, "sop", universal)
        return netlist

    def cost_and_delay(self):
        functions = self.functions()
        implementations = [("Canonical SOP   AND-OR", "canonical", False),
                           ("Minimized SOP   AND-OR", "sop", False),
                           ("Minimized SOP   NAND-NAND", "sop", True),
                           ("Minimized POS   OR-AND", "pos", False),
                           ("Minimized POS   NOR-NOR", "pos", True),
                           ("Hazard-free SOP AND-OR", "hazard_free", False)]
        rows = []
        for label, kind, universal in implementations:
            rows.append((label, self.build_netlist(kind, universal, functions).metrics()))

        lines = [f"[12] Implementation cost & delay (custom #2) -- outputs: "
                 f"{', '.join(f.name for f in functions)}",
                 "  Transistors: NOT = 2, k-input NAND/NOR = 2k, AND/OR = 2k + 2",
                 "  Delay in inverter delays (tau): NOT = 1, NAND/NOR = 1 + 0.25(k-1), AND/OR = NAND/NOR + 1",
                 "",
                 f"  {'Implementation':<27}{'gates':>6}{'inputs':>8}{'transistors':>13}{'levels':>8}{'delay':>8}",
                 "  " + "-" * 70]
        for label, m in rows:
            lines.append(f"  {label:<27}{m['gates']:>6}{m['gate_inputs']:>8}{m['transistors']:>13}"
                         f"{m['levels']:>8}{m['delay']:>8.2f}")
        smallest = min(rows, key=lambda row: (row[1]["transistors"], row[1]["delay"]))[0]
        fastest = min(rows, key=lambda row: (row[1]["delay"], row[1]["transistors"]))[0]
        lines += ["", f"  Smallest: {' '.join(smallest.split())}   Fastest: {' '.join(fastest.split())}", ""]
        return "\n".join(lines)

    # ------------------------------------------------------------------ other output
    def info(self):
        lines = [f"Design '{self.design.name}'",
                 f"  inputs  ({self.n}): {' '.join(self.inputs)}",
                 f"  outputs ({len(self.design.functions)}): {' '.join(f.name for f in self.design.functions)}"]
        for f in self.design.functions:
            lines.append(f"    {f.name}: ON={len(f.on)} OFF={len(f.off)} DC={len(f.dc)}")
        return "\n".join(lines)

    def check_netlist(self, netlist):
        """True if the circuit gives the right output for every minterm that is not a don't-care."""
        for m in range(2 ** self.n):
            outputs = netlist.simulate(m, self.n)
            for f, value in zip(self.design.functions, outputs):
                if m not in f.dc and value != (m in f.on):
                    return False
        return True

    def verilog_comments(self, netlist, form, universal):
        style = {("sop", False): "AND-OR", ("sop", True): "NAND-NAND",
                 ("pos", False): "OR-AND", ("pos", True): "NOR-NOR"}[(form, universal)]
        m = netlist.metrics()
        comments = ["Structural Verilog generated by LSE (Logic Synthesis Engine)",
                    f"Design: {self.design.name}   inputs: {' '.join(self.inputs)}   style: {style}"]
        for f in self.design.functions:
            expression = self.sop(self.minimize(f).cover) if form == "sop" else self.pos(self.minimize(f, True).cover)
            comments.append(f"  {f.name} = {expression}")
        comments.append(f"Gates: {m['gates']}  transistors: {m['transistors']}  "
                        f"levels: {m['levels']}  delay: {m['delay']:.2f} tau")
        return comments, style

    def write_verilog(self, form="sop", universal=False):
        """Write <module>.v (and a testbench for up to 12 inputs)."""
        netlist = self.build_netlist(form, universal)
        comments, style = self.verilog_comments(netlist, form, universal)
        os.makedirs(self.outdir, exist_ok=True)
        path = os.path.join(self.outdir, netlist.module + ".v")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(netlist.verilog(comments))
        lines = [f"Structural Verilog written to {path}",
                 f"  module {netlist.module}: {netlist.metrics()['gates']} gates ({style})",
                 f"  circuit check against the truth table: {'PASS' if self.check_netlist(netlist) else 'FAIL'}"]
        if self.n <= 12:
            tb_path = os.path.join(self.outdir, f"tb_{netlist.module}.v")
            with open(tb_path, "w", encoding="utf-8") as fh:
                fh.write(netlist.testbench(self.design.functions, self.n))
            lines.append(f"  testbench written to {tb_path}")
        return "\n".join(lines)

    def write_fpga_files(self, form="sop", universal=False):
        """Write the FPGA files:
            <name>.v            the generated logic module on its own
            <name>_hdlboard.v   'top' for the SW/LEDR/HEX (DE1-SoC style) board + logic module
            <name>_nexysa7.v    'top' for the Nexys A7 board + logic module
            <name>_nexysa7.xdc  Nexys A7 pin constraints
        """
        netlist = self.build_netlist(form, universal)
        comments, _ = self.verilog_comments(netlist, form, universal)
        logic_verilog = netlist.verilog(comments)
        board = FpgaTop(netlist)
        files = [
            (netlist.module + ".v", logic_verilog, "logic module"),
            (netlist.module + "_hdlboard.v", board.hdlboard_verilog(logic_verilog), "SW/LEDR/HEX board top level"),
            (netlist.module + "_nexysa7.v", board.nexys_a7_verilog(logic_verilog), "Nexys A7 top level"),
            (netlist.module + "_nexysa7.xdc", board.nexys_a7_xdc(), "Nexys A7 pin constraints"),
        ]
        os.makedirs(self.outdir, exist_ok=True)
        lines = []
        for filename, text, description in files:
            path = os.path.join(self.outdir, filename)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(text)
            lines.append(f"{description:<28} written to {path}")
        mapping = [f"{x} = SW[{self.n - 1 - k}]" for k, x in enumerate(self.inputs)]
        mapping += [f"{f.name} = LED {j}" for j, f in enumerate(self.design.functions)]
        lines.append("  " + ", ".join(mapping))
        return "\n".join(lines)


# ============================================================================
#  Command line
# ============================================================================
def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="lse", description="LSE - Logic Synthesis Engine",
        epilog="operations: " + ", ".join(f"{num}={short}" for num, short, _, _ in LogicEngine.OPERATIONS))
    parser.add_argument("input", nargs="?", help="input file (.pla or .eqn)")
    parser.add_argument("-e", "--expr", action="append", help="equation on the command line (repeatable)")
    parser.add_argument("-a", "--all", action="store_true", help="run operations 1-12")
    parser.add_argument("-c", "--commands", help='operations to run, e.g. "1;5;9"')
    parser.add_argument("--output", help="report only this output, e.g. --output a")
    parser.add_argument("--verilog", action="store_true", help="write structural Verilog and a testbench")
    parser.add_argument("--fpga", action="store_true", help="write <name>.v, <name>_hdlboard.v, <name>_nexysa7.v and <name>_nexysa7.xdc")
    parser.add_argument("--form", choices=["sop", "pos"], default="sop", help="two-level form for Verilog")
    parser.add_argument("--style", choices=["andor", "universal"], default="andor",
                        help="andor = AND-OR / OR-AND, universal = NAND-NAND / NOR-NOR")
    parser.add_argument("--outdir", default="build", help="folder for generated files (default: build)")
    parser.add_argument("-o", "--report", help="also save the text results to this file")
    args = parser.parse_args(argv)

    if hasattr(sys.stdout, "reconfigure"):              # allow Σ and Π on Windows consoles
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    # 1. read the input
    try:
        if args.input:
            design = Parser.load_file(args.input)
        elif args.expr:
            design = Parser.parse_equations("\n".join(args.expr), "expr")
        else:
            parser.error("give an input file or an equation with -e")
    except (OSError, ParseError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    engine = LogicEngine(design, args.outdir)
    if args.output:
        if args.output not in [f.name for f in design.functions]:
            print(f"error: no output named '{args.output}'", file=sys.stderr)
            return 1
        engine.selected = args.output

    # 2. run the requested operations (all of them if nothing was requested)
    results = []
    commands = [c for c in (args.commands or "").split(";") if c.strip()]
    if args.all or not (commands or args.verilog or args.fpga):
        results.append(engine.run_all())
    for command in commands:
        results.append(engine.run(command))

    # 3. write the generated files
    universal = args.style == "universal"
    if args.verilog:
        results.append(engine.write_verilog(args.form, universal))
    if args.fpga:
        results.append(engine.write_fpga_files(args.form, universal))

    text = "\n".join(results)
    print(text)
    if args.report:
        with open(args.report, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
        print(f"Report written to {args.report}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
