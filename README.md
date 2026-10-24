# EC551 Programming HW 1 
## Contact Name: Francis Liri
## Partner Name: Tanner Armstard

# LSE — Logic Synthesis Engine (Python, single file)

`lse.py` reads a Boolean function via and input file or command line, then minimizes and analyzes it using a maximum of 12 operations listed below.
The code then  writes **structural Verilog** (primitive gates only) with a self-checking testbench. The code also writes 2 sets of  **FPGA files** . The first file (xxx_hdlboard.v) runs on the HDLBoard an online FPGA simulator (https://hdlboard.onrender.com/) using their Terasic DE1-SoC FPGA board.  The next set of files (xxx_nexysa7.v) run on the **Diligent Nexys A7** FPGA board  and includes the verilog file and a xxx_nexysa7.xdc file with the pin constraints.

The code has been tested with two examples, a 7 segment display and a full adder and the input files for these are in the examples folder,

## Software requirements
Python 3.8+, no packages to install.

## Running the code
#### NAME
       lse.py - logic synthesis engine for two-level Boolean functions

#### SYNOPSIS
       python lse.py [OPTION]... FILE
       python lse.py [OPTION]... -e EQUATION [-e EQUATION]...

#### DESCRIPTION
       lse.py reads a Boolean function or combinational circuit from FILE or
       from the command line. It reports canonical and minimized SOP/POS
       forms, prime implicants, minterm/maxterm counts, static hazards and
       implementation cost, and can write structural Verilog and FPGA
       top-level files.

       FILE is either an Espresso PLA file (.pla) or an equation file
       (.eqn). Equations may be in SOP, POS or multi-level form, or given as
       minterm/maxterm lists, e.g. F(A,B,C) = m(1,3,5) + d(7).

       If no operation and no file output is requested, all operations
       (1-12) are run.

#### OPTIONS
       -e, --expr EQUATION
              Read the function from EQUATION instead of a file. May be
              repeated to give several equations. Equations can be one per line or separated by `;`.
              Examples of equations are below
              ```
              F = A'B + AC                     sum of products
              F = (A + B')(C + D)              product of sums
              F(A,B,C) = m(1,3,5) + d(7)       minterms with don't-cares
              F(A,B,C) = M(0,2)                maxterms
              INORDER = a b cin; OUTORDER = sum cout;
              p = a ^ b; sum = p ^ cin; cout = a*b + p*cin;
              ```

              The last form is a multi-level circuit: each equation is a gate (node) and each signal
              name is a wire (edge) — see `examples/full_adder.eqn`.
              Operators: NOT `'` `~` `!` · AND `*` `&` or `AB` · XOR `^` · OR `+` `|`.
              Without a `*` or `&` anywhere, `AB` is read as `A AND B`.

       -a, --all
              Run operations 1-12.

       -c, --commands LIST
              Run the operations in LIST, separated by ';'. Each entry is a
              number or short name:
                no  short name  description
                 1  csop     canonical SOP
                 2  cpos     canonical POS
                 3  icsop    canonical SOP of the inverse
                 4  icpos    canonical POS of the inverse
                 5  minsop   minimized SOP and literals saved
                 6  minpos   minimized POS and literals saved
                 7  pi       number of prime implicants
                 8  epi      number of essential prime implicants
                 9  on       number of ON-set minterms
                 10 off      number of OFF-set maxterms
                 11 hazard   static hazard detection
                 12 cost     gate, transistor and delay estimation
              info prints a summary of the design; all runs 1-12.

       --output NAME
              Report only the output called NAME.

       --verilog
              Write the structural Verilog module to build/NAME.v and, for designs
              with up to 12 inputs, the exhaustive testbench tb_NAME.v. The NAME.v file has only
              `and/or/nand/nor/not/buf` gates  and the testbench tries every input combination.
              For example for a bcd7seg example  `iverilog -o sim build/tb_bcd7seg.v build/bcd7seg.v && vvp sim`

       --fpga Write the four FPGA files to the build folder:
                 NAME.v             logic module only (same as `--verilog`) to instantiate in the top level.
                 NAME_hdlboard.v    top for HDLBoard (DE1-SoC) board followed by the logic module
                 NAME_nexysa7.v     top for the Digilent Nexys A7 module  followed by the logic module. 
                 NAME_nexysa7.xdc   Nexys A7 pin constraints

       --form sop|pos
              Two-level form used for generated Verilog. Default: sop.

       --style andor|universal
              Gate style: andor gives AND-OR or OR-AND; universal gives
              NAND-NAND or NOR-NOR. Default: andor.

       --outdir DIR
              Write generated files to DIR. Default: build.

       -o, --report FILE
              Also save the text results to FILE.

       -h, --help
              Display a help message and exit.

#### EXIT STATUS
       0      Success.
       1      The input could not be read or parsed, or --output named an
              output that does not exist.
       2      Invalid command-line arguments.

#### EXAMPLES
       python lse.py examples/bcd7seg.pla -a
              Run all twelve operations on the BCD-to-7-segment decoder.

       python lse.py examples/full_adder.eqn -c "1;5;9"
              Print the canonical SOP, minimized SOP and ON-set count.

       python lse.py -e "F = A'B + AC" -c "minsop;hazard"
              Minimize an equation typed on the command line and check it
              for hazards.

       python lse.py examples/bcd7seg.pla --output a -a -o seg_a.txt
              Report only segment a and save the results to seg_a.txt.

       python lse.py examples/bcd7seg.pla --fpga --style universal
              Write NAND-NAND Verilog and the FPGA files to build/.

        python lse.py examples/bcd7seg.pla --verilog --fpga    
             Write verilog, testbench and FPGA files and save them in build/

        python lse.py examples/bcd7seg.pla -a -o report.txt    
            Run all operations and save the results to a file


## Code structure (`lse.py`)
The main classes in the code are described below
| Class | Role |
|---|---|
| `Cube` | Helpers for product terms written as strings like `1-0` (= A C') |
| `BoolFunction`, `Design` | A function as sets of ON, don't-care and OFF minterms |
| `ExprParser`, `Parser` | Read equations and PLA files |
| `Minimizer` | Quine-McCluskey primes, essential primes, minimum-literal cover |
| `HazardAnalyzer` | Hazard detection and hazard-free covers |
| `Netlist` | Gate circuit: simulation, cost/delay, Verilog, testbench |
| `FpgaTop` | Board top levels (`<name>_hdlboard.v`, `<name>_nexysa7.v`) and the Nexys A7 `.xdc` |
| `LogicEngine` | The 12 operations |

`main()` handles the command line.

## Tests

```
python -m unittest discover -s tests -v
```
## AI Usage: 
AI tools, including Claude, Gemini and ChatGPT, were used to generate and test parts of this code, make it more efficient and concise, and improve its documentation.

