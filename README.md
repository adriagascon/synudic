# Synudic 0.1

SYNUDIC is a tool for synthesis of small loop-free programs.

The user provides a sketch of the desired program in an input file
(with extension .sketch).  The tool uses an SMT solver (Yices or Z3)
to generate a program meeting the specification in file.sketch.


INSTALLATION:

1. Install Yices2 (and optionally Z3, if you want to use Z3 as the backend).
(yices.csl.sri.com)

2. Synudic requires python 2.7.x. Requeriments regarding python packages can be found at src/requeriments.txt, and installed in your python instance or virtualenv with pip as `pip install -r requeriments.txt`


USING SYNUDIC:

1. Create a sketch
   For example, see files in directory examples/
   For example, see average.sketch and oeap.sketch

2. Run the program thus:
   `python src/main.py examples/oeap.sketch na=4 nb=2`

DETAILS:

Synudic works by converting the input <filename.sketch> into a
 (EF-)Yices formula (stored as synth.ys), or just an exists SMT
 formula (if there are no primal interpretations in filename.sketch).
 It then invokes Yices on synth.ys
 Output is stored in synth.yout; and the model is generated in tmp.txt.
 These files are generated in the current working directory.
 
We are currently updating the Synudic frontend language for the next version. 

