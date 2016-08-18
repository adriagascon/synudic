from solver import YicesSolver, Z3Solver
from parser import Sketch
import re
import argparse
import os

if __name__ == "__main__":  # {{{
    parser = argparse.ArgumentParser(description='Synudic SLP synthesizer')
    parser.add_argument('input_file', help='Input sketch file')
    parser.add_argument('parameters', nargs='+',
        help='Parameters list, e.g. p1=1 p2=2 p3=3')
    parser.add_argument('--all_solutions',
        help='Enumerates all solutions to the sketch. Requires Z3. '
        'Only available in the adsence of primal interpretations.',
        action='store_true')
    parser.add_argument('--solver',
        help='Sets solver from {yices, z3}, default is yices.',
        default='yices')
    parser.add_argument('--max_iters_yices',
        help='Sets maximum number of iterations for yices solver, '
            'default is 20000.', type=int, default=20000)
    parser.add_argument('--verbosity', '-v',
        help='Sets the verbosity level, default is 0', type=int, default=0)

    args = parser.parse_args()

    # Check that provided non-optional files actually exist
    for f in [args.input_file]:
        assert os.path.isfile(f), 'File {0} does not exist'.format(f)

    parameters_dict = {}
    for a in args.parameters:
        m = re.match('(\S+)=([0-9]+)', a)
        assert m, 'Wrong format in parameters, ' +\
        'it should be a list os strings matching \'\S+=[0-9]+\', ' +\
        'e.g. p1=1 p2=2 p3=3. Found {0}'.format(a)
        parameters_dict[m.group(1)] = int(m.group(2))

    if args.solver == 'z3' or args.all_solutions:
        solver = Z3Solver(args.all_solutions)
    else:
        solver = YicesSolver(args.verbosity, args.max_iters_yices)
    solver.parse_input(args.input_file, parameters_dict,
        args.solver, args.all_solutions)
    size = solver.get_estimated_search_space_size()
    print 'SEARCH SPACE SIZE ~ {0}'.format(size)
    solver.solve()
