
"""
    =======
    `Parser`
    =======

    This module contains a pyparsing bnf for
    synudic.

    Adria Gascon, 2016.
"""

from pyparsing import Keyword, Literal, OneOrMore, ZeroOrMore, \
    Optional, Suppress, Word, alphanums, nums, restOfLine
import sexpParser
import logging
import sys
import itertools
import copy
from constants import *
from utils import *
from yices_to_z3 import expand_forall_def

logging.basicConfig(level=logging.INFO)
log = logging.getLogger(__name__)

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class Sketch:
    """
    A synudic sketch

    * Attributes:
        * name
        * blocks
        * signature
        * parameters
        * interps
        * existsforall
        * parameters_dict
        * solver
        * enum_all_solutions

    """
    def __init__(self):
        self.blocks = []
        self.signature = None
        self.interps = []
        self.existsforall = None
        self.name = None
        self.parameters = None
        self.parameters_dict = None
        self.solver = None
        self.enum_all_solutions = None

    def __str__(self):
        return self.name

    def parse_input(self, filename, parameters_dict,
            solver, enum_all_solutions):
        """
        Parses the sketch in [filename] into this sketch instance
        """
        bnf(self)['sketch'].parseFile(filename, True)
        self.parameters_dict = parameters_dict
        formals = set(self.parameters)
        actuals = set(self.parameters_dict.keys())
        assert formals == actuals, 'Declared parameters must match those ' +\
            'provided on the command line: {0} != {1}'.format(formals, actuals)
        # Instantiate every block with specific parameters
        for i, b in enumerate(self.blocks):
            b.instantiate(
                self.parameters_dict, self.signature, self.blocks[:i])
            # We replace function names by function instances in
            # fucntion constraints
            for c in b.constraints:
                if b.is_input:
                    continue
                c.function =\
                    self.signature.function_name2function_symbol[c.function]
        for i in self.interps:
            i.instantiate(
                self.blocks, self.signature, self.parameters_dict)

    def make_sketch_from_parser(self, t):
        self.signature = t['signature'][0]
        self.parameters = t['parameters_list']
        self.name = t['sketch_name']
        self.blocks = t['blocks']
        self.interps = t['interps']
        self.existsforall = any(map(lambda x: x.is_primal, self.interps))
        logger.debug('Parsing sketch {0}'.format(self.name))
        logger.debug('\tExistsForall = {0}'.format(self.existsforall))
        logger.debug('\tBlocks = {0}'.format(self.blocks))
        logger.debug('\tInterpretation names = {0}'.format(
            map(lambda x: x.name, self.interps)))

    def make_interp_from_parser(self, t):
        is_global = 'is_global' in t.asDict().keys()
        is_parametric = 'is_parametric' in t.asDict().keys()
        is_primal = t['type'] == 'primal'
        name = t['interpretation_name']
        decls = t['decls'].asList()
        decls = expand_forall_def(decls)
        try:
            ensure = t['ensure'].asList()
        except KeyError:
            ensure = []
        logger.debug('Parsing interpretation {0}'.format(name))
        logger.debug('\tdecls = {0}'.format(decls))
        logger.debug('\tensure = {0}'.format(ensure))
        return [Interp(is_primal, name, is_parametric,
            is_global, decls, ensure)]

    def make_signature_from_parser(self, t):
        return [Signature(t['function_list'])]

    def make_function_symbol_from_parser(self, t):
        try:
            is_ac = t['is_ac']
            assert is_ac == 'ac'
            return [FunctionSymbol(t['function_name'], int(t['arity']), True)]
        except KeyError:
            return [FunctionSymbol(t['function_name'], int(t['arity']), False)]

    def make_block_from_parser(self, t):
        length = t['length']  # might be a parameter
        name = t['block_name']
        constraints = t['line_constraints']
        return [BlockDecl(name, length, constraints)]

    def make_block_list_from_parser(self, t):
        return t['block_decls']

    def make_function_constraint_from_parser(self, t):
        name = t['function_name']
        try:
            param_constraint = t['parameters_constraints']
        except KeyError:
            param_constraint = []
        return FunctionConstraint(name, param_constraint)

class FunctionSymbol:# {{{
    """
    The Signature in a synudic sketch

    * Attributes:
        * name
        * arity
        * is_ac (associative, commutative)
        * interp_decl
        * interp_names
    """
    def __init__(self, name, arity, is_ac = False):
        self.name = name
        self.arity = arity
        self.is_ac = is_ac
        self.interp_decl = {}
        self.interp_names = {}

    def get_input_filter(self):
        """
        :returns:
        A function that takes a set of input arguments and returns a
        filtered list with equivalent inputs removed.
        This function is used to avoid
        considering equivalent possibilities
        for commutative operations.
        """
        def id(l):
            return l
        def filter_commutative(l):

            if len(l) == 0: return l
            if len(l[0]) == 2:
                redundant = filter(lambda (x,y): (y,x) in l and y < x, l)
                return filter(lambda x:not x in redundant, l)
            return l
        if self.is_ac:
            return filter_commutative
        else:
            return id

    def set_interp_decl(self, interp_name, func_interp_name):
        self.interp_names[interp_name] = func_interp_name

    def get_interp_name(self, interp_name):
        return self.interp_names[interp_name]


class Interp:
    """
    A primal or dual interpretation

    * Attributes:
        * type_decls
        * self
        * primal
        * params
        * signature # global signature
        * type_decls
        * aux_fun_decls
        * ensure_expr
        * block_constraints
    """

    def __init__(self, is_primal, name, is_parametric,
            is_global, decls, ensure=[]):
        self.is_primal = is_primal
        self.name = name
        self.is_parametric = is_parametric
        self.is_global = is_global
        self.decls = decls
        self.ensure_expr = ensure

    def instantiate(self, blocks, signature, params_dict):
        self.params_dict = params_dict
        self.signature = signature
        type_decls = []
        fun_decls = []
        fun_decls_names = []
        aux_fun_decls = []
        for d in self.decls:
            if d[0] == 'define-type':
                type_decls.append(expr2str(d))
            elif d[0] == 'define':
                fname = re.match('[^:\s]*', d[1]).group()
                if isinstance(d[2], str) and re.match('^[\s:]+$', d[2]): # parser separates colons from words
                    d.pop(2)                                             # adjust for that
                if fname in self.signature.get_function_names():
                    # name mangle this function
                    fname_mod = "{0}-{1}".format(self.name, fname)
                    d[1] = fname_mod + " ::"
                    # then we'll have to customize internal function names for this interpretation
                    def rec(expr):
                        if isinstance(expr, str):
                            if expr in self.signature.get_function_names():
                                return "{0}-{1}".format(self.name, expr)
                            else:
                                return expr
                        elif isinstance(expr, list):
                            return [ rec(e) for e in expr ]
                        else:
                            return expr
                    d = rec(d)
                    sym = self.signature.get_function_symbol(fname)
                    sym.set_interp_decl(self.name, fname_mod)
                    fun_decls.append(expr2str(d))
                    fun_decls_names.append(fname)
                else:
                    aux_fun_decls.append(expr2str(d))
            elif d[0] == 'constraint':
                self.parametric_constraint = d
            else:
                raise ValueError("Not supported: {0}".format(d[0]))

        if not self.is_global:
            ns = set(fun_decls_names) 
            ss = set(self.signature.get_function_names())
            assert ns == ss,\
                    "missing function definitions in interp {0}: {1}".format(
                        self.name, " ".join(ss.difference(ns)))

        self.type_decls = type_decls
        self.fun_decls = fun_decls
        self.aux_fun_decls = aux_fun_decls


        self.block_names = {}
        self.input_line_names = []
        self.line_names = []
        self.interp_decls = []
        self.block_constraints = []
        self.var_decls = {}
        for b in blocks:
            self.block_names[b.name] = []
            if b.is_input:
                self.input_line_names += b.line_names
            else:
                # need to know line_names for generating parametric constraints
                self.line_names += b.line_names
                self.block_names[b.name].extend(b.line_names)
            line_vars = b.get_block_vars()
            if line_vars:
                self.var_decls.update(dict(line_vars))
            if not self.is_global:
                [block_interp_decls, block_constraint] = b.get_constraint(self)
                self.interp_decls += block_interp_decls
                if block_constraint:
                    self.block_constraints.append(block_constraint)

    def gen_type_decls(self):
        return "\n".join(self.type_decls)

    def gen_aux_defns(self):
        content = []
        content += self.aux_fun_decls
        if self.is_parametric:
            content += ["\n;; Parametric declarations for {0} interpretation".format(self.name)]
            content += self.gen_parametric_variables()
            content += ["\n;; Parametric level accessor for {0} interpretation".format(self.name)]
            content += self.gen_parametric_level_accessor()
        return "\n".join(content)

    def get_var_decls(self):
        return self.var_decls.copy()

    def get_ensure_expr(self):
        if self.ensure_expr:
            res = self._expand_loops(self.ensure_expr)
            return self._replace_macros(res)
        else:
            return ""

    def gen_parametric_level_accessor(self):
        assert self.is_parametric
        assert self.line_names and self.parametric_variables and self.parametric_constraint
        lines = self.line_names + self.input_line_names
        nlevels = self.params_dict[self.parametric_constraint[1][0]]
        func_name = "{0}-get-level".format(self.name)
        s = "(define {0}::(-> lineType int {1})\n".format(func_name, self.name)
        s += "  (lambda (x::lineType lvl::int)\n"
        for line in lines:
            s += "    (if (= x {0})".format(line)
            for l in range(nlevels):
                s += "\n      (if (= lvl {0}) {1} ".format(l, self.parametric_variables[line][l])
            #s += "\n      false" # final clause in levels switch
            s += "\n      decr_enc_1_lvl_0" # final clause in levels switch
            for l in range(nlevels-1):
                s += ")"
            s += ")\n"
        #s += "     false" # final clause in line switch
        s += "     decr_enc_1_lvl_0" # final clause in line switch
        for line in lines:
            s += ")"
        s += "\n  )\n" # lambda
        s += ")"   # define
        self.parametric_level_accessor = func_name
        return [s]


    def get_parametric_variable_name(self, level, line_name):
        return "{0}_{1}_lvl_{2}".format(self.name, line_name, level)

    def gen_parametric_variables(self):
        assert self.is_parametric
        assert self.line_names, self.parametric_constraint
        self.parametric_variables = {}
        nlevels = self.params_dict[self.parametric_constraint[1][0]]
        for line in self.line_names + self.input_line_names:
            self.parametric_variables[line] = []
            for lvl in range(nlevels):
                self.parametric_variables[line].append(self.get_parametric_variable_name(lvl, line))
        new_vars = sum(self.parametric_variables.values(), []) # concatenate
        decls = [ "(define {0} :: {1})".format(x, self.name) for x in new_vars ]
        return decls

    def gen_parametric_constraint(self):
        c = self.parametric_constraint
        # definine the number of levels
        assert len(c[1]) == 1, "unknown syntax: {0}".format(expr2str(c))
        nlevels = self.params_dict[c[1][0]]
        # need to replace this-level and next-level
        def write_levels(expr, level):
            if isinstance(expr, list):
                if expr[0] == "this-level":
                    assert len(expr) == 2, "syntax error: {0}".format(expr)
                    expr[0] = self.parametric_level_accessor
                    expr.append(level)
                    return expr
                elif expr[0] == "next-level":
                    assert len(expr) == 2, "syntax error: {0}".format(expr)
                    expr[0] = self.parametric_level_accessor
                    expr.append(level+1)
                    return expr
                else:
                    return [write_levels(x, level) for x in expr]
            else:
                return expr
        def write_levels_template(expr):
            if isinstance(expr, list):
                if expr[0] == "this-level":
                    assert len(expr) == 2, "syntax error: {0}".format(expr)
                    expr[0] = self.parametric_level_accessor
                    expr.append('$thislevel')
                    return expr
                elif expr[0] == "next-level":
                    assert len(expr) == 2, "syntax error: {0}".format(expr)
                    expr[0] = self.parametric_level_accessor
                    expr.append('$nextlevel')
                    return expr
                else:
                    return [write_levels_template(x) for x in expr]
            else:
                return expr
        cs = []
        expr = write_levels_template(copy.deepcopy(c[2]))
        #expr = write_levels(copy.deepcopy(c[2]), 0)
        expr = self._expand_loops(expr)
        expr = self._replace_macros(expr)
        cs.append(expr)
        from string import Template
        s =  Template(expr2pstr(['dummy']+cs, 2))
        res = ["\t(and ;; expansion of of {0} constraint\n".format(self.name)]
        for lvl in range(nlevels-1):
            res.append(";; level {0}".format(lvl+1))
            res.append(s.substitute({'thislevel': lvl, 'nextlevel': lvl+1})[10:-4])
            #print cs
            #expr = write_levels(copy.deepcopy(c[2]), lvl)
            #print expr
            #print 'here2'
            #expr = self._expand_loops(expr)
            #print expr
            #print 'here3'
            #expr = self._replace_macros(expr)
            #print expr
                        
        res.append('\t)\n')
        #cs.insert(0, "and ;; expansion of of {0} constraint".format(self.name))
        return '\n'.join(res)

    def _unroll_foreach(self, f):
        assert f[0] in ["foreach", "forsplice", "forsome"]
        assert len(f) == 3, "foreach expr must have 3 terms"
        assert self.line_names
        foreach_vars = []
        choices = []
        for v in f[1]:
            assert len(v) > 1, v
            foreach_vars.append(v[0])
            c = []
            for e in v[1:]:
                if e == "lines":
                    c.extend(self.line_names)
                elif e == "inputs":
                    c.extend(self.input_line_names)
                elif e in self.block_names:
                    c.extend(self.block_names[e])
                else:
                    raise AssertionError, "unknown keyword: " + e
            choices.append(c)
        def recurse(expr, assn):
            if isinstance(expr, str) or isinstance(expr, int):
                if expr in foreach_vars: 
                    i = foreach_vars.index(expr)
                    return assn[i]
                else:
                    return expr
            elif isinstance(expr, list):
                expr = self._expand_loops(expr)
                res = [ recurse(x, assn) for x in expr ]
                return res
        # generate possible assignments to each line var
        # finding the cartesian product is sketchy in python
        assignments = itertools.product(*choices) 
        res = [ recurse(f[2], assn) for assn in assignments ]
        return res

    def _expand_loops(self, expr):
        def recurse(expr):
            if isinstance(expr, list):
                if expr[0] == "foreach":
                    res = self._unroll_foreach(expr)
                    res.insert(0, 'and')
                    return (res, False)
                elif expr[0] == "forsome":
                    res = self._unroll_foreach(expr)
                    res.insert(0, 'or')
                    return (res, False)
                elif expr[0] == "forsplice":
                    res = self._unroll_foreach(expr)
                    return (res, True)
                else:
                    res = []
                    for e in expr:
                        (expr, splice) = recurse(e)
                        if splice:
                            res += expr
                        else:
                            res.append(expr)
                    return (res, False)
            else:
                return (expr, False)
        (res, splice) = recurse(expr)
        return res

    def _replace_macros(self, expr):
        assert self.line_names, "Interp {0} must know line names!".format(
            self.name)
        def recurse(expr):
            if isinstance(expr, list):
                if expr[0] == "func":
                    assert len(expr) == 2, expr
                    s = recurse(expr[1])
                    # assert s in self.line_names, s
                    return s + "_func"
                elif expr[0] == self.name:
                    if len(expr) == 2: # occurs in foreach loops: eg (foreach ((x lines)) (typ x)) <- x is a lineType
                        assert expr[1] in self.line_names +\
                            self.input_line_names
                        return "{0}_{1}".format(expr[1], self.name)
                    if len(expr) == 3:
                        s = recurse(expr[1])
                        try:
                            assert isinstance(expr[2], int), expr
                        except AssertionError:
                            expr[2] = self.params_dict[expr[2]]
                        line_name = s + "_" + str(expr[2])
                        assert line_name in self.line_names + self.input_line_names, line_name + " unknown"
                        return "{0}_{1}".format(line_name, self.name)
                elif expr[0] == "level" and len(expr) == 3:
                    assert self.parametric_level_accessor, "no level accessor defined"
                    try:
                        assert isinstance(expr[2], int), expr
                    except AssertionError:
                        expr[2] = self.params_dict[expr[2]]
                    s = recurse(expr[1])
                    assert s in self.line_names + self.input_line_names, s
                    return [ self.parametric_level_accessor, s, expr[2] - 1 ]
                elif expr[0] == "line" and len(expr) == 3:
                    assert isinstance(expr[2], int), expr
                    s = expr[1] + "_" + str(expr[2])
                    assert s in self.line_names + self.input_line_names, s
                    return s 
                else:
                    return [ recurse(x) for x in expr ]
            else:
                return expr
        return recurse(expr)




    def to_yices(self, content):
        #content = []
        content.append("\n;; {0} constraints".format(self.name))
        if self.is_primal:
            content.append("(assert\n  (forall (")
            for (d,t) in self.interp_decls:
                content.append("    {0} :: {1}".format(d,t))
            content.append("  )\n  (=>\n    (and")
            for c in self.block_constraints:
                content.append(expr2pstr(c, 3))
            content.append("    )") # and
            content.append(expr2pstr(self.get_ensure_expr(), 2))
            content.append("  )\n  )\n)") # =>, forall, assert
        
        elif not self.is_primal and not self.is_global: # dual non-parametric interp
            for (d,t) in self.interp_decls:
                content.append("(define {0} :: {1})".format(d,t))
            content.append("(assert\n  (and")
            for c in self.block_constraints:
                content.append(expr2pstr(c, 2))
            content.append("    ;; {0} ensure expression".format(self.name))
            content.append(expr2pstr(self.get_ensure_expr(), 2))
            content.append("  )\n)") # assert

        elif not self.is_primal and self.is_global and self.is_parametric:
            content.append("\n;; {0} global parametric constraints {1}".format(self.name, "")) #'{'*3))
            content.append("(assert")
            content.append("  (and")
            content.append("    ;; parametric constraint")
            s = self.gen_parametric_constraint()
            content.append(s)
            content.append("    ;; ensure expr")
            content.append(expr2pstr(self.get_ensure_expr(), 2))
            content.append("  )")
            content.append(") ;; {0}".format("")) #'}'*3))





class Signature:
    """
    The Signature in a synudic sketch

    * Attributes:
        * function_symbol_list
        * function_name2function_symbol
    """
    def __init__(self, function_symbol_list):
        self.function_symbol_list = function_symbol_list
        self.function_name2function_symbol =\
            dict([(x.name, x) for x in self.function_symbol_list])

    def add_symbol(self, s):
        self.function_symbol_list.append(s)
        self.function_name2function_symbol[s.name] = s

    def get_constants(self):
        return [f for f in self.function_symbol_list if f.arity == 0]

    def get_function_names(self):
        return [x.name for x in self.function_symbol_list]

    def get_functions(self):
        return self.function_name2function_symbol.values()

    def get_function_symbol(self, name):
        return self.function_name2function_symbol[name]


class BlockDecl:
    """
    A block in a synudic sketch
    """

    def __init__(self, name, length, constraints):#, previous_blocks, signature):
        self.name = name
        self.length = length  # Might be a parameter
        self.constraints = constraints
        self.is_input = constraints[0] == 'input'



    def instantiate(self, params_dict, signature, previous_blocks):
        """
        This function is called after parsing,
        when the parameters are available.
        """
        self.previous_blocks_dict = { b.name: b for b in previous_blocks }
        try:
            self.length = int(self.length)
        except ValueError:
            self.length = params_dict[self.length]
        self.line_names = [get_block_line_name(self.name, i)
            for i in range(self.length)]
        self.unused_arg_line_names = [
            get_block_unused_arg_line_name(self.name, i, j)
            for i in range(self.length)
            for j in range(0, MAX_NUM_BLK_INPUTS)]

        self.signature = signature
        if self.is_input:
            assert len(self.line_names) == 1
            length = 1
            init_val = self.constraints[1]
            self.constraints = ['(= {0} {1})'.format(
                get_line_typ_val_name(self.line_names[0]), init_val)]
        else:
            #continue
            #self.constraints = []
            for c in self.constraints:
                c_function = self.signature.get_function_symbol(
                    c.function)
                params_constraint = []
                for p in c.param_constraint:
                    param_constraint = []
                    for block_name in p:
                        if block_name != '-':
                            param_constraint += self.previous_blocks_dict[block_name].line_names
                        else:
                            param_constraint += self.line_names
                    params_constraint.append(param_constraint)
                c.param_constraint = params_constraint
                #constraint = FunctionConstraint(c.function, params_constraint)
                #self.constraints.append(constraint)
                assert len(params_constraint) == c_function.arity, \
                '{0} != {1}'.format(len(params_constraint), c_function.arity)




        self.line_input_line_names_dict = dict(
            [(self.line_names[i],
                tuple([get_block_input_line_name(self.name, i, j)
                        for j in range(MAX_NUM_BLK_INPUTS)]))
             for i in range(self.length)]
        )
        self.line_func_name_dict = dict(
            [(self.line_names[i], get_block_function_name(self.name, i))
             for i in range(self.length)])



    def get_block_vars(self):
        variables = []  # [(x, type)]
        if not self.is_input:
            for l in self.line_names:
                for i in self.line_input_line_names_dict[l]:
                    variables.append((i, LINE_TYPE_NAME))
            for n, f in self.line_func_name_dict.iteritems():
                variables.append((f, FUNC_TYPE_NAME))
        return variables

    def get_constraint(self, interp):
        """
        :return: An expression containing the Yices encoding of the block
        """
        constraint = []
        variables = []
        for i in range(self.length):
            val = get_block_interp_val_name(self.name, interp.name, i)
            variables.append((val, interp.name))

        for i, l in enumerate(self.line_names):
            expr = []
            for c in self.constraints:
                if isinstance(c, str):
                    expr.append(c)
                else:
                    s = c.to_yices(self, i, interp)
                    if s:
                        expr.append(s)
            if expr and not self.is_input:
                expr.insert(0, 'or')
                constraint.append(expr)

        if constraint:
            constraint.insert(0, 'and')
        return [variables, constraint]


class FunctionConstraint:
    """
    A Synudic constraint, such as (f (blk3 -) (blk1 blk2 blk3 -)),
    representing all possible expressions f(x, y), where
    x is a variable computed in either blk3 or the current block
    and y is a variable computed in either blk1, blk2, blk3, or the
    current block. We call this a function constraint because
    f is fixed.
    """
    def __init__(self, function, param_constraint):
        self.function = function
        self.param_constraint = param_constraint

    def to_yices(self, block, line_number, interp):
        """
        :param block: The block containing the constraint
        :param line_number: The line number containing the constraint
        :interp: the interpretation under consideration
        """
        line_name = block.line_names[line_number]
        line_func_name = block.line_func_name_dict[line_name]
        invalid_lines_in_block = block.line_names[line_number:]
        filtered_param_constraint = map(
            lambda x: filter(
                lambda y: y not in invalid_lines_in_block, x),
            self.param_constraint)
        input_lines_options = self.function.get_input_filter()(
            list(itertools.product(*filtered_param_constraint)))
        input_lines_formals = block.line_input_line_names_dict[line_name]
        line_interp_name = "{0}_{1}".format(line_name, interp.name)
        input_lines_options_expr = []
        for actuals in input_lines_options:
            assignment = zip(
                input_lines_formals[:self.function.arity], actuals)
            unassigned_inputs = input_lines_formals[self.function.arity:]
            #print unassigned_inputs
            #print [(x, get_unused_arg_line_from_line_name(line_name, self.function.arity + k))
            #    for k, x in enumerate(unassigned_inputs)]
            assignment += [(x, get_unused_arg_line_from_line_name(
                line_name, self.function.arity + k))
                for k, x in enumerate(unassigned_inputs)]
            assignment_expr =\
                ['(= {0} {1})'.format(x, y) for (x, y) in assignment]
            actuals_types = map(lambda x: get_line_interp_val_name(
                interp.name, x), actuals)
            fname = self.function.get_interp_name(interp.name)
            if interp.is_primal:
                type_constraint = '(= ({0} {1}) {2})'.format(
                    fname, ' '.join(actuals_types), line_interp_name)
            else:
                type_constraint = '({0} {1} {2})'.format(
                    fname, ' '.join(actuals_types), line_interp_name)
            input_lines_options_expr.append(
                ['and'] + assignment_expr + [type_constraint])
        if not input_lines_options_expr:
            return []
        input_lines_options_expr = ['or'] + input_lines_options_expr
        line_func_constraint = ('(= {0} {1})'.format(
            line_func_name, self.function.name))
        block_yices_expr = ['and'] + [line_func_constraint] +\
            [input_lines_options_expr]
        return block_yices_expr

def bnf(sk):
    """
    Defines the Grammar for synudic sketches
    :return: Pyparsing objects for parsing provn
    """
    lpar = Suppress("(")
    rpar = Suppress(")")
    colon = Literal(":")
    word = Word(alphanums + '_/-#:.=')
    number = Word(nums)
    double_quote = Suppress('\"')
    text = ZeroOrMore(word)

    # block input
    block_input_decl = (lpar + Keyword('input') +
            word +
                Optional(colon + colon + 'true') + rpar)

    def in_list(t):
        return [t]

    # function constraint
    function_constraint = lpar + word.setResultsName('function_name') +\
        ZeroOrMore(
            lpar + OneOrMore(word).setParseAction(in_list) + rpar).\
            setResultsName('parameters_constraints') + rpar
    function_constraint.setParseAction(sk.make_function_constraint_from_parser)

    # program line constraint
    line_constraint = lpar + (block_input_decl |
            OneOrMore(function_constraint)) + rpar

    # block
    block = lpar + word.setResultsName('block_name') +\
        (word | number).setResultsName('length') +\
        OneOrMore(line_constraint).setResultsName('line_constraints') +\
        rpar
    block.setParseAction(sk.make_block_from_parser)

    # blocks declarations
    block_decls = lpar + Keyword('blocks') + ZeroOrMore(
        block).setResultsName('block_decls') + rpar
    block_decls.setParseAction(sk.make_block_list_from_parser)

    # ensure expression
    ensure = (lpar +
        Keyword('ensure') + sexpParser.sexp.setResultsName('ensure') +
        rpar)

    # library function
    function_declaration = lpar + word.setResultsName('function_name') +\
        number.setResultsName('arity') +\
        Optional('ac').setResultsName('is_ac') + rpar
    function_declaration.setParseAction(sk.make_function_symbol_from_parser)

    # library
    signature_decl = lpar + Keyword('library') + ZeroOrMore(
        function_declaration).setResultsName('function_list') + rpar
    signature_decl.setParseAction(sk.make_signature_from_parser)

    # parameters
    parameters_decl = lpar + Keyword('parameters') + ZeroOrMore(word).\
        setResultsName('parameters_list') + rpar

    # interpretation declaration
    interpretation_decl = (lpar +
        (Keyword('dual') | Keyword('primal')).setResultsName('type') +
        word.setResultsName('interpretation_name') +
        Optional(Keyword('PARAMETRIC').setResultsName('is_parametric')) +
        Optional(Keyword('GLOBAL').setResultsName('is_global')) +
        lpar + Keyword('decls') + ZeroOrMore(sexpParser.sexp)
            .setResultsName('decls') + rpar +
        Optional(ensure) + rpar)
    interpretation_decl.setParseAction(sk.make_interp_from_parser)

    # comment
    comment = ((lpar + Keyword('comment') +
        double_quote + text.setResultsName('text') + double_quote +
        rpar) | ';' + restOfLine)

    # sketch
    sketch = (ZeroOrMore(';' + restOfLine) +
        lpar + word.setResultsName('sketch_name') +
        ZeroOrMore(comment.setResultsName('comments')) +
        (parameters_decl.setResultsName('parameters') &
        signature_decl.setResultsName('signature') &
        block_decls.setResultsName('blocks') &
        OneOrMore(interpretation_decl.setResultsName('interps'))
        ) + rpar)

    sketch.setParseAction(sk.make_sketch_from_parser)
    comment = ';' + restOfLine
    sexpParser.sexp.ignore(comment)

    return {"sketch": sketch}


if __name__ == "__main__":
    def test(s, nt):
        sk = Sketch()
        result = bnf(sk)[nt].parseString(s, True)
        print(s, '\n\t=>\n', result)
        print('---------------------')

    def test_file(f, nt):
        sk = Sketch()
        result = bnf(sk)[nt].parseFile(f, True)
        #print(f, '\n\t=>\n', result)
        #print('---------------------')

    f = sys.argv[1]
    test_file(f, 'sketch')
