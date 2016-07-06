from parser import Sketch
from z3 import *
import time
import subprocess
import re
import sexpParser
import os

from constants import *
from utils import gen_arg_accessor, MyFile, show_dot
from yices_to_z3 import *

class Solver(Sketch):
    def __init__(self):
        Sketch.__init__(self)

    def show_result(self, model, block, types=None, out_fd=None):
        program_lines = {}
        processed_blocks = []
        for i, l in list(enumerate(block.line_names)):
            try:
                line_func_name = model[get_block_function_name(block.name, i)]
            except KeyError as e:
                # b is an input block
                assert len(block.line_names) == 1, block.name
                #print '{0}'.format(l)
                continue
            f = self.signature.get_function_symbol(line_func_name)
            line_args = [model[arg] for arg in [get_block_input_line_name(
                block.name, i, j) for j in range(f.arity)]]
            program_lines[l] = (line_func_name, tuple(line_args))
            print '{0} = {1}({2})'.format(
                l, line_func_name, ' '.join(line_args))
            if out_fd:
                out_fd.write('{0} = {1}({2})\n'.format(
                    l, line_func_name, ' '.join(line_args)))

            def printOT(t):
                for m in ['m1', 'm2']:
                    print '  ' + m + ':' , 
                    if m in t:
                        for a in ['a1', 'a2', 'a3']:
                            if a in t[m]:
                                if a == 'a2': print '+',
                                elif a == 'a3': print '-',
                                print "".join(t[m][a]),
                print

            if types and l in types:
                for i in types[l].keys():
                    if OT:
                        printOT(types[l][i])
                    else:
                        types[l][i].sort()
                        print '  {0} :: {1}'.format(i, " ".join(types[l][i]))
                        if out_fd:
                            out_fd.write('{0} :: {1}\n'.format(
                                i, " ".join(types[l][i])))
            # for i in self.interps:
            #     n = l + "_" + i.name
            #     if n in model:
            #         m = re.match("(.*)_" + i.name, model[n])
            #         if m:
            #             s = m.group(1)
            #             if s != l and s in types and i.name in types[s]:
            #                 if OT:
            #                     printOT(types[s][i.name])
            #                 else:
            #                     types[s][i.name].sort()
            #                     print '  {0} :: {1}'.format(i.name, " ".join(types[s][i.name]))
            #                     if out_fd:
            #                         out_fd.write('  {0} :: {1}\n'.format(
            #                             i.name, " ".join(types[s][i.name])))
            #         else:
            #             print '  {0} :: {1}'.format(i.name, model[n])
            #             if out_fd:
            #                 out_fd.write('  {0} :: {1}\n'.format(
            #                     i.name, model[n]))

            print ""

    def to_yices(self, content, with_check=True):
        content.append(';; Line type declarations')
        all_line_names = [' '.join(b.line_names + b.unused_arg_line_names)
            for b in self.blocks]
        line = '(define-type {0} (scalar {1}))'.format(
            LINE_TYPE_NAME, ' '.join(all_line_names + ['NUL']))
        content.append(line)

        content.append('\n;; Function type declarations')
        all_func_names = [f.name for f in self.signature.function_symbol_list] + ["input"]
        line = '(define-type {0} (scalar {1}))'.format(FUNC_TYPE_NAME, ' '.join(all_func_names))
        content.append(line)

        content.append('\n;; Input declarations')
        all_inputs = set()
        for i in self.interps:
            for l in i.input_line_names:
                all_inputs.add(l)
        for l in all_inputs:
            line = '(define {0}_func::funcType input)'.format(l)
            content.append(line)

        content.append("\n;; Interpretation type declarations")
        self.interps = sorted(self.interps, key=lambda x:len(x.aux_fun_decls), reverse=True)
        for interp in self.interps:
            content.append(interp.gen_type_decls())
            
        content.append("\n;; Function definitions")
        for interp in self.interps:
            content.append(interp.gen_aux_defns())
            if not interp.is_global:
                for f in interp.fun_decls:
                    content.append(f)

        # there will be overlap in var decls, since we initialize multiple
        # interpretations with the same blocks. So we have to keep track of them
        # and make sure not to redefine existing variables. Hence the dictionary.
        content.append("\n;; Line, func, and arg definitions")
        var_decls = {}
        for interp in self.interps:
            var_decls.update(interp.get_var_decls())
        for name, ty in var_decls.iteritems():
            s = "(define {0} :: {1})".format(name, ty)
            content.append(s)

        content.append("\n;; Argument accessor")
        content.append(gen_arg_accessor(self.interps[0].line_names, self.interps[0].input_line_names))

        # generate assertions
        for interp in self.interps:
            #content.append(interp.gen_constraints())
            interp.to_yices(content)

        if with_check:
            if self.existsforall:
                content.append('(ef-solve)')
            else:
                content.append('(check)')
                content.append('(show-model)')
        content.fd.close()

    def parse_output(self, filename, existsforall):
        def parse_yices_types(typs):
            model = {}
            for t in typs:
                sexp = sexpParser.sexp.parseString(t, parseAll=False)
                if sexp[0][0] == 'function':
                    typeName = sexp[0][2][1]
                    m = re.match("(.*)_" + typeName, sexp[0][1])
                    lineName = m.group(1)
                    if not lineName in model: model[lineName] = {}
                    if OT:
                        if not typeName in model[lineName]: model[lineName][typeName] = {}
                        m = model[lineName][typeName]
                        for s in sexp[0][3:]:
                            if s[0] == '=':
                                branch = s[1][1]
                                addend = s[1][2]
                                if not branch in m: m[branch] = {}
                                if not addend in m[branch]: m[branch][addend] = []
                                if s[-1] != 'bot':
                                    m[branch][addend].append(s[-1])
                            elif s[0] == 'default' and s[1] != 'bot':
                                for b in ['m1','m2']:
                                    for a in ['a1', 'a2', 'a3']:
                                        if not b in m: m[branch] = {}
                                        if not a in m[b]: m[b][a] = []
                                        m[b][a].append(s[1])

                    else:
                        if not typeName in model[lineName]: model[lineName][typeName] = []
                        for s in sexp[0][3:]:
                            if s[0] == "=":
                                x = "[" + " ".join(s[1][1:] + [s[2]]) + "]"
                                model[lineName][typeName].append(x)
                            else:
                                x = "[~" + " ".join(s) + "]"
                                model[lineName][typeName].append(x)
            return model

        parsing_model = False
        model = {}
        types = []
        with open(filename, 'r') as f_desc:
            for line in f_desc.readlines():
                #print line
                if not line.strip(): continue
                if line.strip() == 'unsat':
                    return None
                elif line.strip() == 'sat':
                    parsing_model = True
                    continue
                if parsing_model:
                    if existsforall: # the output format is different for the ef solver
                        m = re.match('\s*(\S+)\s*:=\s*(\S+)', line)
                    else:
                        m = re.match ('\(= (\S+) (\S+)\)', line)
                    if m and line:
                        var, val = m.group(1), m.group(2)
                        model[var] = val
                    else:
                        if re.match('.*function.*', line):
                            types.append(line.rstrip())
                        # else:
                            # types[-1] += line.rstrip()
        if not existsforall:
            pass
            #model["_types_"] = parse_yices_types(types)
        return model


class YicesSolver(Solver):
    def __init__(self):
        Solver.__init__(self)

 

    def solve(self, dont_run=False):
        tmp_filename = 'tmp.txt'
        if dont_run:
            model = self.parse_output(tmp_filename, self.existsforall)
            if model:
                for b in self.blocks:
                    print "-- block \"{0}\" --".format(b.name)
                    if "_types_" in model:
                        self.show_result(model, b, model["_types_"])
                    else:
                        self.show_result(model, b)
            return

        yices_filename = 'synth.ys'
        f = MyFile(yices_filename)
        self.to_yices(f)
        with open(tmp_filename, 'w') as tmp_file_desc:
            if self.existsforall:
                yices_command_list =\
                    ['yices', '--mode=ef', '--verbosity=10', yices_filename]
            else:
                yices_command_list = ['yices', '--mode=one-shot',
                    '--verbosity=10', yices_filename]
            print 'Running "{0}"'.format(' '.join(yices_command_list))
            start = time.time()
            subprocess.call(yices_command_list, stdout=tmp_file_desc)
            end = time.time()
            print "smt took {0} seconds".format(end - start)

        model = self.parse_output(tmp_filename, self.existsforall)
        if model:
            for b in self.blocks:
                print "-- block \"{0}\" --".format(b.name)
                if "_types_" in model:
                    self.show_result(model, b, model["_types_"])
                else:
                    self.show_result(model, b)


class Z3Solver(Solver):
    def __init__(self, enumerate_solutions):
        Solver.__init__(self)
        self.enumerate_solutions = enumerate_solutions

    def solve(self):
        yices_filename = 'synth.ys'
        z3_filename = 'synth.z3'
        f = MyFile(yices_filename)
        self.to_yices(f, with_check=False)
        with open(yices_filename, "r") as fp:
            s = ""
            for line in fp:
                if re.search("^\s*$", line): continue
                m = re.search("^([^;]*);.*$", line)
                if m: line = m.group(1)
                s += line
            s = "(" + s + ")"
            sexpr = sexpParser.sexp.parseString(s, parseAll=True)
        with open(z3_filename, "w") as f:
            exprs = expr_to_z3(sexpr[0], not self.enumerate_solutions)
            for eprime in exprs:
                s = expr2pstr(z3_translate(z3_capitalize(eprime)), 0)
                f.write(s + "\n")

        f = parse_smt2_file(z3_filename)
        # The following function is a slight modification of the one in
        # http://stackoverflow.com/questions/11867611/z3py-checking-all-solutions-for-equation

        def get_models(F, M=-1):
            dup1_datatype_ref = None
            dup2_datatype_ref = None
            result = []
            s = z3.Solver()
            s.add(F)
            while (M < 0 or len(result) < M) and s.check() == sat:
                print 'Found {0} solution(s) so far'.format(len(result) + 1)
                m = s.model()
                if result:
                    m_ = result[len(result) - 1]
                    found_diff = False
                    for y in m:
                        if str(y()).endswith('_func') or\
                                re.match('\S+_arg_[0-3]', str(y())):
                            if str(m[y]) != str(m_[y]):
                                found_diff = True
                    assert found_diff
                result.append(m)
                # Create a new constraint the blocks the current model
                block = []
                for d in m:
                    # d is a declaration
                    if d.arity() > 0:
                        raise Z3Exception(
                            "uninterpreted functions are not supported")
                    # create a constant from declaration
                    c = d()
                    if is_array(c) or c.sort().kind() == Z3_UNINTERPRETED_SORT:
                        raise Z3Exception(
                            "arrays and uninterpreted sorts are not supported")
                    if str(c).endswith('_func') or\
                            re.match('\S+_arg_[0-3]', str(c)):
                        block.append(c != m[d])
                s.add(Or(block))
            print 'Done finding solutions.'
            return result
        start_time = time.time()
        results = get_models(f, -1 if self.enumerate_solutions else 1)
        elapsed_time = time.time() - start_time
        print 'elapsed_time: {}'.format(elapsed_time)
        # tmp_filename = 'tmp.txt'
        # for j, m in enumerate(results):
        #     with open(tmp_filename, 'w') as tmp_file_desc:
        #         tmp_file_desc.write("sat\n")
        #         for e in m:
        #             tmp_file_desc.write('(= {0} {1})\n'.format(e, m[e]))
        #     model = self.parse_output(tmp_filename, self.existsforall)
        #     if model:
        #         for b in self.blocks:
        #             print "-- block \"{0}\" --".format(b.name)
        #             if "_types_" in model:
        #                 self.show_result(model, b, model["_types_"])
        #             else:
        #                 self.show_result(model, b)
            # with open('tmp_{}.tmp'.format(j), 'w') as out_file:
                #     for b in self.blocks:
                #         out_file.write("-- block \"{0}\" --\n".format(b.name))
                #         if "_types_" in model:
                #             self.show_result(
                #                 model, b, model["_types_"], out_fd=out_file)
                #         else:
                #             self.show_result(model, b, out_fd=out_file)

            # import networkx as NX
            # G = NX.DiGraph()

            # with open('tmp_{}.tmp'.format(j)) as f:
            #     for line in f:
            #         m1 = re.match('(\S+)\s+=\s+(\S+)\((\S+)\)', line.strip())
            #         if m1:
            #             lhs = m1.group(1)
            #             op = m1.group(2)+' '*len(G.nodes())
            #             rhs = m1.group(3)
            #             G.add_nodes_from([lhs, op, rhs])
            #             G.add_edges_from([(op, lhs), (rhs, op)])
            #         else:
            #             m2 = re.match('(\S+)\s+=\s+oplus\((\S+)\s*(\S+)\)', line.strip())
            #             if m2:
            #                 lhs = m2.group(1)
            #                 op = 'oplus'+' '*len(G.nodes())
            #                 rhs1 = m2.group(2)
            #                 rhs2 = m2.group(3)
            #                 G.add_nodes_from([lhs, op, rhs1, rhs2])
            #                 G.add_edges_from([(op, lhs), (rhs1, op), (rhs2, op)])

            # labels = {}
            # for n in G.nodes():
            #     labels[n] = str(n)
            # NX.write_dot(G,'test_{}.dot'.format(j))
            # os.system('dot -Tpdf test_{0}.dot > test_{0}.pdf; okular test_{0}.pdf &'.format(j))

        #show_dot(results, tmp_filename)
