import re
from constants import MAX_NUM_BLK_INPUTS
import pyparsing

def show_dot(results, tmp_filename):
    for j, m in enumerate(results):
        with open(tmp_filename, 'w') as tmp_file_desc:
            tmp_file_desc.write("sat\n")
            for e in m:
                tmp_file_desc.write('(= {0} {1})\n'.format(e, m[e]))
        model = parse_yices_output(tmp_filename, sketch.existsforall)
        if model:
            for b in sketch.blocks:
                print "-- block \"{0}\" --".format(b.name)
                if "_types_" in model:
                    sketch.show_result(model, b, model["_types_"])
                else:
                    sketch.show_result(model, b)
            with open('tmp_{}.tmp'.format(j), 'w') as out_file:
                for b in sketch.blocks:
                    out_file.write("-- block \"{0}\" --\n".format(b.name))
                    if "_types_" in model:
                        sketch.show_result(
                            model, b, model["_types_"], out_fd=out_file)
                    else:
                        sketch.show_result(model, b, out_fd=out_file)
            import re, os
            import networkx as NX
            G = NX.DiGraph()

            with open('tmp_{}.tmp'.format(j)) as f:
                for line in f:
                    m1 = re.match('(\S+)\s+=\s+(\S+)\((\S+)\)', line.strip())
                    if m1:
                        lhs = m1.group(1)
                        op = m1.group(2)+' '*len(G.nodes())
                        rhs = m1.group(3)
                        G.add_nodes_from([lhs, op, rhs])
                        G.add_edges_from([(op, lhs), (rhs, op)])
                    else:
                        m2 = re.match('(\S+)\s+=\s+oplus\((\S+)\s*(\S+)\)', line.strip())
                        if m2:
                            lhs = m2.group(1)
                            op = 'oplus'+' '*len(G.nodes())
                            rhs1 = m2.group(2)
                            rhs2 = m2.group(3)
                            G.add_nodes_from([lhs, op, rhs1, rhs2])
                            G.add_edges_from([(op, lhs), (rhs1, op), (rhs2, op)])

            labels = {}
            for n in G.nodes():
                labels[n] = str(n)
            NX.write_dot(G,'test_{}.dot'.format(j))
            os.system('dot -Tpdf test_{0}.dot > test_{0}.pdf; okular test_{0}.pdf &'.format(j))


class MyFile():
    def __init__(self, filepath):
        self.fd = open(filepath, 'w')

    def append(self, s):
        self.fd.write(s+'\n')


def isList(expr):
    return isinstance(expr, pyparsing.ParseResults) or isinstance(expr, list)


def stripComments(line):
    # ignore comments as everything after ';' in a line
    m = re.search("([^;]*);.*", line)
    if m:
        line = m.group(1)
    return line


def expr2pstr(e, level = 0):# {{{
    if isinstance(e, str):
        return '  '*level+e
    elif isinstance(e, int):
        return '  '*level+str(e)
    elif isList(e) and all(map(lambda x:isinstance(x, str) or isinstance(x, int), e)):
        if len(e) == 0: return ''
        return '  '*level+'({0})'.format(' '.join(map(str, e)))
    else:
        if len(e) == 0: return ''
        maybe = '  '*level+expr2str(e)
        if len(maybe) <= 120:
            return maybe
        else:
            l = [ expr2pstr(x, level + 1) for x in e[1:] ]
            return '  '*level+'({0}\n{1}\n'.format(expr2str(e[0]),'\n'.join(l))+'  '*level+')'

def expr2str(e):
    if isinstance(e, str):
        return e
    elif isinstance(e, int):
        return str(e)
    else:
        l = [ expr2str(x) for x in e ]
        return '({0})'.format(' '.join(l))


def gen_arg_accessor(line_names, input_line_names):
    s  = "(define arg::(-> lineType int lineType)\n"
    s += "  (lambda (x::lineType i::int)\n"
    for name in line_names:
        s += "    (if (= x {0})\n".format(name)
        for i in range(MAX_NUM_BLK_INPUTS):
            s += "      (if (= i {0}) {1}_arg_{0}\n".format(i, name)
        s += "      " + name
        for i in range(MAX_NUM_BLK_INPUTS):
            s += ")"
        s += "\n"
    for name in input_line_names:
        s += "    (if (= x {0})\n".format(name)
        for i in range(MAX_NUM_BLK_INPUTS):
            s += "      (if (= i {0}) NUL\n".format(i)
        s += "      " + name
        for i in range(MAX_NUM_BLK_INPUTS):
            s += ")"
        s += "\n"
    s += "    " + name
    for name in line_names:
        s += ")"
    for name in input_line_names:
        s += ")"
    s += "))"
    return s
