import re
from constants import MAX_NUM_BLK_INPUTS
import pyparsing

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
