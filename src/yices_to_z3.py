import pyparsing
import re

def expand_forall_def(expr):
        def replace_str(expr, formal, actual):
            if isinstance(expr, list):
                res = []
                for e in expr:
                    expr = replace_str(e, formal, actual)
                    res.append(expr)
                return res
            else:
                return actual if expr == formal else expr
        def instantiate_unary_function(expr, var, fun):
            if isinstance(expr, list):
                if expr[0] == var:
                    actual = expr[1]
                    (body, formal) = fun
                    return replace_str(body, formal, actual)
                else:
                    res = []
                    for e in expr:
                        expr = instantiate_unary_function(e, var, fun)
                        res.append(expr)
                return res
            else:
                return expr
        def recurse(expr, d1, d2):
            if isinstance(expr, list):
                if expr[0] == "forall_def":
                    body = expr[1][2]
                    var = expr[1][1][0][:expr[1][1][0].find(':')]
                    d2[var] = body
                    fun = (body, var)
                    [(var, expr)] = d1.items()
                    return instantiate_unary_function(expr, var, fun)
                if expr[0] == "define" and expr[1] == "forall_def::":
                    body = expr[3][2:]
                    var = expr[3][1][0][:expr[3][1][0].find(':')]
                    d1[var] = body
                    return expr
                res = []
                for e in expr:
                    expr = recurse(e, d1, d2)
                    res.append(expr)
                return res
            else:
                return expr
        d1 = {}
        d2 = {}  
        res = recurse(expr, d1, d2)
        return res

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
# }}}
def expr2str(e):# {{{
    if isinstance(e, str):
        return e
    elif isinstance(e, int):
        return str(e)
    else:
        l = [ expr2str(x) for x in e ]
        return '({0})'.format(' '.join(l))
# }}}

def isList(expr):
    return isinstance(expr, pyparsing.ParseResults) or isinstance(expr, list)


def convert_z3_output(filename, sketch):# {{{
    with open(filename, 'r') as f:
        sat = f.readline().strip()
        if sat != 'sat': return
        s = ""
        for line in f: 
            s += stripComments(line.strip())

    out = ""
    sexp = sexpParser.sexp.parseString(s, parseAll=True)
    mappings = {}
    lineNames = sketch.interps[0].line_names + sketch.interps[0].input_line_names
    for e in sexp[0]:
        if isList(e):
            if len(e) == 4 and e[0] == 'define-fun' and e[1] in sketch.signature.get_function_names() and (not isList(e[3])):
                mappings[e[3]] = e[1]
            if len(e) == 4 and e[0] == 'define-fun' and e[1] in lineNames and (not isList(e[3])):
                mappings[e[3]] = e[1]        

    with open(filename, 'w') as f:
        f.write("sat\n")
        for e in sexp[0]:
            if len(e) == 4 and e[0] == 'define-fun' and e[3] in mappings:
                s = "(= {0} {1})\n".format(e[1], mappings[e[3]])
                f.write(s)

def expr_to_z3(exprs, solve=True): # {{{
    ret = []
    arrays = []
    for expr in exprs:
        if expr[0] == "define-type":
            ret += z3_define_type(expr, arrays) # may return multiple elements
        elif expr[0] == "define":
            ret.append(z3_define_function(expr, arrays))
        elif expr[0] == 'check':
            if solve:
                ret.append(['check-sat'])
        elif expr[0] == 'show-model':
            if solve:
                ret.append(['get-model'])
        else:
            ret.append(expr)
    return ret

def z3_define_function(expr, arrays):
    fexpr = None
    # different cases occur because "stuff::type" parsing is inconsistent
    m = re.match('^([^:]*)::([^:]*)$', expr[1])
    if m:
        fname = m.group(1)
        if m.group(2):
            ftype = m.group(2)
            if len(expr) == 3:
                fexpr = expr[2]
        else:
            ftype = expr[2]
            if len(expr) == 4:
                fexpr = expr[3]
    elif expr[2] == '::':
        fname = expr[1]
        ftype = expr[3]
        if len(expr) == 5:
            fexpr = expr[4]

    if not fexpr and isinstance(ftype, str):
        ret = ["declare-fun", fname, [], ftype]

    elif fexpr and isinstance(ftype, str) and (isinstance(fexpr, str) or isinstance(fexpr, int)):
        ret = ["define-fun", fname, [], ftype, fexpr]

    elif fexpr and isList(ftype) and ftype[0] == '->' and fexpr[0] == 'lambda':
        args = []
        arrayArgs = []
        for arg in fexpr[1]:
            try:
                m = re.match('^([^:]*)::([^:]*)$', arg)
            except TypeError:
                return []
            if m.group(2) in arrays: arrayArgs.append(m.group(1))
            args.append([m.group(1), m.group(2)])
        resultType = ftype[-1]
        body = fexpr[2]
        
        def insertSelect(expr):
            if isList(expr) and expr[0] in arrayArgs:
                expr.insert(0, 'select')
            if isList(expr):
                for e in expr: insertSelect(e)
        def replaceUpdate(expr):
            if isList(expr) and expr[0] == 'update' and isList(expr[2]):
                rec1 = replaceUpdate(expr[1])
                rec3 = replaceUpdate(expr[3])
                ret = ['store', rec1]
                ret.extend(expr[2])
                ret.append(rec3)
                return ret
            elif isList(expr):
                return [ replaceUpdate(e) for e in expr ]
            else:
                return expr
        insertSelect(body)
        body = replaceUpdate(body)
        ret = ["define-fun", fname, args, resultType, z3_translate(body)]
    else:
        ret = []
    return ret

def z3_define_type(expr, arrays):
    ret = []
    if len(expr) == 3 and isinstance(expr[2], pyparsing.ParseResults) and expr[2][0] == 'scalar':
        typeName = expr[1]
        ret.append(["declare-datatypes", [' '], [[typeName] + expr[2][1:]]])
        #for constName in expr[2][1:]:
        #    ret.append(["declare-fun", constName, [], typeName])
    if len(expr) == 3 and isinstance(expr[2], pyparsing.ParseResults) and expr[2][0] == '->':
        typeName = expr[1]
        ret.append(["define-sort", typeName, [], ["Array"] + expr[2][1:]])
        arrays.append(typeName)
    elif len(expr[2]) == 3 and isinstance(expr[2], str):
        typeName = expr[1]
        target = expr[2]
        ret.append(["define-sort", typeName, [], target])
    elif len(expr) == 3 and isinstance(expr[2], str):
        typeName = expr[1]
        target = expr[2]
        ret.append(["define-sort", typeName, [], target])
    elif len(expr) == 3 and not isinstance(expr[2], str) and len(expr[2]) == 2\
            and expr[2][0] == 'bitvector':
        typeName = expr[1]
        target = ['_', 'BitVec', expr[2][1]]
        ret.append(["define-sort", typeName, [], target])
    return ret

def z3_translate(expr):
    if isList(expr):
        if len(expr) > 0 and expr[0] == 'bit':
            assert len(expr) == 3
            return '(ite (= ((_ extract {0} {0}) x) #b1) true false)'.format(
                expr[2])
        if len(expr) > 0 and expr[0] == 'bool-to-bv':
            bv_val = map(lambda x: '1' if x == "true" else '0', expr[1:])
            return '#b{0}'.format(''.join(bv_val))
        #print expr
        if len(expr) > 0 and isinstance(expr[0], str) and \
                expr[0].startswith('bv-'):
            if expr[0] == 'bv-gt':
                return ['bvugt'] + z3_translate(expr[1:])
            return [expr[0].replace('-', '')] + z3_translate(expr[1:])
        if len(expr) > 0 and isinstance(expr[0], str) and \
                expr[0].startswith('mk-bv'):
            assert len(expr) == 3
            bitwidth = expr[1]
            dec_val = expr[2]
            assert re.match('[0-9]+', str(dec_val))
            bin_val = bin(dec_val)
            return  '#b' + '0'*(bitwidth-(len(bin_val)-2)) + bin_val[2:]
        return [z3_translate(e) for e in expr]
    else:
        return expr


def z3_capitalize(expr):
    if expr in ['bool', 'int', 'real']:
        return expr.capitalize()
    elif isList(expr):
        return [ z3_capitalize(e) for e in expr ]
    else:
        return expr
