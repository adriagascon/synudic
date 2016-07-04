import re

MAX_NUM_BLK_INPUTS = 3
LINE_TYPE_NAME = 'lineType'
FUNC_TYPE_NAME = 'funcType'
MAX_NUM_BLK_INPUTS = 3


def get_block_line_name(block_name, line_num):
    return '{0}_{1}'.format(block_name, line_num + 1)


def get_block_unused_arg_line_name(block_name, line_num, arg_num):
    return '{0}_{1}_unused_arg_{2}'.format(
        block_name, int(line_num) + 1, arg_num)


def get_unused_arg_line_from_line_name(line_name, arg_num):
    m = re.match('(\S+)_([0-9]+)', line_name)
    assert m, line_name
    block_name = m.group(1)
    line_num = m.group(2)
    return get_block_unused_arg_line_name(
        block_name, int(line_num) - 1, arg_num)


def get_block_from_line_name(line_name):
    m = re.match('(\S+)_[0-9]+', line_name)
    assert m, line_name
    return m.group(1)


def get_block_input_name(block_name, line_num, input_num):
    return '{0}_arg_{1}'.format(
        get_block_line_name(block_name, line_num), input_num)


def get_block_input_line_name(block_name, line_num, input_num):
    return '{0}_arg_{1}'.format(
        get_block_line_name(block_name, line_num), input_num)


def get_block_input_val_name(block_name, line_num, input_num):
    return '{0}_arg_val_{1}'.format(
        get_block_line_name(block_name, line_num), input_num)


def get_block_interp_val_name(block_name, interp_name, line_num):
    return '{0}_{1}'.format(
        get_block_line_name(block_name, line_num), interp_name)


def get_block_dom_val_name(block_name, line_num):
    return '{0}_dom'.format(get_block_line_name(block_name, line_num))


def get_block_typ_val_name(block_name, line_num):
    return '{0}_typ'.format(get_block_line_name(block_name, line_num))


def get_line_interp_val_name(interp_name, line_name):
    return '{0}_{1}'.format(line_name, interp_name)


def get_line_typ_val_name(line_name):
    return '{0}_typ'.format(line_name)


def get_line_dom_val_name(line_name):
    return '{0}_dom'.format(line_name)


def get_block_function_name(block_name, line_num):
    return '{0}_func'.format(get_block_line_name(block_name, line_num))
